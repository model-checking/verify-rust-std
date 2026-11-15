#!/usr/bin/env python3
"""Pin the specifications a benchmark gives its target crates, so a solver can neither weaken, strengthen
(e.g. `req false` on an unsafe entry) nor remove them (without a spec, `-skip_specless_fns` would skip the
entry silently).

Usage (from the benchmark root):
  entry_spec_pin.py record CRATE_DIR...   run once on freshly generated crates; writes spec/entry_spec_pins.json
  entry_spec_pin.py check CRATE_DIR       exit 1 (with a message) unless every recorded spec is still there

A pinned spec is an annotation block (`//@` lines, `/*@ .. @*/` blocks) outside the marked
`// ===== BEGIN ... =====` / `// ===== END ... =====` blocks (those are diffed separately) that contains
`req`, does not define a `lem`/`pred`, and is directly followed by a line starting a body (`{`). It is
identified by its function's signature (the code from the last line containing `fn` up to the spec, with
whitespace and comments removed) and the number of earlier occurrences of that signature text in the file's
code, so that reformatting does not matter and identical signatures in different impls are told apart.
A solver may add ghost code and callee specs anywhere else.
"""
import json
import os
import re
import sys

MASTER = 'spec/entry_spec_pins.json'
MARKER = re.compile(r'^// ===== (BEGIN|END) ')
FN = re.compile(r'\bfn\b')


def strip_code(line):
    line = re.sub(r'/\*.*?\*/', '', line)
    return re.sub(r'\s+', '', line.split('//')[0])


def specs(path):
    out = []
    lines = open(path, errors='replace').read().split('\n')
    stream = ''
    sig_start = None
    ann = []
    in_marked = in_ghost = False
    for line in lines:
        s = line.strip()
        m = MARKER.match(s)
        if m:
            in_marked = m.group(1) == 'BEGIN'
            continue
        if in_marked:
            continue
        if in_ghost:
            ann.append(line)
            in_ghost = '@*/' not in s
            continue
        if s.startswith('/*@'):
            ann.append(line)
            in_ghost = '@*/' not in s
            continue
        if s.startswith('//@'):
            ann.append(line)
            continue
        code = strip_code(line)
        if not code:
            continue
        if ann:
            a = '\n'.join(x.strip() for x in ann)
            if (code.startswith('{') and re.search(r'\breq\b', a) and not re.search(r'\b(lem|pred)\b', a)
                    and sig_start is not None):
                sig = stream[sig_start:]
                out.append({'sig': sig, 'occ': stream[:sig_start].count(sig), 'spec': a})
            ann = []
        if FN.search(line.split('//')[0]):
            sig_start = len(stream)
        stream += code
    return out


def crate_specs(crate):
    res = {}
    for root, _, files in os.walk(crate):
        for f in sorted(files):
            if f.endswith('.rs'):
                p = os.path.join(root, f)
                found = specs(p)
                if found:
                    res[os.path.relpath(p, crate)] = found
    return res


def key(crate):
    return os.path.relpath(os.path.realpath(crate), os.path.realpath('.'))


if __name__ == '__main__':
    mode, crates = sys.argv[1], sys.argv[2:]
    if mode == 'record':
        master = json.load(open(MASTER)) if os.path.exists(MASTER) else {}
        for c in crates:
            master[key(c)] = crate_specs(c)
        os.makedirs(os.path.dirname(MASTER), exist_ok=True)
        json.dump(master, open(MASTER, 'w'), indent=1, sort_keys=True)
        print(f'recorded {len(crates)} crates, '
              f'{sum(len(v) for c in crates for v in master[key(c)].values())} specs')
    elif mode == 'check':
        crate = crates[0]
        master = json.load(open(MASTER))
        k = key(crate)
        if k not in master:
            sys.exit(f'error: no pinned entry specs for {k} in {MASTER}')
        have = crate_specs(crate)
        for f, pins in master[k].items():
            got = have.get(f, [])
            for p in pins:
                if not any(g['sig'] == p['sig'] and g['occ'] == p['occ'] and g['spec'] == p['spec'] for g in got):
                    sys.exit(f'error: the pinned specification of `{p["sig"][:80]}` in {k}/{f} '
                             f'was changed or removed ({MASTER})')
    else:
        sys.exit(__doc__)
