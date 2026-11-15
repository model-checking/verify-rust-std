#!/usr/bin/env python3
"""Reject ghost constructs that let a solver derive `false` in VeriFast 26.10 without any axiom.

Usage: ghost_gate.py CRATE_DIR       exit 1 (with a message) if a forbidden construct occurs outside the
                                     benchmark's marked `// ===== BEGIN ... =====` / `// ===== END ... =====`
                                     blocks (those are diffed against pinned masters by verify.sh).

Forbidden: `pointer_ctor` and `pointer_metadata_ctor`. VeriFast assumes that a lemma parameter `s: *T`
(`T: Sized`) has metadata `pointer_metadata_none` inside the lemma body, but does not check it at the call,
so ghost code passing `pointer_ctor(.., pointer_metadata_ctor(1)) as *u8` derives `false` (probe:
`lem thin_meta_none<T>(s: *T) req (s as pointer).metadata != pointer_metadata_none; ens false; {}`).
A real cast (`fat as *u8`) strips the metadata and is not affected.
"""
import os
import re
import sys

MARKER = re.compile(r'^\s*// ===== (BEGIN|END) ')
FORBIDDEN = re.compile(r'\b(pointer_ctor|pointer_metadata_ctor)\b')

crate = sys.argv[1]
bad = []
for root, _, files in os.walk(crate):
    for f in sorted(files):
        if not f.endswith(('.rs', '.rsspec')):
            continue
        p = os.path.join(root, f)
        inside = False
        for i, line in enumerate(open(p, errors='replace'), 1):
            m = MARKER.match(line)
            if m:
                inside = m.group(1) == 'BEGIN'
                continue
            if not inside and FORBIDDEN.search(line):
                bad.append(f'{os.path.relpath(p, crate)}:{i}')
if bad:
    sys.exit('error: forbidden ghost construct (pointer_ctor / pointer_metadata_ctor) outside the trusted '
             'blocks, which lets VeriFast 26.10 derive false: ' + ', '.join(bad[:5]))
