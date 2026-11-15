#!/usr/bin/env python3
"""Reject direct calls of the `ptr::copy` family outside the benchmark's marked trusted blocks.

Usage: copy_gate.py CRATE_DIR       exit 1 (with a message) if a `.rs` file of the crate calls or names
                                    `ptr::copy`, `intrinsics::copy`, `copy::<..>(..)`, `copy(..)`,
                                    `.copy_to(..)` or `.copy_from(..)`, or imports
                                    one of these names with `use`, outside the marked
                                    `// ===== BEGIN ... =====` / `// ===== END ... =====` blocks.

Why: VeriFast 26.10's prelude spec of `std::ptr::copy` (std/lib.rsspec) does not bound `offset` in its
`some(offset)` branch, so at a real call whose regions are disjoint and more than `count` elements apart,
ghost code can choose that branch and derive `false`. Every such call of the challenge code therefore goes
through a trusted `ptr_copy..__VeriFast_wrapper` (inside a marked block, pinned by verify.sh) whose spec adds
`-count <= offset <= count`. refinement-checker accepts the original call in place of the wrapper call too,
so this gate keeps a solver from reverting a call site to the unbounded prelude spec.
Plain `//` comments are ignored; ghost annotations (`//@`, `/*@ .. @*/`) and code are checked.
"""
import os
import re
import sys

MARKER = re.compile(r'^\s*// ===== (BEGIN|END) ')
FORBIDDEN = re.compile(r'\b(?:ptr|intrinsics)\s*::\s*copy\b'
                       r'|\b(?:copy|copy_to|copy_from)\s*(?:::\s*<[^()]*>\s*)?\('
                       r'|^\s*(?:pub(?:\([^)]*\))?\s+)?use\b.*\b(?:copy|copy_to|copy_from)\b')

crate = sys.argv[1]
bad = []
for root, _, files in os.walk(crate):
    for f in sorted(files):
        if not f.endswith('.rs'):
            continue
        p = os.path.join(root, f)
        inside = False
        in_block_comment = False
        for i, line in enumerate(open(p, errors='replace'), 1):
            m = MARKER.match(line)
            if m:
                inside = m.group(1) == 'BEGIN'
                continue
            if inside:
                continue
            code = line
            # drop plain `//` comments (keep `//@` ghost lines) and plain `/* .. */` comments
            code = re.sub(r'/\*(?!@).*?\*/', '', code)
            if in_block_comment:
                if '*/' in code:
                    code = code.split('*/', 1)[1]
                    in_block_comment = False
                else:
                    continue
            if re.search(r'/\*(?!@)', code):
                code = re.split(r'/\*(?!@)', code, 1)[0]
                in_block_comment = True
            idx = [mm.start() for mm in re.finditer(r'//(?!@)', code)]
            if idx:
                code = code[:idx[0]]
            if FORBIDDEN.search(code):
                bad.append(f'{os.path.relpath(p, crate)}:{i}')
if bad:
    sys.exit('error: `ptr::copy`-family call outside the trusted blocks (use the trusted '
             'ptr_copy..__VeriFast_wrapper; the prelude spec of ptr::copy lets VeriFast 26.10 derive false): '
             + ', '.join(bad[:5]))
