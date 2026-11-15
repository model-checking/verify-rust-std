# stub_fns.py FILE NAME...: marks the (spec'd) functions NAME `assume_correct` (speed-up for probes of other
# functions, which are verified on their own). Functions that are absent or have no spec are skipped.
import sys, re
f = sys.argv[1]
s = open(f).read()
for name in sys.argv[2:]:
    m = re.search(r'^[^\n]*\bfn ' + name + r'\b[<(]', s, re.M)
    if not m:
        continue
    b = s.index('\n{\n', m.start())
    sig_end = re.search(r'\{\n', s[m.start():])            # first opening brace after the signature
    if m.start() + sig_end.start() < b or ('@*/' not in s[m.start():b] and '//@' not in s[m.start():b]):
        continue                                            # `... ) {` on the signature line: no spec
    s = s[:b + 1] + '//@ assume_correct\n' + s[b + 1:]
open(f, 'w').write(s)
