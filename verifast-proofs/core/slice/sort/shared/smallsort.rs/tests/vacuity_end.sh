#!/bin/bash
# Vacuity probe for the proofs: for each function NAME given, in a copy of crate DIR, `//@ assert false;` is
# inserted as the last statement of NAME's body; VeriFast must then fail there with "Cannot prove false"
# ("REACHABLE": some path reaches the end of the body). "0 errors found" would mean every path to the end
# is infeasible (a vacuous proof). Usage: [STUB="f g"] vacuity_end.sh DIR NAME...
B="$(cd "$(dirname "$0")/.." && pwd)"
VF=${VERIFAST_HOME:-$HOME/.verifast/toolchains/verifast-26.10}/bin/verifast
dir=$1; shift
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
for name in "$@"; do
  rm -rf "$work/c"; cp -a "$B/$dir" "$work/c"
  # STUB="f g ..": functions (other than NAME, verified on their own) marked assume_correct to save time.
  stubs=$(for s in $STUB; do [[ $s != "$name" ]] && echo -n "$s "; done)
  [[ -n $stubs ]] && python3 "$B/tests/stub_fns.py" "$work/c/smallsort.rs" $stubs
  line=$(python3 - "$work/c/smallsort.rs" "$name" <<'PY'
import re, sys
p, name = sys.argv[1], sys.argv[2]
s = open(p).read()
m = re.search(r'^[^\n]*\bfn ' + name + r'\b[<(]', s, re.M)
b = s.index('\n{\n', m.start()) + 3
e = s.index('\n}\n', b)          # the function's closing brace (column 0)
last = s.rfind('\n', 0, e)       # a tail expression (e.g. `(left_src, right_src, dst)`) stays last
tail = s[last + 1:e].strip()
if tail and not tail.endswith((';', '}')) and not tail.startswith('//'):
    e = last
s = s[:e] + '\n    //@ assert false;' + s[e:]
open(p, 'w').write(s)
print(s[:e].count('\n') + 2)
PY
)
  r=$(cd "$work/c" && systemd-run --user --scope --quiet -p MemoryMax=${VF_MEM:-6G} -p MemorySwapMax=0 "$(command -v timeout)" ${VF_TIMEOUT:-5400} "$VF" \
        -rustc_args "--edition 2024" -skip_specless_fns -allow_assume -allow_dead_code -ignore_unwind_paths -ignore_ref_creation \
        -extern_spec std=std_extra.rsspec lib.rs 2>&1 | grep -E '^0 errors found|error:' | head -1)
  if [[ $r == "smallsort.rs($line,"*"Cannot prove false"* ]]; then echo "REACHABLE   $dir $name (line $line)"
  elif [[ $r == "0 errors found"* ]]; then echo "VACUOUS     $dir $name: $r"
  else echo "OTHER       $dir $name: $r"; fi
done
