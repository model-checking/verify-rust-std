#!/bin/bash
# Consistency check: in a copy of each crate, `//@ assert false;` is inserted as the first statement of every
# body whose `{` line directly follows a spec outside the marked trusted blocks (the entry function), and
# VeriFast must then FAIL at that line ("CONSISTENT"); "0 errors found" would mean the entry's context is
# contradictory. Memory-capped scope, timeout inside it. Log: consistency.log.
B="$(cd "$(dirname "$0")/.." && pwd)"
VF=${VERIFAST_HOME:-$HOME/.verifast/toolchains/verifast-26.10}/bin/verifast
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
for c in $(cd "$B" && find targets -name lib.rs -printf '%h\n' | sort); do
  rm -rf "$work/c"; cp -a "$B/$c" "$work/c"
  lines=$(python3 - "$work/c/smallsort.rs" <<'PY'
import re, sys
p = sys.argv[1]; L = open(p).read().split('\n'); out = []; inside = False; hits = []
for i, l in enumerate(L):
    m = re.match(r'^// ===== (BEGIN|END) ', l)
    if m: inside = m.group(1) == 'BEGIN'
    out.append(l)
    if not inside and i and l.strip() == '{':
        prev = L[i-1].strip()
        if prev.endswith('@*/') or prev.startswith('//@'):
            out.append(re.match(r'\s*', l).group(0) + '    //@ assert false;'); hits.append(len(out))
open(p, 'w').write('\n'.join(out)); print(' '.join(map(str, hits)))
PY
)
  r=$(cd "$work/c" && systemd-run --user --scope --quiet -p MemoryMax=5G -p MemorySwapMax=0 "$(command -v timeout)" 900 "$VF" \
        -rustc_args "--edition 2024" -skip_specless_fns -allow_assume -allow_dead_code -ignore_unwind_paths -ignore_ref_creation -extern_spec std=std_extra.rsspec lib.rs 2>&1 |
      grep -E '^0 errors found|error:' | head -1)
  ok=0; for n in $lines; do [[ $r == "smallsort.rs($n,"*"Cannot prove false"* ]] && ok=1; done
  if [[ $ok == 1 ]]; then echo "CONSISTENT    $c: assert false at line $lines fails: ${r#*error: }"
  elif [[ $r == "0 errors found"* ]]; then echo "INCONSISTENT  $c: $r"
  else echo "OTHER         $c (assert at $lines): $r"; fi
done
