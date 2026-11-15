#!/bin/bash
# Soundness probes for the comparator-call wrapper and the ptr::copy wrapper (2026-10-31). Each probe is
# put into a scratch crate (original/lib.rs as crate root; smallsort.rs = the pinned comparator model in a
# ghost block + the comparator call wrapper + the ptr::copy wrapper + the probe) and VeriFast is run
# (memory-capped scope, timeout inside it). Expected:
#   call.rs             FAIL (No such function: is_less_call)      -- the free-argument lemma is gone
#   rcall.rs            FAIL at `assert false`                     -- repeated/swapped wrapper calls
#   rcall_nomodel.rs    FAIL at `assert false`                     -- no model: results unconstrained
#   rcall_pos.rs        0 errors                                   -- the wrapper's facts are usable
#   copy1_raw_far.rs    0 errors for `ens false`                   -- Bug A through VeriFast's ptr::copy spec
#   copy1_far.rs, copy1_far_neg.rs  FAIL (bound)                   -- the same pattern against the wrapper
#   copy1_ok.rs         0 errors                                   -- offsets 1, 0, -1 and disjoint (none)
here="$(cd "$(dirname "$0")" && pwd)"
B="$(cd "$here/../.." && pwd)"
VF=${VERIFAST_HOME:-$HOME/.verifast/toolchains/verifast-26.10}/bin/verifast
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cp "$B/original/lib.rs" "$work/lib.rs"; cp "$B/trusted/std_extra.rsspec" "$work/"
copyw=$(python3 - "$B/trusted/std_wrappers.rs" <<'PY'
import sys
s = open(sys.argv[1]).read()
print(s[s.index('// `ptr::copy(src, dst, 1)`'):s.index('// ===== END TRUSTED STD WRAPPERS')])
PY
)
one() {  # expect probe
  { echo 'use crate::ptr;'; echo '/*@'; cat "$B/trusted/comparator_model.rs"; echo '@*/';
    cat "$B/trusted/comparator_call_wrapper.rs"; echo "$copyw"; cat "$here/$2"; } > "$work/smallsort.rs"
  r=$(systemd-run --user --scope --quiet -p MemoryMax=5G -p MemorySwapMax=0 "$(command -v timeout)" 600 "$VF" \
        -rustc_args "--edition 2024" -skip_specless_fns -allow_assume -allow_dead_code \
        -extern_spec "std=$work/std_extra.rsspec" "$work/lib.rs" 2>&1 | grep -E '^0 errors found|error:' | head -1 | sed "s|$work/||")
  if { [[ $1 == OK ]] && [[ $r == "0 errors found"* ]]; } || { [[ $1 == FAIL ]] && [[ $r == *error:* ]]; }; then s=as-expected; else s=UNEXPECTED; fi
  echo "$s  expect $1  $2: $r"
}
one FAIL call.rs
one FAIL rcall.rs
one FAIL rcall_nomodel.rs
one OK   rcall_pos.rs
one OK   copy1_raw_far.rs
one FAIL copy1_far.rs
one FAIL copy1_far_neg.rs
one OK   copy1_ok.rs
