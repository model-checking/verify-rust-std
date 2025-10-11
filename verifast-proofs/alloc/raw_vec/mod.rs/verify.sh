set -e -x

export VFVERSION=25.07

verifast -skip_specless_fns -ignore_unwind_paths -allow_assume verified/lib.rs
refinement-checker with-directives/lib.rs verified/lib.rs > /dev/null
refinement-checker --ignore-directives original/lib.rs with-directives/lib.rs > /dev/null
if ! diff original/raw_vec.rs ../../../../library/alloc/src/raw_vec/mod.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi
