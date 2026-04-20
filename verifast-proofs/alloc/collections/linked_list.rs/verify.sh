set -e -x

export VFVERSION=26.01

verifast -rustc_args "--edition 2021 --cfg test" -skip_specless_fns -ignore_unwind_paths -allow_assume verified/lib.rs
refinement-checker --rustc-args "--edition 2021 --cfg test" original/lib.rs verified/lib.rs > /dev/null
if ! diff original/linked_list.rs ../../../../library/alloc/src/collections/linked_list.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi
