set -e -x

export VFVERSION=25.07

! verifast -rustc_args "--edition 2021 --cfg test" -skip_specless_fns verified/lib.rs
! refinement-checker --rustc-args "--edition 2021 --cfg test" original/lib.rs verified/lib.rs
if ! diff ../../../../library/alloc/src/collections/linked_list.rs original/linked_list.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi
