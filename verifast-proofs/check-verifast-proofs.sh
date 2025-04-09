set -e -x

cd alloc
  cd collections
    cd linked_list.rs
      verifast -rustc_args "--edition 2021 --cfg test" -skip_specless_fns verified/lib.rs
      refinement-checker --rustc-args "--edition 2021 --cfg test" original/lib.rs verified/lib.rs > /dev/null
      if ! diff original/linked_list.rs ../../../../library/alloc/src/collections/linked_list.rs; then
        echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please run verifast-proofs/patch-verifast-proofs.sh to update them."
        false
      fi
    cd ..
  cd ..
cd ..
