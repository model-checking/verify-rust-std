#! /bin/bash

set -eu

DIR=$(realpath $(dirname $0))

cd $DIR

start_symbols=$(sed -n -e 's,// @kmir prove-rs: ,,p' unchecked_arithmetic.rs)
# By default: unchecked_add_i32 unchecked_sub_usize unchecked_mul_isize
# See `main` in program. start symbols need to be reachable from `main`.

echo "Running proofs for start symbols ${start_symbols} in unchecked_arithmetic.rs"

for sym in ${start_symbols}; do
    echo "#########################################"
    echo "Running proof for $sym"
    echo "#########################################"

    kmir prove-rs --start-symbol $sym --verbose --proof-dir proofs --reload unchecked_arithmetic.rs

    echo "#########################################"
    echo "Proof finished, with the following graph:"
    echo "#########################################"
    kmir show --proof-dir proofs unchecked_arithmetic.${sym} --no-full-printer

    echo "#########################################"
done
