#!/bin/bash
# Run KMIR passing proofs for Challenge 11: Safety of Methods for Numeric Primitive Types
# https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html

set -eu

if ! command -v kmir &> /dev/null; then
    echo "ERROR: kmir not found on PATH"
    exit 2
fi

DIR=$(realpath "$(dirname "$0")")
cd "$DIR"

PROOF_DIR=proofs
FAILED_PROOFS=""

# Mapping of FILENAME -> START_SYMBOLS
declare -A FILE_SYMBOLS
FILE_SYMBOLS=(
    [unchecked_add]="unchecked_add_u8 unchecked_add_u16 unchecked_add_u32 unchecked_add_u64 unchecked_add_u128 unchecked_add_i8 unchecked_add_i16 unchecked_add_i32 unchecked_add_i64 unchecked_add_i128"
    [unchecked_sub]="unchecked_sub_u8 unchecked_sub_u16 unchecked_sub_u32 unchecked_sub_u64 unchecked_sub_u128 unchecked_sub_i8 unchecked_sub_i16 unchecked_sub_i32 unchecked_sub_i64 unchecked_sub_i128"
    [unchecked_mul]="unchecked_mul_u8 unchecked_mul_u16 unchecked_mul_u32 unchecked_mul_u64 unchecked_mul_u128 unchecked_mul_i8 unchecked_mul_i16 unchecked_mul_i32 unchecked_mul_i64 unchecked_mul_i128"
    [unchecked_shl]="unchecked_shl_u8 unchecked_shl_u16 unchecked_shl_u32 unchecked_shl_u64 unchecked_shl_u128 unchecked_shl_i8 unchecked_shl_i16 unchecked_shl_i32 unchecked_shl_i64 unchecked_shl_i128"
    [unchecked_shr]="unchecked_shr_u8 unchecked_shr_u16 unchecked_shr_u32 unchecked_shr_u64 unchecked_shr_u128 unchecked_shr_i8 unchecked_shr_i16 unchecked_shr_i32 unchecked_shr_i64 unchecked_shr_i128"
    [unchecked_neg]="unchecked_neg_i8 unchecked_neg_i16 unchecked_neg_i32 unchecked_neg_i64 unchecked_neg_i128"
    [wrapping_shl]="wrapping_shl_u8 wrapping_shl_u16 wrapping_shl_u32 wrapping_shl_u64 wrapping_shl_u128 wrapping_shl_i8 wrapping_shl_i16 wrapping_shl_i32 wrapping_shl_i64 wrapping_shl_i128"
    [wrapping_shr]="wrapping_shr_u8 wrapping_shr_u16 wrapping_shr_u32 wrapping_shr_u64 wrapping_shr_u128 wrapping_shr_i8 wrapping_shr_i16 wrapping_shr_i32 wrapping_shr_i64 wrapping_shr_i128"
    [widening_mul]="widening_mul_u8 widening_mul_u16 widening_mul_u32 widening_mul_u64"
    [carrying_mul]="carrying_mul_u8 carrying_mul_u16 carrying_mul_u32 carrying_mul_u64"
)

for file in "${!FILE_SYMBOLS[@]}"; do
    rs_file="${file}.rs"
    if [ ! -f "$rs_file" ]; then
        echo "ERROR: $rs_file not found"
        FAILED_PROOFS="${FAILED_PROOFS} ${file}(missing)"
        continue
    fi

    symbols="${FILE_SYMBOLS[$file]}"
    echo "========================================="
    echo "File: $rs_file"
    echo "========================================="

    for sym in $symbols; do
        proof_id="${file}.${sym}"
        echo "-----------------------------------------"
        echo "Proving: ${proof_id}"
        echo "-----------------------------------------"

        if ! kmir prove --start-symbol "$sym" --terminate-on-thunk --proof-dir "$PROOF_DIR" --reload "$rs_file"; then
            FAILED_PROOFS="${FAILED_PROOFS} ${proof_id}"
        fi

        kmir show --proof-dir "$PROOF_DIR" "${proof_id}" || true
    done
done

echo ""
echo "========================================="
echo "SUMMARY"
echo "========================================="

if [ -n "$FAILED_PROOFS" ]; then
    echo ""
    echo "FAILED:"
    for f in $FAILED_PROOFS; do
        echo "  - $f"
    done
    echo ""
    echo -e "\033[31m=========================================\033[0m"
    echo -e "\033[31mSOME PROOFS FAILED\033[0m"
    echo -e "\033[31m=========================================\033[0m"
    exit 1
fi

echo ""
echo -e "\033[32m=========================================\033[0m"
echo -e "\033[32mALL PROOFS PASSED\033[0m"
echo -e "\033[32m=========================================\033[0m"
