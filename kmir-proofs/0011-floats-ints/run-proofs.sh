#!/bin/bash
# Run KMIR proofs for Challenge 11: Safety of Methods for Numeric Primitive Types
# https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html
#
# Usage: ./run-proofs.sh              # run passing proofs
#        ./run-proofs.sh --negative   # run negative proofs (expect failure)

set -eux

if ! command -v kmir &> /dev/null; then
    echo "ERROR: kmir not found on PATH"
    exit 2
fi

DIR=$(realpath "$(dirname "$0")")
cd "$DIR"

if [ "${1:-}" = "--negative" ]; then
    PROOF_DIR=proofs-fail
    rm -rf "$PROOF_DIR"

    # Negative tests: proofs should FAIL as KMIR detects UB.
    # If any proof unexpectedly passes, the script exits non-zero.
    printf '%s\n' \
      "kmir prove unchecked_add-fail.rs --terminate-on-thunk --fail-fast --proof-dir $PROOF_DIR --start-symbol unchecked_add_u8,unchecked_add_u16,unchecked_add_u32,unchecked_add_u64,unchecked_add_u128,unchecked_add_i8,unchecked_add_i16,unchecked_add_i32,unchecked_add_i64,unchecked_add_i128" \
      "kmir prove unchecked_sub-fail.rs --terminate-on-thunk --fail-fast --proof-dir $PROOF_DIR --start-symbol unchecked_sub_u8,unchecked_sub_u16,unchecked_sub_u32,unchecked_sub_u64,unchecked_sub_u128,unchecked_sub_i8,unchecked_sub_i16,unchecked_sub_i32,unchecked_sub_i64,unchecked_sub_i128" \
      "kmir prove unchecked_mul-fail.rs --terminate-on-thunk --fail-fast --proof-dir $PROOF_DIR --start-symbol unchecked_mul_u8,unchecked_mul_u16,unchecked_mul_u32,unchecked_mul_u64,unchecked_mul_u128,unchecked_mul_i8,unchecked_mul_i16,unchecked_mul_i32,unchecked_mul_i64,unchecked_mul_i128" \
      "kmir prove unchecked_shl-fail.rs --terminate-on-thunk --fail-fast --proof-dir $PROOF_DIR --start-symbol unchecked_shl_u8,unchecked_shl_u16,unchecked_shl_u32,unchecked_shl_u64,unchecked_shl_u128,unchecked_shl_i8,unchecked_shl_i16,unchecked_shl_i32,unchecked_shl_i64,unchecked_shl_i128" \
      "kmir prove unchecked_shr-fail.rs --terminate-on-thunk --fail-fast --proof-dir $PROOF_DIR --start-symbol unchecked_shr_u8,unchecked_shr_u16,unchecked_shr_u32,unchecked_shr_u64,unchecked_shr_u128,unchecked_shr_i8,unchecked_shr_i16,unchecked_shr_i32,unchecked_shr_i64,unchecked_shr_i128" \
      "kmir prove unchecked_neg-fail.rs --terminate-on-thunk --fail-fast --proof-dir $PROOF_DIR --start-symbol unchecked_neg_i8,unchecked_neg_i16,unchecked_neg_i32,unchecked_neg_i64,unchecked_neg_i128" \
      | xargs -P 2 -I{} bash -xc 'if {}; then echo "ERROR: expected failure but passed: {}"; exit 1; fi'
else
    PROOF_DIR=proofs
    rm -rf "$PROOF_DIR"

    # Positive tests: proofs should PASS
    printf '%s\n' \
      "kmir prove carrying_mul.rs  --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol carrying_mul_u8,carrying_mul_u16,carrying_mul_u32,carrying_mul_u64" \
      "kmir prove unchecked_add.rs --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol unchecked_add_u8,unchecked_add_u16,unchecked_add_u32,unchecked_add_u64,unchecked_add_u128,unchecked_add_i8,unchecked_add_i16,unchecked_add_i32,unchecked_add_i64,unchecked_add_i128" \
      "kmir prove widening_mul.rs  --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol widening_mul_u8,widening_mul_u16,widening_mul_u32,widening_mul_u64" \
      "kmir prove unchecked_sub.rs --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol unchecked_sub_u8,unchecked_sub_u16,unchecked_sub_u32,unchecked_sub_u64,unchecked_sub_u128,unchecked_sub_i8,unchecked_sub_i16,unchecked_sub_i32,unchecked_sub_i64,unchecked_sub_i128" \
      "kmir prove unchecked_neg.rs --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol unchecked_neg_i8,unchecked_neg_i16,unchecked_neg_i32,unchecked_neg_i64,unchecked_neg_i128" \
      "kmir prove unchecked_mul.rs --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol unchecked_mul_u8,unchecked_mul_u16,unchecked_mul_u32,unchecked_mul_u64,unchecked_mul_u128,unchecked_mul_i8,unchecked_mul_i16,unchecked_mul_i32,unchecked_mul_i64,unchecked_mul_i128" \
      "kmir prove unchecked_shl.rs --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol unchecked_shl_u8,unchecked_shl_u16,unchecked_shl_u32,unchecked_shl_u64,unchecked_shl_u128,unchecked_shl_i8,unchecked_shl_i16,unchecked_shl_i32,unchecked_shl_i64,unchecked_shl_i128" \
      "kmir prove unchecked_shr.rs --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol unchecked_shr_u8,unchecked_shr_u16,unchecked_shr_u32,unchecked_shr_u64,unchecked_shr_u128,unchecked_shr_i8,unchecked_shr_i16,unchecked_shr_i32,unchecked_shr_i64,unchecked_shr_i128" \
      "kmir prove wrapping_shl.rs  --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol wrapping_shl_u8,wrapping_shl_u16,wrapping_shl_u32,wrapping_shl_u64,wrapping_shl_u128,wrapping_shl_i8,wrapping_shl_i16,wrapping_shl_i32,wrapping_shl_i64,wrapping_shl_i128" \
      "kmir prove wrapping_shr.rs  --terminate-on-thunk --proof-dir $PROOF_DIR --start-symbol wrapping_shr_u8,wrapping_shr_u16,wrapping_shr_u32,wrapping_shr_u64,wrapping_shr_u128,wrapping_shr_i8,wrapping_shr_i16,wrapping_shr_i32,wrapping_shr_i64,wrapping_shr_i128" \
      | xargs -P 2 -I{} bash -xc '{}'
fi
