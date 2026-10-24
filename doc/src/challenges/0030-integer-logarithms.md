# Challenge 30: Safety and Correctness of Integer Logarithms

- **Status:** Open
- **Solution:** Not yet submitted.
- **Tracking Issue:** [#728](https://github.com/model-checking/verify-rust-std/issues/728)
- **Reward:** TBD

-------------------

## Goal

Verify the safety and correctness of `ilog10`, `ilog2`, and their checked variants in `core::num`.

## Motivation

Decimal logarithms make unsafe promises about arithmetic result bounds; binary logarithms
call intrinsics that require nonzero inputs. Violating either requirement is undefined
behavior, even though the public APIs are safe.

## Description

| Function | Integer Types | Location |
|---------|---------------|----------|
| `ilog10`, `checked_ilog10`, `ilog2`, `checked_ilog2` | All signed and unsigned integer types | [int_macros.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/int_macros.rs), [uint_macros.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/uint_macros.rs) |
| `NonZero<T>::ilog2` | All unsigned integer types | [nonzero.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/nonzero.rs) |
| `u8_impl`, `u16_impl`, `u32_impl`, `u64_impl`, `u128_impl`, `less_than_5` | Each helper's documented input domain | [int_log10.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/imp/int_log10.rs) |
| Internal wrappers `u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128` | Corresponding integer types | [int_log10.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/imp/int_log10.rs) |

- **Signed:** `i8`, `i16`, `i32`, `i64`, `i128`, `isize`.
- **Unsigned:** `u8`, `u16`, `u32`, `u64`, `u128`, `usize`.

Arbitrary-base `ilog` is excluded: its general calculation contains no direct unsafe
operations, and its unsafe dependencies overlap with the implementations above.

This extends [Challenge 11](0011-floats-ints.md) to logarithm methods, which are not
in that challenge's target list. NonZero constructor verification belongs to
[Challenge 12](0012-nonzero.md) and is not repeated here.

### Assumptions

- Existing verified NonZero contracts and documented layout guarantees may be reused.

### Success Criteria

Cover every input to the public methods and each internal helper's documented input domain:

- Verify the safety conditions of all unsafe operations, including result-bound assertions and nonzero-input requirements.
- For positive input `n`, prove the result is the greatest nonnegative integer `r` with `b^r <= n`, where `b` is 2 or 10 and powers are interpreted mathematically.
- Prove checked methods return `None` for zero or negative inputs, and `ilog2` and `ilog10` panic on those inputs.
- Prove the calculations do not overflow or underflow.
- The proofs must run automatically in the repository's CI without breaking existing verification workflows.

All proofs must automatically ensure the absence of the following
[undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

- Invoking undefined behavior through compiler intrinsics.
- Reading from uninitialized memory.
- Mutating immutable bytes.
- Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the
[challenge book](../general-rules.md) in addition to the ones listed above.
