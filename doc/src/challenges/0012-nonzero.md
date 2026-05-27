# Challenge 12: Safety of `NonZero`

- **Status:** Open
- **Tracking Issue:** [#71](https://github.com/model-checking/verify-rust-std/issues/71)
- **Start date:** *2024/08/23*
- **End date:** *2025/04/10*
- **Reward:** *10000 USD*

-------------------

## Goal

Verify the safety of `NonZero` in `core::num`.

### Assumptions

`new` and `get` leverage `transmute_unchecked`, so verifying the safety of these methods would require verifying that transmutations are safe. This task is out of scope for this challenge (instead, it's work for [Challenge 1](0001-core-transmutation.md)). For this challenge, for a transmutation from type `T` to type `U`, it suffices to write and verify a contract that `T` and `U` have the same size.

You may assume that each `NonZeroInner` type upholds the safety conditions of the `ZeroablePrimitive` trait. Specifically, you need not verify that the integer primitives which implement `ZeroablePrimitive` are valid when 0, or that transmutations to the `Option` type are sound.

### Success Criteria

#### Part 1: `new` and `new_unchecked`

Verify the safety and correctness of `NonZero::new` and `NonZero::new_unchecked`.

Specifically, write and verify contracts specifying the following:
1. The preconditions specified by the `SAFETY` comments are upheld. 
2. For an input `n`:  
    a. A `NonZero` object is created if and only if the input was nonzero.  
    b. The value of the `NonZeroInner` object equals `n`.

#### Part 2: Other Uses of `unsafe`

Verify the safety of the following functions and methods (all located within `core::num::nonzero`):

| Function |
|--------- |
|  `max`   |
|  `min`   |
|  `clamp`   |
|  `bitor`  (all 3 implementations) |
|  `count_ones`   |
|  `rotate_left`   |
|  `rotate_right`   |
|  `swap_bytes`   |
|  `reverse_bits`   |
|  `from_be`   |
|  `from_le`   |
|  `to_be`   |
|  `to_le`   |
|  `checked_mul`   |
|  `saturating_mul`   |
|  `unchecked_mul`   |
|  `checked_pow`   |
|  `saturating_pow`   |
|  `neg`   |
|  `checked_add`   |
|  `saturating_add`   |
|  `unchecked_add`   |
|  `checked_next_power_of_two`   |
|  `midpoint`   |
|  `isqrt`   |
|  `abs`   |
|  `checked_abs`   |
|  `overflowing_abs`   |
|  `saturating_abs`   |
|  `wrapping_abs`   |
|  `unsigned_abs`   |
|  `checked_neg`   |
|  `overflowing_neg`   |
|  `wrapping_neg` |
|  `from_mut`   |
|  `from_mut_unchecked` |


### List of UBs

In addition to any properties called out as `SAFETY` comments in the source
code, all proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Invoking undefined behavior via compiler intrinsics.
* Reading from uninitialized memory.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.

-------------------

## Verification Summary

All 38 functions verified using Kani proof harnesses. 432 total harnesses pass across all 12 integer types.

### Part 1: Core Creation

| Function | Harness | Types | Approach |
|----------|---------|-------|----------|
| `new` | `nonzero_check_new` | all 12 | `#[kani::proof]` — proves iff: `result.is_some() == (n != 0)` and `nz.get() == n` |
| `new_unchecked` | `nonzero_check` (pre-existing) | all 12 | `#[kani::proof_for_contract]` — verifies `#[requires]` + `#[ensures]` |
| `from_mut` | `nonzero_check_from_mut` | all 12 | `#[kani::proof]` — proves iff + dereferences returned reference |
| `from_mut_unchecked` | `nonzero_check_from_mut_unchecked` (pre-existing) | all 12 | `#[kani::proof_for_contract]` — verifies `#[requires]` |

### Part 2: Bitwise & Conversion

| Function | Harness | Types |
|----------|---------|-------|
| `bitor` (NZ\|NZ) | `nonzero_check_bitor_nznz` | all 12 |
| `bitor` (NZ\|T) | `nonzero_check_bitor_nzt` | all 12 |
| `bitor` (T\|NZ) | `nonzero_check_bitor_tnz` | all 12 |
| `count_ones` | `nonzero_check_count_ones` | all 12 |
| `rotate_left` | `nonzero_check_rotate_left` | all 12 |
| `rotate_right` | `nonzero_check_rotate_right` | all 12 |
| `swap_bytes` | `nonzero_check_swap_bytes` | all 12 |
| `reverse_bits` | `nonzero_check_reverse_bits` | all 12 |
| `from_be` | `nonzero_check_from_be` | all 12 |
| `from_le` | `nonzero_check_from_le` | all 12 |
| `to_be` | `nonzero_check_to_be` | all 12 |
| `to_le` | `nonzero_check_to_le` | all 12 |

### Part 2: Arithmetic

| Function | Harness | Types | Notes |
|----------|---------|-------|-------|
| `checked_mul` | `nonzero_check_checked_mul` | all 12 | |
| `saturating_mul` | `nonzero_check_saturating_mul` | all 12 | |
| `unchecked_mul` | `check_mul_unchecked_*` (pre-existing) | all 12 | `proof_for_contract` with interval testing |
| `checked_pow` | `nonzero_check_checked_pow` | all 12 | Required strengthened loop invariant |
| `saturating_pow` | `nonzero_check_saturating_pow` | all 12 | Required strengthened loop invariant |
| `checked_add` | `nonzero_check_checked_add` | 6 unsigned | |
| `saturating_add` | `nonzero_check_saturating_add` | 6 unsigned | |
| `unchecked_add` | `nonzero_check_add` (pre-existing) | 6 unsigned | `proof_for_contract` |
| `checked_next_power_of_two` | `nonzero_check_checked_next_power_of_two` | 6 unsigned | |
| `midpoint` | `nonzero_check_midpoint` | 6 unsigned | |
| `isqrt` | `nonzero_check_isqrt` | 6 unsigned | `#[kani::unwind(65)]` |

### Part 2: Absolute Value & Negation (signed only)

| Function | Harness | Types | Notes |
|----------|---------|-------|-------|
| `abs` | `nonzero_check_abs` | 6 signed | Excludes MIN (documented overflow) |
| `checked_abs` | `nonzero_check_checked_abs` | 6 signed | |
| `overflowing_abs` | `nonzero_check_overflowing_abs` | 6 signed | |
| `saturating_abs` | `nonzero_check_saturating_abs` | 6 signed | |
| `wrapping_abs` | `nonzero_check_wrapping_abs` | 6 signed | Covers MIN |
| `unsigned_abs` | `nonzero_check_unsigned_abs` | 6 signed | |
| `neg` | `nonzero_check_neg` | 6 signed | Excludes MIN (documented overflow) |
| `checked_neg` | `nonzero_check_checked_neg` | 6 signed | |
| `overflowing_neg` | `nonzero_check_overflowing_neg` | 6 signed | Covers MIN |
| `wrapping_neg` | `nonzero_check_wrapping_neg` | 6 signed | Covers MIN |
| `max` | `nonzero_check_max` (pre-existing) | all 12 | |
| `min` | `nonzero_check_min` (pre-existing) | all 12 | |
| `clamp` | `nonzero_check_clamp` (pre-existing) | all 12 | |

### Additional Changes

Strengthened `#[safety::loop_invariant]` on `checked_pow` in `uint_macros.rs` and `int_macros.rs` from `true` to a property that preserves the nonzero invariant through loop iterations. This is a verification annotation fix, not a runtime logic change.
