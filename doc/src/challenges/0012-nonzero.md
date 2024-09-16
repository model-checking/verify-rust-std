# Challenge 12: Safety of `NonZero`

- **Status:** Open
- **Tracking Issue:** [#71](https://github.com/model-checking/verify-rust-std/issues/71)
- **Start date:** *2024-08-23*
- **End date:** *2024-12-10*

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

You are not required to write correctness contracts for these methods (e.g., for `max`, ensuring that the `result` is indeed the maximum of the inputs), but it would be great to do so!

### List of UBs

In addition to any properties called out as `SAFETY` comments in the source
code, all proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Invoking undefined behavior via compiler intrinsics.
* Reading from uninitialized memory.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
