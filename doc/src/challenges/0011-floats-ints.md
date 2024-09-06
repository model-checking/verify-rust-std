# Challenge 11: Safety of Methods for Numeric Primitive Types


- **Status:** Open
- **Tracking Issue:** [#59](https://github.com/model-checking/verify-rust-std/issues/59)
- **Start date:** *2024-08-20*
- **End date:** *2024-12-10*

-------------------

## Goal

Verify the safety of public unsafe methods for floats and integers in `core::num`.

To find the documentation for these methods, navigate first to the [`core::num` documentation](https://doc.rust-lang.org/core/num/index.html), then click on the appropriate primitive type in the left-side menu bar. For example, for `i8::unchecked_add`, click on `i8`.

## Success Criteria

### Part 1: Unsafe Integer Methods

Prove the absence of arithmetic overflow/underflow and undefined behavior in the following methods for each of the listed integer types, given that their safety preconditions are satisfied:

| Method              | Integer Types |
| :---           |     :---
| `unchecked_add`  |  `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128` |
| `unchecked_sub`  |  `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128` |
| `unchecked_mul`  |  `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128` |
| `unchecked_shl`  |  `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128` |
| `unchecked_shr`  |  `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128` |
| `unchecked_neg`  |  `i8`, `i16`, `i32`, `i64`, `i128` |


### Part 2: Safe API Verification

Now, verify some of the safe APIs that leverage the unsafe integer methods from Part 1. Verify the absence of arithmetic overflow/underflow and undefined behavior of the following methods for each of the listed integer types:

| Method              | Integer Types |
| :---           |     :---
| `wrapping_shl`  |  `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128` |
| `wrapping_shr`  |  `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128` |
| `widening_mul`  |  `u8`, `u16`, `u32`, `u64` |
| `carrying_mul`  |  `u8`, `u16`, `u32`, `u64` |


### Part 3: Float to Integer Conversion

Verify the absence of arithmetic overflow/underflow and undefined behavior in `to_int_unchecked` for `f16`, `f32`, `f64`, and `f128`.


## List of UBs

In addition to any properties called out as SAFETY comments in the source code, all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Invoking undefined behavior via compiler intrinsics.
* Reading from uninitialized memory.
* Mutating immutable bytes.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md) in addition to the ones listed above.
