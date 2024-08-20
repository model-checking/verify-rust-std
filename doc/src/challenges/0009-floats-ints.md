# Challenge 9: Safety of Floats and Integers


- **Status:** Open
- **Tracking Issue:** [Link to issue](https://github.com/model-checking/verify-rust-std/issues/XX)
- **Start date:** *2024-08-20*
- **End date:** *2024-12-10*

-------------------

## Goal

Verify the memory safety of public unsafe methods for floats and integers in `core::num`.

## Success Criteria

### Signed Integers

Prove the absence of undefined behavior in the following methods:

1. `int_macros::unchecked_add`
2. `int_macros::unchecked_sub`
3. `int_macros::unchecked_mul`
4. `int_macros::unchecked_neg`
5. `int_macros::unchecked_shl`
6. `int_macros::unchecked_shr`

for each of the [signed integer types](https://doc.rust-lang.org/beta/book/ch03-02-data-types.html#integer-types).

### Unsigned Integers

Prove the absence of undefined behavior in the following methods:

1. `uint_macros::unchecked_add`
2. `uint_macros::unchecked_sub`
3. `uint_macros::unchecked_mul`
4. `uint_macros::unchecked_shl`
5. `uint_macros::unchecked_shr`

for each of the [unsigned integer types](https://doc.rust-lang.org/beta/book/ch03-02-data-types.html#integer-types). 

### Float to Integer Conversion

Verify the absence of undefined behavior in `to_int_unchecked` for `f16`, `f32`, `f64`, and `f128`. 

## List of UBs

In addition to any properties called out as SAFETY comments in the source code, all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Invoking undefined behavior via compiler intrinsics.
* Reading from uninitialized memory.
* Mutating immutable bytes.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md) in addition to the ones listed above.
