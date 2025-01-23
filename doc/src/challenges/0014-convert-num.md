# Challenge 14: Safety of Primitive Conversions

- **Status:** Open
- **Tracking Issue:** https://github.com/model-checking/verify-rust-std/issues/220
- **Start date:** 2024/12/15
- **End date:** 2025/2/28
- **Prize:** *TBD*

-------------------

## Goal

Verify the safety of number conversions in `core::convert::num`.

There are two conversions that use unsafe code: conversion from NonZero integer to NonZero integer and conversion from floating point number to integer. All conversions use macros to implement traits for primitive types in bulk. You will need to add contracts into the macros so that contracts are generated for each implementation. As the conversions are all macro generated, it is probably a good idea to write your own macro for generating the harnesses.

### Success Criteria

#### NonZero Conversions
Write a type invariant for `core::num::NonZero`, then write harnesses for all `nonzero` conversions.

Write proof contracts for each NonZero primitive conversion, listed in full below. These conversions are implemented through two macros: `impl_nonzero_int_from_nonzero_int!` and `impl_nonzero_int_try_from_nonzero_int!`. 

For each invocation of `impl_nonzero_int_from_nonzero_int!`, prove that the conversion it implements does not cause undefined behavior nor panic. For example, for `impl_nonzero_int_from_nonzero_int!(u8 => u16);`, prove that calling `NonZero<u16>::from(small: NonZero<u8>)` does not cause undefined behavior nor panic for an arbitrary `small` that satisfies the `NonZero` type invariant.

For each invocation of `impl_nonzero_int_try_from_nonzero_int!`, prove that the conversion it implements does not cause undefined behavior. For example, for `impl_nonzero_int_try_from_nonzero_int!(u16 => u8);`, prove that calling `NonZero<u8>::try_from(value: NonZero<u16>)` does not cause undefined behavior for an arbitrary `value` that satisfies the `NonZero` type invariant. Additionally, prove that if the `value` does not fit into the target type (e.g., `value` is too large to fit into a `NonZero<u8>`) that the function panics.

non-zero unsigned integer -> non-zero unsigned integer
- `impl_nonzero_int_from_nonzero_int!(u8 => u16);`
- `impl_nonzero_int_from_nonzero_int!(u8 => u32);`
- `impl_nonzero_int_from_nonzero_int!(u8 => u64);`
- `impl_nonzero_int_from_nonzero_int!(u8 => u128);`
- `impl_nonzero_int_from_nonzero_int!(u8 => usize);`
- `impl_nonzero_int_from_nonzero_int!(u16 => u32);`
- `impl_nonzero_int_from_nonzero_int!(u16 => u64);`
- `impl_nonzero_int_from_nonzero_int!(u16 => u128);`
- `impl_nonzero_int_from_nonzero_int!(u16 => usize);`
- `impl_nonzero_int_from_nonzero_int!(u32 => u64);`
- `impl_nonzero_int_from_nonzero_int!(u32 => u128);`
- `impl_nonzero_int_from_nonzero_int!(u64 => u128);`

non-zero signed integer -> non-zero signed integer
- `impl_nonzero_int_from_nonzero_int!(i8 => i16);`
- `impl_nonzero_int_from_nonzero_int!(i8 => i32);`
- `impl_nonzero_int_from_nonzero_int!(i8 => i64);`
- `impl_nonzero_int_from_nonzero_int!(i8 => i128);`
- `impl_nonzero_int_from_nonzero_int!(i8 => isize);`
- `impl_nonzero_int_from_nonzero_int!(i16 => i32);`
- `impl_nonzero_int_from_nonzero_int!(i16 => i64);`
- `impl_nonzero_int_from_nonzero_int!(i16 => i128);`
- `impl_nonzero_int_from_nonzero_int!(i16 => isize);`
- `impl_nonzero_int_from_nonzero_int!(i32 => i64);`
- `impl_nonzero_int_from_nonzero_int!(i32 => i128);`
- `impl_nonzero_int_from_nonzero_int!(i64 => i128);`

non-zero unsigned -> non-zero signed integer
- `impl_nonzero_int_from_nonzero_int!(u8 => i16);`
- `impl_nonzero_int_from_nonzero_int!(u8 => i32);`
- `impl_nonzero_int_from_nonzero_int!(u8 => i64);`
- `impl_nonzero_int_from_nonzero_int!(u8 => i128);`
- `impl_nonzero_int_from_nonzero_int!(u8 => isize);`
- `impl_nonzero_int_from_nonzero_int!(u16 => i32);`
- `impl_nonzero_int_from_nonzero_int!(u16 => i64);`
- `impl_nonzero_int_from_nonzero_int!(u16 => i128);`
- `impl_nonzero_int_from_nonzero_int!(u32 => i64);`
- `impl_nonzero_int_from_nonzero_int!(u32 => i128);`
- `impl_nonzero_int_from_nonzero_int!(u64 => i128);`

There are also the fallible versions. Remember to cover both the panicking and non-panicking cases. 

unsigned non-zero integer -> unsigned non-zero integer
- `impl_nonzero_int_try_from_nonzero_int!(u16 => u8);`
- `impl_nonzero_int_try_from_nonzero_int!(u32 => u8, u16, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(u64 => u8, u16, u32, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(u128 => u8, u16, u32, u64, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(usize => u8, u16, u32, u64, u128);`

signed non-zero integer -> signed non-zero integer
- `impl_nonzero_int_try_from_nonzero_int!(i16 => i8);`
- `impl_nonzero_int_try_from_nonzero_int!(i32 => i8, i16, isize);`
- `impl_nonzero_int_try_from_nonzero_int!(i64 => i8, i16, i32, isize);`
- `impl_nonzero_int_try_from_nonzero_int!(i128 => i8, i16, i32, i64, isize);`
- `impl_nonzero_int_try_from_nonzero_int!(isize => i8, i16, i32, i64, i128);`

unsigned non-zero integer -> signed non-zero integer
- `impl_nonzero_int_try_from_nonzero_int!(u8 => i8);`
- `impl_nonzero_int_try_from_nonzero_int!(u16 => i8, i16, isize);`
- `impl_nonzero_int_try_from_nonzero_int!(u32 => i8, i16, i32, isize);`
- `impl_nonzero_int_try_from_nonzero_int!(u64 => i8, i16, i32, i64, isize);`
- `impl_nonzero_int_try_from_nonzero_int!(u128 => i8, i16, i32, i64, i128, isize);`
- `impl_nonzero_int_try_from_nonzero_int!(usize => i8, i16, i32, i64, i128, isize);`

signed non-zero integer -> unsigned non-zero integer
- `impl_nonzero_int_try_from_nonzero_int!(i8 => u8, u16, u32, u64, u128, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(i16 => u8, u16, u32, u64, u128, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(i32 => u8, u16, u32, u64, u128, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(i64 => u8, u16, u32, u64, u128, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(i128 => u8, u16, u32, u64, u128, usize);`
- `impl_nonzero_int_try_from_nonzero_int!(isize => u8, u16, u32, u64, u128, usize);`


#### Safety for Float to Int

```rust
macro_rules! impl_float_to_int {
    ($Float:ty => $($Int:ty),+) => {
        #[unstable(feature = "convert_float_to_int", issue = "67057")]
        impl private::Sealed for $Float {}
        $(
            #[unstable(feature = "convert_float_to_int", issue = "67057")]
            impl FloatToInt<$Int> for $Float {
                #[inline]
                unsafe fn to_int_unchecked(self) -> $Int {
                    // SAFETY: the safety contract must be upheld by the caller.
                    unsafe { crate::intrinsics::float_to_int_unchecked(self) }
                }
            }
        )+
    }
}
```

The safety constraints referenced in the comments are that the input value must:
- Not be NaN
- Not be infinite
- Be representable in the return type Int, after truncating off its fractional part

These constraints are given in the [documentation](https://doc.rust-lang.org/std/primitive.f32.html#method.to_int_unchecked). 
 
The intrinsic corresponds to the [fptoui](https://llvm.org/docs/LangRef.html#fptoui-to-instruction)/[fptosi](https://llvm.org/docs/LangRef.html#fptosi-to-instruction) LLVM instructions, which may be useful for reference.
Prove safety for each of the following conversions:

- `impl_float_to_int!(f16 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize)`
- `impl_float_to_int!(f32 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize)`
- `impl_float_to_int!(f64 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize)`
- `impl_float_to_int!(f128 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize)`

### List of UBs

In addition to any properties called out as `SAFETY` comments in the source
code,
all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory.
* Mutating immutable bytes.
* Producing an invalid value

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
