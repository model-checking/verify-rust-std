# testable-simd-models

This crate contains executable, independently testable specifications
for the SIMD intrinsics provided by the `core::arch` library in Rust. 
The structure of this crate is based on [rust-lang/stdarch/crates/core_arch](https://github.com/rust-lang/stdarch/tree/master/crates/core_arch).

## Code Structure
Within the `core_arch` folder in this crate, there is a different
folder for each architecture for which we have written models. 
In particular, it contains folders for `x86` and `arm_shared`.
Each such folder has 2 sub-folders: `models` and `tests`. 

The `models` folder contains the models of the intrinsics, with
different files for different target features (e.g. `sse2`, `avx2`
etc.). The code in this folder is written using the various
abstractions implemented in `abstractions`, especially those in
`abstractions::simd`. These models are meant to closely
resemble their implementations within the Rust core itself.

The `tests` folder contains the tests of these models, and is
structured the same way as `models`. Each file additionally includes
the definition of a macro that makes writing these tests easier. The
tests work by testing the models against the intrinsics in the Rust
core, trying out random inputs (generally 1000), and comparing their
outputs.

All tests can be run by executing `cargo test`, and we expect this to be
run as part of CI.

## Modeling a SIMD Intrinsic

There are three kinds of SIMD intrinsics in `core::arch`.

The first kind are builtin Rust compiler intrinsics, some of which are 
in the [`intrinsics/simd.rs` file](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/intrinsics/simd.rs)
in the `core` crate, and others are in the [`simd.rs` file of `core_arch`](https://github.com/model-checking/verify-rust-std/blob/main/library/stdarch/crates/core_arch/src/simd.rs).
These builtin intrinsics define generic SIMD operations that the Rust compiler knows how to implement on each platform.

The second kind are `extern` intrinsics that are links to definitions in LLVM.
See, for example, [this list](https://github.com/rust-lang/stdarch/blob/master/crates/core_arch/src/x86/avx2.rs#L3596C8-L3596C14)
of `extern` intrinsics used in the Intel x86 AVX2 library.
These extern intrinsics are typically platform-specific functions that map to low-level instructions.

The third kind are `defined` intrinsics that are given proper definitions in Rust, and their code may
depend on the builtin intrinsics or the extern intrinsics. These defined intrinsics represent higher-level
operations that are wrappers around one or more assembly instructions.

### Modeling builtin intrinsics manually

We model all three kinds of intrinsics, but in slightly different
ways.  For the builtin intrinsics, we can write implementations once
and for all, and to this end, we use a library within the
`abstractions/simd.rs` file, where we copy the signatures of the
intrinsics from Rust but give them our own implementation. In
particular, we model each SIMD vector as an array of scalars, and
define each generic operation as functions over such arrays. This can
be seen as a reference implementation of the builtin intrinsics.

Hence, for example, the SIMD add intrinsic `simd_add` is modeled as follows,
it takes two arrays of machine integers and adds them pointwise using a
`wrapping_add` operation:

```rust
pub fn simd_add<const N: u64, T: MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| (x[i].wrapping_add(y[i])))
}
```

Notably, we model a strongly typed version of `simd_add`, in contrast to the compiler
intrinsic, which is too generic and unimplementable in safe Rust:

```rust
/// Adds two simd vectors elementwise.
///
/// `T` must be a vector of integers or floats.
#[rustc_intrinsic]
#[rustc_nounwind]
pub unsafe fn simd_add<T>(x: T, y: T) -> T;
```

The main rules for writing these models are that they should be simple and self-contained,
relying only on the libraries in `abstractions`, on builtin Rust language features, or 
other testable models. In particular, they should not themselves directly call Rust libraries
or external crates, without going through the abstractions API.


### Modeling extern intrinsics manually

For each file in `core::arch`, we split the code into extern
intrinsics that must be modeled by hand and defined intrinsics whose
models can be derived semi-automatically. The extern intrinsics are
placed in a module suffixed with `_handwritten`. Hence, for example,
the extern intrinsics used in `avx2.rs` can be found in `avx2_handwritten.rs`.

Modeling extern intrinsics is similar to modeling the builtin ones,
in that the models are written by hand and treat the SIMD vectors
as arrays of machine integers. The main difference is that these intrinsics
are platform-specific and so their modeling requires looking at the Intel or ARM
documentation for the underlying operation.

For example, the extern intrinsic `phaddw` used in `avx2` corresponds to an
Intel instruction called "Packed Horizontal Add" and is used in AVX2 intrinsics
like `_mm256_hadd_epi16` documented [here](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadd_epi16&ig_expand=3667_)
By inspecting the Intel documentation, we can write a Rust model for it
as follows 

```rust
pub fn phaddw(a: i16x16, b: i16x16) -> i16x16 {
    i16x16::from_fn(|i| {
        if i < 4 {
            a[2 * i].wrapping_add(a[2 * i + 1])
        } else if i < 8 {
            b[2 * (i - 4)].wrapping_add(b[2 * (i - 4) + 1])
        } else if i < 12 {
            a[2 * (i - 4)].wrapping_add(a[2 * (i - 4) + 1])
        } else {
            b[2 * (i - 8)].wrapping_add(b[2 * (i - 8) + 1])
        }
    })
}
```

### Modeling defined intrinsics semi-automatically

To model a defined intrinsic, we essentially copy the Rust code of
the intrinsic from `core::arch` and adapt it to use our underlying abstractions.  The
changes needed to the code are sometimes scriptable, and indeed most
of our models were generated from a script, but some changes are still
needed by hand.

For example, let us say the intrinsic we are modeling is
`_mm256_bsrli_epi128` from the avx2 feature set.

1. We go to [rust-lang/stdarch/crates/core_arch/src/x86/](https://github.com/rust-lang/stdarch/tree/master/crates/core_arch/src/x86/), and find the implementation of the intrinsic in `avx2.rs`.

2. We see that the implementation looks like this:
``` rust
/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)
#[inline]
#[target_feature(enable = "avx2")]
#[cfg_attr(test, assert_instr(vpsrldq, IMM8 = 1))]
#[rustc_legacy_const_generics(1)]
#[stable(feature = "simd_x86", since = "1.27.0")]
pub fn _mm256_bsrli_epi128<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    const fn mask(shift: i32, i: u32) -> u32 {
        let shift = shift as u32 & 0xff;
        if shift > 15 || (15 - (i % 16)) < shift {
            0
        } else {
            32 + (i + shift)
        }
    }
    unsafe {
        let a = a.as_i8x32();
        let r: i8x32 = simd_shuffle!(
            i8x32::ZERO,
            a,
            [
                mask(IMM8, 0),
                mask(IMM8, 1),
                mask(IMM8, 2),
                mask(IMM8, 3),
		...
                mask(IMM8, 31),
            ],
        );
        transmute(r)
    }
}
```

Thus, we then go to `core_arch/x86/models/avx2.rs`, and add this implementation.
The only change it requires here is that the `simd_shuffle` macro is a function in our model,
and we discard all the function attributes.

For other intrinsics, we sometimes need to make more changes. Since our model of the builtin intrinsics
is more precise concerning the type of their arguments compared to their Rust counterparts, we
sometimes need to add more type annotations in our defined models. We also remove all `unsafe` guards,
since our models are always in safe Rust. Otherwise, our code for the defined intrinsics looks very
similar to the upstream code in `core::arch`.
  
3. Next, we add a test for this intrinsic in `core_arch/avx2/tests/avx2.rs`. For convenience purposes, we have defined a `mk!` macro, which can be used to automatically generate
   tests. The test generated by the macro generates a number of random inputs (by default, 1000), and compares the output generated by the model
   and that generated by the intrinsic in upstream `core::arch`.  A valid test of the intrinsic above looks like this.
   ```rust
	   mk!([100]_mm256_bsrli_epi128{<0>,<1>,<2>,<3>,...,<255>}(a: BitVec));
   ```
   The macro invocation has four parts. 
   1. `mk!([100]...`: By default, the macro tests for a thousand randomly generated inputs. If needed, this can be modified, such as here, where the `[100]` is used so that
      only 100 inputs are generated. 
   2. `_mm256_bsrli_epi128`: This is the name of the intrinsic being tested, and is necessary in all cases.
   3. `{<0>,<1>,<2>,<3>,...,<255>}`: This part only appears when the intrinsic has a const generic argument, like the `IMM8` in this intrinsic.
      As the name indicates, this constant argument is supposed to be at most 8 bits wide.
      We can confirm this by looking at the implementation and spotting the `static_assert_uimm_bits!(IMM8, 8);`
      line, which asserts that constant argument is positive and fits in 8 bits. Thus, we add `{<0>,<1>,<2>,<3>,...,<255>}` to test for each possible constant
      value of the constant argument. 
   4. `(a: BitVec)`: This part contains all the arguments of the intrinsic and their types.
   
   This summarizes the steps needed to use the `mk!` macro to generate a test. There is a caveat: in the case that the output of an intrinsic is _not_
   a bit-vector (and is instead, say, an integer like `i32`), then the macro will not work, and a manual test has to be written. You can see examples in the test files.
  


## Contributing Models

To contribute new models of intrinsics, we expect the author to follow
the above steps and provide comprehensive tests.  It is important that
the model author looks carefully at both the Intel/ARM specifications
and the Rust `stdarch` implementation, because they may look quite different
from each other. 

In some cases, the Rust implementation may not be correct.
Indeed, the previous implementation of `_mm256_bsrli_epi128` (and a
similar intrinsic called `_mm512_bsrli_epi128`) in `stdarch` had a
bug, which we found during the process of modeling and testing this
intrinsic. This bug was [reported by
us](https://github.com/rust-lang/stdarch/issues/1822) using a failing
test case generated from the testable model and then fixed by [our
PR](https://github.com/rust-lang/stdarch/pull/1823) in the 2025-06-30
version of `stdarch`.
