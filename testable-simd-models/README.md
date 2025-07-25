# testable-simd-models

This crate contains executable, independently testable specifications
for the SIMD intrinsics provided by the `core::arch` library in Rust. 
The structure of this crate is based on [rust-lang/stdarch/crates/core_arch](https://github.com/rust-lang/stdarch/tree/master/crates/core_arch).

## Code Structure
Within the `core_arch` folder in this crate, there is a different
folder for each architecture for which we have wrtten models. 
In particular, it contains folders for `x86` and `arm_shared`.
Each such folder has 3 sub-folders, `models`, `tests`, and `specs`. 

The `models` folder contains the models of the intrinsics, with a file
corresponding to different target features, and are written using the
various abstractions implementedin `crate::abstractions`, especially
those in `crate::abstractions::simd`. These models are meant to
closely resemble their implementations within the Rust core itself.

The `tests` folder contains the tests of these models, and is
structured the same way as `models`. Each file additionally contains
the definition of a macro that makes writing these tests easier. The
tests work by testing the models against the intrinsics in the Rust
core, trying out random inputs (generally 1000), and comparing their
outputs.

## Modeling Process
The process of adding a specific intrinsic's model goes as follows.
For this example, let us say the intrinsic we are adding is
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
Thus, we then go to to `core_arch/x86/models/avx2.rs`, and add the implementation. After some modification, it ends up looking like this.
``` rust
/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)

pub fn _mm256_bsrli_epi128<const IMM8: i32>(a: __m256i) -> __m256i {
    const fn mask(shift: i32, i: u32) -> u64 {
        let shift = shift as u32 & 0xff;
        if shift > 15 || (15 - (i % 16)) < shift {
            0 as u64
        } else {
            (32 + (i + shift)) as u64
        }
    }
    
	let a = BitVec::to_i8x32(a);
	let r: i8x32 = simd_shuffle(
		i8x32::from_fn(|_| 0),
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
	r.into()
}
  ```
  
3. Next, we add a test for this intrinsic. For this, we navigate to `core_arch/avx2/tests/avx2.rs`. Since the value of
   `IMM8` can be up to 8 bits, we want to test constant arguments up to 255. Thus, we write the following macro invocation.
   ```rust
	   mk!([100]_mm256_bsrli_epi128{<0>,<1>,<2>,<3>,...,<255>}(a: BitVec));
   ```
   Here, the `[100]` means we test 100 random inputs for each constant value. This concludes the necessary steps for implementing an intrinsic.


## Contributing Models

To contribute new models of intrinsics, we expect the author to follow
the above steps and provide comprehensive tests.  It is important that
the model author look carefully at both the Intel/ARM specification
and the Rust `stdarch` implementation, because the Rust implementation
may not necessarily be correct.

Indeed, the previous implementation of `_mm256_bsrli_epi128` (and a
similar intrinsic called `_mm512_bsrli_epi128`) in `stdarch` had a
bug, which we found during the process of modeling and testing this
intrinsic. This bug was [reported by
us](https://github.com/rust-lang/stdarch/issues/1822) using a failing
test case generated from the testable model and then fixed by [our
PR](https://github.com/rust-lang/stdarch/pull/1823) in the 2025-06-30
version of `stdarch`.
