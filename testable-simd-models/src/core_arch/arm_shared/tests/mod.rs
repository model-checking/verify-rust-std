//! Tests for intrinsics defined in `crate::core_arch::models::arm_shared`
//!
//! Each and every modelled intrinsic is tested against the Rust
//! implementation here. For the most part, the tests work by
//! generating random inputs, passing them as arguments
//! to both the models in this crate, and the corresponding intrinsics
//! in the Rust core and then comparing their outputs.
//!
//! To add a test for a modelled intrinsic, go the appropriate file, and
//! use the `mk!` macro to define it.
//!
//! A `mk!` macro invocation looks like the following,
//! `mk!([<number of times the random test happens>]<function name>{<<const values, if the function takes any>,>}(<function arguments : with types,>))
//!
//! For example, some valid invocations are
//!
//! `mk!([100]_mm256_extracti128_si256{<0>,<1>}(a: BitVec));`
//! `mk!(_mm256_extracti128_si256{<0>,<1>}(a: BitVec));`
//! `mk!(_mm256_abs_epi16(a: BitVec));`
//!
//! The number of random tests is optional. If not provided, it is taken to be 1000 by default.
//! The const values are necessary if the function has constant arguments, but should be discarded if not.
//! The function name and the function arguments are necessary in all cases.
//!
//! Note: This only works if the function returns a bit-vector or funarray. If it returns an integer, the
//! test has to be written manually. It is recommended that the manually defined test follows
//! the pattern of tests defined via the `mk!` invocation. It is also recommended that, in the
//! case that the intrinsic takes constant arguments, each and every possible constant value
//! (upto a maximum of 255) that can be passed to the function be used for testing. The number
//! of constant values passed depends on if the Rust intrinsics statically asserts that the
//! length of the constant argument be less than or equal to a certain number of bits.

pub mod neon;

#[allow(non_camel_case_types)]
mod types {
    use crate::abstractions::simd::*;
    pub type int32x4_t = i32x4;
    pub type int64x1_t = i64x1;
    pub type int64x2_t = i64x2;
    pub type int16x8_t = i16x8;
    pub type int8x16_t = i8x16;
    pub type uint32x4_t = u32x4;
    pub type uint64x1_t = u64x1;
    pub type uint64x2_t = u64x2;
    pub type uint16x8_t = u16x8;
    pub type uint8x16_t = u8x16;
    pub type int32x2_t = i32x2;
    pub type int16x4_t = i16x4;
    pub type int8x8_t = i8x8;
    pub type uint32x2_t = u32x2;
    pub type uint16x4_t = u16x4;
    pub type uint8x8_t = u8x8;
}

pub(crate) mod upstream {
    #[cfg(target_arch = "aarch64")]
    pub use core::arch::aarch64::*;
    #[cfg(target_arch = "arm")]
    pub use core::arch::arm::*;
}

#[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
pub mod conversions {
    use super::upstream::*;

    use super::types;
    use crate::abstractions::bitvec::BitVec;
    use crate::abstractions::funarr::FunArray;

    macro_rules! convert{
	($($ty1:ident [$ty2:ty ; $n:literal]),*) => {
	    $(
		impl From<$ty1> for types::$ty1 {
		    fn from (arg: $ty1) -> types::$ty1 {
			let stuff = unsafe { *(&arg as *const $ty1 as *const [$ty2; $n])};
			FunArray::from_fn(|i|
					  stuff[i as usize]
			)
		    }
		}
		impl From<types::$ty1> for $ty1 {
		    fn from (arg: types::$ty1) -> $ty1 {
			let bv: &[u8] = &(BitVec::from(arg)).to_vec()[..];
			unsafe {
			    *(bv.as_ptr() as *const [$ty2; $n] as *const _)
			}
		    }
		}
	    )*
	}
    }

    convert!(
    int32x4_t [i32; 4],
    int64x1_t [i64; 1],
    int64x2_t [i64; 2],
    int16x8_t [i16; 8],
    int8x16_t [i8; 16],
    uint32x4_t [u32; 4],
    uint64x1_t [u64; 1],
    uint64x2_t [u64; 2],
    uint16x8_t [u16; 8],
    uint8x16_t [u8; 16],
    int32x2_t [i32; 2],
    int16x4_t [i16; 4],
    int8x8_t [i8; 8],
    uint32x2_t [u32; 2],
    uint16x4_t [u16; 4],
    uint8x8_t [u8; 8]
    );
}
