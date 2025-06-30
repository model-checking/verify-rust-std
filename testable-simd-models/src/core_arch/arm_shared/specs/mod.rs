//! Specifications for ARM intrinsics.
//!
//! Specifications for ARM intrinsics are written manually by consulting the appropriate [ARM documentation][https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html].
//! These specifications are written to match what the intrinsic does, instead of being like
//! the Rust implementations as in `crate::core_arch::x86::models`. This is for the possibility
//! the Rust core incorrectly implements an intrinsic. As a rule of thumb, any intrinsic whose
//! implementation is more than 3-5 lines of code, might benefit from a manually defined
//! specification. Any existing specifications are trusted to be completely correct. Thus
//! the addition of any new specification needs extensive manual review.
//!
//! Some mandatory requirements for added specifications.
//! - A specification cannot use any of the functions in `crate::abstractions::simd`
//! - A specification cannot call any other specification.
//! - A specification's type signature must match that of the corresponding intrinsic.
//!
//! For a better understanding, one can take a look at the specifications which are already
//! defined.

#[allow(unused)]
#[allow(non_camel_case_types)]
mod types {
    use crate::abstractions::bitvec::int_vec_interp::*;
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
