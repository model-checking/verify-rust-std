//! Rust models for x86 intrinsics.
//!
//! This module contains models for the intrinsics as they are defined in the Rust core.
//! Since this is supposed to model the Rust core, the implemented functions must
//! mirror the Rust implementations as closely as they can.
//!
//! For example, calls to simd functions like simd_add and simd_sub are left as is,
//! with their implementations defined in `crate::abstractions::simd`. Some other
//! operations like simd_cast or simd_shuffle might need a little modification
//! for correct compilation.
//!
//! Calls to transmute are replaced with either an explicit call to a `BitVec::from_ function`,
//! or with `.into()`.
//!
//! Sometimes, an intrinsic in Rust is implemented by directly using the corresponding
//! LLVM instruction via an `unsafe extern "C"` module. In those cases, the corresponding
//! function is defined in the `c_extern` module in each file, which contain manually
//! written implementations made by consulting the appropriate Intel documentation.
//!
//! In general, it is best to gain an idea of how an implementation should be written by looking
//! at how other functions are implemented. Also see `core::arch::x86` for [reference](https://github.com/rust-lang/stdarch/tree/master/crates/core_arch).

pub mod avx;
pub mod avx2;
pub mod avx2_handwritten;
pub mod avx_handwritten;
pub mod sse;
pub mod sse2;
pub mod sse2_handwritten;
pub mod ssse3;
pub mod ssse3_handwritten;

pub(crate) mod types {
    use crate::abstractions::bitvec::*;

    #[allow(non_camel_case_types)]
    pub type __m256i = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m256 = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m256d = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m128 = BitVec<128>;
    #[allow(non_camel_case_types)]
    pub type __m128i = BitVec<128>;
    #[allow(non_camel_case_types)]
    pub type __m128d = BitVec<128>;
}
