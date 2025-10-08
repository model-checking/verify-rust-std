//! Tests for intrinsics defined in `crate::core_arch::x86::models`
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
//! `mk!([100]_mm256_extracti128_si256{<0>,<1>}(a: __m256i));`
//! `mk!(_mm256_extracti128_si256{<0>,<1>}(a: __m256i));`
//! `mk!(_mm256_abs_epi16(a: __m256i));`
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

mod avx;
mod avx2;
mod sse2;
mod ssse3;
use crate::abstractions::bitvec::*;

pub(crate) mod types {
    use crate::abstractions::bitvec::*;

    #[allow(non_camel_case_types)]
    pub type __m256i = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m256 = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m128i = BitVec<128>;
    #[allow(non_camel_case_types)]
    pub type __m256d = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m128 = BitVec<128>;
    #[allow(non_camel_case_types)]
    pub type __m128d = BitVec<128>;
}

pub(crate) mod upstream {
    #[cfg(target_arch = "x86")]
    pub use core::arch::x86::*;
    #[cfg(target_arch = "x86_64")]
    pub use core::arch::x86_64::*;
}

mod conversions {
    use super::upstream::{
        __m128, __m128d, __m128i, __m256, __m256d, __m256i, _mm256_castpd_si256,
        _mm256_castps_si256, _mm256_castsi256_pd, _mm256_castsi256_ps, _mm256_loadu_si256,
        _mm256_storeu_si256, _mm_castpd_si128, _mm_castps_si128, _mm_castsi128_pd,
        _mm_castsi128_ps, _mm_loadu_si128, _mm_storeu_si128,
    };
    use super::BitVec;

    impl From<BitVec<256>> for __m256i {
        fn from(bv: BitVec<256>) -> __m256i {
            let bv: &[u8] = &bv.to_vec()[..];
            unsafe { _mm256_loadu_si256(bv.as_ptr() as *const _) }
        }
    }
    impl From<BitVec<256>> for __m256 {
        fn from(bv: BitVec<256>) -> __m256 {
            let bv: &[u8] = &bv.to_vec()[..];
            unsafe { _mm256_castsi256_ps(_mm256_loadu_si256(bv.as_ptr() as *const _)) }
        }
    }

    impl From<BitVec<128>> for __m128i {
        fn from(bv: BitVec<128>) -> __m128i {
            let slice: &[u8] = &bv.to_vec()[..];
            unsafe { _mm_loadu_si128(slice.as_ptr() as *const __m128i) }
        }
    }

    impl From<BitVec<128>> for __m128 {
        fn from(bv: BitVec<128>) -> __m128 {
            let slice: &[u8] = &bv.to_vec()[..];
            unsafe { _mm_castsi128_ps(_mm_loadu_si128(slice.as_ptr() as *const __m128i)) }
        }
    }

    impl From<BitVec<128>> for __m128d {
        fn from(bv: BitVec<128>) -> __m128d {
            let slice: &[u8] = &bv.to_vec()[..];
            unsafe { _mm_castsi128_pd(_mm_loadu_si128(slice.as_ptr() as *const __m128i)) }
        }
    }

    impl From<BitVec<256>> for __m256d {
        fn from(bv: BitVec<256>) -> __m256d {
            let bv: &[u8] = &bv.to_vec()[..];
            unsafe { _mm256_castsi256_pd(_mm256_loadu_si256(bv.as_ptr() as *const _)) }
        }
    }

    impl From<__m256i> for BitVec<256> {
        fn from(vec: __m256i) -> BitVec<256> {
            let mut v = [0u8; 32];
            unsafe {
                _mm256_storeu_si256(v.as_mut_ptr() as *mut _, vec);
            }
            BitVec::from_slice(&v[..], 8)
        }
    }

    impl From<__m256> for BitVec<256> {
        fn from(vec: __m256) -> BitVec<256> {
            let mut v = [0u8; 32];
            unsafe {
                _mm256_storeu_si256(v.as_mut_ptr() as *mut _, _mm256_castps_si256(vec));
            }
            BitVec::from_slice(&v[..], 8)
        }
    }

    impl From<__m256d> for BitVec<256> {
        fn from(vec: __m256d) -> BitVec<256> {
            let mut v = [0u8; 32];
            unsafe {
                _mm256_storeu_si256(v.as_mut_ptr() as *mut _, _mm256_castpd_si256(vec));
            }
            BitVec::from_slice(&v[..], 8)
        }
    }

    impl From<__m128i> for BitVec<128> {
        fn from(vec: __m128i) -> BitVec<128> {
            let mut v = [0u8; 16];
            unsafe {
                _mm_storeu_si128(v.as_mut_ptr() as *mut _, vec);
            }
            BitVec::from_slice(&v[..], 8)
        }
    }

    impl From<__m128> for BitVec<128> {
        fn from(vec: __m128) -> BitVec<128> {
            let mut v = [0u8; 16];
            unsafe {
                _mm_storeu_si128(v.as_mut_ptr() as *mut _, _mm_castps_si128(vec));
            }
            BitVec::from_slice(&v[..], 8)
        }
    }

    impl From<__m128d> for BitVec<128> {
        fn from(vec: __m128d) -> BitVec<128> {
            let mut v = [0u8; 16];
            unsafe {
                _mm_storeu_si128(v.as_mut_ptr() as *mut _, _mm_castpd_si128(vec));
            }
            BitVec::from_slice(&v[..], 8)
        }
    }
}
