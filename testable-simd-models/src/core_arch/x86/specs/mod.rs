//! Specifications for x86 intrinsics.
//!
//! Specifications for x86 intrinsics are written manually by consulting the appropriate [Intel documentation][https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html].
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

pub mod avx;
pub mod avx2;
pub mod sse2;
pub mod ssse3;

pub(crate) mod types {
    use crate::abstractions::bitvec::*;

    #[allow(non_camel_case_types)]
    pub type __m256i = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m256 = BitVec<256>;
    #[allow(non_camel_case_types)]
    pub type __m128i = BitVec<128>;
}
