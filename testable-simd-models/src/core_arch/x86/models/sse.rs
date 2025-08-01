//! Streaming SIMD Extensions (SSE)
use super::types::*;
use crate::abstractions::simd::*;
use crate::abstractions::utilities::*;

/// Returns vector of type __m128 with indeterminate elements.with indetermination elements.
/// Despite using the word "undefined" (following Intel's naming scheme), this non-deterministically
/// picks some valid value and is not equivalent to [`mem::MaybeUninit`].
/// In practice, this is typically equivalent to [`mem::zeroed`].
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_undefined_ps)
pub fn _mm_undefined_ps() -> __m128 {
    transmute(f32x4::ZERO())
}

/// Construct a `__m128` with all elements initialized to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setzero_ps)
pub fn _mm_setzero_ps() -> __m128 {
    transmute(f32x4::ZERO())
}
