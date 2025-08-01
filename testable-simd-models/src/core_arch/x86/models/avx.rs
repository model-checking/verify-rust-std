//! Advanced Vector Extensions (AVX)
//!
//! The references are:
//!
//! - [Intel 64 and IA-32 Architectures Software Developer's Manual Volume 2:
//!   Instruction Set Reference, A-Z][intel64_ref]. - [AMD64 Architecture
//!   Programmer's Manual, Volume 3: General-Purpose and System
//!   Instructions][amd64_ref].
//!
//! [Wikipedia][wiki] provides a quick overview of the instructions available.
//!
//! [intel64_ref]: http://www.intel.de/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-instruction-set-reference-manual-325383.pdf
//! [amd64_ref]: http://support.amd.com/TechDocs/24594.pdf
//! [wiki]: https://en.wikipedia.org/wiki/Advanced_Vector_Extensions

use super::avx_handwritten::*;
use super::sse::*;
use super::sse2::*;
use super::types::*;
use crate::abstractions::simd::*;
use crate::abstractions::utilities::*;

/// Adds packed double-precision (64-bit) floating-point elements
/// in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_add_pd)
// NOTE: Not modeled yet
// pub fn _mm256_add_pd(a: __m256d, b: __m256d) -> __m256d {
//     { transmute(simd_add(a.as_f64x4(), b.as_f64x4())) }
// }

/// Adds packed single-precision (32-bit) floating-point elements in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_add_ps)
// NOTE: Not modeled yet
// pub fn _mm256_add_ps(a: __m256, b: __m256) -> __m256 {
//     { transmute(simd_add(a.as_f32x8(), b.as_f32x8())) }
// }

/// Computes the bitwise AND of a packed double-precision (64-bit)
/// floating-point elements in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_and_pd)
pub fn _mm256_and_pd(a: __m256d, b: __m256d) -> __m256d {
    {
        let a: u64x4 = transmute(a);
        let b: u64x4 = transmute(b);
        transmute(simd_and(a, b))
    }
}
/// Computes the bitwise AND of packed single-precision (32-bit) floating-point
/// elements in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_and_ps)
pub fn _mm256_and_ps(a: __m256, b: __m256) -> __m256 {
    {
        let a: u32x8 = transmute(a);
        let b: u32x8 = transmute(b);
        transmute(simd_and(a, b))
    }
}
/// Computes the bitwise OR packed double-precision (64-bit) floating-point
/// elements in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_or_pd)
pub fn _mm256_or_pd(a: __m256d, b: __m256d) -> __m256d {
    {
        let a: u64x4 = transmute(a);
        let b: u64x4 = transmute(b);
        transmute(simd_or(a, b))
    }
}
/// Computes the bitwise OR packed single-precision (32-bit) floating-point
/// elements in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_or_ps)
pub fn _mm256_or_ps(a: __m256, b: __m256) -> __m256 {
    {
        let a: u32x8 = transmute(a);
        let b: u32x8 = transmute(b);
        transmute(simd_or(a, b))
    }
}
/// Shuffles double-precision (64-bit) floating-point elements within 128-bit
/// lanes using the control in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_shuffle_pd)
pub fn _mm256_shuffle_pd<const MASK: i32>(a: __m256d, b: __m256d) -> __m256d {
    static_assert_uimm_bits!(MASK, 8);
    {
        transmute(simd_shuffle(
            a.as_f64x4(),
            b.as_f64x4(),
            [
                MASK as u32 & 0b1,
                ((MASK as u32 >> 1) & 0b1) + 4,
                ((MASK as u32 >> 2) & 0b1) + 2,
                ((MASK as u32 >> 3) & 0b1) + 6,
            ],
        ))
    }
}
/// Shuffles single-precision (32-bit) floating-point elements in `a` within
/// 128-bit lanes using the control in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_shuffle_ps)
pub fn _mm256_shuffle_ps<const MASK: i32>(a: __m256, b: __m256) -> __m256 {
    static_assert_uimm_bits!(MASK, 8);
    {
        transmute(simd_shuffle(
            a.as_f32x8(),
            b.as_f32x8(),
            [
                MASK as u32 & 0b11,
                (MASK as u32 >> 2) & 0b11,
                ((MASK as u32 >> 4) & 0b11) + 8,
                ((MASK as u32 >> 6) & 0b11) + 8,
                (MASK as u32 & 0b11) + 4,
                ((MASK as u32 >> 2) & 0b11) + 4,
                ((MASK as u32 >> 4) & 0b11) + 12,
                ((MASK as u32 >> 6) & 0b11) + 12,
            ],
        ))
    }
}
/// Computes the bitwise NOT of packed double-precision (64-bit) floating-point
/// elements in `a`, and then AND with `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_andnot_pd)
pub fn _mm256_andnot_pd(a: __m256d, b: __m256d) -> __m256d {
    {
        let a: u64x4 = transmute(a);
        let b: u64x4 = transmute(b);
        transmute(simd_and(simd_xor(u64x4::splat(!(0_u64)), a), b))
    }
}
/// Computes the bitwise NOT of packed single-precision (32-bit) floating-point
/// elements in `a`
/// and then AND with `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_andnot_ps)
pub fn _mm256_andnot_ps(a: __m256, b: __m256) -> __m256 {
    {
        let a: u32x8 = transmute(a);
        let b: u32x8 = transmute(b);
        transmute(simd_and(simd_xor(u32x8::splat(!(0_u32)), a), b))
    }
}
/// Compares packed double-precision (64-bit) floating-point elements
/// in `a` and `b`, and returns packed maximum values
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_max_pd)
// NOTE: Not modeled yet
// pub fn _mm256_max_pd(a: __m256d, b: __m256d) -> __m256d {
//     { vmaxpd(a, b) }
// }

/// Compares packed single-precision (32-bit) floating-point elements in `a`
/// and `b`, and returns packed maximum values
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_max_ps)
// NOTE: Not modeled yet
// pub fn _mm256_max_ps(a: __m256, b: __m256) -> __m256 {
//     { vmaxps(a, b) }
// }

/// Compares packed double-precision (64-bit) floating-point elements
/// in `a` and `b`, and returns packed minimum values
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_min_pd)
// NOTE: Not modeled yet
// pub fn _mm256_min_pd(a: __m256d, b: __m256d) -> __m256d {
//     { vminpd(a, b) }
// }

/// Compares packed single-precision (32-bit) floating-point elements in `a`
/// and `b`, and returns packed minimum values
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_min_ps)
// NOTE: Not modeled yet
// pub fn _mm256_min_ps(a: __m256, b: __m256) -> __m256 {
//     { vminps(a, b) }
// }

/// Multiplies packed double-precision (64-bit) floating-point elements
/// in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_mul_pd)
// NOTE: Not modeled yet
// pub fn _mm256_mul_pd(a: __m256d, b: __m256d) -> __m256d {
//     { transmute(simd_mul(a.as_f64x4(), b.as_f64x4())) }
// }

/// Multiplies packed single-precision (32-bit) floating-point elements in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_mul_ps)
// NOTE: Not modeled yet
// pub fn _mm256_mul_ps(a: __m256, b: __m256) -> __m256 {
//     { transmute(simd_mul(a.as_f32x8(), b.as_f32x8())) }
// }

/// Alternatively adds and subtracts packed double-precision (64-bit)
/// floating-point elements in `a` to/from packed elements in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_addsub_pd)
// NOTE: Not modeled yet
// pub fn _mm256_addsub_pd(a: __m256d, b: __m256d) -> __m256d {
//     {
//         let a = a.as_f64x4();
//         let b = b.as_f64x4();
//         let add = simd_add(a, b);
//         let sub = simd_sub(a, b);
//         simd_shuffle(add, sub, [4, 1, 6, 3])
//     }
// }

/// Alternatively adds and subtracts packed single-precision (32-bit)
/// floating-point elements in `a` to/from packed elements in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_addsub_ps)
// NOTE: Not modeled yet
// pub fn _mm256_addsub_ps(a: __m256, b: __m256) -> __m256 {
//     {
//         let a = a.as_f32x8();
//         let b = b.as_f32x8();
//         let add = simd_add(a, b);
//         let sub = simd_sub(a, b);
//         simd_shuffle(add, sub, [8, 1, 10, 3, 12, 5, 14, 7])
//     }
// }

/// Subtracts packed double-precision (64-bit) floating-point elements in `b`
/// from packed elements in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_sub_pd)
// NOTE: Not modeled yet
// pub fn _mm256_sub_pd(a: __m256d, b: __m256d) -> __m256d {
//     { simd_sub(a, b) }
// }

/// Subtracts packed single-precision (32-bit) floating-point elements in `b`
/// from packed elements in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_sub_ps)
// NOTE: Not modeled yet
// pub fn _mm256_sub_ps(a: __m256, b: __m256) -> __m256 {
//     { simd_sub(a, b) }
// }

/// Computes the division of each of the 8 packed 32-bit floating-point elements
/// in `a` by the corresponding packed elements in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_div_ps)
// NOTE: Not modeled yet
// pub fn _mm256_div_ps(a: __m256, b: __m256) -> __m256 {
//     { simd_div(a, b) }
// }

/// Computes the division of each of the 4 packed 64-bit floating-point elements
/// in `a` by the corresponding packed elements in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_div_pd)
// NOTE: Not modeled yet
// pub fn _mm256_div_pd(a: __m256d, b: __m256d) -> __m256d {
//     { simd_div(a, b) }
// }

/// Rounds packed double-precision (64-bit) floating point elements in `a`
/// according to the flag `ROUNDING`. The value of `ROUNDING` may be as follows:
///
/// - `0x00`: Round to the nearest whole number.
/// - `0x01`: Round down, toward negative infinity.
/// - `0x02`: Round up, toward positive infinity.
/// - `0x03`: Truncate the values.
///
/// For a complete list of options, check [the LLVM docs][llvm_docs].
///
/// [llvm_docs]: https://github.com/llvm-mirror/clang/blob/dcd8d797b20291f1a6b3e0ddda085aa2bbb382a8/lib/Headers/avxintrin.h#L382
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_round_pd)
// NOTE: Not modeled yet
// pub fn _mm256_round_pd<const ROUNDING: i32>(a: __m256d) -> __m256d {
//     static_assert_uimm_bits!(ROUNDING, 4);
//     { roundpd256(a, ROUNDING) }
// }

/// Rounds packed double-precision (64-bit) floating point elements in `a`
/// toward positive infinity.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_ceil_pd)
// NOTE: Not modeled yet
// pub fn _mm256_ceil_pd(a: __m256d) -> __m256d {
//     { simd_ceil(a) }
// }

/// Rounds packed double-precision (64-bit) floating point elements in `a`
/// toward negative infinity.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_floor_pd)
// NOTE: Not modeled yet
// pub fn _mm256_floor_pd(a: __m256d) -> __m256d {
//     { simd_floor(a) }
// }

/// Rounds packed single-precision (32-bit) floating point elements in `a`
/// according to the flag `ROUNDING`. The value of `ROUNDING` may be as follows:
///
/// - `0x00`: Round to the nearest whole number.
/// - `0x01`: Round down, toward negative infinity.
/// - `0x02`: Round up, toward positive infinity.
/// - `0x03`: Truncate the values.
///
/// For a complete list of options, check [the LLVM docs][llvm_docs].
///
/// [llvm_docs]: https://github.com/llvm-mirror/clang/blob/dcd8d797b20291f1a6b3e0ddda085aa2bbb382a8/lib/Headers/avxintrin.h#L382
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_round_ps)
// NOTE: Not modeled yet
// pub fn _mm256_round_ps<const ROUNDING: i32>(a: __m256) -> __m256 {
//     static_assert_uimm_bits!(ROUNDING, 4);
//     { roundps256(a, ROUNDING) }
// }

/// Rounds packed single-precision (32-bit) floating point elements in `a`
/// toward positive infinity.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_ceil_ps)
// NOTE: Not modeled yet
// pub fn _mm256_ceil_ps(a: __m256) -> __m256 {
//     { simd_ceil(a) }
// }

/// Rounds packed single-precision (32-bit) floating point elements in `a`
/// toward negative infinity.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_floor_ps)
// NOTE: Not modeled yet
// pub fn _mm256_floor_ps(a: __m256) -> __m256 {
//     { simd_floor(a) }
// }

/// Returns the square root of packed single-precision (32-bit) floating point
/// elements in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_sqrt_ps)
// NOTE: Not modeled yet
// pub fn _mm256_sqrt_ps(a: __m256) -> __m256 {
//     { simd_fsqrt(a) }
// }

/// Returns the square root of packed double-precision (64-bit) floating point
/// elements in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_sqrt_pd)
// NOTE: Not modeled yet
// pub fn _mm256_sqrt_pd(a: __m256d) -> __m256d {
//     { simd_fsqrt(a) }
// }

/// Blends packed double-precision (64-bit) floating-point elements from
/// `a` and `b` using control mask `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_blend_pd)
pub fn _mm256_blend_pd<const IMM4: i32>(a: __m256d, b: __m256d) -> __m256d {
    static_assert_uimm_bits!(IMM4, 4);
    {
        transmute(simd_shuffle(
            a.as_f64x4(),
            b.as_f64x4(),
            [
                ((IMM4 as u32 >> 0) & 1) * 4 + 0,
                ((IMM4 as u32 >> 1) & 1) * 4 + 1,
                ((IMM4 as u32 >> 2) & 1) * 4 + 2,
                ((IMM4 as u32 >> 3) & 1) * 4 + 3,
            ],
        ))
    }
}
/// Blends packed single-precision (32-bit) floating-point elements from
/// `a` and `b` using control mask `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_blend_ps)
pub fn _mm256_blend_ps<const IMM8: i32>(a: __m256, b: __m256) -> __m256 {
    static_assert_uimm_bits!(IMM8, 8);
    {
        transmute(simd_shuffle(
            a.as_f32x8(),
            b.as_f32x8(),
            [
                ((IMM8 as u32 >> 0) & 1) * 8 + 0,
                ((IMM8 as u32 >> 1) & 1) * 8 + 1,
                ((IMM8 as u32 >> 2) & 1) * 8 + 2,
                ((IMM8 as u32 >> 3) & 1) * 8 + 3,
                ((IMM8 as u32 >> 4) & 1) * 8 + 4,
                ((IMM8 as u32 >> 5) & 1) * 8 + 5,
                ((IMM8 as u32 >> 6) & 1) * 8 + 6,
                ((IMM8 as u32 >> 7) & 1) * 8 + 7,
            ],
        ))
    }
}
/// Blends packed double-precision (64-bit) floating-point elements from
/// `a` and `b` using `c` as a mask.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_blendv_pd)
pub fn _mm256_blendv_pd(a: __m256d, b: __m256d, c: __m256d) -> __m256d {
    {
        let mask: i64x4 = simd_lt(transmute::<_, i64x4>(c), i64x4::ZERO());
        transmute(simd_select(mask, b.as_f64x4(), a.as_f64x4()))
    }
}
/// Blends packed single-precision (32-bit) floating-point elements from
/// `a` and `b` using `c` as a mask.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_blendv_ps)
pub fn _mm256_blendv_ps(a: __m256, b: __m256, c: __m256) -> __m256 {
    {
        let mask: i32x8 = simd_lt(transmute::<_, i32x8>(c), i32x8::ZERO());
        transmute(simd_select(mask, b.as_f32x8(), a.as_f32x8()))
    }
}
/// Conditionally multiplies the packed single-precision (32-bit) floating-point
/// elements in `a` and `b` using the high 4 bits in `imm8`,
/// sum the four products, and conditionally return the sum
///  using the low 4 bits of `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_dp_ps)
// NOTE: Not modeled yet
// pub fn _mm256_dp_ps<const IMM8: i32>(a: __m256, b: __m256) -> __m256 {
//     static_assert_uimm_bits!(IMM8, 8);
//     { vdpps(a, b, IMM8 as i8) }
// }

/// Horizontal addition of adjacent pairs in the two packed vectors
/// of 4 64-bit floating points `a` and `b`.
/// In the result, sums of elements from `a` are returned in even locations,
/// while sums of elements from `b` are returned in odd locations.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_hadd_pd)
// NOTE: Not modeled yet
// pub fn _mm256_hadd_pd(a: __m256d, b: __m256d) -> __m256d {
//     { vhaddpd(a, b) }
// }

/// Horizontal addition of adjacent pairs in the two packed vectors
/// of 8 32-bit floating points `a` and `b`.
/// In the result, sums of elements from `a` are returned in locations of
/// indices 0, 1, 4, 5; while sums of elements from `b` are locations
/// 2, 3, 6, 7.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_hadd_ps)
// NOTE: Not modeled yet
// pub fn _mm256_hadd_ps(a: __m256, b: __m256) -> __m256 {
//     { vhaddps(a, b) }
// }

/// Horizontal subtraction of adjacent pairs in the two packed vectors
/// of 4 64-bit floating points `a` and `b`.
/// In the result, sums of elements from `a` are returned in even locations,
/// while sums of elements from `b` are returned in odd locations.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_hsub_pd)
// NOTE: Not modeled yet
// pub fn _mm256_hsub_pd(a: __m256d, b: __m256d) -> __m256d {
//     { vhsubpd(a, b) }
// }

/// Horizontal subtraction of adjacent pairs in the two packed vectors
/// of 8 32-bit floating points `a` and `b`.
/// In the result, sums of elements from `a` are returned in locations of
/// indices 0, 1, 4, 5; while sums of elements from `b` are locations
/// 2, 3, 6, 7.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_hsub_ps)
// NOTE: Not modeled yet
// pub fn _mm256_hsub_ps(a: __m256, b: __m256) -> __m256 {
//     { vhsubps(a, b) }
// }

/// Computes the bitwise XOR of packed double-precision (64-bit) floating-point
/// elements in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_xor_pd)
pub fn _mm256_xor_pd(a: __m256d, b: __m256d) -> __m256d {
    {
        let a: u64x4 = transmute(a);
        let b: u64x4 = transmute(b);
        transmute(simd_xor(a, b))
    }
}
/// Computes the bitwise XOR of packed single-precision (32-bit) floating-point
/// elements in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_xor_ps)
pub fn _mm256_xor_ps(a: __m256, b: __m256) -> __m256 {
    {
        let a: u32x8 = transmute(a);
        let b: u32x8 = transmute(b);
        transmute(simd_xor(a, b))
    }
}
/// Equal (ordered, non-signaling)
pub const _CMP_EQ_OQ: i32 = 0x00;
/// Less-than (ordered, signaling)
pub const _CMP_LT_OS: i32 = 0x01;
/// Less-than-or-equal (ordered, signaling)
pub const _CMP_LE_OS: i32 = 0x02;
/// Unordered (non-signaling)
pub const _CMP_UNORD_Q: i32 = 0x03;
/// Not-equal (unordered, non-signaling)
pub const _CMP_NEQ_UQ: i32 = 0x04;
/// Not-less-than (unordered, signaling)
pub const _CMP_NLT_US: i32 = 0x05;
/// Not-less-than-or-equal (unordered, signaling)
pub const _CMP_NLE_US: i32 = 0x06;
/// Ordered (non-signaling)
pub const _CMP_ORD_Q: i32 = 0x07;
/// Equal (unordered, non-signaling)
pub const _CMP_EQ_UQ: i32 = 0x08;
/// Not-greater-than-or-equal (unordered, signaling)
pub const _CMP_NGE_US: i32 = 0x09;
/// Not-greater-than (unordered, signaling)
pub const _CMP_NGT_US: i32 = 0x0a;
/// False (ordered, non-signaling)
pub const _CMP_FALSE_OQ: i32 = 0x0b;
/// Not-equal (ordered, non-signaling)
pub const _CMP_NEQ_OQ: i32 = 0x0c;
/// Greater-than-or-equal (ordered, signaling)
pub const _CMP_GE_OS: i32 = 0x0d;
/// Greater-than (ordered, signaling)
pub const _CMP_GT_OS: i32 = 0x0e;
/// True (unordered, non-signaling)
pub const _CMP_TRUE_UQ: i32 = 0x0f;
/// Equal (ordered, signaling)
pub const _CMP_EQ_OS: i32 = 0x10;
/// Less-than (ordered, non-signaling)
pub const _CMP_LT_OQ: i32 = 0x11;
/// Less-than-or-equal (ordered, non-signaling)
pub const _CMP_LE_OQ: i32 = 0x12;
/// Unordered (signaling)
pub const _CMP_UNORD_S: i32 = 0x13;
/// Not-equal (unordered, signaling)
pub const _CMP_NEQ_US: i32 = 0x14;
/// Not-less-than (unordered, non-signaling)
pub const _CMP_NLT_UQ: i32 = 0x15;
/// Not-less-than-or-equal (unordered, non-signaling)
pub const _CMP_NLE_UQ: i32 = 0x16;
/// Ordered (signaling)
pub const _CMP_ORD_S: i32 = 0x17;
/// Equal (unordered, signaling)
pub const _CMP_EQ_US: i32 = 0x18;
/// Not-greater-than-or-equal (unordered, non-signaling)
pub const _CMP_NGE_UQ: i32 = 0x19;
/// Not-greater-than (unordered, non-signaling)
pub const _CMP_NGT_UQ: i32 = 0x1a;
/// False (ordered, signaling)
pub const _CMP_FALSE_OS: i32 = 0x1b;
/// Not-equal (ordered, signaling)
pub const _CMP_NEQ_OS: i32 = 0x1c;
/// Greater-than-or-equal (ordered, non-signaling)
pub const _CMP_GE_OQ: i32 = 0x1d;
/// Greater-than (ordered, non-signaling)
pub const _CMP_GT_OQ: i32 = 0x1e;
/// True (unordered, signaling)
pub const _CMP_TRUE_US: i32 = 0x1f;
/// Compares packed double-precision (64-bit) floating-point
/// elements in `a` and `b` based on the comparison operand
/// specified by `IMM5`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_cmp_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmp_pd<const IMM5: i32>(a: __m128d, b: __m128d) -> __m128d {
//     static_assert_uimm_bits!(IMM5, 5);
//     { vcmppd(a, b, const { IMM5 as i8 }) }
// }

/// Compares packed double-precision (64-bit) floating-point
/// elements in `a` and `b` based on the comparison operand
/// specified by `IMM5`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cmp_pd)
// NOTE: Not modeled yet
// pub fn _mm256_cmp_pd<const IMM5: i32>(a: __m256d, b: __m256d) -> __m256d {
//     static_assert_uimm_bits!(IMM5, 5);
//     { vcmppd256(a, b, IMM5 as u8) }
// }

/// Compares packed single-precision (32-bit) floating-point
/// elements in `a` and `b` based on the comparison operand
/// specified by `IMM5`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_cmp_ps)
// NOTE: Not modeled yet
// pub fn _mm_cmp_ps<const IMM5: i32>(a: __m128, b: __m128) -> __m128 {
//     static_assert_uimm_bits!(IMM5, 5);
//     { vcmpps(a, b, const { IMM5 as i8 }) }
// }

/// Compares packed single-precision (32-bit) floating-point
/// elements in `a` and `b` based on the comparison operand
/// specified by `IMM5`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cmp_ps)
// NOTE: Not modeled yet
// pub fn _mm256_cmp_ps<const IMM5: i32>(a: __m256, b: __m256) -> __m256 {
//     static_assert_uimm_bits!(IMM5, 5);
//     { vcmpps256(a, b, const { IMM5 as u8 }) }
// }

/// Compares the lower double-precision (64-bit) floating-point element in
/// `a` and `b` based on the comparison operand specified by `IMM5`,
/// store the result in the lower element of returned vector,
/// and copies the upper element from `a` to the upper element of returned
/// vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_cmp_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmp_sd<const IMM5: i32>(a: __m128d, b: __m128d) -> __m128d {
//     static_assert_uimm_bits!(IMM5, 5);
//     { vcmpsd(a, b, IMM5 as i8) }
// }

/// Compares the lower single-precision (32-bit) floating-point element in
/// `a` and `b` based on the comparison operand specified by `IMM5`,
/// store the result in the lower element of returned vector,
/// and copies the upper 3 packed elements from `a` to the upper elements of
/// returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_cmp_ss)
// NOTE: Not modeled yet
// pub fn _mm_cmp_ss<const IMM5: i32>(a: __m128, b: __m128) -> __m128 {
//     static_assert_uimm_bits!(IMM5, 5);
//     { vcmpss(a, b, IMM5 as i8) }
// }

/// Converts packed 32-bit integers in `a` to packed double-precision (64-bit)
/// floating-point elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtepi32_pd)
pub fn _mm256_cvtepi32_pd(a: __m128i) -> __m256d {
    transmute(simd_cast::<4, i32, f64>(a.as_i32x4()))
}
/// Converts packed 32-bit integers in `a` to packed single-precision (32-bit)
/// floating-point elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtepi32_ps)
pub fn _mm256_cvtepi32_ps(a: __m256i) -> __m256 {
    transmute(simd_cast::<8, _, f32>(a.as_i32x8()))
}
/// Converts packed double-precision (64-bit) floating-point elements in `a`
/// to packed single-precision (32-bit) floating-point elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtpd_ps)
pub fn _mm256_cvtpd_ps(a: __m256d) -> __m128 {
    transmute(simd_cast::<4, _, f32>(a.as_f64x4()))
}
/// Converts packed single-precision (32-bit) floating-point elements in `a`
/// to packed 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtps_epi32)
// NOTE: Not modeled yet
// pub fn _mm256_cvtps_epi32(a: __m256) -> __m256i {
//     { transmute(vcvtps2dq(a)) }
// }

/// Converts packed single-precision (32-bit) floating-point elements in `a`
/// to packed double-precision (64-bit) floating-point elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtps_pd)
pub fn _mm256_cvtps_pd(a: __m128) -> __m256d {
    transmute(simd_cast::<4, _, f64>(a.as_f32x4()))
}
/// Returns the first element of the input vector of `[4 x double]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtsd_f64)
pub fn _mm256_cvtsd_f64(a: __m256d) -> f64 {
    simd_extract(a.as_f64x4(), 0)
}

/// Converts packed double-precision (64-bit) floating-point elements in `a`
/// to packed 32-bit integers with truncation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvttpd_epi32)
// NOTE: Not modeled yet
// pub fn _mm256_cvttpd_epi32(a: __m256d) -> __m128i {
//     { transmute(vcvttpd2dq(a)) }
// }

/// Converts packed double-precision (64-bit) floating-point elements in `a`
/// to packed 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtpd_epi32)
// NOTE: Not modeled yet
// pub fn _mm256_cvtpd_epi32(a: __m256d) -> __m128i {
//     { transmute(vcvtpd2dq(a)) }
// }

/// Converts packed single-precision (32-bit) floating-point elements in `a`
/// to packed 32-bit integers with truncation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvttps_epi32)
// NOTE: Not modeled yet
// pub fn _mm256_cvttps_epi32(a: __m256) -> __m256i {
//     { transmute(vcvttps2dq(a)) }
// }

/// Extracts 128 bits (composed of 4 packed single-precision (32-bit)
/// floating-point elements) from `a`, selected with `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_extractf128_ps)
pub fn _mm256_extractf128_ps<const IMM1: i32>(a: __m256) -> __m128 {
    static_assert_uimm_bits!(IMM1, 1);
    {
        transmute(simd_shuffle(
            a.as_f32x8(),
            _mm256_undefined_ps().as_f32x8(),
            [[0, 1, 2, 3], [4, 5, 6, 7]][IMM1 as usize],
        ))
    }
}
/// Extracts 128 bits (composed of 2 packed double-precision (64-bit)
/// floating-point elements) from `a`, selected with `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_extractf128_pd)
pub fn _mm256_extractf128_pd<const IMM1: i32>(a: __m256d) -> __m128d {
    static_assert_uimm_bits!(IMM1, 1);
    transmute(simd_shuffle(
        a.as_f64x4(),
        _mm256_undefined_pd().as_f64x4(),
        [[0, 1], [2, 3]][IMM1 as usize],
    ))
}
/// Extracts 128 bits (composed of integer data) from `a`, selected with `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_extractf128_si256)
pub fn _mm256_extractf128_si256<const IMM1: i32>(a: __m256i) -> __m128i {
    static_assert_uimm_bits!(IMM1, 1);
    {
        let dst: i64x2 = simd_shuffle(a.as_i64x4(), i64x4::ZERO(), [[0, 1], [2, 3]][IMM1 as usize]);
        transmute(dst)
    }
}
/// Extracts a 32-bit integer from `a`, selected with `INDEX`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_extract_epi32)
pub fn _mm256_extract_epi32<const INDEX: i32>(a: __m256i) -> i32 {
    static_assert_uimm_bits!(INDEX, 3);
    simd_extract(a.as_i32x8(), INDEX as u32)
}
/// Returns the first element of the input vector of `[8 x i32]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtsi256_si32)
pub fn _mm256_cvtsi256_si32(a: __m256i) -> i32 {
    simd_extract(a.as_i32x8(), 0)
}
/// Zeroes the contents of all XMM or YMM registers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_zeroall)
// NOTE: Not modeled yet
// pub fn _mm256_zeroall() {
//     { vzeroall() }
// }

/// Zeroes the upper 128 bits of all YMM registers;
/// the lower 128-bits of the registers are unmodified.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_zeroupper)
// NOTE: Not modeled yet
// pub fn _mm256_zeroupper() {
//     { vzeroupper() }
// }

/// Shuffles single-precision (32-bit) floating-point elements in `a`
/// within 128-bit lanes using the control in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_permutevar_ps)
// NOTE: Not modeled yet
// pub fn _mm256_permutevar_ps(a: __m256, b: __m256i) -> __m256 {
//     { vpermilps256(a, b.as_i32x8()) }
// }

/// Shuffles single-precision (32-bit) floating-point elements in `a`
/// using the control in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_permutevar_ps)
// NOTE: Not modeled yet
// pub fn _mm_permutevar_ps(a: __m128, b: __m128i) -> __m128 {
//     { vpermilps(a, b.as_i32x4()) }
// }

/// Shuffles single-precision (32-bit) floating-point elements in `a`
/// within 128-bit lanes using the control in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_permute_ps)
pub fn _mm256_permute_ps<const IMM8: i32>(a: __m256) -> __m256 {
    static_assert_uimm_bits!(IMM8, 8);
    {
        transmute(simd_shuffle(
            a.as_f32x8(),
            _mm256_undefined_ps().as_f32x8(),
            [
                (IMM8 as u32 >> 0) & 0b11,
                (IMM8 as u32 >> 2) & 0b11,
                (IMM8 as u32 >> 4) & 0b11,
                (IMM8 as u32 >> 6) & 0b11,
                ((IMM8 as u32 >> 0) & 0b11) + 4,
                ((IMM8 as u32 >> 2) & 0b11) + 4,
                ((IMM8 as u32 >> 4) & 0b11) + 4,
                ((IMM8 as u32 >> 6) & 0b11) + 4,
            ],
        ))
    }
}
/// Shuffles single-precision (32-bit) floating-point elements in `a`
/// using the control in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_permute_ps)
pub fn _mm_permute_ps<const IMM8: i32>(a: __m128) -> __m128 {
    static_assert_uimm_bits!(IMM8, 8);
    {
        transmute(simd_shuffle(
            a.as_f32x4(),
            _mm_undefined_ps().as_f32x4(),
            [
                (IMM8 as u32 >> 0) & 0b11,
                (IMM8 as u32 >> 2) & 0b11,
                (IMM8 as u32 >> 4) & 0b11,
                (IMM8 as u32 >> 6) & 0b11,
            ],
        ))
    }
}

/// Shuffles double-precision (64-bit) floating-point elements in `a`
/// within 256-bit lanes using the control in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_permutevar_pd)
// NOTE: Not modeled yet
// pub fn _mm256_permutevar_pd(a: __m256d, b: __m256i) -> __m256d {
//     { vpermilpd256(a, b.as_i64x4()) }
// }

/// Shuffles double-precision (64-bit) floating-point elements in `a`
/// using the control in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_permutevar_pd)
// NOTE: Not modeled yet
// pub fn _mm_permutevar_pd(a: __m128d, b: __m128i) -> __m128d {
//     { vpermilpd(a, b.as_i64x2()) }
// }

/// Shuffles double-precision (64-bit) floating-point elements in `a`
/// within 128-bit lanes using the control in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_permute_pd)
pub fn _mm256_permute_pd<const IMM4: i32>(a: __m256d) -> __m256d {
    static_assert_uimm_bits!(IMM4, 4);
    {
        transmute(simd_shuffle(
            a.as_f64x4(),
            _mm256_undefined_pd().as_f64x4(),
            [
                ((IMM4 as u32 >> 0) & 1),
                ((IMM4 as u32 >> 1) & 1),
                ((IMM4 as u32 >> 2) & 1) + 2,
                ((IMM4 as u32 >> 3) & 1) + 2,
            ],
        ))
    }
}
/// Shuffles double-precision (64-bit) floating-point elements in `a`
/// using the control in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_permute_pd)
pub fn _mm_permute_pd<const IMM2: i32>(a: __m128d) -> __m128d {
    static_assert_uimm_bits!(IMM2, 2);
    {
        transmute(simd_shuffle(
            a.as_f64x2(),
            _mm_undefined_pd().as_f64x2(),
            [(IMM2 as u32) & 1, (IMM2 as u32 >> 1) & 1],
        ))
    }
}
/// Shuffles 256 bits (composed of 8 packed single-precision (32-bit)
/// floating-point elements) selected by `imm8` from `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_permute2f128_ps)
// NOTE: Not modeled yet
// pub fn _mm256_permute2f128_ps<const IMM8: i32>(a: __m256, b: __m256) -> __m256 {
//     static_assert_uimm_bits!(IMM8, 8);
//     { vperm2f128ps256(a, b, IMM8 as i8) }
// }
/// Shuffles 256 bits (composed of 4 packed double-precision (64-bit)
/// floating-point elements) selected by `imm8` from `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_permute2f128_pd)
// NOTE: Not modeled yet
// pub fn _mm256_permute2f128_pd<const IMM8: i32>(a: __m256d, b: __m256d) -> __m256d {
//     static_assert_uimm_bits!(IMM8, 8);
//     { vperm2f128pd256(a, b, IMM8 as i8) }
// }
/// Shuffles 128-bits (composed of integer data) selected by `imm8`
/// from `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_permute2f128_si256)
pub fn _mm256_permute2f128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    transmute(vperm2f128si256(a.as_i32x8(), b.as_i32x8(), IMM8 as i8))
}
/// Broadcasts a single-precision (32-bit) floating-point element from memory
/// to all elements of the returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_broadcast_ss)
pub fn _mm256_broadcast_ss(f: &f32) -> __m256 {
    _mm256_set1_ps(*f)
}
/// Broadcasts a single-precision (32-bit) floating-point element from memory
/// to all elements of the returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_broadcast_ss)
// NOTE: Not modeled yet
// pub fn _mm_broadcast_ss(f: &f32) -> __m128 {
//     _mm_set1_ps(*f)
// }
/// Broadcasts a double-precision (64-bit) floating-point element from memory
/// to all elements of the returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_broadcast_sd)
// NOTE: Not modeled yet
// pub fn _mm256_broadcast_sd(f: &f64) -> __m256d {
//     _mm256_set1_pd(*f)
// }
/// Broadcasts 128 bits from memory (composed of 4 packed single-precision
/// (32-bit) floating-point elements) to all elements of the returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_broadcast_ps)
pub fn _mm256_broadcast_ps(a: &__m128) -> __m256 {
    {
        transmute(simd_shuffle(
            (*a).as_f32x4(),
            _mm_setzero_ps().as_f32x4(),
            [0, 1, 2, 3, 0, 1, 2, 3],
        ))
    }
}
/// Broadcasts 128 bits from memory (composed of 2 packed double-precision
/// (64-bit) floating-point elements) to all elements of the returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_broadcast_pd)
pub fn _mm256_broadcast_pd(a: &__m128d) -> __m256d {
    transmute(simd_shuffle(
        (*a).as_f64x2(),
        _mm_setzero_pd().as_f64x2(),
        [0, 1, 0, 1],
    ))
}
/// Copies `a` to result, then inserts 128 bits (composed of 4 packed
/// single-precision (32-bit) floating-point elements) from `b` into result
/// at the location specified by `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_insertf128_ps)
pub fn _mm256_insertf128_ps<const IMM1: i32>(a: __m256, b: __m128) -> __m256 {
    static_assert_uimm_bits!(IMM1, 1);
    {
        transmute(simd_shuffle(
            a.as_f32x8(),
            _mm256_castps128_ps256(b).as_f32x8(),
            [[8, 9, 10, 11, 4, 5, 6, 7], [0, 1, 2, 3, 8, 9, 10, 11]][IMM1 as usize],
        ))
    }
}
/// Copies `a` to result, then inserts 128 bits (composed of 2 packed
/// double-precision (64-bit) floating-point elements) from `b` into result
/// at the location specified by `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_insertf128_pd)
pub fn _mm256_insertf128_pd<const IMM1: i32>(a: __m256d, b: __m128d) -> __m256d {
    static_assert_uimm_bits!(IMM1, 1);
    {
        transmute(simd_shuffle(
            a.as_f64x4(),
            _mm256_castpd128_pd256(b).as_f64x4(),
            [[4, 5, 2, 3], [0, 1, 4, 5]][IMM1 as usize],
        ))
    }
}
/// Copies `a` to result, then inserts 128 bits from `b` into result
/// at the location specified by `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_insertf128_si256)
pub fn _mm256_insertf128_si256<const IMM1: i32>(a: __m256i, b: __m128i) -> __m256i {
    static_assert_uimm_bits!(IMM1, 1);
    {
        let dst: i64x4 = simd_shuffle(
            a.as_i64x4(),
            _mm256_castsi128_si256(b).as_i64x4(),
            [[4, 5, 2, 3], [0, 1, 4, 5]][IMM1 as usize],
        );
        transmute(dst)
    }
}
/// Copies `a` to result, and inserts the 8-bit integer `i` into result
/// at the location specified by `index`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_insert_epi8)
pub fn _mm256_insert_epi8<const INDEX: i32>(a: __m256i, i: i8) -> __m256i {
    static_assert_uimm_bits!(INDEX, 5);
    transmute(simd_insert(a.as_i8x32(), INDEX as u32, i))
}
/// Copies `a` to result, and inserts the 16-bit integer `i` into result
/// at the location specified by `index`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_insert_epi16)
pub fn _mm256_insert_epi16<const INDEX: i32>(a: __m256i, i: i16) -> __m256i {
    static_assert_uimm_bits!(INDEX, 4);
    transmute(simd_insert(a.as_i16x16(), INDEX as u32, i))
}
/// Copies `a` to result, and inserts the 32-bit integer `i` into result
/// at the location specified by `index`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_insert_epi32)
pub fn _mm256_insert_epi32<const INDEX: i32>(a: __m256i, i: i32) -> __m256i {
    static_assert_uimm_bits!(INDEX, 3);
    transmute(simd_insert(a.as_i32x8(), INDEX as u32, i))
}
/// Duplicate odd-indexed single-precision (32-bit) floating-point elements
/// from `a`, and returns the results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_movehdup_ps)
pub fn _mm256_movehdup_ps(a: __m256) -> __m256 {
    transmute(simd_shuffle(
        a.as_f32x8(),
        a.as_f32x8(),
        [1, 1, 3, 3, 5, 5, 7, 7],
    ))
}
/// Duplicate even-indexed single-precision (32-bit) floating-point elements
/// from `a`, and returns the results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_moveldup_ps)
pub fn _mm256_moveldup_ps(a: __m256) -> __m256 {
    transmute(simd_shuffle(
        a.as_f32x8(),
        a.as_f32x8(),
        [0, 0, 2, 2, 4, 4, 6, 6],
    ))
}
/// Duplicate even-indexed double-precision (64-bit) floating-point elements
/// from `a`, and returns the results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_movedup_pd)
pub fn _mm256_movedup_pd(a: __m256d) -> __m256d {
    transmute(simd_shuffle(a.as_f64x4(), a.as_f64x4(), [0, 0, 2, 2]))
}
/// Computes the approximate reciprocal of packed single-precision (32-bit)
/// floating-point elements in `a`, and returns the results. The maximum
/// relative error for this approximation is less than 1.5*2^-12.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_rcp_ps)
// NOTE: Not modeled yet
// pub fn _mm256_rcp_ps(a: __m256) -> __m256 {
//     { vrcpps(a) }
// }
/// Computes the approximate reciprocal square root of packed single-precision
/// (32-bit) floating-point elements in `a`, and returns the results.
/// The maximum relative error for this approximation is less than 1.5*2^-12.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_rsqrt_ps)
// NOTE: Not modeled yet
// pub fn _mm256_rsqrt_ps(a: __m256) -> __m256 {
//     { vrsqrtps(a) }
// }
/// Unpacks and interleave double-precision (64-bit) floating-point elements
/// from the high half of each 128-bit lane in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_unpackhi_pd)
pub fn _mm256_unpackhi_pd(a: __m256d, b: __m256d) -> __m256d {
    transmute(simd_shuffle(a.as_f64x4(), b.as_f64x4(), [1, 5, 3, 7]))
}
/// Unpacks and interleave single-precision (32-bit) floating-point elements
/// from the high half of each 128-bit lane in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_unpackhi_ps)
pub fn _mm256_unpackhi_ps(a: __m256, b: __m256) -> __m256 {
    transmute(simd_shuffle(
        a.as_f32x8(),
        b.as_f32x8(),
        [2, 10, 3, 11, 6, 14, 7, 15],
    ))
}
/// Unpacks and interleave double-precision (64-bit) floating-point elements
/// from the low half of each 128-bit lane in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_unpacklo_pd)
pub fn _mm256_unpacklo_pd(a: __m256d, b: __m256d) -> __m256d {
    transmute(simd_shuffle(a.as_f64x4(), b.as_f64x4(), [0, 4, 2, 6]))
}
/// Unpacks and interleave single-precision (32-bit) floating-point elements
/// from the low half of each 128-bit lane in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_unpacklo_ps)
pub fn _mm256_unpacklo_ps(a: __m256, b: __m256) -> __m256 {
    transmute(simd_shuffle(
        a.as_f32x8(),
        b.as_f32x8(),
        [0, 8, 1, 9, 4, 12, 5, 13],
    ))
}
/// Computes the bitwise AND of 256 bits (representing integer data) in `a` and
/// `b`, and set `ZF` to 1 if the result is zero, otherwise set `ZF` to 0.
/// Computes the bitwise NOT of `a` and then AND with `b`, and set `CF` to 1 if
/// the result is zero, otherwise set `CF` to 0. Return the `ZF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testz_si256)
pub fn _mm256_testz_si256(a: __m256i, b: __m256i) -> i32 {
    ptestz256(a.as_i64x4(), b.as_i64x4())
}
/// Computes the bitwise AND of 256 bits (representing integer data) in `a` and
/// `b`, and set `ZF` to 1 if the result is zero, otherwise set `ZF` to 0.
/// Computes the bitwise NOT of `a` and then AND with `b`, and set `CF` to 1 if
/// the result is zero, otherwise set `CF` to 0. Return the `CF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testc_si256)
pub fn _mm256_testc_si256(a: __m256i, b: __m256i) -> i32 {
    ptestc256(a.as_i64x4(), b.as_i64x4())
}

/// Computes the bitwise AND of 256 bits (representing integer data) in `a` and
/// `b`, and set `ZF` to 1 if the result is zero, otherwise set `ZF` to 0.
/// Computes the bitwise NOT of `a` and then AND with `b`, and set `CF` to 1 if
/// the result is zero, otherwise set `CF` to 0. Return 1 if both the `ZF` and
/// `CF` values are zero, otherwise return 0.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testnzc_si256)
// NOTE: Not modeled yet
// pub fn _mm256_testnzc_si256(a: __m256i, b: __m256i) -> i32 {
//     { ptestnzc256(a.as_i64x4(), b.as_i64x4()) }
// }

/// Computes the bitwise AND of 256 bits (representing double-precision (64-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 256-bit
/// value, and set `ZF` to 1 if the sign bit of each 64-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 64-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `ZF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testz_pd)
// NOTE: Not modeled yet
// pub fn _mm256_testz_pd(a: __m256d, b: __m256d) -> i32 {
//     { vtestzpd256(a, b) }
// }

/// Computes the bitwise AND of 256 bits (representing double-precision (64-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 256-bit
/// value, and set `ZF` to 1 if the sign bit of each 64-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 64-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `CF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testc_pd)
// NOTE: Not modeled yet
// pub fn _mm256_testc_pd(a: __m256d, b: __m256d) -> i32 {
//     { vtestcpd256(a, b) }
// }

/// Computes the bitwise AND of 256 bits (representing double-precision (64-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 256-bit
/// value, and set `ZF` to 1 if the sign bit of each 64-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 64-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return 1 if both the `ZF` and `CF` values
/// are zero, otherwise return 0.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testnzc_pd)
// NOTE: Not modeled yet
// pub fn _mm256_testnzc_pd(a: __m256d, b: __m256d) -> i32 {
//     { vtestnzcpd256(a, b) }
// }

/// Computes the bitwise AND of 128 bits (representing double-precision (64-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 128-bit
/// value, and set `ZF` to 1 if the sign bit of each 64-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 64-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `ZF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_testz_pd)
// NOTE: Not modeled yet
// pub fn _mm_testz_pd(a: __m128d, b: __m128d) -> i32 {
//     { vtestzpd(a, b) }
// }

/// Computes the bitwise AND of 128 bits (representing double-precision (64-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 128-bit
/// value, and set `ZF` to 1 if the sign bit of each 64-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 64-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `CF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_testc_pd)
// NOTE: Not modeled yet
// pub fn _mm_testc_pd(a: __m128d, b: __m128d) -> i32 {
//     { vtestcpd(a, b) }
// }

/// Computes the bitwise AND of 128 bits (representing double-precision (64-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 128-bit
/// value, and set `ZF` to 1 if the sign bit of each 64-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 64-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return 1 if both the `ZF` and `CF` values
/// are zero, otherwise return 0.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_testnzc_pd)
// NOTE: Not modeled yet
// pub fn _mm_testnzc_pd(a: __m128d, b: __m128d) -> i32 {
//     { vtestnzcpd(a, b) }
// }

/// Computes the bitwise AND of 256 bits (representing single-precision (32-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 256-bit
/// value, and set `ZF` to 1 if the sign bit of each 32-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 32-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `ZF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testz_ps)
// NOTE: Not modeled yet
// pub fn _mm256_testz_ps(a: __m256, b: __m256) -> i32 {
//     { vtestzps256(a, b) }
// }

/// Computes the bitwise AND of 256 bits (representing single-precision (32-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 256-bit
/// value, and set `ZF` to 1 if the sign bit of each 32-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 32-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `CF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testc_ps)
// NOTE: Not modeled yet
// pub fn _mm256_testc_ps(a: __m256, b: __m256) -> i32 {
//     { vtestcps256(a, b) }
// }

/// Computes the bitwise AND of 256 bits (representing single-precision (32-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 256-bit
/// value, and set `ZF` to 1 if the sign bit of each 32-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 32-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return 1 if both the `ZF` and `CF` values
/// are zero, otherwise return 0.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_testnzc_ps)
// NOTE: Not modeled yet
// pub fn _mm256_testnzc_ps(a: __m256, b: __m256) -> i32 {
//     { vtestnzcps256(a, b) }
// }

/// Computes the bitwise AND of 128 bits (representing single-precision (32-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 128-bit
/// value, and set `ZF` to 1 if the sign bit of each 32-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 32-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `ZF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_testz_ps)
// NOTE: Not modeled yet
// pub fn _mm_testz_ps(a: __m128, b: __m128) -> i32 {
//     { vtestzps(a, b) }
// }

/// Computes the bitwise AND of 128 bits (representing single-precision (32-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 128-bit
/// value, and set `ZF` to 1 if the sign bit of each 32-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 32-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return the `CF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_testc_ps)
// NOTE: Not modeled yet
// pub fn _mm_testc_ps(a: __m128, b: __m128) -> i32 {
//     { vtestcps(a, b) }
// }

/// Computes the bitwise AND of 128 bits (representing single-precision (32-bit)
/// floating-point elements) in `a` and `b`, producing an intermediate 128-bit
/// value, and set `ZF` to 1 if the sign bit of each 32-bit element in the
/// intermediate value is zero, otherwise set `ZF` to 0. Compute the bitwise
/// NOT of `a` and then AND with `b`, producing an intermediate value, and set
/// `CF` to 1 if the sign bit of each 32-bit element in the intermediate value
/// is zero, otherwise set `CF` to 0. Return 1 if both the `ZF` and `CF` values
/// are zero, otherwise return 0.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm_testnzc_ps)
// NOTE: Not modeled yet
// pub fn _mm_testnzc_ps(a: __m128, b: __m128) -> i32 {
//     { vtestnzcps(a, b) }
// }

/// Sets each bit of the returned mask based on the most significant bit of the
/// corresponding packed double-precision (64-bit) floating-point element in
/// `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_movemask_pd)
pub fn _mm256_movemask_pd(a: __m256d) -> i32 {
    {
        let mask: i64x4 = simd_lt(a.as_i64x4(), i64x4::ZERO());
        simd_bitmask_little!(3, mask, u8) as i32
    }
}
/// Sets each bit of the returned mask based on the most significant bit of the
/// corresponding packed single-precision (32-bit) floating-point element in
/// `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_movemask_ps)
pub fn _mm256_movemask_ps(a: __m256) -> i32 {
    {
        let mask: i32x8 = simd_lt(transmute(a), i32x8::ZERO());
        simd_bitmask_little!(7, mask, u8) as i32
    }
}
/// Returns vector of type __m256d with all elements set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setzero_pd)
pub fn _mm256_setzero_pd() -> __m256d {
    transmute(f64x4::ZERO())
}
/// Returns vector of type __m256 with all elements set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setzero_ps)
pub fn _mm256_setzero_ps() -> __m256 {
    transmute(f32x8::ZERO())
}
/// Returns vector of type __m256i with all elements set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setzero_si256)
pub fn _mm256_setzero_si256() -> __m256i {
    transmute(i64x4::ZERO())
}
/// Sets packed double-precision (64-bit) floating-point elements in returned
/// vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_pd)
pub fn _mm256_set_pd(a: f64, b: f64, c: f64, d: f64) -> __m256d {
    _mm256_setr_pd(d, c, b, a)
}
/// Sets packed single-precision (32-bit) floating-point elements in returned
/// vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_ps)
pub fn _mm256_set_ps(a: f32, b: f32, c: f32, d: f32, e: f32, f: f32, g: f32, h: f32) -> __m256 {
    _mm256_setr_ps(h, g, f, e, d, c, b, a)
}
/// Sets packed 8-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_epi8)
pub fn _mm256_set_epi8(
    e00: i8,
    e01: i8,
    e02: i8,
    e03: i8,
    e04: i8,
    e05: i8,
    e06: i8,
    e07: i8,
    e08: i8,
    e09: i8,
    e10: i8,
    e11: i8,
    e12: i8,
    e13: i8,
    e14: i8,
    e15: i8,
    e16: i8,
    e17: i8,
    e18: i8,
    e19: i8,
    e20: i8,
    e21: i8,
    e22: i8,
    e23: i8,
    e24: i8,
    e25: i8,
    e26: i8,
    e27: i8,
    e28: i8,
    e29: i8,
    e30: i8,
    e31: i8,
) -> __m256i {
    _mm256_setr_epi8(
        e31, e30, e29, e28, e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14,
        e13, e12, e11, e10, e09, e08, e07, e06, e05, e04, e03, e02, e01, e00,
    )
}
/// Sets packed 16-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_epi16)
pub fn _mm256_set_epi16(
    e00: i16,
    e01: i16,
    e02: i16,
    e03: i16,
    e04: i16,
    e05: i16,
    e06: i16,
    e07: i16,
    e08: i16,
    e09: i16,
    e10: i16,
    e11: i16,
    e12: i16,
    e13: i16,
    e14: i16,
    e15: i16,
) -> __m256i {
    _mm256_setr_epi16(
        e15, e14, e13, e12, e11, e10, e09, e08, e07, e06, e05, e04, e03, e02, e01, e00,
    )
}
/// Sets packed 32-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_epi32)
pub fn _mm256_set_epi32(
    e0: i32,
    e1: i32,
    e2: i32,
    e3: i32,
    e4: i32,
    e5: i32,
    e6: i32,
    e7: i32,
) -> __m256i {
    _mm256_setr_epi32(e7, e6, e5, e4, e3, e2, e1, e0)
}
/// Sets packed 64-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_epi64x)
pub fn _mm256_set_epi64x(a: i64, b: i64, c: i64, d: i64) -> __m256i {
    _mm256_setr_epi64x(d, c, b, a)
}
/// Sets packed double-precision (64-bit) floating-point elements in returned
/// vector with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_pd)
pub fn _mm256_setr_pd(a: f64, b: f64, c: f64, d: f64) -> __m256d {
    transmute(f64x4::new(a, b, c, d))
}
/// Sets packed single-precision (32-bit) floating-point elements in returned
/// vector with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_ps)
pub fn _mm256_setr_ps(a: f32, b: f32, c: f32, d: f32, e: f32, f: f32, g: f32, h: f32) -> __m256 {
    transmute(f32x8::new(a, b, c, d, e, f, g, h))
}
/// Sets packed 8-bit integers in returned vector with the supplied values in
/// reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_epi8)
pub fn _mm256_setr_epi8(
    e00: i8,
    e01: i8,
    e02: i8,
    e03: i8,
    e04: i8,
    e05: i8,
    e06: i8,
    e07: i8,
    e08: i8,
    e09: i8,
    e10: i8,
    e11: i8,
    e12: i8,
    e13: i8,
    e14: i8,
    e15: i8,
    e16: i8,
    e17: i8,
    e18: i8,
    e19: i8,
    e20: i8,
    e21: i8,
    e22: i8,
    e23: i8,
    e24: i8,
    e25: i8,
    e26: i8,
    e27: i8,
    e28: i8,
    e29: i8,
    e30: i8,
    e31: i8,
) -> __m256i {
    {
        transmute(i8x32::new(
            e00, e01, e02, e03, e04, e05, e06, e07, e08, e09, e10, e11, e12, e13, e14, e15, e16,
            e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31,
        ))
    }
}
/// Sets packed 16-bit integers in returned vector with the supplied values in
/// reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_epi16)
pub fn _mm256_setr_epi16(
    e00: i16,
    e01: i16,
    e02: i16,
    e03: i16,
    e04: i16,
    e05: i16,
    e06: i16,
    e07: i16,
    e08: i16,
    e09: i16,
    e10: i16,
    e11: i16,
    e12: i16,
    e13: i16,
    e14: i16,
    e15: i16,
) -> __m256i {
    {
        transmute(i16x16::new(
            e00, e01, e02, e03, e04, e05, e06, e07, e08, e09, e10, e11, e12, e13, e14, e15,
        ))
    }
}
/// Sets packed 32-bit integers in returned vector with the supplied values in
/// reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_epi32)
pub fn _mm256_setr_epi32(
    e0: i32,
    e1: i32,
    e2: i32,
    e3: i32,
    e4: i32,
    e5: i32,
    e6: i32,
    e7: i32,
) -> __m256i {
    transmute(i32x8::new(e0, e1, e2, e3, e4, e5, e6, e7))
}
/// Sets packed 64-bit integers in returned vector with the supplied values in
/// reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_epi64x)
pub fn _mm256_setr_epi64x(a: i64, b: i64, c: i64, d: i64) -> __m256i {
    transmute(i64x4::new(a, b, c, d))
}
/// Broadcasts double-precision (64-bit) floating-point value `a` to all
/// elements of returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set1_pd)
pub fn _mm256_set1_pd(a: f64) -> __m256d {
    _mm256_setr_pd(a, a, a, a)
}
/// Broadcasts single-precision (32-bit) floating-point value `a` to all
/// elements of returned vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set1_ps)
pub fn _mm256_set1_ps(a: f32) -> __m256 {
    _mm256_setr_ps(a, a, a, a, a, a, a, a)
}
/// Broadcasts 8-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastb`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set1_epi8)
pub fn _mm256_set1_epi8(a: i8) -> __m256i {
    _mm256_setr_epi8(
        a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a,
        a, a,
    )
}
/// Broadcasts 16-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastw`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set1_epi16)
pub fn _mm256_set1_epi16(a: i16) -> __m256i {
    _mm256_setr_epi16(a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a)
}
/// Broadcasts 32-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastd`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set1_epi32)
pub fn _mm256_set1_epi32(a: i32) -> __m256i {
    _mm256_setr_epi32(a, a, a, a, a, a, a, a)
}
/// Broadcasts 64-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastq`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set1_epi64x)
pub fn _mm256_set1_epi64x(a: i64) -> __m256i {
    _mm256_setr_epi64x(a, a, a, a)
}
/// Cast vector of type __m256d to type __m256.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castpd_ps)
pub fn _mm256_castpd_ps(a: __m256d) -> __m256 {
    transmute(a)
}
/// Cast vector of type __m256 to type __m256d.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castps_pd)
pub fn _mm256_castps_pd(a: __m256) -> __m256d {
    transmute(a)
}
/// Casts vector of type __m256 to type __m256i.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castps_si256)
pub fn _mm256_castps_si256(a: __m256) -> __m256i {
    transmute(a)
}
/// Casts vector of type __m256i to type __m256.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castsi256_ps)
pub fn _mm256_castsi256_ps(a: __m256i) -> __m256 {
    transmute(a)
}
/// Casts vector of type __m256d to type __m256i.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castpd_si256)
pub fn _mm256_castpd_si256(a: __m256d) -> __m256i {
    transmute(a)
}
/// Casts vector of type __m256i to type __m256d.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castsi256_pd)
pub fn _mm256_castsi256_pd(a: __m256i) -> __m256d {
    transmute(a)
}
/// Casts vector of type __m256 to type __m128.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castps256_ps128)
pub fn _mm256_castps256_ps128(a: __m256) -> __m128 {
    transmute(simd_shuffle(a.as_f32x8(), a.as_f32x8(), [0, 1, 2, 3]))
}
/// Casts vector of type __m256d to type __m128d.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castpd256_pd128)
pub fn _mm256_castpd256_pd128(a: __m256d) -> __m128d {
    transmute(simd_shuffle(a.as_f64x4(), a.as_f64x4(), [0, 1]))
}
/// Casts vector of type __m256i to type __m128i.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castsi256_si128)
pub fn _mm256_castsi256_si128(a: __m256i) -> __m128i {
    {
        let a = a.as_i64x4();
        let dst: i64x2 = simd_shuffle(a, a, [0, 1]);
        transmute(dst)
    }
}
/// Casts vector of type __m128 to type __m256;
/// the upper 128 bits of the result are undefined.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castps128_ps256)
pub fn _mm256_castps128_ps256(a: __m128) -> __m256 {
    {
        transmute(simd_shuffle(
            a.as_f32x4(),
            _mm_undefined_ps().as_f32x4(),
            [0, 1, 2, 3, 4, 4, 4, 4],
        ))
    }
}
/// Casts vector of type __m128d to type __m256d;
/// the upper 128 bits of the result are undefined.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castpd128_pd256)
pub fn _mm256_castpd128_pd256(a: __m128d) -> __m256d {
    transmute(simd_shuffle(
        a.as_f64x2(),
        _mm_undefined_pd().as_f64x2(),
        [0, 1, 2, 2],
    ))
}
/// Casts vector of type __m128i to type __m256i;
/// the upper 128 bits of the result are undefined.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_castsi128_si256)
pub fn _mm256_castsi128_si256(a: __m128i) -> __m256i {
    {
        let a = a.as_i64x2();
        let undefined = i64x2::ZERO();
        let dst: i64x4 = simd_shuffle(a, undefined, [0, 1, 2, 2]);
        transmute(dst)
    }
}
/// Constructs a 256-bit floating-point vector of `[8 x float]` from a
/// 128-bit floating-point vector of `[4 x float]`. The lower 128 bits contain
/// the value of the source vector. The upper 128 bits are set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_zextps128_ps256)
pub fn _mm256_zextps128_ps256(a: __m128) -> __m256 {
    {
        transmute(simd_shuffle(
            a.as_f32x4(),
            _mm_setzero_ps().as_f32x4(),
            [0, 1, 2, 3, 4, 5, 6, 7],
        ))
    }
}
/// Constructs a 256-bit integer vector from a 128-bit integer vector.
/// The lower 128 bits contain the value of the source vector. The upper
/// 128 bits are set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_zextsi128_si256)
pub fn _mm256_zextsi128_si256(a: __m128i) -> __m256i {
    {
        let b = i64x2::ZERO();
        let dst: i64x4 = simd_shuffle(a.as_i64x2(), b, [0, 1, 2, 3]);
        transmute(dst)
    }
}
/// Constructs a 256-bit floating-point vector of `[4 x double]` from a
/// 128-bit floating-point vector of `[2 x double]`. The lower 128 bits
/// contain the value of the source vector. The upper 128 bits are set
/// to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_zextpd128_pd256)
// NOTE: Not modeled yet
pub fn _mm256_zextpd128_pd256(a: __m128d) -> __m256d {
    {
        transmute(simd_shuffle(
            a.as_f64x2(),
            _mm_setzero_pd().as_f64x2(),
            [0, 1, 2, 3],
        ))
    }
}
/// Returns vector of type `__m256` with indeterminate elements.
/// Despite using the word "undefined" (following Intel's naming scheme), this non-deterministically
/// picks some valid value and is not equivalent to [`mem::MaybeUninit`].
/// In practice, this is typically equivalent to [`mem::zeroed`].
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_undefined_ps)
pub fn _mm256_undefined_ps() -> __m256 {
    transmute(f32x8::ZERO())
}
/// Returns vector of type `__m256d` with indeterminate elements.
/// Despite using the word "undefined" (following Intel's naming scheme), this non-deterministically
/// picks some valid value and is not equivalent to [`mem::MaybeUninit`].
/// In practice, this is typically equivalent to [`mem::zeroed`].
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_undefined_pd)
pub fn _mm256_undefined_pd() -> __m256d {
    transmute(f32x8::ZERO())
}
/// Returns vector of type __m256i with with indeterminate elements.
/// Despite using the word "undefined" (following Intel's naming scheme), this non-deterministically
/// picks some valid value and is not equivalent to [`mem::MaybeUninit`].
/// In practice, this is typically equivalent to [`mem::zeroed`].
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_undefined_si256)
pub fn _mm256_undefined_si256() -> __m256i {
    transmute(i32x8::ZERO())
}
/// Sets packed __m256 returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_m128)
pub fn _mm256_set_m128(hi: __m128, lo: __m128) -> __m256 {
    transmute(simd_shuffle(
        lo.as_i32x4(),
        hi.as_i32x4(),
        [0, 1, 2, 3, 4, 5, 6, 7],
    ))
}
/// Sets packed __m256d returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_m128d)
pub fn _mm256_set_m128d(hi: __m128d, lo: __m128d) -> __m256d {
    {
        let hi: __m128 = transmute(hi);
        let lo: __m128 = transmute(lo);
        transmute(_mm256_set_m128(hi, lo))
    }
}
/// Sets packed __m256i returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_set_m128i)
pub fn _mm256_set_m128i(hi: __m128i, lo: __m128i) -> __m256i {
    {
        let hi: __m128 = transmute(hi);
        let lo: __m128 = transmute(lo);
        transmute(_mm256_set_m128(hi, lo))
    }
}
/// Sets packed __m256 returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_m128)
pub fn _mm256_setr_m128(lo: __m128, hi: __m128) -> __m256 {
    _mm256_set_m128(hi, lo)
}
/// Sets packed __m256d returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_m128d)
pub fn _mm256_setr_m128d(lo: __m128d, hi: __m128d) -> __m256d {
    _mm256_set_m128d(hi, lo)
}
/// Sets packed __m256i returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_setr_m128i)
pub fn _mm256_setr_m128i(lo: __m128i, hi: __m128i) -> __m256i {
    _mm256_set_m128i(hi, lo)
}
/// Returns the first element of the input vector of `[8 x float]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.htmlext=_mm256_cvtss_f32)
pub fn _mm256_cvtss_f32(a: __m256) -> f32 {
    simd_extract(a.as_f32x8(), 0)
}
