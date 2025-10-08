//! Advanced Vector Extensions 2 (AVX)
//!
//!
//! This module contains models for AVX2 intrinsics.
//! AVX2 expands most AVX commands to 256-bit wide vector registers and
//! adds [FMA](https://en.wikipedia.org/wiki/Fused_multiply-accumulate).
//!
//! The references are:
//!
//! - [Intel 64 and IA-32 Architectures Software Developer's Manual Volume 2:
//!   Instruction Set Reference, A-Z][intel64_ref].
//! - [AMD64 Architecture Programmer's Manual, Volume 3: General-Purpose and
//!   System Instructions][amd64_ref].
//!
//! Wikipedia's [AVX][wiki_avx] and [FMA][wiki_fma] pages provide a quick
//! overview of the instructions available.
//!
//! [intel64_ref]: http://www.intel.de/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-instruction-set-reference-manual-325383.pdf
//! [amd64_ref]: http://support.amd.com/TechDocs/24594.pdf
//! [wiki_avx]: https://en.wikipedia.org/wiki/Advanced_Vector_Extensions
//! [wiki_fma]: https://en.wikipedia.org/wiki/Fused_multiply-accumulate
use crate::abstractions::simd::*;
use crate::abstractions::utilities::*;

use super::avx::*;
use super::avx2_handwritten::*;
use super::sse::*;
use super::sse2::*;
use super::types::*;

/// Computes the absolute values of packed 32-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi32)
pub fn _mm256_abs_epi32(a: __m256i) -> __m256i {
    {
        let a = a.as_i32x8();
        let r = simd_select(simd_lt(a, i32x8::ZERO()), simd_neg(a), a);
        transmute(r)
    }
}
/// Computes the absolute values of packed 16-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi16)
pub fn _mm256_abs_epi16(a: __m256i) -> __m256i {
    {
        let a = a.as_i16x16();
        let r = simd_select(simd_lt(a, i16x16::ZERO()), simd_neg(a), a);
        transmute(r)
    }
}
/// Computes the absolute values of packed 8-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi8)
pub fn _mm256_abs_epi8(a: __m256i) -> __m256i {
    {
        let a = a.as_i8x32();
        let r = simd_select(simd_lt(a, i8x32::ZERO()), simd_neg(a), a);
        transmute(r)
    }
}
/// Adds packed 64-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi64)
pub fn _mm256_add_epi64(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_add(a.as_i64x4(), b.as_i64x4()))
    }
}
/// Adds packed 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi32)
pub fn _mm256_add_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_add(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Adds packed 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi16)
pub fn _mm256_add_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_add(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Adds packed 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi8)
pub fn _mm256_add_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_add(a.as_i8x32(), b.as_i8x32()))
    }
}
/// Adds packed 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epi8)
pub fn _mm256_adds_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_add(a.as_i8x32(), b.as_i8x32()))
    }
}
/// Adds packed 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epi16)
pub fn _mm256_adds_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_add(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Adds packed unsigned 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epu8)
pub fn _mm256_adds_epu8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_add(a.as_u8x32(), b.as_u8x32()))
    }
}
/// Adds packed unsigned 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epu16)
pub fn _mm256_adds_epu16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_add(a.as_u16x16(), b.as_u16x16()))
    }
}
/// Concatenates pairs of 16-byte blocks in `a` and `b` into a 32-byte temporary
/// result, shifts the result right by `n` bytes, and returns the low 16 bytes.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_alignr_epi8)
pub fn _mm256_alignr_epi8<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    if IMM8 >= 32 {
        return _mm256_setzero_si256();
    }
    let (a, b) = if IMM8 > 16 {
        (_mm256_setzero_si256(), a)
    } else {
        (a, b)
    };
    {
        if IMM8 == 16 {
            return transmute(a);
        }
    }
    const fn mask(shift: u32, i: u32) -> u32 {
        let shift = shift % 16;
        let mod_i = i % 16;
        if mod_i < (16 - shift) {
            i + shift
        } else {
            i + 16 + shift
        }
    }
    {
        let r: i8x32 = simd_shuffle(
            b.as_i8x32(),
            a.as_i8x32(),
            [
                mask(IMM8 as u32, 0),
                mask(IMM8 as u32, 1),
                mask(IMM8 as u32, 2),
                mask(IMM8 as u32, 3),
                mask(IMM8 as u32, 4),
                mask(IMM8 as u32, 5),
                mask(IMM8 as u32, 6),
                mask(IMM8 as u32, 7),
                mask(IMM8 as u32, 8),
                mask(IMM8 as u32, 9),
                mask(IMM8 as u32, 10),
                mask(IMM8 as u32, 11),
                mask(IMM8 as u32, 12),
                mask(IMM8 as u32, 13),
                mask(IMM8 as u32, 14),
                mask(IMM8 as u32, 15),
                mask(IMM8 as u32, 16),
                mask(IMM8 as u32, 17),
                mask(IMM8 as u32, 18),
                mask(IMM8 as u32, 19),
                mask(IMM8 as u32, 20),
                mask(IMM8 as u32, 21),
                mask(IMM8 as u32, 22),
                mask(IMM8 as u32, 23),
                mask(IMM8 as u32, 24),
                mask(IMM8 as u32, 25),
                mask(IMM8 as u32, 26),
                mask(IMM8 as u32, 27),
                mask(IMM8 as u32, 28),
                mask(IMM8 as u32, 29),
                mask(IMM8 as u32, 30),
                mask(IMM8 as u32, 31),
            ],
        );
        transmute(r)
    }
}
/// Computes the bitwise AND of 256 bits (representing integer data)
/// in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_and_si256)
pub fn _mm256_and_si256(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_and(a.as_i64x4(), b.as_i64x4()))
    }
}
/// Computes the bitwise NOT of 256 bits (representing integer data)
/// in `a` and then AND with `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_andnot_si256)
pub fn _mm256_andnot_si256(a: __m256i, b: __m256i) -> __m256i {
    {
        let all_ones = _mm256_set1_epi8(-1);
        transmute(simd_and(
            simd_xor(a.as_i64x4(), all_ones.as_i64x4()),
            b.as_i64x4(),
        ))
    }
}
/// Averages packed unsigned 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_avg_epu16)
pub fn _mm256_avg_epu16(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = simd_cast::<16, _, u32>(a.as_u16x16());
        let b = simd_cast::<16, _, u32>(b.as_u16x16());
        let r = simd_shr(simd_add(simd_add(a, b), u32x16::splat(1)), u32x16::splat(1));
        transmute(simd_cast::<16, _, u16>(r))
    }
}
/// Averages packed unsigned 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_avg_epu8)
pub fn _mm256_avg_epu8(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = simd_cast::<32, _, u16>(a.as_u8x32());
        let b = simd_cast::<32, _, u16>(b.as_u8x32());
        let r = simd_shr(simd_add(simd_add(a, b), u16x32::splat(1)), u16x32::splat(1));
        transmute(simd_cast::<32, _, u8>(r))
    }
}
/// Blends packed 32-bit integers from `a` and `b` using control mask `IMM4`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_blend_epi32)
pub fn _mm_blend_epi32<const IMM4: i32>(a: __m128i, b: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM4, 4);
    {
        let a = a.as_i32x4();
        let b = b.as_i32x4();
        let r: i32x4 = simd_shuffle(
            a,
            b,
            [
                [0, 4, 0, 4][IMM4 as usize & 0b11],
                [1, 1, 5, 5][IMM4 as usize & 0b11],
                [2, 6, 2, 6][(IMM4 as usize >> 2) & 0b11],
                [3, 3, 7, 7][(IMM4 as usize >> 2) & 0b11],
            ],
        );
        transmute(r)
    }
}
/// Blends packed 32-bit integers from `a` and `b` using control mask `IMM8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi32)
pub fn _mm256_blend_epi32<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let a = a.as_i32x8();
        let b = b.as_i32x8();
        let r: i32x8 = simd_shuffle(
            a,
            b,
            [
                [0, 8, 0, 8][IMM8 as usize & 0b11],
                [1, 1, 9, 9][IMM8 as usize & 0b11],
                [2, 10, 2, 10][(IMM8 as usize >> 2) & 0b11],
                [3, 3, 11, 11][(IMM8 as usize >> 2) & 0b11],
                [4, 12, 4, 12][(IMM8 as usize >> 4) & 0b11],
                [5, 5, 13, 13][(IMM8 as usize >> 4) & 0b11],
                [6, 14, 6, 14][(IMM8 as usize >> 6) & 0b11],
                [7, 7, 15, 15][(IMM8 as usize >> 6) & 0b11],
            ],
        );
        transmute(r)
    }
}
/// Blends packed 16-bit integers from `a` and `b` using control mask `IMM8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi16)
pub fn _mm256_blend_epi16<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let a = a.as_i16x16();
        let b = b.as_i16x16();
        let r: i16x16 = simd_shuffle(
            a,
            b,
            [
                [0, 16, 0, 16][IMM8 as usize & 0b11],
                [1, 1, 17, 17][IMM8 as usize & 0b11],
                [2, 18, 2, 18][(IMM8 as usize >> 2) & 0b11],
                [3, 3, 19, 19][(IMM8 as usize >> 2) & 0b11],
                [4, 20, 4, 20][(IMM8 as usize >> 4) & 0b11],
                [5, 5, 21, 21][(IMM8 as usize >> 4) & 0b11],
                [6, 22, 6, 22][(IMM8 as usize >> 6) & 0b11],
                [7, 7, 23, 23][(IMM8 as usize >> 6) & 0b11],
                [8, 24, 8, 24][IMM8 as usize & 0b11],
                [9, 9, 25, 25][IMM8 as usize & 0b11],
                [10, 26, 10, 26][(IMM8 as usize >> 2) & 0b11],
                [11, 11, 27, 27][(IMM8 as usize >> 2) & 0b11],
                [12, 28, 12, 28][(IMM8 as usize >> 4) & 0b11],
                [13, 13, 29, 29][(IMM8 as usize >> 4) & 0b11],
                [14, 30, 14, 30][(IMM8 as usize >> 6) & 0b11],
                [15, 15, 31, 31][(IMM8 as usize >> 6) & 0b11],
            ],
        );
        transmute(r)
    }
}
/// Blends packed 8-bit integers from `a` and `b` using `mask`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_epi8)
pub fn _mm256_blendv_epi8(a: __m256i, b: __m256i, mask: __m256i) -> __m256i {
    {
        let mask: i8x32 = simd_lt(mask.as_i8x32(), i8x32::ZERO());
        transmute(simd_select(mask, b.as_i8x32(), a.as_i8x32()))
    }
}
/// Broadcasts the low packed 8-bit integer from `a` to all elements of
/// the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastb_epi8)
pub fn _mm_broadcastb_epi8(a: __m128i) -> __m128i {
    {
        let ret = simd_shuffle(a.as_i8x16(), i8x16::ZERO(), [0_u32; 16]);
        transmute::<i8x16, _>(ret)
    }
}
/// Broadcasts the low packed 8-bit integer from `a` to all elements of
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastb_epi8)
pub fn _mm256_broadcastb_epi8(a: __m128i) -> __m256i {
    {
        let ret = simd_shuffle(a.as_i8x16(), i8x16::ZERO(), [0_u32; 32]);
        transmute::<i8x32, _>(ret)
    }
}
/// Broadcasts the low packed 32-bit integer from `a` to all elements of
/// the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastd_epi32)
pub fn _mm_broadcastd_epi32(a: __m128i) -> __m128i {
    {
        let ret = simd_shuffle(a.as_i32x4(), i32x4::ZERO(), [0_u32; 4]);
        transmute::<i32x4, _>(ret)
    }
}
/// Broadcasts the low packed 32-bit integer from `a` to all elements of
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastd_epi32)
pub fn _mm256_broadcastd_epi32(a: __m128i) -> __m256i {
    {
        let ret = simd_shuffle(a.as_i32x4(), i32x4::ZERO(), [0_u32; 8]);
        transmute::<i32x8, _>(ret)
    }
}
/// Broadcasts the low packed 64-bit integer from `a` to all elements of
/// the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastq_epi64)
pub fn _mm_broadcastq_epi64(a: __m128i) -> __m128i {
    {
        let ret = simd_shuffle(a.as_i64x2(), a.as_i64x2(), [0_u32; 2]);
        transmute::<i64x2, _>(ret)
    }
}
/// Broadcasts the low packed 64-bit integer from `a` to all elements of
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastq_epi64)
pub fn _mm256_broadcastq_epi64(a: __m128i) -> __m256i {
    {
        let ret = simd_shuffle(a.as_i64x2(), a.as_i64x2(), [0_u32; 4]);
        transmute::<i64x4, _>(ret)
    }
}
/// Broadcasts the low double-precision (64-bit) floating-point element
/// from `a` to all elements of the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastsd_pd)
pub fn _mm_broadcastsd_pd(a: __m128d) -> __m128d {
    {
        transmute(simd_shuffle(
            a.as_f64x2(),
            _mm_setzero_pd().as_f64x2(),
            [0_u32; 2],
        ))
    }
}
/// Broadcasts the low double-precision (64-bit) floating-point element
/// from `a` to all elements of the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastsd_pd)
pub fn _mm256_broadcastsd_pd(a: __m128d) -> __m256d {
    {
        transmute(simd_shuffle(
            a.as_f64x2(),
            _mm_setzero_pd().as_f64x2(),
            [0_u32; 4],
        ))
    }
}
/// Broadcasts 128 bits of integer data from a to all 128-bit lanes in
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastsi128_si256)
pub fn _mm_broadcastsi128_si256(a: __m128i) -> __m256i {
    {
        let ret = simd_shuffle(a.as_i64x2(), i64x2::ZERO(), [0, 1, 0, 1]);
        transmute::<i64x4, _>(ret)
    }
}
/// Broadcasts 128 bits of integer data from a to all 128-bit lanes in
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastsi128_si256)
pub fn _mm256_broadcastsi128_si256(a: __m128i) -> __m256i {
    {
        let ret = simd_shuffle(a.as_i64x2(), i64x2::ZERO(), [0, 1, 0, 1]);
        transmute::<i64x4, _>(ret)
    }
}
/// Broadcasts the low single-precision (32-bit) floating-point element
/// from `a` to all elements of the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastss_ps)
pub fn _mm_broadcastss_ps(a: __m128) -> __m128 {
    {
        transmute(simd_shuffle(
            a.as_f32x4(),
            _mm_setzero_ps().as_f32x4(),
            [0_u32; 4],
        ))
    }
}
/// Broadcasts the low single-precision (32-bit) floating-point element
/// from `a` to all elements of the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastss_ps)
pub fn _mm256_broadcastss_ps(a: __m128) -> __m256 {
    {
        transmute(simd_shuffle(
            a.as_f32x4(),
            _mm_setzero_ps().as_f32x4(),
            [0_u32; 8],
        ))
    }
}
/// Broadcasts the low packed 16-bit integer from a to all elements of
/// the 128-bit returned value
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastw_epi16)
pub fn _mm_broadcastw_epi16(a: __m128i) -> __m128i {
    {
        let ret = simd_shuffle(a.as_i16x8(), i16x8::ZERO(), [0_u32; 8]);
        transmute::<i16x8, _>(ret)
    }
}
/// Broadcasts the low packed 16-bit integer from a to all elements of
/// the 256-bit returned value
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastw_epi16)
pub fn _mm256_broadcastw_epi16(a: __m128i) -> __m256i {
    {
        let ret = simd_shuffle(a.as_i16x8(), i16x8::ZERO(), [0_u32; 16]);
        transmute::<i16x16, _>(ret)
    }
}
/// Compares packed 64-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi64)
pub fn _mm256_cmpeq_epi64(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i64x4, _>(simd_eq(a.as_i64x4(), b.as_i64x4()))
    }
}
/// Compares packed 32-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi32)
pub fn _mm256_cmpeq_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i32x8, _>(simd_eq(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Compares packed 16-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi16)
pub fn _mm256_cmpeq_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i16x16, _>(simd_eq(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Compares packed 8-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi8)
pub fn _mm256_cmpeq_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i8x32, _>(simd_eq(a.as_i8x32(), b.as_i8x32()))
    }
}
/// Compares packed 64-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi64)
pub fn _mm256_cmpgt_epi64(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i64x4, _>(simd_gt(a.as_i64x4(), b.as_i64x4()))
    }
}
/// Compares packed 32-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi32)
pub fn _mm256_cmpgt_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i32x8, _>(simd_gt(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Compares packed 16-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi16)
pub fn _mm256_cmpgt_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i16x16, _>(simd_gt(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Compares packed 8-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi8)
pub fn _mm256_cmpgt_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute::<i8x32, _>(simd_gt(a.as_i8x32(), b.as_i8x32()))
    }
}
/// Sign-extend 16-bit integers to 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi32)
pub fn _mm256_cvtepi16_epi32(a: __m128i) -> __m256i {
    {
        transmute::<i32x8, _>(simd_cast(a.as_i16x8()))
    }
}
/// Sign-extend 16-bit integers to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi64)
pub fn _mm256_cvtepi16_epi64(a: __m128i) -> __m256i {
    {
        let a = a.as_i16x8();
        let v64: i16x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
        transmute::<i64x4, _>(simd_cast(v64))
    }
}
/// Sign-extend 32-bit integers to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi32_epi64)
pub fn _mm256_cvtepi32_epi64(a: __m128i) -> __m256i {
    {
        transmute::<i64x4, _>(simd_cast(a.as_i32x4()))
    }
}
/// Sign-extend 8-bit integers to 16-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi16)
pub fn _mm256_cvtepi8_epi16(a: __m128i) -> __m256i {
    {
        transmute::<i16x16, _>(simd_cast(a.as_i8x16()))
    }
}
/// Sign-extend 8-bit integers to 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi32)
pub fn _mm256_cvtepi8_epi32(a: __m128i) -> __m256i {
    {
        let a = a.as_i8x16();
        let v64: i8x8 = simd_shuffle(a, a, [0, 1, 2, 3, 4, 5, 6, 7]);
        transmute::<i32x8, _>(simd_cast(v64))
    }
}
/// Sign-extend 8-bit integers to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi64)
pub fn _mm256_cvtepi8_epi64(a: __m128i) -> __m256i {
    {
        let a = a.as_i8x16();
        let v32: i8x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
        transmute::<i64x4, _>(simd_cast(v32))
    }
}
/// Zeroes extend packed unsigned 16-bit integers in `a` to packed 32-bit
/// integers, and stores the results in `dst`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu16_epi32)
pub fn _mm256_cvtepu16_epi32(a: __m128i) -> __m256i {
    {
        transmute(simd_cast::<8, _, u32>(a.as_u16x8()))
    }
}
/// Zero-extend the lower four unsigned 16-bit integers in `a` to 64-bit
/// integers. The upper four elements of `a` are unused.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu16_epi64)
pub fn _mm256_cvtepu16_epi64(a: __m128i) -> __m256i {
    {
        let a = a.as_u16x8();
        let v64: u16x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
        transmute(simd_cast::<4, _, u64>(v64))
    }
}
/// Zero-extend unsigned 32-bit integers in `a` to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu32_epi64)
pub fn _mm256_cvtepu32_epi64(a: __m128i) -> __m256i {
    {
        transmute(simd_cast::<4, _, u64>(a.as_u32x4()))
    }
}
/// Zero-extend unsigned 8-bit integers in `a` to 16-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi16)
pub fn _mm256_cvtepu8_epi16(a: __m128i) -> __m256i {
    {
        transmute(simd_cast::<16, _, u16>(a.as_u8x16()))
    }
}
/// Zero-extend the lower eight unsigned 8-bit integers in `a` to 32-bit
/// integers. The upper eight elements of `a` are unused.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi32)
pub fn _mm256_cvtepu8_epi32(a: __m128i) -> __m256i {
    {
        let a = a.as_u8x16();
        let v64: u8x8 = simd_shuffle(a, a, [0, 1, 2, 3, 4, 5, 6, 7]);
        transmute(simd_cast::<8, _, u32>(v64))
    }
}
/// Zero-extend the lower four unsigned 8-bit integers in `a` to 64-bit
/// integers. The upper twelve elements of `a` are unused.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi64)
pub fn _mm256_cvtepu8_epi64(a: __m128i) -> __m256i {
    {
        let a = a.as_u8x16();
        let v32: u8x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
        transmute(simd_cast::<4, _, u64>(v32))
    }
}
/// Extracts 128 bits (of integer data) from `a` selected with `IMM1`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extracti128_si256)
pub fn _mm256_extracti128_si256<const IMM1: i32>(a: __m256i) -> __m128i {
    static_assert_uimm_bits!(IMM1, 1);
    {
        let a = a.as_i64x4();
        let b = i64x4::ZERO();
        let dst: i64x2 = simd_shuffle(a, b, [[0, 1], [2, 3]][IMM1 as usize]);
        transmute(dst)
    }
}
/// Horizontally adds adjacent pairs of 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadd_epi16)
pub fn _mm256_hadd_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(phaddw(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Horizontally adds adjacent pairs of 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadd_epi32)
pub fn _mm256_hadd_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(phaddd(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Horizontally adds adjacent pairs of 16-bit integers in `a` and `b`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadds_epi16)
pub fn _mm256_hadds_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(phaddsw(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Horizontally subtract adjacent pairs of 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsub_epi16)
pub fn _mm256_hsub_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(phsubw(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Horizontally subtract adjacent pairs of 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsub_epi32)
pub fn _mm256_hsub_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(phsubd(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Horizontally subtract adjacent pairs of 16-bit integers in `a` and `b`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsubs_epi16)
pub fn _mm256_hsubs_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(phsubsw(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Copies `a` to `dst`, then insert 128 bits (of integer data) from `b` at the
/// location specified by `IMM1`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_inserti128_si256)
pub fn _mm256_inserti128_si256<const IMM1: i32>(a: __m256i, b: __m128i) -> __m256i {
    static_assert_uimm_bits!(IMM1, 1);
    {
        let a = a.as_i64x4();
        let b = _mm256_castsi128_si256(b).as_i64x4();
        let dst: i64x4 = simd_shuffle(a, b, [[4, 5, 2, 3], [0, 1, 4, 5]][IMM1 as usize]);
        transmute(dst)
    }
}
/// Multiplies packed signed 16-bit integers in `a` and `b`, producing
/// intermediate signed 32-bit integers. Horizontally add adjacent pairs
/// of intermediate 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_madd_epi16)
pub fn _mm256_madd_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(pmaddwd(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Vertically multiplies each unsigned 8-bit integer from `a` with the
/// corresponding signed 8-bit integer from `b`, producing intermediate
/// signed 16-bit integers. Horizontally add adjacent pairs of intermediate
/// signed 16-bit integers
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_maddubs_epi16)
pub fn _mm256_maddubs_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(pmaddubsw(a.as_u8x32(), b.as_u8x32()))
    }
}
/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi16)
pub fn _mm256_max_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_i16x16();
        let b = b.as_i16x16();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed 32-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi32)
pub fn _mm256_max_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_i32x8();
        let b = b.as_i32x8();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed 8-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi8)
pub fn _mm256_max_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_i8x32();
        let b = b.as_i8x32();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed unsigned 16-bit integers in `a` and `b`, and returns
/// the packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu16)
pub fn _mm256_max_epu16(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_u16x16();
        let b = b.as_u16x16();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed unsigned 32-bit integers in `a` and `b`, and returns
/// the packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu32)
pub fn _mm256_max_epu32(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_u32x8();
        let b = b.as_u32x8();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns
/// the packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu8)
pub fn _mm256_max_epu8(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_u8x32();
        let b = b.as_u8x32();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi16)
pub fn _mm256_min_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_i16x16();
        let b = b.as_i16x16();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Compares packed 32-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi32)
pub fn _mm256_min_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_i32x8();
        let b = b.as_i32x8();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Compares packed 8-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi8)
pub fn _mm256_min_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_i8x32();
        let b = b.as_i8x32();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Compares packed unsigned 16-bit integers in `a` and `b`, and returns
/// the packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu16)
pub fn _mm256_min_epu16(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_u16x16();
        let b = b.as_u16x16();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Compares packed unsigned 32-bit integers in `a` and `b`, and returns
/// the packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu32)
pub fn _mm256_min_epu32(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_u32x8();
        let b = b.as_u32x8();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns
/// the packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu8)
pub fn _mm256_min_epu8(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_u8x32();
        let b = b.as_u8x32();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Creates mask from the most significant bit of each 8-bit element in `a`,
/// return the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_epi8)
pub fn _mm256_movemask_epi8(a: __m256i) -> i32 {
    {
        let z = i8x32::ZERO();
        let m: i8x32 = simd_lt(a.as_i8x32(), z);
        simd_bitmask_little!(31, m, u32) as i32
    }
}
/// Computes the sum of absolute differences (SADs) of quadruplets of unsigned
/// 8-bit integers in `a` compared to those in `b`, and stores the 16-bit
/// results in dst. Eight SADs are performed for each 128-bit lane using one
/// quadruplet from `b` and eight quadruplets from `a`. One quadruplet is
/// selected from `b` starting at on the offset specified in `imm8`. Eight
/// quadruplets are formed from sequential 8-bit integers selected from `a`
/// starting at the offset specified in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mpsadbw_epu8)
pub fn _mm256_mpsadbw_epu8<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        transmute(mpsadbw(a.as_u8x32(), b.as_u8x32(), IMM8 as i8))
    }
}
/// Multiplies the low 32-bit integers from each packed 64-bit element in
/// `a` and `b`
///
/// Returns the 64-bit results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epi32)
pub fn _mm256_mul_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = simd_cast::<4, _, i64>(simd_cast::<4, _, i32>(a.as_i64x4()));
        let b = simd_cast::<4, _, i64>(simd_cast::<4, _, i32>(b.as_i64x4()));
        transmute(simd_mul(a, b))
    }
}
/// Multiplies the low unsigned 32-bit integers from each packed 64-bit
/// element in `a` and `b`
///
/// Returns the unsigned 64-bit results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epu32)
pub fn _mm256_mul_epu32(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = a.as_u64x4();
        let b = b.as_u64x4();
        let mask = u64x4::splat(u32::MAX.into());
        transmute(simd_mul(simd_and(a, mask), simd_and(b, mask)))
    }
}
/// Multiplies the packed 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers and returning the high 16 bits of the
/// intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epi16)
pub fn _mm256_mulhi_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = simd_cast::<16, _, i32>(a.as_i16x16());
        let b = simd_cast::<16, _, i32>(b.as_i16x16());
        let r = simd_shr(simd_mul(a, b), i32x16::splat(16));
        transmute(simd_cast::<16, i32, i16>(r))
    }
}
/// Multiplies the packed unsigned 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers and returning the high 16 bits of the
/// intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epu16)
pub fn _mm256_mulhi_epu16(a: __m256i, b: __m256i) -> __m256i {
    {
        let a = simd_cast::<16, _, u32>(a.as_u16x16());
        let b = simd_cast::<16, _, u32>(b.as_u16x16());
        let r = simd_shr(simd_mul(a, b), u32x16::splat(16));
        transmute(simd_cast::<16, u32, u16>(r))
    }
}
/// Multiplies the packed 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers, and returns the low 16 bits of the
/// intermediate integers
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi16)
pub fn _mm256_mullo_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_mul(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Multiplies the packed 32-bit integers in `a` and `b`, producing
/// intermediate 64-bit integers, and returns the low 32 bits of the
/// intermediate integers
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi32)
pub fn _mm256_mullo_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_mul(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Multiplies packed 16-bit integers in `a` and `b`, producing
/// intermediate signed 32-bit integers. Truncate each intermediate
/// integer to the 18 most significant bits, round by adding 1, and
/// return bits `[16:1]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhrs_epi16)
pub fn _mm256_mulhrs_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(pmulhrsw(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Computes the bitwise OR of 256 bits (representing integer data) in `a`
/// and `b`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_or_si256)
pub fn _mm256_or_si256(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_or(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using signed saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi16)
pub fn _mm256_packs_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(packsswb(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using signed saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi32)
pub fn _mm256_packs_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(packssdw(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using unsigned saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packus_epi16)
pub fn _mm256_packus_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(packuswb(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using unsigned saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packus_epi32)
pub fn _mm256_packus_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(packusdw(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Permutes packed 32-bit integers from `a` according to the content of `b`.
///
/// The last 3 bits of each integer of `b` are used as addresses into the 8
/// integers of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permutevar8x32_epi32)
pub fn _mm256_permutevar8x32_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(permd(a.as_u32x8(), b.as_u32x8()))
    }
}
/// Permutes 64-bit integers from `a` using control mask `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute4x64_epi64)
pub fn _mm256_permute4x64_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let zero = i64x4::ZERO();
        let r: i64x4 = simd_shuffle(
            a.as_i64x4(),
            zero,
            [
                IMM8 as u32 & 0b11,
                (IMM8 as u32 >> 2) & 0b11,
                (IMM8 as u32 >> 4) & 0b11,
                (IMM8 as u32 >> 6) & 0b11,
            ],
        );
        transmute(r)
    }
}
/// Shuffles 128-bits of integer data selected by `imm8` from `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute2x128_si256)
pub fn _mm256_permute2x128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        transmute(vperm2i128(a.as_i64x4(), b.as_i64x4(), IMM8 as i8))
    }
}
/// Shuffles 64-bit floating-point elements in `a` across lanes using the
/// control in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute4x64_pd)
// NOTE: Not modeled yet
// pub fn _mm256_permute4x64_pd<const IMM8: i32>(a: __m256d) -> __m256d {
//     static_assert_uimm_bits!(IMM8, 8);
//     {
//         transmute(simd_shuffle(
//             a, _mm256_undefined_pd(), [IMM8 as u32 & 0b11, (IMM8 as u32 >> 2) & 0b11,
//             (IMM8 as u32 >> 4) & 0b11, (IMM8 as u32 >> 6) & 0b11,],
//         ))
//     }
// }

/// Shuffles eight 32-bit floating-point elements in `a` across lanes using
/// the corresponding 32-bit integer index in `idx`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permutevar8x32_ps)
// NOTE: Not modeled yet
// pub fn _mm256_permutevar8x32_ps(a: __m256, idx: __m256i) -> __m256 {
//     { permps(a, idx.as_i32x8()) }
// }

/// Computes the absolute differences of packed unsigned 8-bit integers in `a`
/// and `b`, then horizontally sum each consecutive 8 differences to
/// produce four unsigned 16-bit integers, and pack these unsigned 16-bit
/// integers in the low 16 bits of the 64-bit return value
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sad_epu8)
pub fn _mm256_sad_epu8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(psadbw(a.as_u8x32(), b.as_u8x32()))
    }
}
/// Shuffles bytes from `a` according to the content of `b`.
///
/// For each of the 128-bit low and high halves of the vectors, the last
/// 4 bits of each byte of `b` are used as addresses into the respective
/// low or high 16 bytes of `a`. That is, the halves are shuffled separately.
///
/// In addition, if the highest significant bit of a byte of `b` is set, the
/// respective destination byte is set to 0.
///
/// Picturing `a` and `b` as `[u8; 32]`, `_mm256_shuffle_epi8` is logically
/// equivalent to:
///
/// ```
/// fn mm256_shuffle_epi8(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
///     let mut r = [0; 32];
///     for i in 0..16 {
///         // if the most significant bit of b is set,
///         // then the destination byte is set to 0.
///         if b[i] & 0x80 == 0u8 {
///             r[i] = a[(b[i] % 16) as usize];
///         }
///         if b[i + 16] & 0x80 == 0u8 {
///             r[i + 16] = a[(b[i + 16] % 16 + 16) as usize];
///         }
///     }
///     r
/// }
/// ```
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi8)
pub fn _mm256_shuffle_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(pshufb(a.as_u8x32(), b.as_u8x32()))
    }
}
/// Shuffles 32-bit integers in 128-bit lanes of `a` using the control in
/// `imm8`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi32)
pub fn _mm256_shuffle_epi32<const MASK: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(MASK, 8);
    {
        let r: i32x8 = simd_shuffle(
            a.as_i32x8(),
            a.as_i32x8(),
            [
                MASK as u32 & 0b11,
                (MASK as u32 >> 2) & 0b11,
                (MASK as u32 >> 4) & 0b11,
                (MASK as u32 >> 6) & 0b11,
                (MASK as u32 & 0b11) + 4,
                ((MASK as u32 >> 2) & 0b11) + 4,
                ((MASK as u32 >> 4) & 0b11) + 4,
                ((MASK as u32 >> 6) & 0b11) + 4,
            ],
        );
        transmute(r)
    }
}
/// Shuffles 16-bit integers in the high 64 bits of 128-bit lanes of `a` using
/// the control in `imm8`. The low 64 bits of 128-bit lanes of `a` are copied
/// to the output.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shufflehi_epi16)
pub fn _mm256_shufflehi_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let a = a.as_i16x16();
        let r: i16x16 = simd_shuffle(
            a,
            a,
            [
                0,
                1,
                2,
                3,
                4 + (IMM8 as u32 & 0b11),
                4 + ((IMM8 as u32 >> 2) & 0b11),
                4 + ((IMM8 as u32 >> 4) & 0b11),
                4 + ((IMM8 as u32 >> 6) & 0b11),
                8,
                9,
                10,
                11,
                12 + (IMM8 as u32 & 0b11),
                12 + ((IMM8 as u32 >> 2) & 0b11),
                12 + ((IMM8 as u32 >> 4) & 0b11),
                12 + ((IMM8 as u32 >> 6) & 0b11),
            ],
        );
        transmute(r)
    }
}
/// Shuffles 16-bit integers in the low 64 bits of 128-bit lanes of `a` using
/// the control in `imm8`. The high 64 bits of 128-bit lanes of `a` are copied
/// to the output.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shufflelo_epi16)
pub fn _mm256_shufflelo_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let a = a.as_i16x16();
        let r: i16x16 = simd_shuffle(
            a,
            a,
            [
                0 + (IMM8 as u32 & 0b11),
                0 + ((IMM8 as u32 >> 2) & 0b11),
                0 + ((IMM8 as u32 >> 4) & 0b11),
                0 + ((IMM8 as u32 >> 6) & 0b11),
                4,
                5,
                6,
                7,
                8 + (IMM8 as u32 & 0b11),
                8 + ((IMM8 as u32 >> 2) & 0b11),
                8 + ((IMM8 as u32 >> 4) & 0b11),
                8 + ((IMM8 as u32 >> 6) & 0b11),
                12,
                13,
                14,
                15,
            ],
        );
        transmute(r)
    }
}
/// Negates packed 16-bit integers in `a` when the corresponding signed
/// 16-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi16)
pub fn _mm256_sign_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(psignw(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Negates packed 32-bit integers in `a` when the corresponding signed
/// 32-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi32)
pub fn _mm256_sign_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(psignd(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Negates packed 8-bit integers in `a` when the corresponding signed
/// 8-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi8)
pub fn _mm256_sign_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(psignb(a.as_i8x32(), b.as_i8x32()))
    }
}
/// Shifts packed 16-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi16)
pub fn _mm256_sll_epi16(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(psllw(a.as_i16x16(), count.as_i16x8()))
    }
}
/// Shifts packed 32-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi32)
pub fn _mm256_sll_epi32(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(pslld(a.as_i32x8(), count.as_i32x4()))
    }
}
/// Shifts packed 64-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi64)
pub fn _mm256_sll_epi64(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(psllq(a.as_i64x4(), count.as_i64x2()))
    }
}
/// Shifts packed 16-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi16)
pub fn _mm256_slli_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 16 {
            _mm256_setzero_si256()
        } else {
            transmute(simd_shl(a.as_u16x16(), u16x16::splat(IMM8 as u16)))
        }
    }
}
/// Shifts packed 32-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi32)
pub fn _mm256_slli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    {
        static_assert_uimm_bits!(IMM8, 8);
        if IMM8 >= 32 {
            _mm256_setzero_si256()
        } else {
            transmute(simd_shl(a.as_u32x8(), u32x8::splat(IMM8 as u32)))
        }
    }
}
/// Shifts packed 64-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi64)
pub fn _mm256_slli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    {
        static_assert_uimm_bits!(IMM8, 8);
        if IMM8 >= 64 {
            _mm256_setzero_si256()
        } else {
            transmute(simd_shl(a.as_u64x4(), u64x4::splat(IMM8 as u64)))
        }
    }
}
/// Shifts 128-bit lanes in `a` left by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_si256)
pub fn _mm256_slli_si256<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    _mm256_bslli_epi128::<IMM8>(a)
}

/// Shifts 128-bit lanes in `a` left by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bslli_epi128)
pub fn _mm256_bslli_epi128<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    const fn mask(shift: i32, i: u32) -> u32 {
        let shift = shift as u32 & 0xff;
        if shift > 15 || i % 16 < shift {
            0
        } else {
            32 + (i - shift)
        }
    }
    {
        let a = a.as_i8x32();
        let r: i8x32 = simd_shuffle(
            i8x32::ZERO(),
            a,
            [
                mask(IMM8, 0),
                mask(IMM8, 1),
                mask(IMM8, 2),
                mask(IMM8, 3),
                mask(IMM8, 4),
                mask(IMM8, 5),
                mask(IMM8, 6),
                mask(IMM8, 7),
                mask(IMM8, 8),
                mask(IMM8, 9),
                mask(IMM8, 10),
                mask(IMM8, 11),
                mask(IMM8, 12),
                mask(IMM8, 13),
                mask(IMM8, 14),
                mask(IMM8, 15),
                mask(IMM8, 16),
                mask(IMM8, 17),
                mask(IMM8, 18),
                mask(IMM8, 19),
                mask(IMM8, 20),
                mask(IMM8, 21),
                mask(IMM8, 22),
                mask(IMM8, 23),
                mask(IMM8, 24),
                mask(IMM8, 25),
                mask(IMM8, 26),
                mask(IMM8, 27),
                mask(IMM8, 28),
                mask(IMM8, 29),
                mask(IMM8, 30),
                mask(IMM8, 31),
            ],
        );
        transmute(r)
    }
}
/// Shifts packed 32-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi32)
pub fn _mm_sllv_epi32(a: __m128i, count: __m128i) -> __m128i {
    {
        transmute(psllvd(a.as_i32x4(), count.as_i32x4()))
    }
}
/// Shifts packed 32-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi32)
pub fn _mm256_sllv_epi32(a: __m256i, count: __m256i) -> __m256i {
    {
        transmute(psllvd256(a.as_i32x8(), count.as_i32x8()))
    }
}
/// Shifts packed 64-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi64)
pub fn _mm_sllv_epi64(a: __m128i, count: __m128i) -> __m128i {
    {
        transmute(psllvq(a.as_i64x2(), count.as_i64x2()))
    }
}
/// Shifts packed 64-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi64)
pub fn _mm256_sllv_epi64(a: __m256i, count: __m256i) -> __m256i {
    {
        transmute(psllvq256(a.as_i64x4(), count.as_i64x4()))
    }
}
/// Shifts packed 16-bit integers in `a` right by `count` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sra_epi16)
pub fn _mm256_sra_epi16(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(psraw(a.as_i16x16(), count.as_i16x8()))
    }
}
/// Shifts packed 32-bit integers in `a` right by `count` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sra_epi32)
pub fn _mm256_sra_epi32(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(psrad(a.as_i32x8(), count.as_i32x4()))
    }
}
/// Shifts packed 16-bit integers in `a` right by `IMM8` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi16)
pub fn _mm256_srai_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        transmute(simd_shr(a.as_i16x16(), i16x16::splat(IMM8.min(15) as i16)))
    }
}
/// Shifts packed 32-bit integers in `a` right by `IMM8` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi32)
pub fn _mm256_srai_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        transmute(simd_shr(a.as_i32x8(), i32x8::splat(IMM8.min(31))))
    }
}
/// Shifts packed 32-bit integers in `a` right by the amount specified by the
/// corresponding element in `count` while shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srav_epi32)
pub fn _mm_srav_epi32(a: __m128i, count: __m128i) -> __m128i {
    {
        transmute(psravd(a.as_i32x4(), count.as_i32x4()))
    }
}
/// Shifts packed 32-bit integers in `a` right by the amount specified by the
/// corresponding element in `count` while shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srav_epi32)
pub fn _mm256_srav_epi32(a: __m256i, count: __m256i) -> __m256i {
    {
        transmute(psravd256(a.as_i32x8(), count.as_i32x8()))
    }
}
/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_si256)
pub fn _mm256_srli_si256<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    _mm256_bsrli_epi128::<IMM8>(a)
}
/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)
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
    {
        let a = a.as_i8x32();
        let r: i8x32 = simd_shuffle(
            i8x32::ZERO(),
            a,
            [
                mask(IMM8, 0),
                mask(IMM8, 1),
                mask(IMM8, 2),
                mask(IMM8, 3),
                mask(IMM8, 4),
                mask(IMM8, 5),
                mask(IMM8, 6),
                mask(IMM8, 7),
                mask(IMM8, 8),
                mask(IMM8, 9),
                mask(IMM8, 10),
                mask(IMM8, 11),
                mask(IMM8, 12),
                mask(IMM8, 13),
                mask(IMM8, 14),
                mask(IMM8, 15),
                mask(IMM8, 16),
                mask(IMM8, 17),
                mask(IMM8, 18),
                mask(IMM8, 19),
                mask(IMM8, 20),
                mask(IMM8, 21),
                mask(IMM8, 22),
                mask(IMM8, 23),
                mask(IMM8, 24),
                mask(IMM8, 25),
                mask(IMM8, 26),
                mask(IMM8, 27),
                mask(IMM8, 28),
                mask(IMM8, 29),
                mask(IMM8, 30),
                mask(IMM8, 31),
            ],
        );
        transmute(r)
    }
}
/// Shifts packed 16-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi16)
pub fn _mm256_srl_epi16(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(psrlw(a.as_i16x16(), count.as_i16x8()))
    }
}
/// Shifts packed 32-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi32)
pub fn _mm256_srl_epi32(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(psrld(a.as_i32x8(), count.as_i32x4()))
    }
}
/// Shifts packed 64-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi64)
pub fn _mm256_srl_epi64(a: __m256i, count: __m128i) -> __m256i {
    {
        transmute(psrlq(a.as_i64x4(), count.as_i64x2()))
    }
}
/// Shifts packed 16-bit integers in `a` right by `IMM8` while shifting in
/// zeros
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi16)
pub fn _mm256_srli_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 16 {
            _mm256_setzero_si256()
        } else {
            transmute(simd_shr(a.as_u16x16(), u16x16::splat(IMM8 as u16)))
        }
    }
}
/// Shifts packed 32-bit integers in `a` right by `IMM8` while shifting in
/// zeros
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi32)
pub fn _mm256_srli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 32 {
            _mm256_setzero_si256()
        } else {
            transmute(simd_shr(a.as_u32x8(), u32x8::splat(IMM8 as u32)))
        }
    }
}
/// Shifts packed 64-bit integers in `a` right by `IMM8` while shifting in
/// zeros
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi64)
pub fn _mm256_srli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 64 {
            _mm256_setzero_si256()
        } else {
            transmute(simd_shr(a.as_u64x4(), u64x4::splat(IMM8 as u64)))
        }
    }
}
/// Shifts packed 32-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srlv_epi32)
pub fn _mm_srlv_epi32(a: __m128i, count: __m128i) -> __m128i {
    {
        transmute(psrlvd(a.as_i32x4(), count.as_i32x4()))
    }
}
/// Shifts packed 32-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi32)
pub fn _mm256_srlv_epi32(a: __m256i, count: __m256i) -> __m256i {
    {
        transmute(psrlvd256(a.as_i32x8(), count.as_i32x8()))
    }
}
/// Shifts packed 64-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srlv_epi64)
pub fn _mm_srlv_epi64(a: __m128i, count: __m128i) -> __m128i {
    {
        transmute(psrlvq(a.as_i64x2(), count.as_i64x2()))
    }
}
/// Shifts packed 64-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi64)
pub fn _mm256_srlv_epi64(a: __m256i, count: __m256i) -> __m256i {
    {
        transmute(psrlvq256(a.as_i64x4(), count.as_i64x4()))
    }
}
/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi16)
pub fn _mm256_sub_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_sub(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Subtract packed 32-bit integers in `b` from packed 32-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi32)
pub fn _mm256_sub_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_sub(a.as_i32x8(), b.as_i32x8()))
    }
}
/// Subtract packed 64-bit integers in `b` from packed 64-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi64)
pub fn _mm256_sub_epi64(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_sub(a.as_i64x4(), b.as_i64x4()))
    }
}
/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi8)
pub fn _mm256_sub_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_sub(a.as_i8x32(), b.as_i8x32()))
    }
}
/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in
/// `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epi16)
pub fn _mm256_subs_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_sub(a.as_i16x16(), b.as_i16x16()))
    }
}
/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in
/// `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epi8)
pub fn _mm256_subs_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_sub(a.as_i8x32(), b.as_i8x32()))
    }
}
/// Subtract packed unsigned 16-bit integers in `b` from packed 16-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epu16)
pub fn _mm256_subs_epu16(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_sub(a.as_u16x16(), b.as_u16x16()))
    }
}
/// Subtract packed unsigned 8-bit integers in `b` from packed 8-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epu8)
pub fn _mm256_subs_epu8(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_saturating_sub(a.as_u8x32(), b.as_u8x32()))
    }
}
/// Unpacks and interleave 8-bit integers from the high half of each
/// 128-bit lane in `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi8)
pub fn _mm256_unpackhi_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        #[rustfmt::skip]
        let r: i8x32 = simd_shuffle(
            a.as_i8x32(), b.as_i8x32(), [8, 40, 9, 41, 10, 42, 11, 43, 12, 44, 13, 45,
            14, 46, 15, 47, 24, 56, 25, 57, 26, 58, 27, 59, 28, 60, 29, 61, 30, 62, 31,
            63,]
        );
        transmute(r)
    }
}
/// Unpacks and interleave 8-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi8)
pub fn _mm256_unpacklo_epi8(a: __m256i, b: __m256i) -> __m256i {
    {
        #[rustfmt::skip]
        let r: i8x32 = simd_shuffle(
            a.as_i8x32(), b.as_i8x32(), [0, 32, 1, 33, 2, 34, 3, 35, 4, 36, 5, 37, 6, 38,
            7, 39, 16, 48, 17, 49, 18, 50, 19, 51, 20, 52, 21, 53, 22, 54, 23, 55,]
        );
        transmute(r)
    }
}
/// Unpacks and interleave 16-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi16)
pub fn _mm256_unpackhi_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        let r: i16x16 = simd_shuffle(
            a.as_i16x16(),
            b.as_i16x16(),
            [4, 20, 5, 21, 6, 22, 7, 23, 12, 28, 13, 29, 14, 30, 15, 31],
        );
        transmute(r)
    }
}
/// Unpacks and interleave 16-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi16)
pub fn _mm256_unpacklo_epi16(a: __m256i, b: __m256i) -> __m256i {
    {
        let r: i16x16 = simd_shuffle(
            a.as_i16x16(),
            b.as_i16x16(),
            [0, 16, 1, 17, 2, 18, 3, 19, 8, 24, 9, 25, 10, 26, 11, 27],
        );
        transmute(r)
    }
}
/// Unpacks and interleave 32-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi32)
pub fn _mm256_unpackhi_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        let r: i32x8 = simd_shuffle(a.as_i32x8(), b.as_i32x8(), [2, 10, 3, 11, 6, 14, 7, 15]);
        transmute(r)
    }
}
/// Unpacks and interleave 32-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi32)
pub fn _mm256_unpacklo_epi32(a: __m256i, b: __m256i) -> __m256i {
    {
        let r: i32x8 = simd_shuffle(a.as_i32x8(), b.as_i32x8(), [0, 8, 1, 9, 4, 12, 5, 13]);
        transmute(r)
    }
}
/// Unpacks and interleave 64-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi64)
pub fn _mm256_unpackhi_epi64(a: __m256i, b: __m256i) -> __m256i {
    {
        let r: i64x4 = simd_shuffle(a.as_i64x4(), b.as_i64x4(), [1, 5, 3, 7]);
        transmute(r)
    }
}
/// Unpacks and interleave 64-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
///
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi64)
pub fn _mm256_unpacklo_epi64(a: __m256i, b: __m256i) -> __m256i {
    {
        let r: i64x4 = simd_shuffle(a.as_i64x4(), b.as_i64x4(), [0, 4, 2, 6]);
        transmute(r)
    }
}
/// Computes the bitwise XOR of 256 bits (representing integer data)
/// in `a` and `b`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_xor_si256)
pub fn _mm256_xor_si256(a: __m256i, b: __m256i) -> __m256i {
    {
        transmute(simd_xor(a.as_i64x4(), b.as_i64x4()))
    }
}
/// Extracts an 8-bit integer from `a`, selected with `INDEX`. Returns a 32-bit
/// integer containing the zero-extended integer data.
///
/// See [LLVM commit D20468](https://reviews.llvm.org/D20468).
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extract_epi8)
pub fn _mm256_extract_epi8<const INDEX: i32>(a: __m256i) -> i32 {
    static_assert_uimm_bits!(INDEX, 5);
    {
        simd_extract(a.as_u8x32(), INDEX as u32) as i32
    }
}
/// Extracts a 16-bit integer from `a`, selected with `INDEX`. Returns a 32-bit
/// integer containing the zero-extended integer data.
///
/// See [LLVM commit D20468](https://reviews.llvm.org/D20468).
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extract_epi16)
pub fn _mm256_extract_epi16<const INDEX: i32>(a: __m256i) -> i32 {
    static_assert_uimm_bits!(INDEX, 4);
    {
        simd_extract(a.as_u16x16(), INDEX as u32) as i32
    }
}
