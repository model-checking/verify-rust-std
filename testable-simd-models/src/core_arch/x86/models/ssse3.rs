//! Supplemental Streaming SIMD Extensions 3 (SSSE3)
use crate::abstractions::simd::*;
use crate::abstractions::utilities::*;

use super::sse2::*;
use super::ssse3_handwritten::*;
use super::types::*;

/// Computes the absolute value of packed 8-bit signed integers in `a` and
/// return the unsigned results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi8)
pub fn _mm_abs_epi8(a: __m128i) -> __m128i {
    {
        let a = a.as_i8x16();
        let zero = i8x16::ZERO();
        let r = simd_select(simd_lt(a, zero), simd_neg(a), a);
        transmute(r)
    }
}
/// Computes the absolute value of each of the packed 16-bit signed integers in
/// `a` and
/// return the 16-bit unsigned integer
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi16)
pub fn _mm_abs_epi16(a: __m128i) -> __m128i {
    {
        let a = a.as_i16x8();
        let zero = i16x8::ZERO();
        let r = simd_select(simd_lt(a, zero), simd_neg(a), a);
        transmute(r)
    }
}
/// Computes the absolute value of each of the packed 32-bit signed integers in
/// `a` and
/// return the 32-bit unsigned integer
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi32)
pub fn _mm_abs_epi32(a: __m128i) -> __m128i {
    {
        let a = a.as_i32x4();
        let zero = i32x4::ZERO();
        let r = simd_select(simd_lt(a, zero), simd_neg(a), a);
        transmute(r)
    }
}
/// Shuffles bytes from `a` according to the content of `b`.
///
/// The last 4 bits of each byte of `b` are used as addresses
/// into the 16 bytes of `a`.
///
/// In addition, if the highest significant bit of a byte of `b`
/// is set, the respective destination byte is set to 0.
///
/// Picturing `a` and `b` as `[u8; 16]`, `_mm_shuffle_epi8` is
/// logically equivalent to:
///
/// ```
/// fn mm_shuffle_epi8(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
///     let mut r = [0u8; 16];
///     for i in 0..16 {
///         // if the most significant bit of b is set,
///         // then the destination byte is set to 0.
///         if b[i] & 0x80 == 0u8 {
///             r[i] = a[(b[i] % 16) as usize];
///         }
///     }
///     r
/// }
/// ```
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shuffle_epi8)
pub fn _mm_shuffle_epi8(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(pshufb128(a.as_u8x16(), b.as_u8x16()))
    }
}
/// Concatenate 16-byte blocks in `a` and `b` into a 32-byte temporary result,
/// shift the result right by `n` bytes, and returns the low 16 bytes.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_alignr_epi8)
pub fn _mm_alignr_epi8<const IMM8: i32>(a: __m128i, b: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    if IMM8 > 32 {
        return _mm_setzero_si128();
    }
    let (a, b) = if IMM8 > 16 {
        (_mm_setzero_si128(), a)
    } else {
        (a, b)
    };
    const fn mask(shift: u32, i: u32) -> u32 {
        if shift > 32 {
            i
        } else if shift > 16 {
            shift - 16 + i
        } else {
            shift + i
        }
    }
    {
        let r: i8x16 = simd_shuffle(
            b.as_i8x16(),
            a.as_i8x16(),
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
            ],
        );
        transmute(r)
    }
}
/// Horizontally adds the adjacent pairs of values contained in 2 packed
/// 128-bit vectors of `[8 x i16]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hadd_epi16)
pub fn _mm_hadd_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(phaddw128(a.as_i16x8(), b.as_i16x8()))
    }
}
/// Horizontally adds the adjacent pairs of values contained in 2 packed
/// 128-bit vectors of `[8 x i16]`. Positive sums greater than 7FFFh are
/// saturated to 7FFFh. Negative sums less than 8000h are saturated to 8000h.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hadds_epi16)
pub fn _mm_hadds_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(phaddsw128(a.as_i16x8(), b.as_i16x8()))
    }
}
/// Horizontally adds the adjacent pairs of values contained in 2 packed
/// 128-bit vectors of `[4 x i32]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hadd_epi32)
pub fn _mm_hadd_epi32(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(phaddd128(a.as_i32x4(), b.as_i32x4()))
    }
}
/// Horizontally subtract the adjacent pairs of values contained in 2
/// packed 128-bit vectors of `[8 x i16]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hsub_epi16)
pub fn _mm_hsub_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(phsubw128(a.as_i16x8(), b.as_i16x8()))
    }
}
/// Horizontally subtract the adjacent pairs of values contained in 2
/// packed 128-bit vectors of `[8 x i16]`. Positive differences greater than
/// 7FFFh are saturated to 7FFFh. Negative differences less than 8000h are
/// saturated to 8000h.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hsubs_epi16)
pub fn _mm_hsubs_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(phsubsw128(a.as_i16x8(), b.as_i16x8()))
    }
}
/// Horizontally subtract the adjacent pairs of values contained in 2
/// packed 128-bit vectors of `[4 x i32]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hsub_epi32)
pub fn _mm_hsub_epi32(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(phsubd128(a.as_i32x4(), b.as_i32x4()))
    }
}
/// Multiplies corresponding pairs of packed 8-bit unsigned integer
/// values contained in the first source operand and packed 8-bit signed
/// integer values contained in the second source operand, add pairs of
/// contiguous products with signed saturation, and writes the 16-bit sums to
/// the corresponding bits in the destination.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_maddubs_epi16)
pub fn _mm_maddubs_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(pmaddubsw128(a.as_u8x16(), b.as_i8x16()))
    }
}
/// Multiplies packed 16-bit signed integer values, truncate the 32-bit
/// product to the 18 most significant bits by right-shifting, round the
/// truncated value by adding 1, and write bits `[16:1]` to the destination.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhrs_epi16)
pub fn _mm_mulhrs_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(pmulhrsw128(a.as_i16x8(), b.as_i16x8()))
    }
}
/// Negates packed 8-bit integers in `a` when the corresponding signed 8-bit
/// integer in `b` is negative, and returns the result.
/// Elements in result are zeroed out when the corresponding element in `b`
/// is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sign_epi8)
pub fn _mm_sign_epi8(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(psignb128(a.as_i8x16(), b.as_i8x16()))
    }
}
/// Negates packed 16-bit integers in `a` when the corresponding signed 16-bit
/// integer in `b` is negative, and returns the results.
/// Elements in result are zeroed out when the corresponding element in `b`
/// is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sign_epi16)
pub fn _mm_sign_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(psignw128(a.as_i16x8(), b.as_i16x8()))
    }
}
/// Negates packed 32-bit integers in `a` when the corresponding signed 32-bit
/// integer in `b` is negative, and returns the results.
/// Element in result are zeroed out when the corresponding element in `b`
/// is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sign_epi32)
pub fn _mm_sign_epi32(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute(psignd128(a.as_i32x4(), b.as_i32x4()))
    }
}
