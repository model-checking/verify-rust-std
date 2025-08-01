//! Streaming SIMD Extensions 2 (SSE2)
use super::sse2_handwritten::*;
use super::types::*;
use crate::abstractions::simd::*;
use crate::abstractions::utilities::*;

/// Adds packed 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi8)
pub fn _mm_add_epi8(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_add(a.as_i8x16(), b.as_i8x16()))
}
/// Adds packed 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi16)
pub fn _mm_add_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_add(a.as_i16x8(), b.as_i16x8()))
}
/// Adds packed 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi32)
pub fn _mm_add_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_add(a.as_i32x4(), b.as_i32x4()))
}
/// Adds packed 64-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi64)
pub fn _mm_add_epi64(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_add(a.as_i64x2(), b.as_i64x2()))
}
/// Adds packed 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epi8)
pub fn _mm_adds_epi8(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_add(a.as_i8x16(), b.as_i8x16()))
}
/// Adds packed 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epi16)
pub fn _mm_adds_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_add(a.as_i16x8(), b.as_i16x8()))
}
/// Adds packed unsigned 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epu8)
pub fn _mm_adds_epu8(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_add(a.as_u8x16(), b.as_u8x16()))
}
/// Adds packed unsigned 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epu16)
pub fn _mm_adds_epu16(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_add(a.as_u16x8(), b.as_u16x8()))
}
/// Averages packed unsigned 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_avg_epu8)
pub fn _mm_avg_epu8(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = simd_cast::<16, _, u16>(a.as_u8x16());
        let b = simd_cast::<16, _, u16>(b.as_u8x16());
        let r = simd_shr(simd_add(simd_add(a, b), u16x16::splat(1)), u16x16::splat(1));
        transmute(simd_cast::<16, _, u8>(r))
    }
}
/// Averages packed unsigned 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_avg_epu16)
pub fn _mm_avg_epu16(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = simd_cast::<8, _, u32>(a.as_u16x8());
        let b = simd_cast::<8, _, u32>(b.as_u16x8());
        let r = simd_shr(simd_add(simd_add(a, b), u32x8::splat(1)), u32x8::splat(1));
        transmute(simd_cast::<8, _, u16>(r))
    }
}
/// Multiplies and then horizontally add signed 16 bit integers in `a` and `b`.
///
/// Multiplies packed signed 16-bit integers in `a` and `b`, producing
/// intermediate signed 32-bit integers. Horizontally add adjacent pairs of
/// intermediate 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_madd_epi16)
pub fn _mm_madd_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(pmaddwd(a.as_i16x8(), b.as_i16x8()))
}
/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_max_epi16)
pub fn _mm_max_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = a.as_i16x8();
        let b = b.as_i16x8();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns the
/// packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_max_epu8)
pub fn _mm_max_epu8(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = a.as_u8x16();
        let b = b.as_u8x16();
        transmute(simd_select(simd_gt(a, b), a, b))
    }
}
/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_min_epi16)
pub fn _mm_min_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = a.as_i16x8();
        let b = b.as_i16x8();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns the
/// packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_min_epu8)
pub fn _mm_min_epu8(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = a.as_u8x16();
        let b = b.as_u8x16();
        transmute(simd_select(simd_lt(a, b), a, b))
    }
}
/// Multiplies the packed 16-bit integers in `a` and `b`.
///
/// The multiplication produces intermediate 32-bit integers, and returns the
/// high 16 bits of the intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhi_epi16)
pub fn _mm_mulhi_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = simd_cast::<8, _, i32>(a.as_i16x8());
        let b = simd_cast::<8, _, i32>(b.as_i16x8());
        let r = simd_shr(simd_mul(a, b), i32x8::splat(16));
        transmute(simd_cast::<8, i32, i16>(r))
    }
}
/// Multiplies the packed unsigned 16-bit integers in `a` and `b`.
///
/// The multiplication produces intermediate 32-bit integers, and returns the
/// high 16 bits of the intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhi_epu16)
pub fn _mm_mulhi_epu16(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = simd_cast::<8, _, u32>(a.as_u16x8());
        let b = simd_cast::<8, _, u32>(b.as_u16x8());
        let r = simd_shr(simd_mul(a, b), u32x8::splat(16));
        transmute(simd_cast::<8, u32, u16>(r))
    }
}
/// Multiplies the packed 16-bit integers in `a` and `b`.
///
/// The multiplication produces intermediate 32-bit integers, and returns the
/// low 16 bits of the intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mullo_epi16)
pub fn _mm_mullo_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_mul(a.as_i16x8(), b.as_i16x8()))
}
/// Multiplies the low unsigned 32-bit integers from each packed 64-bit element
/// in `a` and `b`.
///
/// Returns the unsigned 64-bit results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mul_epu32)
pub fn _mm_mul_epu32(a: __m128i, b: __m128i) -> __m128i {
    {
        let a = a.as_u64x2();
        let b = b.as_u64x2();
        let mask = u64x2::splat(u32::MAX.into());
        transmute(simd_mul(simd_and(a, mask), simd_and(b, mask)))
    }
}
/// Sum the absolute differences of packed unsigned 8-bit integers.
///
/// Computes the absolute differences of packed unsigned 8-bit integers in `a`
/// and `b`, then horizontally sum each consecutive 8 differences to produce
/// two unsigned 16-bit integers, and pack these unsigned 16-bit integers in
/// the low 16 bits of 64-bit elements returned.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sad_epu8)
pub fn _mm_sad_epu8(a: __m128i, b: __m128i) -> __m128i {
    transmute(psadbw(a.as_u8x16(), b.as_u8x16()))
}
/// Subtracts packed 8-bit integers in `b` from packed 8-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi8)
pub fn _mm_sub_epi8(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_sub(a.as_i8x16(), b.as_i8x16()))
}
/// Subtracts packed 16-bit integers in `b` from packed 16-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi16)
pub fn _mm_sub_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_sub(a.as_i16x8(), b.as_i16x8()))
}
/// Subtract packed 32-bit integers in `b` from packed 32-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi32)
pub fn _mm_sub_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_sub(a.as_i32x4(), b.as_i32x4()))
}
/// Subtract packed 64-bit integers in `b` from packed 64-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi64)
pub fn _mm_sub_epi64(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_sub(a.as_i64x2(), b.as_i64x2()))
}
/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epi8)
pub fn _mm_subs_epi8(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_sub(a.as_i8x16(), b.as_i8x16()))
}
/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epi16)
pub fn _mm_subs_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_sub(a.as_i16x8(), b.as_i16x8()))
}
/// Subtract packed unsigned 8-bit integers in `b` from packed unsigned 8-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epu8)
pub fn _mm_subs_epu8(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_sub(a.as_u8x16(), b.as_u8x16()))
}
/// Subtract packed unsigned 16-bit integers in `b` from packed unsigned 16-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epu16)
pub fn _mm_subs_epu16(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_saturating_sub(a.as_u16x8(), b.as_u16x8()))
}
/// Shifts `a` left by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_si128)
pub fn _mm_slli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    _mm_slli_si128_impl::<IMM8>(a)
}

fn _mm_slli_si128_impl<const IMM8: i32>(a: __m128i) -> __m128i {
    const fn mask(shift: i32, i: u32) -> u32 {
        let shift = shift as u32 & 0xff;
        if shift > 15 {
            i
        } else {
            16 - shift + i
        }
    }
    transmute::<i8x16, _>(simd_shuffle(
        i8x16::ZERO(),
        a.as_i8x16(),
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
        ],
    ))
}

/// Shifts `a` left by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_bslli_si128)
pub fn _mm_bslli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    {
        static_assert_uimm_bits!(IMM8, 8);
        _mm_slli_si128_impl::<IMM8>(a)
    }
}
/// Shifts `a` right by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_bsrli_si128)
pub fn _mm_bsrli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    {
        static_assert_uimm_bits!(IMM8, 8);
        _mm_srli_si128_impl::<IMM8>(a)
    }
}

fn _mm_srli_si128_impl<const IMM8: i32>(a: __m128i) -> __m128i {
    const fn mask(shift: i32, i: u32) -> u32 {
        if (shift as u32) > 15 {
            i + 16
        } else {
            i + (shift as u32)
        }
    }
    let x: i8x16 = simd_shuffle(
        a.as_i8x16(),
        i8x16::ZERO(),
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
        ],
    );
    transmute(x)
}
/// Shifts packed 16-bit integers in `a` left by `IMM8` while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_epi16)
pub fn _mm_slli_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 16 {
            _mm_setzero_si128()
        } else {
            transmute(simd_shl(a.as_u16x8(), u16x8::splat(IMM8 as u16)))
        }
    }
}
/// Shifts packed 16-bit integers in `a` left by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sll_epi16)
pub fn _mm_sll_epi16(a: __m128i, count: __m128i) -> __m128i {
    transmute(psllw(a.as_i16x8(), count.as_i16x8()))
}
/// Shifts packed 32-bit integers in `a` left by `IMM8` while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_epi32)
pub fn _mm_slli_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 32 {
            _mm_setzero_si128()
        } else {
            transmute(simd_shl(a.as_u32x4(), u32x4::splat(IMM8 as u32)))
        }
    }
}
/// Shifts packed 32-bit integers in `a` left by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sll_epi32)
pub fn _mm_sll_epi32(a: __m128i, count: __m128i) -> __m128i {
    transmute(pslld(a.as_i32x4(), count.as_i32x4()))
}
/// Shifts packed 64-bit integers in `a` left by `IMM8` while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_epi64)
pub fn _mm_slli_epi64<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 64 {
            _mm_setzero_si128()
        } else {
            transmute(simd_shl(a.as_u64x2(), u64x2::splat(IMM8 as u64)))
        }
    }
}
/// Shifts packed 64-bit integers in `a` left by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sll_epi64)
pub fn _mm_sll_epi64(a: __m128i, count: __m128i) -> __m128i {
    transmute(psllq(a.as_i64x2(), count.as_i64x2()))
}
/// Shifts packed 16-bit integers in `a` right by `IMM8` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srai_epi16)
pub fn _mm_srai_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    transmute(simd_shr(a.as_i16x8(), i16x8::splat(IMM8.min(15) as i16)))
}
/// Shifts packed 16-bit integers in `a` right by `count` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sra_epi16)
pub fn _mm_sra_epi16(a: __m128i, count: __m128i) -> __m128i {
    transmute(psraw(a.as_i16x8(), count.as_i16x8()))
}
/// Shifts packed 32-bit integers in `a` right by `IMM8` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srai_epi32)
pub fn _mm_srai_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    transmute(simd_shr(a.as_i32x4(), i32x4::splat(IMM8.min(31))))
}
/// Shifts packed 32-bit integers in `a` right by `count` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sra_epi32)
pub fn _mm_sra_epi32(a: __m128i, count: __m128i) -> __m128i {
    transmute(psrad(a.as_i32x4(), count.as_i32x4()))
}
/// Shifts `a` right by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_si128)
pub fn _mm_srli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    _mm_srli_si128_impl::<IMM8>(a)
}
/// Shifts packed 16-bit integers in `a` right by `IMM8` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi16)
pub fn _mm_srli_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 16 {
            _mm_setzero_si128()
        } else {
            transmute(simd_shr(a.as_u16x8(), u16x8::splat(IMM8 as u16)))
        }
    }
}
/// Shifts packed 16-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srl_epi16)
pub fn _mm_srl_epi16(a: __m128i, count: __m128i) -> __m128i {
    transmute(psrlw(a.as_i16x8(), count.as_i16x8()))
}
/// Shifts packed 32-bit integers in `a` right by `IMM8` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi32)
pub fn _mm_srli_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 32 {
            _mm_setzero_si128()
        } else {
            transmute(simd_shr(a.as_u32x4(), u32x4::splat(IMM8 as u32)))
        }
    }
}
/// Shifts packed 32-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srl_epi32)
pub fn _mm_srl_epi32(a: __m128i, count: __m128i) -> __m128i {
    transmute(psrld(a.as_i32x4(), count.as_i32x4()))
}
/// Shifts packed 64-bit integers in `a` right by `IMM8` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi64)
pub fn _mm_srli_epi64<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        if IMM8 >= 64 {
            _mm_setzero_si128()
        } else {
            transmute(simd_shr(a.as_u64x2(), u64x2::splat(IMM8 as u64)))
        }
    }
}
/// Shifts packed 64-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srl_epi64)
pub fn _mm_srl_epi64(a: __m128i, count: __m128i) -> __m128i {
    transmute(psrlq(a.as_i64x2(), count.as_i64x2()))
}
/// Computes the bitwise AND of 128 bits (representing integer data) in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_and_si128)
pub fn _mm_and_si128(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_and(a.as_i32x4(), b.as_i32x4()))
}
/// Computes the bitwise NOT of 128 bits (representing integer data) in `a` and
/// then AND with `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_andnot_si128)
pub fn _mm_andnot_si128(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_and(
        simd_xor(_mm_set1_epi8(-1).as_i32x4(), a.as_i32x4()),
        b.as_i32x4(),
    ))
}
/// Computes the bitwise OR of 128 bits (representing integer data) in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_or_si128)
pub fn _mm_or_si128(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_or(a.as_i32x4(), b.as_i32x4()))
}
/// Computes the bitwise XOR of 128 bits (representing integer data) in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_xor_si128)
pub fn _mm_xor_si128(a: __m128i, b: __m128i) -> __m128i {
    transmute(simd_xor(a.as_i32x4(), b.as_i32x4()))
}
/// Compares packed 8-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_epi8)
pub fn _mm_cmpeq_epi8(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i8x16, _>(simd_eq(a.as_i8x16(), b.as_i8x16()))
}
/// Compares packed 16-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_epi16)
pub fn _mm_cmpeq_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i16x8, _>(simd_eq(a.as_i16x8(), b.as_i16x8()))
}
/// Compares packed 32-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_epi32)
pub fn _mm_cmpeq_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i32x4, _>(simd_eq(a.as_i32x4(), b.as_i32x4()))
}
/// Compares packed 8-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_epi8)
pub fn _mm_cmpgt_epi8(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i8x16, _>(simd_gt(a.as_i8x16(), b.as_i8x16()))
}
/// Compares packed 16-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_epi16)
pub fn _mm_cmpgt_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i16x8, _>(simd_gt(a.as_i16x8(), b.as_i16x8()))
}
/// Compares packed 32-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_epi32)
pub fn _mm_cmpgt_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i32x4, _>(simd_gt(a.as_i32x4(), b.as_i32x4()))
}
/// Compares packed 8-bit integers in `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_epi8)
pub fn _mm_cmplt_epi8(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i8x16, _>(simd_lt(a.as_i8x16(), b.as_i8x16()))
}
/// Compares packed 16-bit integers in `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_epi16)
pub fn _mm_cmplt_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i16x8, _>(simd_lt(a.as_i16x8(), b.as_i16x8()))
}
/// Compares packed 32-bit integers in `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_epi32)
pub fn _mm_cmplt_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i32x4, _>(simd_lt(a.as_i32x4(), b.as_i32x4()))
}
/// Converts the lower two packed 32-bit integers in `a` to packed
/// double-precision (64-bit) floating-point elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtepi32_pd)
pub fn _mm_cvtepi32_pd(a: __m128i) -> __m128d {
    {
        let a = a.as_i32x4();
        transmute(simd_cast::<2, i32, f64>(simd_shuffle(a, a, [0, 1])))
    }
}
/// Returns `a` with its lower element replaced by `b` after converting it to
/// an `f64`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtsi32_sd)
pub fn _mm_cvtsi32_sd(a: __m128d, b: i32) -> __m128d {
    transmute(simd_insert(a.as_f64x2(), 0, b as f64))
}
/// Converts packed 32-bit integers in `a` to packed single-precision (32-bit)
/// floating-point elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtepi32_ps)
pub fn _mm_cvtepi32_ps(a: __m128i) -> __m128 {
    transmute(simd_cast::<4, _, f32>(a.as_i32x4()))
}
/// Converts packed single-precision (32-bit) floating-point elements in `a`
/// to packed 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtps_epi32)
// NOTE: Not modeled yet
// pub fn _mm_cvtps_epi32(a: __m128) -> __m128i {
//     { transmute(cvtps2dq(a)) }
// }
/// Returns a vector whose lowest element is `a` and all higher elements are
/// `0`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtsi32_si128)
pub fn _mm_cvtsi32_si128(a: i32) -> __m128i {
    transmute(i32x4::new(a, 0, 0, 0))
}
/// Returns the lowest element of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtsi128_si32)
pub fn _mm_cvtsi128_si32(a: __m128i) -> i32 {
    simd_extract(a.as_i32x4(), 0)
}
/// Sets packed 64-bit integers with the supplied values, from highest to
/// lowest.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi64x)
pub fn _mm_set_epi64x(e1: i64, e0: i64) -> __m128i {
    transmute(i64x2::new(e0, e1))
}
/// Sets packed 32-bit integers with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi32)
pub fn _mm_set_epi32(e3: i32, e2: i32, e1: i32, e0: i32) -> __m128i {
    transmute(i32x4::new(e0, e1, e2, e3))
}
/// Sets packed 16-bit integers with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi16)
pub fn _mm_set_epi16(
    e7: i16,
    e6: i16,
    e5: i16,
    e4: i16,
    e3: i16,
    e2: i16,
    e1: i16,
    e0: i16,
) -> __m128i {
    transmute(i16x8::new(e0, e1, e2, e3, e4, e5, e6, e7))
}
/// Sets packed 8-bit integers with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi8)
pub fn _mm_set_epi8(
    e15: i8,
    e14: i8,
    e13: i8,
    e12: i8,
    e11: i8,
    e10: i8,
    e9: i8,
    e8: i8,
    e7: i8,
    e6: i8,
    e5: i8,
    e4: i8,
    e3: i8,
    e2: i8,
    e1: i8,
    e0: i8,
) -> __m128i {
    {
        transmute(i8x16::new(
            e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
        ))
    }
}
/// Broadcasts 64-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi64x)
pub fn _mm_set1_epi64x(a: i64) -> __m128i {
    _mm_set_epi64x(a, a)
}
/// Broadcasts 32-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi32)
pub fn _mm_set1_epi32(a: i32) -> __m128i {
    _mm_set_epi32(a, a, a, a)
}
/// Broadcasts 16-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi16)
pub fn _mm_set1_epi16(a: i16) -> __m128i {
    _mm_set_epi16(a, a, a, a, a, a, a, a)
}
/// Broadcasts 8-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi8)
pub fn _mm_set1_epi8(a: i8) -> __m128i {
    _mm_set_epi8(a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a)
}
/// Sets packed 32-bit integers with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setr_epi32)
pub fn _mm_setr_epi32(e3: i32, e2: i32, e1: i32, e0: i32) -> __m128i {
    _mm_set_epi32(e0, e1, e2, e3)
}
/// Sets packed 16-bit integers with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setr_epi16)
pub fn _mm_setr_epi16(
    e7: i16,
    e6: i16,
    e5: i16,
    e4: i16,
    e3: i16,
    e2: i16,
    e1: i16,
    e0: i16,
) -> __m128i {
    _mm_set_epi16(e0, e1, e2, e3, e4, e5, e6, e7)
}
/// Sets packed 8-bit integers with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setr_epi8)
pub fn _mm_setr_epi8(
    e15: i8,
    e14: i8,
    e13: i8,
    e12: i8,
    e11: i8,
    e10: i8,
    e9: i8,
    e8: i8,
    e7: i8,
    e6: i8,
    e5: i8,
    e4: i8,
    e3: i8,
    e2: i8,
    e1: i8,
    e0: i8,
) -> __m128i {
    _mm_set_epi8(
        e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    )
}
/// Returns a vector with all elements set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setzero_si128)
pub fn _mm_setzero_si128() -> __m128i {
    transmute(i32x4::ZERO())
}
/// Returns a vector where the low element is extracted from `a` and its upper
/// element is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_move_epi64)
pub fn _mm_move_epi64(a: __m128i) -> __m128i {
    {
        let r: i64x2 = simd_shuffle(a.as_i64x2(), i64x2::ZERO(), [0, 2]);
        transmute(r)
    }
}
/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using signed saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packs_epi16)
pub fn _mm_packs_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(packsswb(a.as_i16x8(), b.as_i16x8()))
}
/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using signed saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packs_epi32)
pub fn _mm_packs_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute(packssdw(a.as_i32x4(), b.as_i32x4()))
}
/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using unsigned saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packus_epi16)
pub fn _mm_packus_epi16(a: __m128i, b: __m128i) -> __m128i {
    transmute(packuswb(a.as_i16x8(), b.as_i16x8()))
}
/// Returns the `imm8` element of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_extract_epi16)
pub fn _mm_extract_epi16<const IMM8: i32>(a: __m128i) -> i32 {
    static_assert_uimm_bits!(IMM8, 3);
    simd_extract(a.as_u16x8(), IMM8 as u32) as i32
}
/// Returns a new vector where the `imm8` element of `a` is replaced with `i`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_insert_epi16)
pub fn _mm_insert_epi16<const IMM8: i32>(a: __m128i, i: i32) -> __m128i {
    static_assert_uimm_bits!(IMM8, 3);
    transmute(simd_insert(a.as_i16x8(), IMM8 as u32, i as i16))
}
/// Returns a mask of the most significant bit of each element in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_movemask_epi8)
pub fn _mm_movemask_epi8(a: __m128i) -> i32 {
    {
        let z = i8x16::ZERO();
        let m: i8x16 = simd_lt(a.as_i8x16(), z);
        simd_bitmask_little!(15, m, u16) as u32 as i32
    }
}
/// Shuffles 32-bit integers in `a` using the control in `IMM8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shuffle_epi32)
pub fn _mm_shuffle_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let a = a.as_i32x4();
        let x: i32x4 = simd_shuffle(
            a,
            a,
            [
                IMM8 as u32 & 0b11,
                (IMM8 as u32 >> 2) & 0b11,
                (IMM8 as u32 >> 4) & 0b11,
                (IMM8 as u32 >> 6) & 0b11,
            ],
        );
        transmute(x)
    }
}
/// Shuffles 16-bit integers in the high 64 bits of `a` using the control in
/// `IMM8`.
///
/// Put the results in the high 64 bits of the returned vector, with the low 64
/// bits being copied from `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shufflehi_epi16)
pub fn _mm_shufflehi_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let a = a.as_i16x8();
        let x: i16x8 = simd_shuffle(
            a,
            a,
            [
                0,
                1,
                2,
                3,
                (IMM8 as u32 & 0b11) + 4,
                ((IMM8 as u32 >> 2) & 0b11) + 4,
                ((IMM8 as u32 >> 4) & 0b11) + 4,
                ((IMM8 as u32 >> 6) & 0b11) + 4,
            ],
        );
        transmute(x)
    }
}
/// Shuffles 16-bit integers in the low 64 bits of `a` using the control in
/// `IMM8`.
///
/// Put the results in the low 64 bits of the returned vector, with the high 64
/// bits being copied from `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shufflelo_epi16)
pub fn _mm_shufflelo_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    static_assert_uimm_bits!(IMM8, 8);
    {
        let a = a.as_i16x8();
        let x: i16x8 = simd_shuffle(
            a,
            a,
            [
                IMM8 as u32 & 0b11,
                (IMM8 as u32 >> 2) & 0b11,
                (IMM8 as u32 >> 4) & 0b11,
                (IMM8 as u32 >> 6) & 0b11,
                4,
                5,
                6,
                7,
            ],
        );
        transmute(x)
    }
}
/// Unpacks and interleave 8-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi8)
pub fn _mm_unpackhi_epi8(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute::<i8x16, _>(simd_shuffle(
            a.as_i8x16(),
            b.as_i8x16(),
            [8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31],
        ))
    }
}
/// Unpacks and interleave 16-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi16)
pub fn _mm_unpackhi_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        let x = simd_shuffle(a.as_i16x8(), b.as_i16x8(), [4, 12, 5, 13, 6, 14, 7, 15]);
        transmute::<i16x8, _>(x)
    }
}
/// Unpacks and interleave 32-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi32)
pub fn _mm_unpackhi_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i32x4, _>(simd_shuffle(a.as_i32x4(), b.as_i32x4(), [2, 6, 3, 7]))
}
/// Unpacks and interleave 64-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi64)
pub fn _mm_unpackhi_epi64(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i64x2, _>(simd_shuffle(a.as_i64x2(), b.as_i64x2(), [1, 3]))
}
/// Unpacks and interleave 8-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi8)
pub fn _mm_unpacklo_epi8(a: __m128i, b: __m128i) -> __m128i {
    {
        transmute::<i8x16, _>(simd_shuffle(
            a.as_i8x16(),
            b.as_i8x16(),
            [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23],
        ))
    }
}
/// Unpacks and interleave 16-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi16)
pub fn _mm_unpacklo_epi16(a: __m128i, b: __m128i) -> __m128i {
    {
        let x = simd_shuffle(a.as_i16x8(), b.as_i16x8(), [0, 8, 1, 9, 2, 10, 3, 11]);
        transmute::<i16x8, _>(x)
    }
}
/// Unpacks and interleave 32-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi32)
pub fn _mm_unpacklo_epi32(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i32x4, _>(simd_shuffle(a.as_i32x4(), b.as_i32x4(), [0, 4, 1, 5]))
}
/// Unpacks and interleave 64-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi64)
pub fn _mm_unpacklo_epi64(a: __m128i, b: __m128i) -> __m128i {
    transmute::<i64x2, _>(simd_shuffle(a.as_i64x2(), b.as_i64x2(), [0, 2]))
}
/// Returns a new vector with the low element of `a` replaced by the sum of the
/// low elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_sd)
// NOTE: Not modeled yet
// pub fn _mm_add_sd(a: __m128d, b: __m128d) -> __m128d {
//     { transmute(simd_insert(a.as_f64x2(), 0, _mm_cvtsd_f64(a) + _mm_cvtsd_f64(b))) }
// }
/// Adds packed double-precision (64-bit) floating-point elements in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_pd)
// NOTE: Not modeled yet
// pub fn _mm_add_pd(a: __m128d, b: __m128d) -> __m128d {
//     { simd_add(a, b) }
// }
/// Returns a new vector with the low element of `a` replaced by the result of
/// diving the lower element of `a` by the lower element of `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_div_sd)
// NOTE: Not modeled yet
// pub fn _mm_div_sd(a: __m128d, b: __m128d) -> __m128d {
//     { transmute(simd_insert(a.as_f64x2(), 0, _mm_cvtsd_f64(a) / _mm_cvtsd_f64(b))) }
// }
/// Divide packed double-precision (64-bit) floating-point elements in `a` by
/// packed elements in `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_div_pd)
// NOTE: Not modeled yet
// pub fn _mm_div_pd(a: __m128d, b: __m128d) -> __m128d {
//     { simd_div(a, b) }
// }
/// Returns a new vector with the low element of `a` replaced by the maximum
/// of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_max_sd)
// NOTE: Not modeled yet
// pub fn _mm_max_sd(a: __m128d, b: __m128d) -> __m128d {
//     { maxsd(a, b) }
// }
/// Returns a new vector with the maximum values from corresponding elements in
/// `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_max_pd)
// NOTE: Not modeled yet
// pub fn _mm_max_pd(a: __m128d, b: __m128d) -> __m128d {
//     { maxpd(a, b) }
// }
/// Returns a new vector with the low element of `a` replaced by the minimum
/// of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_min_sd)
// NOTE: Not modeled yet
// pub fn _mm_min_sd(a: __m128d, b: __m128d) -> __m128d {
//     { minsd(a, b) }
// }
/// Returns a new vector with the minimum values from corresponding elements in
/// `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_min_pd)
// NOTE: Not modeled yet
// pub fn _mm_min_pd(a: __m128d, b: __m128d) -> __m128d {
//     { minpd(a, b) }
// }
/// Returns a new vector with the low element of `a` replaced by multiplying the
/// low elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mul_sd)
// NOTE: Not modeled yet
// pub fn _mm_mul_sd(a: __m128d, b: __m128d) -> __m128d {
//     { transmute(simd_insert(a.as_f64x2(), 0, _mm_cvtsd_f64(a) * _mm_cvtsd_f64(b))) }
// }
/// Multiplies packed double-precision (64-bit) floating-point elements in `a`
/// and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mul_pd)
// NOTE: Not modeled yet
// pub fn _mm_mul_pd(a: __m128d, b: __m128d) -> __m128d {
//     { transmute(simd_mul(a.as_f64x2(), b.as_f64x2())) }
// }
/// Returns a new vector with the low element of `a` replaced by the square
/// root of the lower element `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sqrt_sd)
// NOTE: Not modeled yet
// pub fn _mm_sqrt_sd(a: __m128d, b: __m128d) -> __m128d {
//     { simd_insert(a, 0, sqrtf64(_mm_cvtsd_f64(b))) }
// }
/// Returns a new vector with the square root of each of the values in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sqrt_pd)
// NOTE: Not modeled yet
// pub fn _mm_sqrt_pd(a: __m128d) -> __m128d {
//     { simd_fsqrt(a) }
// }
/// Returns a new vector with the low element of `a` replaced by subtracting the
/// low element by `b` from the low element of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_sd)
// NOTE: Not modeled yet
// pub fn _mm_sub_sd(a: __m128d, b: __m128d) -> __m128d {
//     { transmute(simd_insert(a.as_f64x2(), 0, _mm_cvtsd_f64(a) - _mm_cvtsd_f64(b))) }
// }
/// Subtract packed double-precision (64-bit) floating-point elements in `b`
/// from `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_pd)
// NOTE: Not modeled yet
// pub fn _mm_sub_pd(a: __m128d, b: __m128d) -> __m128d {
//     { simd_sub(a, b) }
// }
/// Computes the bitwise AND of packed double-precision (64-bit) floating-point
/// elements in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_and_pd)
pub fn _mm_and_pd(a: __m128d, b: __m128d) -> __m128d {
    {
        let a: __m128i = transmute(a);
        let b: __m128i = transmute(b);
        transmute(_mm_and_si128(a, b))
    }
}
/// Computes the bitwise NOT of `a` and then AND with `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_andnot_pd)
pub fn _mm_andnot_pd(a: __m128d, b: __m128d) -> __m128d {
    {
        let a: __m128i = transmute(a);
        let b: __m128i = transmute(b);
        transmute(_mm_andnot_si128(a, b))
    }
}
/// Computes the bitwise OR of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_or_pd)
pub fn _mm_or_pd(a: __m128d, b: __m128d) -> __m128d {
    {
        let a: __m128i = transmute(a);
        let b: __m128i = transmute(b);
        transmute(_mm_or_si128(a, b))
    }
}
/// Computes the bitwise XOR of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_xor_pd)
pub fn _mm_xor_pd(a: __m128d, b: __m128d) -> __m128d {
    {
        let a: __m128i = transmute(a);
        let b: __m128i = transmute(b);
        transmute(_mm_xor_si128(a, b))
    }
}
/// Returns a new vector with the low element of `a` replaced by the equality
/// comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpeq_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 0) }
// }
/// Returns a new vector with the low element of `a` replaced by the less-than
/// comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmplt_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 1) }
// }
/// Returns a new vector with the low element of `a` replaced by the
/// less-than-or-equal comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmple_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmple_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 2) }
// }
/// Returns a new vector with the low element of `a` replaced by the
/// greater-than comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpgt_sd(a: __m128d, b: __m128d) -> __m128d {
//     { transmute(simd_insert(_mm_cmplt_sd(b, a), 1, simd_extract(a, 1))) }
// }
/// Returns a new vector with the low element of `a` replaced by the
/// greater-than-or-equal comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpge_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpge_sd(a: __m128d, b: __m128d) -> __m128d {
//     { simd_insert(_mm_cmple_sd(b, a), 1, simd_extract(a, 1)) }
// }
/// Returns a new vector with the low element of `a` replaced by the result
/// of comparing both of the lower elements of `a` and `b` to `NaN`. If
/// neither are equal to `NaN` then `0xFFFFFFFFFFFFFFFF` is used and `0`
/// otherwise.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpord_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpord_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 7) }
// }
/// Returns a new vector with the low element of `a` replaced by the result of
/// comparing both of the lower elements of `a` and `b` to `NaN`. If either is
/// equal to `NaN` then `0xFFFFFFFFFFFFFFFF` is used and `0` otherwise.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpunord_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpunord_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 3) }
// }
/// Returns a new vector with the low element of `a` replaced by the not-equal
/// comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpneq_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpneq_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 4) }
// }
/// Returns a new vector with the low element of `a` replaced by the
/// not-less-than comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpnlt_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpnlt_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 5) }
// }
/// Returns a new vector with the low element of `a` replaced by the
/// not-less-than-or-equal comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpnle_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpnle_sd(a: __m128d, b: __m128d) -> __m128d {
//     { cmpsd(a, b, 6) }
// }
/// Returns a new vector with the low element of `a` replaced by the
/// not-greater-than comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpngt_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpngt_sd(a: __m128d, b: __m128d) -> __m128d {
//     { simd_insert(_mm_cmpnlt_sd(b, a), 1, simd_extract(a, 1)) }
// }
/// Returns a new vector with the low element of `a` replaced by the
/// not-greater-than-or-equal comparison of the lower elements of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpnge_sd)
// NOTE: Not modeled yet
// pub fn _mm_cmpnge_sd(a: __m128d, b: __m128d) -> __m128d {
//     { simd_insert(_mm_cmpnle_sd(b, a), 1, simd_extract(a, 1)) }
// }
/// Compares corresponding elements in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpeq_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 0) }
// }
/// Compares corresponding elements in `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmplt_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 1) }
// }
/// Compares corresponding elements in `a` and `b` for less-than-or-equal
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmple_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmple_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 2) }
// }
/// Compares corresponding elements in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpgt_pd(a: __m128d, b: __m128d) -> __m128d {
//     _mm_cmplt_pd(b, a)
// }
/// Compares corresponding elements in `a` and `b` for greater-than-or-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpge_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpge_pd(a: __m128d, b: __m128d) -> __m128d {
//     _mm_cmple_pd(b, a)
// }
/// Compares corresponding elements in `a` and `b` to see if neither is `NaN`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpord_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpord_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 7) }
// }
/// Compares corresponding elements in `a` and `b` to see if either is `NaN`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpunord_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpunord_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 3) }
// }
/// Compares corresponding elements in `a` and `b` for not-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpneq_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpneq_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 4) }
// }
/// Compares corresponding elements in `a` and `b` for not-less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpnlt_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpnlt_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 5) }
// }
/// Compares corresponding elements in `a` and `b` for not-less-than-or-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpnle_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpnle_pd(a: __m128d, b: __m128d) -> __m128d {
//     { cmppd(a, b, 6) }
// }
/// Compares corresponding elements in `a` and `b` for not-greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpngt_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpngt_pd(a: __m128d, b: __m128d) -> __m128d {
//     _mm_cmpnlt_pd(b, a)
// }
/// Compares corresponding elements in `a` and `b` for
/// not-greater-than-or-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpnge_pd)
// NOTE: Not modeled yet
// pub fn _mm_cmpnge_pd(a: __m128d, b: __m128d) -> __m128d {
//     _mm_cmpnle_pd(b, a)
// }
/// Compares the lower element of `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_comieq_sd)
// NOTE: Not modeled yet
// pub fn _mm_comieq_sd(a: __m128d, b: __m128d) -> i32 {
//     { comieqsd(a, b) }
// }
/// Compares the lower element of `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_comilt_sd)
// NOTE: Not modeled yet
// pub fn _mm_comilt_sd(a: __m128d, b: __m128d) -> i32 {
//     { comiltsd(a, b) }
// }
/// Compares the lower element of `a` and `b` for less-than-or-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_comile_sd)
// NOTE: Not modeled yet
// pub fn _mm_comile_sd(a: __m128d, b: __m128d) -> i32 {
//     { comilesd(a, b) }
// }
/// Compares the lower element of `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_comigt_sd)
// NOTE: Not modeled yet
// pub fn _mm_comigt_sd(a: __m128d, b: __m128d) -> i32 {
//     { comigtsd(a, b) }
// }
/// Compares the lower element of `a` and `b` for greater-than-or-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_comige_sd)
// NOTE: Not modeled yet
// pub fn _mm_comige_sd(a: __m128d, b: __m128d) -> i32 {
//     { comigesd(a, b) }
// }
/// Compares the lower element of `a` and `b` for not-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_comineq_sd)
// NOTE: Not modeled yet
// pub fn _mm_comineq_sd(a: __m128d, b: __m128d) -> i32 {
//     { comineqsd(a, b) }
// }
/// Compares the lower element of `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_ucomieq_sd)
// NOTE: Not modeled yet
// pub fn _mm_ucomieq_sd(a: __m128d, b: __m128d) -> i32 {
//     { ucomieqsd(a, b) }
// }
/// Compares the lower element of `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_ucomilt_sd)
// NOTE: Not modeled yet
// pub fn _mm_ucomilt_sd(a: __m128d, b: __m128d) -> i32 {
//     { ucomiltsd(a, b) }
// }
/// Compares the lower element of `a` and `b` for less-than-or-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_ucomile_sd)
// NOTE: Not modeled yet
// pub fn _mm_ucomile_sd(a: __m128d, b: __m128d) -> i32 {
//     { ucomilesd(a, b) }
// }
/// Compares the lower element of `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_ucomigt_sd)
// NOTE: Not modeled yet
// pub fn _mm_ucomigt_sd(a: __m128d, b: __m128d) -> i32 {
//     { ucomigtsd(a, b) }
// }
/// Compares the lower element of `a` and `b` for greater-than-or-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_ucomige_sd)
// NOTE: Not modeled yet
// pub fn _mm_ucomige_sd(a: __m128d, b: __m128d) -> i32 {
//     { ucomigesd(a, b) }
// }
/// Compares the lower element of `a` and `b` for not-equal.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_ucomineq_sd)
// NOTE: Not modeled yet
// pub fn _mm_ucomineq_sd(a: __m128d, b: __m128d) -> i32 {
//     { ucomineqsd(a, b) }
// }
/// Converts packed double-precision (64-bit) floating-point elements in `a` to
/// packed single-precision (32-bit) floating-point elements
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtpd_ps)
pub fn _mm_cvtpd_ps(a: __m128d) -> __m128 {
    {
        let r = simd_cast::<2, _, f32>(a.as_f64x2());
        let zero = f32x2::ZERO();
        transmute::<f32x4, _>(simd_shuffle(r, zero, [0, 1, 2, 3]))
    }
}
/// Converts packed single-precision (32-bit) floating-point elements in `a` to
/// packed
/// double-precision (64-bit) floating-point elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtps_pd)
pub fn _mm_cvtps_pd(a: __m128) -> __m128d {
    {
        let a = a.as_f32x4();
        transmute(simd_cast::<2, f32, f64>(simd_shuffle(a, a, [0, 1])))
    }
}
/// Converts packed double-precision (64-bit) floating-point elements in `a` to
/// packed 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtpd_epi32)
// NOTE: Not modeled yet
// pub fn _mm_cvtpd_epi32(a: __m128d) -> __m128i {
//     { transmute(cvtpd2dq(a)) }
// }
/// Converts the lower double-precision (64-bit) floating-point element in a to
/// a 32-bit integer.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtsd_si32)
// NOTE: Not modeled yet
// pub fn _mm_cvtsd_si32(a: __m128d) -> i32 {
//     { cvtsd2si(a) }
// }
/// Converts the lower double-precision (64-bit) floating-point element in `b`
/// to a single-precision (32-bit) floating-point element, store the result in
/// the lower element of the return value, and copies the upper element from `a`
/// to the upper element the return value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtsd_ss)
// NOTE: Not modeled yet
// pub fn _mm_cvtsd_ss(a: __m128, b: __m128d) -> __m128 {
//     { cvtsd2ss(a, b) }
// }
/// Returns the lower double-precision (64-bit) floating-point element of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtsd_f64)
// NOTE: Not modeled yet
// pub fn _mm_cvtsd_f64(a: __m128d) -> f64 {
//     { simd_extract(a, 0) }
// }
/// Converts the lower single-precision (32-bit) floating-point element in `b`
/// to a double-precision (64-bit) floating-point element, store the result in
/// the lower element of the return value, and copies the upper element from `a`
/// to the upper element the return value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtss_sd)
// NOTE: Not modeled yet
// pub fn _mm_cvtss_sd(a: __m128d, b: __m128) -> __m128d {
//     { cvtss2sd(a, b) }
// }
/// Converts packed double-precision (64-bit) floating-point elements in `a` to
/// packed 32-bit integers with truncation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvttpd_epi32)
// NOTE: Not modeled yet
// pub fn _mm_cvttpd_epi32(a: __m128d) -> __m128i {
//     { transmute(cvttpd2dq(a)) }
// }
/// Converts the lower double-precision (64-bit) floating-point element in `a`
/// to a 32-bit integer with truncation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvttsd_si32)
// NOTE: Not modeled yet
// pub fn _mm_cvttsd_si32(a: __m128d) -> i32 {
//     { cvttsd2si(a) }
// }
/// Converts packed single-precision (32-bit) floating-point elements in `a` to
/// packed 32-bit integers with truncation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvttps_epi32)
// NOTE: Not modeled yet
// pub fn _mm_cvttps_epi32(a: __m128) -> __m128i {
//     { transmute(cvttps2dq(a)) }
// }
/// Copies double-precision (64-bit) floating-point element `a` to the lower
/// element of the packed 64-bit return value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_sd)
pub fn _mm_set_sd(a: f64) -> __m128d {
    _mm_set_pd(0.0, a)
}
/// Broadcasts double-precision (64-bit) floating-point value a to all elements
/// of the return value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_pd)
pub fn _mm_set1_pd(a: f64) -> __m128d {
    _mm_set_pd(a, a)
}
/// Broadcasts double-precision (64-bit) floating-point value a to all elements
/// of the return value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_pd1)
pub fn _mm_set_pd1(a: f64) -> __m128d {
    _mm_set_pd(a, a)
}
/// Sets packed double-precision (64-bit) floating-point elements in the return
/// value with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_pd)
pub fn _mm_set_pd(a: f64, b: f64) -> __m128d {
    transmute(f64x2::new(b, a))
}
/// Sets packed double-precision (64-bit) floating-point elements in the return
/// value with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setr_pd)
pub fn _mm_setr_pd(a: f64, b: f64) -> __m128d {
    _mm_set_pd(b, a)
}
/// Returns packed double-precision (64-bit) floating-point elements with all
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setzero_pd)
pub fn _mm_setzero_pd() -> __m128d {
    transmute(f64x2::ZERO())
}
/// Returns a mask of the most significant bit of each element in `a`.
///
/// The mask is stored in the 2 least significant bits of the return value.
/// All other bits are set to `0`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_movemask_pd)
pub fn _mm_movemask_pd(a: __m128d) -> i32 {
    {
        let mask: i64x2 = simd_lt(transmute(a), i64x2::ZERO());
        simd_bitmask_little!(1, mask, u8) as i32
    }
}
/// Constructs a 128-bit floating-point vector of `[2 x double]` from two
/// 128-bit vector parameters of `[2 x double]`, using the immediate-value
/// parameter as a specifier.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shuffle_pd)
pub fn _mm_shuffle_pd<const MASK: i32>(a: __m128d, b: __m128d) -> __m128d {
    static_assert_uimm_bits!(MASK, 8);
    transmute(simd_shuffle(
        a.as_f64x2(),
        b.as_f64x2(),
        [MASK as u32 & 0b1, ((MASK as u32 >> 1) & 0b1) + 2],
    ))
}
/// Constructs a 128-bit floating-point vector of `[2 x double]`. The lower
/// 64 bits are set to the lower 64 bits of the second parameter. The upper
/// 64 bits are set to the upper 64 bits of the first parameter.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_move_sd)
pub fn _mm_move_sd(a: __m128d, b: __m128d) -> __m128d {
    _mm_setr_pd(simd_extract(b.as_f64x2(), 0), simd_extract(a.as_f64x2(), 1))
}
/// Casts a 128-bit floating-point vector of `[2 x double]` into a 128-bit
/// floating-point vector of `[4 x float]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_castpd_ps)
pub fn _mm_castpd_ps(a: __m128d) -> __m128 {
    transmute(a)
}
/// Casts a 128-bit floating-point vector of `[2 x double]` into a 128-bit
/// integer vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_castpd_si128)
pub fn _mm_castpd_si128(a: __m128d) -> __m128i {
    transmute(a)
}
/// Casts a 128-bit floating-point vector of `[4 x float]` into a 128-bit
/// floating-point vector of `[2 x double]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_castps_pd)
pub fn _mm_castps_pd(a: __m128) -> __m128d {
    transmute(a)
}
/// Casts a 128-bit floating-point vector of `[4 x float]` into a 128-bit
/// integer vector.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_castps_si128)
pub fn _mm_castps_si128(a: __m128) -> __m128i {
    transmute(a)
}
/// Casts a 128-bit integer vector into a 128-bit floating-point vector
/// of `[2 x double]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_castsi128_pd)
pub fn _mm_castsi128_pd(a: __m128i) -> __m128d {
    transmute(a)
}
/// Casts a 128-bit integer vector into a 128-bit floating-point vector
/// of `[4 x float]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_castsi128_ps)
pub fn _mm_castsi128_ps(a: __m128i) -> __m128 {
    transmute(a)
}
/// Returns vector of type __m128d with indeterminate elements.with indetermination elements.
/// Despite using the word "undefined" (following Intel's naming scheme), this non-deterministically
/// picks some valid value and is not equivalent to [`mem::MaybeUninit`].
/// In practice, this is typically equivalent to [`mem::zeroed`].
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_undefined_pd)
pub fn _mm_undefined_pd() -> __m128d {
    transmute(f32x4::ZERO())
}
/// Returns vector of type __m128i with indeterminate elements.with indetermination elements.
/// Despite using the word "undefined" (following Intel's naming scheme), this non-deterministically
/// picks some valid value and is not equivalent to [`mem::MaybeUninit`].
/// In practice, this is typically equivalent to [`mem::zeroed`].
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_undefined_si128)
pub fn _mm_undefined_si128() -> __m128i {
    transmute(u32x4::ZERO())
}
/// The resulting `__m128d` element is composed by the low-order values of
/// the two `__m128d` interleaved input elements, i.e.:
///
/// * The `[127:64]` bits are copied from the `[127:64]` bits of the second input
/// * The `[63:0]` bits are copied from the `[127:64]` bits of the first input
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_pd)
pub fn _mm_unpackhi_pd(a: __m128d, b: __m128d) -> __m128d {
    transmute(simd_shuffle(a.as_f64x2(), b.as_f64x2(), [1, 3]))
}
/// The resulting `__m128d` element is composed by the high-order values of
/// the two `__m128d` interleaved input elements, i.e.:
///
/// * The `[127:64]` bits are copied from the `[63:0]` bits of the second input
/// * The `[63:0]` bits are copied from the `[63:0]` bits of the first input
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_pd)
pub fn _mm_unpacklo_pd(a: __m128d, b: __m128d) -> __m128d {
    transmute(simd_shuffle(a.as_f64x2(), b.as_f64x2(), [0, 2]))
}
