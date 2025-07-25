//! Streaming SIMD Extensions 2 (SSE2)
use super::types::*;
use crate::abstractions::{bit::Bit, bitvec::BitVec, simd::*};
mod c_extern {
    use crate::abstractions::{bit::MachineInteger, simd::*};
    pub fn packsswb(a: i16x8, b: i16x8) -> i8x16 {
        i8x16::from_fn(|i| {
            if i < 8 {
                if a[i] > (i8::MAX as i16) {
                    i8::MAX
                } else if a[i] < (i8::MIN as i16) {
                    i8::MIN
                } else {
                    a[i] as i8
                }
            } else {
                if b[i - 8] > (i8::MAX as i16) {
                    i8::MAX
                } else if b[i - 8] < (i8::MIN as i16) {
                    i8::MIN
                } else {
                    b[i - 8] as i8
                }
            }
        })
    }
    pub fn pmaddwd(a: i16x8, b: i16x8) -> i32x4 {
        i32x4::from_fn(|i| {
            (a[2 * i] as i32) * (b[2 * i] as i32) + (a[2 * i + 1] as i32) * (b[2 * i + 1] as i32)
        })
    }
    pub fn psadbw(a: u8x16, b: u8x16) -> u64x2 {
        let tmp = u8x16::from_fn(|i| a[i].absolute_diff(b[i]));
        u64x2::from_fn(|i| {
            (tmp[i * 8] as u16)
                .wrapping_add(tmp[i * 8 + 1] as u16)
                .wrapping_add(tmp[i * 8 + 2] as u16)
                .wrapping_add(tmp[i * 8 + 3] as u16)
                .wrapping_add(tmp[i * 8 + 4] as u16)
                .wrapping_add(tmp[i * 8 + 5] as u16)
                .wrapping_add(tmp[i * 8 + 6] as u16)
                .wrapping_add(tmp[i * 8 + 7] as u16) as u64
        })
    }
    pub fn psllw(a: i16x8, count: i16x8) -> i16x8 {
        let count4: u64 = (count[0] as u16) as u64;
        let count3: u64 = ((count[1] as u16) as u64) * 65536;
        let count2: u64 = ((count[2] as u16) as u64) * 4294967296;
        let count1: u64 = ((count[3] as u16) as u64) * 281474976710656;
        let count = count1 + count2 + count3 + count4;
        i16x8::from_fn(|i| {
            if count > 15 {
                0
            } else {
                ((a[i] as u16) << count) as i16
            }
        })
    }

    pub fn pslld(a: i32x4, count: i32x4) -> i32x4 {
        let count: u64 = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

        i32x4::from_fn(|i| {
            if count > 31 {
                0
            } else {
                ((a[i] as u32) << count) as i32
            }
        })
    }

    pub fn psllq(a: i64x2, count: i64x2) -> i64x2 {
        let count: u64 = count[0] as u64;

        i64x2::from_fn(|i| {
            if count > 63 {
                0
            } else {
                ((a[i] as u64) << count) as i64
            }
        })
    }

    pub fn psraw(a: i16x8, count: i16x8) -> i16x8 {
        let count: u64 = ((count[3] as u16) as u64) * 281474976710656
            + ((count[2] as u16) as u64) * 4294967296
            + ((count[1] as u16) as u64) * 65536
            + ((count[0] as u16) as u64);

        i16x8::from_fn(|i| {
            if count > 15 {
                if a[i] < 0 {
                    -1
                } else {
                    0
                }
            } else {
                a[i] >> count
            }
        })
    }

    pub fn psrad(a: i32x4, count: i32x4) -> i32x4 {
        let count: u64 = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

        i32x4::from_fn(|i| {
            if count > 31 {
                if a[i] < 0 {
                    -1
                } else {
                    0
                }
            } else {
                a[i] << count
            }
        })
    }

    pub fn psrlw(a: i16x8, count: i16x8) -> i16x8 {
        let count: u64 = (count[3] as u16 as u64) * 281474976710656
            + (count[2] as u16 as u64) * 4294967296
            + (count[1] as u16 as u64) * 65536
            + (count[0] as u16 as u64);

        i16x8::from_fn(|i| {
            if count > 15 {
                0
            } else {
                ((a[i] as u16) >> count) as i16
            }
        })
    }

    pub fn psrld(a: i32x4, count: i32x4) -> i32x4 {
        let count: u64 = (count[1] as u32 as u64) * 4294967296 + (count[0] as u32 as u64);

        i32x4::from_fn(|i| {
            if count > 31 {
                0
            } else {
                ((a[i] as u32) >> count) as i32
            }
        })
    }

    pub fn psrlq(a: i64x2, count: i64x2) -> i64x2 {
        let count: u64 = count[0] as u64;

        i64x2::from_fn(|i| {
            if count > 63 {
                0
            } else {
                ((a[i] as u64) >> count) as i64
            }
        })
    }

    pub fn packssdw(a: i32x4, b: i32x4) -> i16x8 {
        i16x8::from_fn(|i| {
            if i < 4 {
                if a[i] > (i16::MAX as i32) {
                    i16::MAX
                } else if a[i] < (i16::MIN as i32) {
                    i16::MIN
                } else {
                    a[i] as i16
                }
            } else {
                if b[i - 4] > (i16::MAX as i32) {
                    i16::MAX
                } else if b[i - 4] < (i16::MIN as i32) {
                    i16::MIN
                } else {
                    b[i - 4] as i16
                }
            }
        })
    }

    pub fn packuswb(a: i16x8, b: i16x8) -> u8x16 {
        u8x16::from_fn(|i| {
            if i < 8 {
                if a[i] > (u8::MAX as i16) {
                    u8::MAX
                } else if a[i] < (u8::MIN as i16) {
                    u8::MIN
                } else {
                    a[i] as u8
                }
            } else {
                if b[i - 8] > (u8::MAX as i16) {
                    u8::MAX
                } else if b[i - 8] < (u8::MIN as i16) {
                    u8::MIN
                } else {
                    b[i - 8] as u8
                }
            }
        })
    }
}

use c_extern::*;

/// Adds packed 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi8)

pub fn _mm_add_epi8(a: __m128i, b: __m128i) -> __m128i {
    simd_add(BitVec::to_i8x16(a), BitVec::to_i8x16(b)).into()
}

/// Adds packed 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi16)

pub fn _mm_add_epi16(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_i16x8(simd_add(BitVec::to_i16x8(a), BitVec::to_i16x8(b)))
}

/// Adds packed 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi32)

pub fn _mm_add_epi32(a: __m128i, b: __m128i) -> __m128i {
    simd_add(BitVec::to_i32x4(a), BitVec::to_i32x4(b)).into()
}

/// Adds packed 64-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi64)

pub fn _mm_add_epi64(a: __m128i, b: __m128i) -> __m128i {
    simd_add(BitVec::to_i64x2(a), BitVec::to_i64x2(b)).into()
}

/// Adds packed 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epi8)

pub fn _mm_adds_epi8(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_add(BitVec::to_i8x16(a), BitVec::to_i8x16(b)).into()
}

/// Adds packed 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epi16)

pub fn _mm_adds_epi16(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_add(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Adds packed unsigned 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epu8)

pub fn _mm_adds_epu8(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_add(BitVec::to_u8x16(a), BitVec::to_u8x16(b)).into()
}

/// Adds packed unsigned 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_adds_epu16)

pub fn _mm_adds_epu16(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_add(BitVec::to_u16x8(a), BitVec::to_u16x8(b)).into()
}

/// Averages packed unsigned 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_avg_epu8)

pub fn _mm_avg_epu8(a: __m128i, b: __m128i) -> __m128i {
    let a = simd_cast::<16, _, u16>(BitVec::to_u8x16(a));
    let b = simd_cast::<16, _, u16>(BitVec::to_u8x16(b));
    let r = simd_shr(simd_add(simd_add(a, b), u16x16::splat(1)), u16x16::splat(1));
    simd_cast::<16, _, u8>(r).into()
}

/// Averages packed unsigned 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_avg_epu16)

pub fn _mm_avg_epu16(a: __m128i, b: __m128i) -> __m128i {
    let a = simd_cast::<8, _, u32>(BitVec::to_u16x8(a));
    let b = simd_cast::<8, _, u32>(BitVec::to_u16x8(b));
    let r = simd_shr(simd_add(simd_add(a, b), u32x8::splat(1)), u32x8::splat(1));
    simd_cast::<8, _, u16>(r).into()
}

/// Multiplies and then horizontally add signed 16 bit integers in `a` and `b`.
///
/// Multiplies packed signed 16-bit integers in `a` and `b`, producing
/// intermediate signed 32-bit integers. Horizontally add adjacent pairs of
/// intermediate 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_madd_epi16)

pub fn _mm_madd_epi16(a: __m128i, b: __m128i) -> __m128i {
    pmaddwd(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_max_epi16)

pub fn _mm_max_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let b = BitVec::to_i16x8(b);
    simd_select(simd_gt(a, b), a, b).into()
}

/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns the
/// packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_max_epu8)

pub fn _mm_max_epu8(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_u8x16(a);
    let b = BitVec::to_u8x16(b);
    simd_select(simd_gt(a, b), a, b).into()
}

/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_min_epi16)

pub fn _mm_min_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let b = BitVec::to_i16x8(b);
    simd_select(simd_lt(a, b), a, b).into()
}

/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns the
/// packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_min_epu8)

pub fn _mm_min_epu8(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_u8x16(a);
    let b = BitVec::to_u8x16(b);
    simd_select(simd_lt(a, b), a, b).into()
}

/// Multiplies the packed 16-bit integers in `a` and `b`.
///
/// The multiplication produces intermediate 32-bit integers, and returns the
/// high 16 bits of the intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhi_epi16)

pub fn _mm_mulhi_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = simd_cast::<8, i16, i32>(BitVec::to_i16x8(a));
    let b = simd_cast::<8, i16, i32>(BitVec::to_i16x8(b));
    let r = simd_shr(simd_mul(a, b), i32x8::splat(16));
    BitVec::from_i16x8(simd_cast::<8, i32, i16>(r))
}

/// Multiplies the packed unsigned 16-bit integers in `a` and `b`.
///
/// The multiplication produces intermediate 32-bit integers, and returns the
/// high 16 bits of the intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhi_epu16)

pub fn _mm_mulhi_epu16(a: __m128i, b: __m128i) -> __m128i {
    let a = simd_cast::<8, _, u32>(BitVec::to_u16x8(a));
    let b = simd_cast::<8, _, u32>(BitVec::to_u16x8(b));
    let r = simd_shr(simd_mul(a, b), u32x8::splat(16));
    simd_cast::<8, u32, u16>(r).into()
}

/// Multiplies the packed 16-bit integers in `a` and `b`.
///
/// The multiplication produces intermediate 32-bit integers, and returns the
/// low 16 bits of the intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mullo_epi16)

pub fn _mm_mullo_epi16(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_i16x8(simd_mul(BitVec::to_i16x8(a), BitVec::to_i16x8(b)))
}

/// Multiplies the low unsigned 32-bit integers from each packed 64-bit element
/// in `a` and `b`.
///
/// Returns the unsigned 64-bit results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mul_epu32)

pub fn _mm_mul_epu32(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_u64x2(a);
    let b = BitVec::to_u64x2(b);
    let mask = u64x2::splat(u32::MAX.into());
    simd_mul(simd_and(a, mask), simd_and(b, mask)).into()
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
    psadbw(BitVec::to_u8x16(a), BitVec::to_u8x16(b)).into()
}

/// Subtracts packed 8-bit integers in `b` from packed 8-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi8)

pub fn _mm_sub_epi8(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_i8x16(simd_sub(BitVec::to_i8x16(a), BitVec::to_i8x16(b)))
}

/// Subtracts packed 16-bit integers in `b` from packed 16-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi16)

pub fn _mm_sub_epi16(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_i16x8(simd_sub(BitVec::to_i16x8(a), BitVec::to_i16x8(b)))
}

/// Subtract packed 32-bit integers in `b` from packed 32-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi32)

pub fn _mm_sub_epi32(a: __m128i, b: __m128i) -> __m128i {
    simd_sub(BitVec::to_i32x4(a), BitVec::to_i32x4(b)).into()
}

/// Subtract packed 64-bit integers in `b` from packed 64-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi64)

pub fn _mm_sub_epi64(a: __m128i, b: __m128i) -> __m128i {
    simd_sub(BitVec::to_i64x2(a), BitVec::to_i64x2(b)).into()
}

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epi8)

pub fn _mm_subs_epi8(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_sub(BitVec::to_i8x16(a), BitVec::to_i8x16(b)).into()
}

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epi16)

pub fn _mm_subs_epi16(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_sub(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Subtract packed unsigned 8-bit integers in `b` from packed unsigned 8-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epu8)

pub fn _mm_subs_epu8(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_sub(BitVec::to_u8x16(a), BitVec::to_u8x16(b)).into()
}

/// Subtract packed unsigned 16-bit integers in `b` from packed unsigned 16-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_subs_epu16)

pub fn _mm_subs_epu16(a: __m128i, b: __m128i) -> __m128i {
    simd_saturating_sub(BitVec::to_u16x8(a), BitVec::to_u16x8(b)).into()
}

/// Shifts `a` left by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_si128)

pub fn _mm_slli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);
    _mm_slli_si128_impl::<IMM8>(a)
}

/// Implementation detail: converts the immediate argument of the
/// `_mm_slli_si128` intrinsic into a compile-time constant.

fn _mm_slli_si128_impl<const IMM8: i32>(a: __m128i) -> __m128i {
    const fn mask(shift: i32, i: u32) -> u64 {
        let shift = shift as u32 & 0xff;
        if shift > 15 {
            i as u64
        } else {
            (16 - shift + i) as u64
        }
    }
    (simd_shuffle(
        i8x16::from_fn(|_| 0),
        BitVec::to_i8x16(a),
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
    .into()
}

/// Shifts `a` left by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_bslli_si128)

pub fn _mm_bslli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);
    _mm_slli_si128_impl::<IMM8>(a)
}

/// Shifts `a` right by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_bsrli_si128)

pub fn _mm_bsrli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);
    _mm_srli_si128_impl::<IMM8>(a)
}

/// Shifts packed 16-bit integers in `a` left by `IMM8` while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_epi16)

pub fn _mm_slli_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    if IMM8 >= 16 {
        _mm_setzero_si128()
    } else {
        simd_shl(BitVec::to_u16x8(a), u16x8::splat(IMM8 as u16)).into()
    }
}

/// Shifts packed 16-bit integers in `a` left by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sll_epi16)

pub fn _mm_sll_epi16(a: __m128i, count: __m128i) -> __m128i {
    psllw(BitVec::to_i16x8(a), BitVec::to_i16x8(count)).into()
}

/// Shifts packed 32-bit integers in `a` left by `IMM8` while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_epi32)

pub fn _mm_slli_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    if IMM8 >= 32 {
        _mm_setzero_si128()
    } else {
        simd_shl(BitVec::to_u32x4(a), u32x4::splat(IMM8 as u32)).into()
    }
}

/// Shifts packed 32-bit integers in `a` left by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sll_epi32)

pub fn _mm_sll_epi32(a: __m128i, count: __m128i) -> __m128i {
    pslld(BitVec::to_i32x4(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 64-bit integers in `a` left by `IMM8` while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_epi64)

pub fn _mm_slli_epi64<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    if IMM8 >= 64 {
        _mm_setzero_si128()
    } else {
        simd_shl(BitVec::to_u64x2(a), u64x2::splat(IMM8 as u64)).into()
    }
}

/// Shifts packed 64-bit integers in `a` left by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sll_epi64)

pub fn _mm_sll_epi64(a: __m128i, count: __m128i) -> __m128i {
    psllq(BitVec::to_i64x2(a), BitVec::to_i64x2(count)).into()
}

/// Shifts packed 16-bit integers in `a` right by `IMM8` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srai_epi16)

pub fn _mm_srai_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);
    simd_shr(BitVec::to_i16x8(a), i16x8::splat(IMM8.min(15) as i16)).into()
}

/// Shifts packed 16-bit integers in `a` right by `count` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sra_epi16)

pub fn _mm_sra_epi16(a: __m128i, count: __m128i) -> __m128i {
    psraw(BitVec::to_i16x8(a), BitVec::to_i16x8(count)).into()
}

/// Shifts packed 32-bit integers in `a` right by `IMM8` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srai_epi32)

pub fn _mm_srai_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);
    simd_shr(BitVec::to_i32x4(a), i32x4::splat(IMM8.min(31))).into()
}

/// Shifts packed 32-bit integers in `a` right by `count` while shifting in sign
/// bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sra_epi32)

pub fn _mm_sra_epi32(a: __m128i, count: __m128i) -> __m128i {
    psrad(BitVec::to_i32x4(a), BitVec::to_i32x4(count)).into()
}

/// Shifts `a` right by `IMM8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_si128)

pub fn _mm_srli_si128<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);
    _mm_srli_si128_impl::<IMM8>(a)
}

/// Implementation detail: converts the immediate argument of the
/// `_mm_srli_si128` intrinsic into a compile-time constant.

fn _mm_srli_si128_impl<const IMM8: i32>(a: __m128i) -> __m128i {
    const fn mask(shift: i32, i: u32) -> u64 {
        if (shift as u32) > 15 {
            (i + 16) as u64
        } else {
            (i + (shift as u32)) as u64
        }
    }
    let x: i8x16 = simd_shuffle(
        BitVec::to_i8x16(a),
        i8x16::from_fn(|_| 0),
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
    x.into()
}

/// Shifts packed 16-bit integers in `a` right by `IMM8` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi16)

pub fn _mm_srli_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    if IMM8 >= 16 {
        _mm_setzero_si128()
    } else {
        simd_shr(BitVec::to_u16x8(a), u16x8::splat(IMM8 as u16)).into()
    }
}

/// Shifts packed 16-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srl_epi16)

pub fn _mm_srl_epi16(a: __m128i, count: __m128i) -> __m128i {
    psrlw(BitVec::to_i16x8(a), BitVec::to_i16x8(count)).into()
}

/// Shifts packed 32-bit integers in `a` right by `IMM8` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi32)

pub fn _mm_srli_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    if IMM8 >= 32 {
        _mm_setzero_si128()
    } else {
        simd_shr(BitVec::to_u32x4(a), u32x4::splat(IMM8 as u32)).into()
    }
}

/// Shifts packed 32-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srl_epi32)

pub fn _mm_srl_epi32(a: __m128i, count: __m128i) -> __m128i {
    psrld(BitVec::to_i32x4(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 64-bit integers in `a` right by `IMM8` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi64)

pub fn _mm_srli_epi64<const IMM8: i32>(a: __m128i) -> __m128i {
    // TODO    // static_assert_uimm_bits!(IMM8, 8);

    if IMM8 >= 64 {
        BitVec::from_fn(|_| Bit::Zero)
    } else {
        BitVec::from_u64x2(simd_shr(BitVec::to_u64x2(a), u64x2::splat(IMM8 as u64)))
    }
}

/// Shifts packed 64-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srl_epi64)

pub fn _mm_srl_epi64(a: __m128i, count: __m128i) -> __m128i {
    psrlq(BitVec::to_i64x2(a), BitVec::to_i64x2(count)).into()
}

/// Computes the bitwise AND of 128 bits (representing integer data) in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_and_si128)

pub fn _mm_and_si128(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_fn(|i| a[i] & b[i])
}

/// Computes the bitwise NOT of 128 bits (representing integer data) in `a` and
/// then AND with `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_andnot_si128)

pub fn _mm_andnot_si128(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_fn(|i| BitVec::<128>::from_fn(|i| _mm_set1_epi8(-1)[i] ^ a[i])[i] & b[i])
}

/// Computes the bitwise OR of 128 bits (representing integer data) in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_or_si128)

pub fn _mm_or_si128(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_fn(|i| a[i] | b[i])
}

/// Computes the bitwise XOR of 128 bits (representing integer data) in `a` and
/// `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_xor_si128)

pub fn _mm_xor_si128(a: __m128i, b: __m128i) -> __m128i {
    BitVec::from_fn(|i| a[i] ^ b[i])
}

/// Compares packed 8-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_epi8)

pub fn _mm_cmpeq_epi8(a: __m128i, b: __m128i) -> __m128i {
    (simd_eq(BitVec::to_i8x16(a), BitVec::to_i8x16(b))).into()
}

/// Compares packed 16-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_epi16)

pub fn _mm_cmpeq_epi16(a: __m128i, b: __m128i) -> __m128i {
    (simd_eq(BitVec::to_i16x8(a), BitVec::to_i16x8(b))).into()
}

/// Compares packed 32-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpeq_epi32)

pub fn _mm_cmpeq_epi32(a: __m128i, b: __m128i) -> __m128i {
    (simd_eq(BitVec::to_i32x4(a), BitVec::to_i32x4(b))).into()
}

/// Compares packed 8-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_epi8)

pub fn _mm_cmpgt_epi8(a: __m128i, b: __m128i) -> __m128i {
    (simd_gt(BitVec::to_i8x16(a), BitVec::to_i8x16(b))).into()
}

/// Compares packed 16-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_epi16)

pub fn _mm_cmpgt_epi16(a: __m128i, b: __m128i) -> __m128i {
    (simd_gt(BitVec::to_i16x8(a), BitVec::to_i16x8(b))).into()
}

/// Compares packed 32-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmpgt_epi32)

pub fn _mm_cmpgt_epi32(a: __m128i, b: __m128i) -> __m128i {
    (simd_gt(BitVec::to_i32x4(a), BitVec::to_i32x4(b))).into()
}

/// Compares packed 8-bit integers in `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_epi8)

pub fn _mm_cmplt_epi8(a: __m128i, b: __m128i) -> __m128i {
    (simd_lt(BitVec::to_i8x16(a), BitVec::to_i8x16(b))).into()
}

/// Compares packed 16-bit integers in `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_epi16)

pub fn _mm_cmplt_epi16(a: __m128i, b: __m128i) -> __m128i {
    (simd_lt(BitVec::to_i16x8(a), BitVec::to_i16x8(b))).into()
}

/// Compares packed 32-bit integers in `a` and `b` for less-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cmplt_epi32)

pub fn _mm_cmplt_epi32(a: __m128i, b: __m128i) -> __m128i {
    (simd_lt(BitVec::to_i32x4(a), BitVec::to_i32x4(b))).into()
}

pub fn _mm_cvtsi32_si128(a: i32) -> __m128i {
    i32x4::from_fn(|i| if i == 0 { a } else { 0 }).into()
}

/// Returns the lowest element of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_cvtsi128_si32)

pub fn _mm_cvtsi128_si32(a: __m128i) -> i32 {
    simd_extract(BitVec::to_i32x4(a), 0)
}

/// Sets packed 64-bit integers with the supplied values, from highest to
/// lowest.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi64x)

// no particular instruction to test

pub fn _mm_set_epi64x(e1: i64, e0: i64) -> __m128i {
    i64x2::from_fn(|i| if i == 0 { e0 } else { e1 }).into()
}

/// Sets packed 32-bit integers with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi32)
// no particular instruction to test
pub fn _mm_set_epi32(e3: i32, e2: i32, e1: i32, e0: i32) -> __m128i {
    let vec = [e0, e1, e2, e3];
    BitVec::from_i32x4(i32x4::from_fn(|i| vec[i as usize]))
}

/// Sets packed 16-bit integers with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi16)

// no particular instruction to test

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
    let vec = [e0, e1, e2, e3, e4, e5, e6, e7];
    BitVec::from_i16x8(i16x8::from_fn(|i| vec[i as usize]))
}

/// Sets packed 8-bit integers with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi8)
// no particular instruction to test
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
    let vec = [
        e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    ];
    BitVec::from_i8x16(i8x16::from_fn(|i| vec[i as usize]))
}

/// Broadcasts 64-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi64x)

// no particular instruction to test

pub fn _mm_set1_epi64x(a: i64) -> __m128i {
    _mm_set_epi64x(a, a)
}

/// Broadcasts 32-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi32)

// no particular instruction to test

pub fn _mm_set1_epi32(a: i32) -> __m128i {
    _mm_set_epi32(a, a, a, a)
}

/// Broadcasts 16-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi16)

// no particular instruction to test

pub fn _mm_set1_epi16(a: i16) -> __m128i {
    BitVec::from_i16x8(i16x8::from_fn(|_| a))
}

/// Broadcasts 8-bit integer `a` to all elements.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi8)

// no particular instruction to test

pub fn _mm_set1_epi8(a: i8) -> __m128i {
    _mm_set_epi8(a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a)
}

/// Sets packed 32-bit integers with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setr_epi32)

// no particular instruction to test

pub fn _mm_setr_epi32(e3: i32, e2: i32, e1: i32, e0: i32) -> __m128i {
    _mm_set_epi32(e0, e1, e2, e3)
}

/// Sets packed 16-bit integers with the supplied values in reverse order.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setr_epi16)

// no particular instruction to test

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

// no particular instruction to test

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
    BitVec::from_fn(|_| Bit::Zero)
}

/// Returns a vector where the low element is extracted from `a` and its upper
/// element is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_move_epi64)

// FIXME movd on msvc, movd on i686

pub fn _mm_move_epi64(a: __m128i) -> __m128i {
    let r: i64x2 = simd_shuffle(BitVec::to_i64x2(a), i64x2::from_fn(|_| 0), [0, 2]);
    r.into()
}

/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using signed saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packs_epi16)

pub fn _mm_packs_epi16(a: __m128i, b: __m128i) -> __m128i {
    packsswb(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using signed saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packs_epi32)

pub fn _mm_packs_epi32(a: __m128i, b: __m128i) -> __m128i {
    packssdw(BitVec::to_i32x4(a), BitVec::to_i32x4(b)).into()
}

/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using unsigned saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packus_epi16)

pub fn _mm_packus_epi16(a: __m128i, b: __m128i) -> __m128i {
    packuswb(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Returns the `imm8` element of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_extract_epi16)

pub fn _mm_extract_epi16<const IMM8: i32>(a: __m128i) -> i32 {
    // static_assert_uimm_bits!(IMM8, 3);
    simd_extract(BitVec::to_u16x8(a), IMM8 as u64) as i32
}

/// Returns a new vector where the `imm8` element of `a` is replaced with `i`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_insert_epi16)

pub fn _mm_insert_epi16<const IMM8: i32>(a: __m128i, i: i32) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 3);
    simd_insert(BitVec::to_i16x8(a), IMM8 as u64, i as i16).into()
}

/// Returns a mask of the most significant bit of each element in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_movemask_epi8)

pub fn _mm_movemask_epi8(a: __m128i) -> i32 {
    let z = i8x16::from_fn(|_| 0);
    let m: i8x16 = simd_lt(BitVec::to_i8x16(a), z);
    let r = simd_bitmask_little!(15, m, u16);
    r as u32 as i32
}

/// Shuffles 32-bit integers in `a` using the control in `IMM8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shuffle_epi32)

pub fn _mm_shuffle_epi32<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    let a = BitVec::to_i32x4(a);
    let x: i32x4 = simd_shuffle(
        a,
        a,
        [
            IMM8 as u64 & 0b11,
            (IMM8 as u64 >> 2) & 0b11,
            (IMM8 as u64 >> 4) & 0b11,
            (IMM8 as u64 >> 6) & 0b11,
        ],
    );
    x.into()
}

/// Shuffles 16-bit integers in the high 64 bits of `a` using the control in
/// `IMM8`.
///
/// Put the results in the high 64 bits of the returned vector, with the low 64
/// bits being copied from `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shufflehi_epi16)

pub fn _mm_shufflehi_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    let a = BitVec::to_i16x8(a);
    let x: i16x8 = simd_shuffle(
        a,
        a,
        [
            0,
            1,
            2,
            3,
            (IMM8 as u64 & 0b11) + 4,
            ((IMM8 as u64 >> 2) & 0b11) + 4,
            ((IMM8 as u64 >> 4) & 0b11) + 4,
            ((IMM8 as u64 >> 6) & 0b11) + 4,
        ],
    );
    x.into()
}

/// Shuffles 16-bit integers in the low 64 bits of `a` using the control in
/// `IMM8`.
///
/// Put the results in the low 64 bits of the returned vector, with the high 64
/// bits being copied from `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shufflelo_epi16)

pub fn _mm_shufflelo_epi16<const IMM8: i32>(a: __m128i) -> __m128i {
    // static_assert_uimm_bits!(IMM8, 8);

    let a = BitVec::to_i16x8(a);
    let x: i16x8 = simd_shuffle(
        a,
        a,
        [
            IMM8 as u64 & 0b11,
            (IMM8 as u64 >> 2) & 0b11,
            (IMM8 as u64 >> 4) & 0b11,
            (IMM8 as u64 >> 6) & 0b11,
            4,
            5,
            6,
            7,
        ],
    );
    x.into()
}

/// Unpacks and interleave 8-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi8)

pub fn _mm_unpackhi_epi8(a: __m128i, b: __m128i) -> __m128i {
    (simd_shuffle(
        BitVec::to_i8x16(a),
        BitVec::to_i8x16(b),
        [8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31],
    ))
    .into()
}

/// Unpacks and interleave 16-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi16)

pub fn _mm_unpackhi_epi16(a: __m128i, b: __m128i) -> __m128i {
    let x = simd_shuffle(
        BitVec::to_i16x8(a),
        BitVec::to_i16x8(b),
        [4, 12, 5, 13, 6, 14, 7, 15],
    );
    (x).into()
}

/// Unpacks and interleave 32-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi32)

pub fn _mm_unpackhi_epi32(a: __m128i, b: __m128i) -> __m128i {
    (simd_shuffle(BitVec::to_i32x4(a), BitVec::to_i32x4(b), [2, 6, 3, 7])).into()
}

/// Unpacks and interleave 64-bit integers from the high half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi64)

pub fn _mm_unpackhi_epi64(a: __m128i, b: __m128i) -> __m128i {
    (simd_shuffle(BitVec::to_i64x2(a), BitVec::to_i64x2(b), [1, 3])).into()
}

/// Unpacks and interleave 8-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi8)

pub fn _mm_unpacklo_epi8(a: __m128i, b: __m128i) -> __m128i {
    (simd_shuffle(
        BitVec::to_i8x16(a),
        BitVec::to_i8x16(b),
        [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23],
    ))
    .into()
}

/// Unpacks and interleave 16-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi16)

pub fn _mm_unpacklo_epi16(a: __m128i, b: __m128i) -> __m128i {
    let x = simd_shuffle(
        BitVec::to_i16x8(a),
        BitVec::to_i16x8(b),
        [0, 8, 1, 9, 2, 10, 3, 11],
    );
    x.into()
}

/// Unpacks and interleave 32-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi32)

pub fn _mm_unpacklo_epi32(a: __m128i, b: __m128i) -> __m128i {
    simd_shuffle(BitVec::to_i32x4(a), BitVec::to_i32x4(b), [0, 4, 1, 5]).into()
}

/// Unpacks and interleave 64-bit integers from the low half of `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi64)

pub fn _mm_unpacklo_epi64(a: __m128i, b: __m128i) -> __m128i {
    simd_shuffle(BitVec::to_i64x2(a), BitVec::to_i64x2(b), [0, 2]).into()
}

/// Returns vector of type __m128i with indeterminate elements.with indetermination elements.
/// Despite using the word "undefined" (following Intel's naming scheme), this non-deterministically
/// picks some valid value and is not equivalent to [`core::mem::MaybeUninit`].
/// In practice, this is typically equivalent to [`core::mem::zeroed`].
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_undefined_si128)

pub fn _mm_undefined_si128() -> __m128i {
    BitVec::from_fn(|_| Bit::Zero)
}
