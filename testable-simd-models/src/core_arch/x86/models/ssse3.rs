//! Supplemental Streaming SIMD Extensions 3 (SSSE3)

use crate::abstractions::{bitvec::BitVec, simd::*};

use super::types::*;

mod c_extern {
    use crate::abstractions::simd::*;
    pub fn pshufb128(a: u8x16, b: u8x16) -> u8x16 {
        u8x16::from_fn(|i| if b[i] > 127 { 0 } else { a[(b[i] % 16) as u64] })
    }

    pub fn phaddw128(a: i16x8, b: i16x8) -> i16x8 {
        i16x8::from_fn(|i| {
            if i < 4 {
                a[2 * i].wrapping_add(a[2 * i + 1])
            } else {
                b[2 * (i - 4)].wrapping_add(b[2 * (i - 4) + 1])
            }
        })
    }

    pub fn phaddsw128(a: i16x8, b: i16x8) -> i16x8 {
        i16x8::from_fn(|i| {
            if i < 4 {
                a[2 * i].saturating_add(a[2 * i + 1])
            } else {
                b[2 * (i - 4)].saturating_add(b[2 * (i - 4) + 1])
            }
        })
    }

    pub fn phaddd128(a: i32x4, b: i32x4) -> i32x4 {
        i32x4::from_fn(|i| {
            if i < 2 {
                a[2 * i].wrapping_add(a[2 * i + 1])
            } else {
                b[2 * (i - 2)].wrapping_add(b[2 * (i - 2) + 1])
            }
        })
    }

    pub fn phsubw128(a: i16x8, b: i16x8) -> i16x8 {
        i16x8::from_fn(|i| {
            if i < 4 {
                a[2 * i].wrapping_sub(a[2 * i + 1])
            } else {
                b[2 * (i - 4)].wrapping_sub(b[2 * (i - 4) + 1])
            }
        })
    }

    pub fn phsubsw128(a: i16x8, b: i16x8) -> i16x8 {
        i16x8::from_fn(|i| {
            if i < 4 {
                a[2 * i].saturating_sub(a[2 * i + 1])
            } else {
                b[2 * (i - 4)].saturating_sub(b[2 * (i - 4) + 1])
            }
        })
    }

    pub fn phsubd128(a: i32x4, b: i32x4) -> i32x4 {
        i32x4::from_fn(|i| {
            if i < 2 {
                a[2 * i].wrapping_sub(a[2 * i + 1])
            } else {
                b[2 * (i - 2)].wrapping_sub(b[2 * (i - 2) + 1])
            }
        })
    }

    pub fn pmaddubsw128(a: u8x16, b: i8x16) -> i16x8 {
        i16x8::from_fn(|i| {
            ((a[2 * i] as u8 as u16 as i16) * (b[2 * i] as i8 as i16))
                .saturating_add((a[2 * i + 1] as u8 as u16 as i16) * (b[2 * i + 1] as i8 as i16))
        })
    }

    pub fn pmulhrsw128(a: i16x8, b: i16x8) -> i16x8 {
        i16x8::from_fn(|i| {
            let temp = (a[i] as i32) * (b[i] as i32);
            let temp = (temp >> 14).wrapping_add(1) >> 1;
            temp as i16
        })
    }

    pub fn psignb128(a: i8x16, b: i8x16) -> i8x16 {
        i8x16::from_fn(|i| {
            if b[i] < 0 {
                if a[i] == i8::MIN {
                    a[i]
                } else {
                    -a[i]
                }
            } else if b[i] > 0 {
                a[i]
            } else {
                0
            }
        })
    }

    pub fn psignw128(a: i16x8, b: i16x8) -> i16x8 {
        i16x8::from_fn(|i| {
            if b[i] < 0 {
                if a[i] == i16::MIN {
                    a[i]
                } else {
                    -a[i]
                }
            } else if b[i] > 0 {
                a[i]
            } else {
                0
            }
        })
    }

    pub fn psignd128(a: i32x4, b: i32x4) -> i32x4 {
        i32x4::from_fn(|i| {
            if b[i] < 0 {
                if a[i] == i32::MIN {
                    a[i]
                } else {
                    -a[i]
                }
            } else if b[i] > 0 {
                a[i]
            } else {
                0
            }
        })
    }
}

use super::sse2::*;
use c_extern::*;
/// Computes the absolute value of packed 8-bit signed integers in `a` and
/// return the unsigned results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi8)
pub fn _mm_abs_epi8(a: __m128i) -> __m128i {
    let a = BitVec::to_i8x16(a);
    let zero = i8x16::from_fn(|_| 0);
    let r = simd_select(simd_lt(a, zero), simd_neg(a), a);
    BitVec::from_i8x16(r)
}

/// Computes the absolute value of each of the packed 16-bit signed integers in
/// `a` and
/// return the 16-bit unsigned integer
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi16)
pub fn _mm_abs_epi16(a: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let zero = i16x8::from_fn(|_| 0);
    let r = simd_select(simd_lt(a, zero), simd_neg(a), a);
    BitVec::from_i16x8(r)
}

/// Computes the absolute value of each of the packed 32-bit signed integers in
/// `a` and
/// return the 32-bit unsigned integer
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi32)
pub fn _mm_abs_epi32(a: __m128i) -> __m128i {
    let a = BitVec::to_i32x4(a);
    let zero = i32x4::from_fn(|_| 0);
    let r = simd_select(simd_lt(a, zero), simd_neg(a), a);
    BitVec::from_i32x4(r)
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
    BitVec::from_u8x16(pshufb128(BitVec::to_u8x16(a), BitVec::to_u8x16(b)))
}

/// Concatenate 16-byte blocks in `a` and `b` into a 32-byte temporary result,
/// shift the result right by `n` bytes, and returns the low 16 bytes.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_alignr_epi8)

pub fn _mm_alignr_epi8<const IMM8: i32>(a: __m128i, b: __m128i) -> __m128i {
    // TODO static_assert_uimm_bits!(IMM8, 8);
    // If palignr is shifting the pair of vectors more than the size of two
    // lanes, emit zero.
    if IMM8 > 32 {
        return _mm_setzero_si128();
    }
    // If palignr is shifting the pair of input vectors more than one lane,
    // but less than two lanes, convert to shifting in zeroes.
    let (a, b) = if IMM8 > 16 {
        (_mm_setzero_si128(), a)
    } else {
        (a, b)
    };
    const fn mask(shift: u64, i: u64) -> u64 {
        if shift > 32 {
            // Unused, but needs to be a valid index.
            i
        } else if shift > 16 {
            shift - 16 + i
        } else {
            shift + i
        }
    }

    let r: i8x16 = simd_shuffle(
        BitVec::to_i8x16(b),
        BitVec::to_i8x16(a),
        [
            mask(IMM8 as u64, 0),
            mask(IMM8 as u64, 1),
            mask(IMM8 as u64, 2),
            mask(IMM8 as u64, 3),
            mask(IMM8 as u64, 4),
            mask(IMM8 as u64, 5),
            mask(IMM8 as u64, 6),
            mask(IMM8 as u64, 7),
            mask(IMM8 as u64, 8),
            mask(IMM8 as u64, 9),
            mask(IMM8 as u64, 10),
            mask(IMM8 as u64, 11),
            mask(IMM8 as u64, 12),
            mask(IMM8 as u64, 13),
            mask(IMM8 as u64, 14),
            mask(IMM8 as u64, 15),
        ],
    );
    r.into()
}

/// Horizontally adds the adjacent pairs of values contained in 2 packed
/// 128-bit vectors of `[8 x i16]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hadd_epi16)

pub fn _mm_hadd_epi16(a: __m128i, b: __m128i) -> __m128i {
    phaddw128(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Horizontally adds the adjacent pairs of values contained in 2 packed
/// 128-bit vectors of `[8 x i16]`. Positive sums greater than 7FFFh are
/// saturated to 7FFFh. Negative sums less than 8000h are saturated to 8000h.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hadds_epi16)

pub fn _mm_hadds_epi16(a: __m128i, b: __m128i) -> __m128i {
    phaddsw128(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Horizontally adds the adjacent pairs of values contained in 2 packed
/// 128-bit vectors of `[4 x i32]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hadd_epi32)

pub fn _mm_hadd_epi32(a: __m128i, b: __m128i) -> __m128i {
    phaddd128(BitVec::to_i32x4(a), BitVec::to_i32x4(b)).into()
}

/// Horizontally subtract the adjacent pairs of values contained in 2
/// packed 128-bit vectors of `[8 x i16]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hsub_epi16)

pub fn _mm_hsub_epi16(a: __m128i, b: __m128i) -> __m128i {
    phsubw128(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Horizontally subtract the adjacent pairs of values contained in 2
/// packed 128-bit vectors of `[8 x i16]`. Positive differences greater than
/// 7FFFh are saturated to 7FFFh. Negative differences less than 8000h are
/// saturated to 8000h.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hsubs_epi16)

pub fn _mm_hsubs_epi16(a: __m128i, b: __m128i) -> __m128i {
    phsubsw128(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Horizontally subtract the adjacent pairs of values contained in 2
/// packed 128-bit vectors of `[4 x i32]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_hsub_epi32)

pub fn _mm_hsub_epi32(a: __m128i, b: __m128i) -> __m128i {
    phsubd128(BitVec::to_i32x4(a), BitVec::to_i32x4(b)).into()
}

/// Multiplies corresponding pairs of packed 8-bit unsigned integer
/// values contained in the first source operand and packed 8-bit signed
/// integer values contained in the second source operand, add pairs of
/// contiguous products with signed saturation, and writes the 16-bit sums to
/// the corresponding bits in the destination.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_maddubs_epi16)

pub fn _mm_maddubs_epi16(a: __m128i, b: __m128i) -> __m128i {
    pmaddubsw128(BitVec::to_u8x16(a), BitVec::to_i8x16(b)).into()
}

/// Multiplies packed 16-bit signed integer values, truncate the 32-bit
/// product to the 18 most significant bits by right-shifting, round the
/// truncated value by adding 1, and write bits `[16:1]` to the destination.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhrs_epi16)

pub fn _mm_mulhrs_epi16(a: __m128i, b: __m128i) -> __m128i {
    pmulhrsw128(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Negates packed 8-bit integers in `a` when the corresponding signed 8-bit
/// integer in `b` is negative, and returns the result.
/// Elements in result are zeroed out when the corresponding element in `b`
/// is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sign_epi8)

pub fn _mm_sign_epi8(a: __m128i, b: __m128i) -> __m128i {
    psignb128(BitVec::to_i8x16(a), BitVec::to_i8x16(b)).into()
}

/// Negates packed 16-bit integers in `a` when the corresponding signed 16-bit
/// integer in `b` is negative, and returns the results.
/// Elements in result are zeroed out when the corresponding element in `b`
/// is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sign_epi16)

pub fn _mm_sign_epi16(a: __m128i, b: __m128i) -> __m128i {
    psignw128(BitVec::to_i16x8(a), BitVec::to_i16x8(b)).into()
}

/// Negates packed 32-bit integers in `a` when the corresponding signed 32-bit
/// integer in `b` is negative, and returns the results.
/// Element in result are zeroed out when the corresponding element in `b`
/// is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sign_epi32)

pub fn _mm_sign_epi32(a: __m128i, b: __m128i) -> __m128i {
    psignd128(BitVec::to_i32x4(a), BitVec::to_i32x4(b)).into()
}
