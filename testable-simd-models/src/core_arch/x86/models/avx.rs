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

use super::types::*;
use crate::abstractions::{bit::Bit, bitvec::BitVec, simd::*};

mod c_extern {
    use crate::abstractions::simd::*;

    pub fn vperm2f128si256(a: i32x8, b: i32x8, imm8: i8) -> i32x8 {
        let temp = i128x2::from_fn(|i| match (imm8 as u8) >> (i * 4) {
            0 => (a[4 * i] as i128) + 16 * (a[4 * i + 1] as i128),
            1 => (a[4 * i + 2] as i128) + 16 * (a[4 * i + 3] as i128),
            2 => (b[4 * i] as i128) + 16 * (b[4 * i + 1] as i128),
            3 => (b[4 * i + 2] as i128) + 16 * (b[4 * i + 3] as i128),
            _ => unreachable!(),
        });

        i32x8::from_fn(|i| (temp[if i < 4 { 0 } else { 1 }] >> (i % 4)) as i32)
    }
}

use c_extern::*;
/// Blends packed single-precision (32-bit) floating-point elements from
/// `a` and `b` using `c` as a mask.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_ps)
pub fn _mm256_blendv_ps(a: __m256, b: __m256, c: __m256) -> __m256 {
    let mask: i32x8 = simd_lt(BitVec::to_i32x8(c), i32x8::from_fn(|_| 0));
    BitVec::from_i32x8(simd_select(mask, BitVec::to_i32x8(b), BitVec::to_i32x8(a)))
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

pub fn _mm256_permute2f128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    // // static_assert_uimm_bits!(IMM8, 8);
    vperm2f128si256(BitVec::to_i32x8(a), BitVec::to_i32x8(b), IMM8 as i8).into()
}

/// Copies `a` to result, then inserts 128 bits from `b` into result
/// at the location specified by `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_insertf128_si256)

pub fn _mm256_insertf128_si256<const IMM1: i32>(a: __m256i, b: __m128i) -> __m256i {
    // // static_assert_uimm_bits!(IMM1, 1);

    let dst: i64x4 = simd_shuffle(
        BitVec::to_i64x4(a),
        BitVec::to_i64x4(_mm256_castsi128_si256(b)),
        [[4, 5, 2, 3], [0, 1, 4, 5]][IMM1 as usize],
    );
    dst.into()
}

/// Copies `a` to result, and inserts the 8-bit integer `i` into result
/// at the location specified by `index`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_insert_epi8)

// This intrinsic has no corresponding instruction.

pub fn _mm256_insert_epi8<const INDEX: i32>(a: __m256i, i: i8) -> __m256i {
    // // static_assert_uimm_bits!(INDEX, 5);
    simd_insert(BitVec::to_i8x32(a), INDEX as u64, i).into()
}

/// Copies `a` to result, and inserts the 16-bit integer `i` into result
/// at the location specified by `index`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_insert_epi16)

// This intrinsic has no corresponding instruction.

pub fn _mm256_insert_epi16<const INDEX: i32>(a: __m256i, i: i16) -> __m256i {
    // // static_assert_uimm_bits!(INDEX, 4);
    simd_insert(BitVec::to_i16x16(a), INDEX as u64, i).into()
}

/// Computes the bitwise AND of 256 bits (representing integer data) in `a` and
/// `b`, and set `ZF` to 1 if the result is zero, otherwise set `ZF` to 0.
/// Computes the bitwise NOT of `a` and then AND with `b`, and set `CF` to 1 if
/// the result is zero, otherwise set `CF` to 0. Return the `ZF` value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_testz_si256)
pub fn _mm256_testz_si256(a: __m256i, b: __m256i) -> i32 {
    let c = BitVec::<256>::from_fn(|i| match (a[i], b[i]) {
        (Bit::One, Bit::One) => Bit::One,
        _ => Bit::Zero,
    });
    let all_zero = c.fold(true, |acc, bit| acc && bit == Bit::Zero);
    if all_zero {
        1
    } else {
        0
    }
}

/// Sets each bit of the returned mask based on the most significant bit of the
/// corresponding packed single-precision (32-bit) floating-point element in
/// `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_ps)
pub fn _mm256_movemask_ps(a: __m256) -> i32 {
    // Propagate the highest bit to the rest, because simd_bitmask
    // requires all-1 or all-0.
    let mask: i32x8 = simd_lt(BitVec::to_i32x8(a), i32x8::from_fn(|_| 0));
    let r = simd_bitmask_little!(7, mask, u8);
    r as u32 as i32
}

/// Returns vector of type __m256 with all elements set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_setzero_ps)

pub fn _mm256_setzero_ps() -> __m256 {
    BitVec::from_fn(|_| Bit::Zero)
}

/// Returns vector of type __m256i with all elements set to zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_setzero_si256)

pub fn _mm256_setzero_si256() -> __m256i {
    BitVec::from_fn(|_| Bit::Zero)
}

/// Sets packed 8-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi8)

// This intrinsic has no corresponding instruction.

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
    let vec = [
        e00, e01, e02, e03, e04, e05, e06, e07, e08, e09, e10, e11, e12, e13, e14, e15, e16, e17,
        e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31,
    ];
    BitVec::from_i8x32(i8x32::from_fn(|i| vec[(31 - i) as usize]))
}

/// Sets packed 16-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi16)

// This intrinsic has no corresponding instruction.

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
    let vec = [
        e00, e01, e02, e03, e04, e05, e06, e07, e08, e09, e10, e11, e12, e13, e14, e15,
    ];
    BitVec::from_i16x16(i16x16::from_fn(|i| vec[(15 - i) as usize]))
}

/// Sets packed 32-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi32)

// This intrinsic has no corresponding instruction.

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
    let vec = [e0, e1, e2, e3, e4, e5, e6, e7];
    BitVec::from_i32x8(i32x8::from_fn(|i| vec[(7 - i) as usize]))
}

/// Sets packed 64-bit integers in returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi64x)
// This intrinsic has no corresponding instruction.
pub fn _mm256_set_epi64x(a: i64, b: i64, c: i64, d: i64) -> __m256i {
    let vec = [d, c, b, a];
    BitVec::from_i64x4(i64x4::from_fn(|i| vec[i as usize]))
}

/// Broadcasts 8-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastw`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi16)

//

// This intrinsic has no corresponding instruction.

pub fn _mm256_set1_epi8(val: i8) -> BitVec<256> {
    BitVec::from_i8x32(i8x32::from_fn(|_| val))
}

/// Broadcasts 16-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastw`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi16)

//

// This intrinsic has no corresponding instruction.

pub fn _mm256_set1_epi16(a: i16) -> __m256i {
    BitVec::from_i16x16(i16x16::from_fn(|_| a))
}

/// Broadcasts 32-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastd`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi32)

// This intrinsic has no corresponding instruction.

pub fn _mm256_set1_epi32(a: i32) -> __m256i {
    BitVec::from_i32x8(i32x8::from_fn(|_| a))
}

/// Broadcasts 64-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastq`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi64x)
// This intrinsic has no corresponding instruction.
pub fn _mm256_set1_epi64x(a: i64) -> __m256i {
    BitVec::from_i64x4(i64x4::from_fn(|_| a))
}

pub fn _mm256_castps_si256(a: __m256) -> __m256i {
    a
}

/// Casts vector of type __m256i to type __m256.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi256_ps)
// This intrinsic is only used for compilation and does not generate any
// instructions, thus it has zero latency.
pub fn _mm256_castsi256_ps(a: __m256i) -> __m256 {
    a
}

/// Casts vector of type __m256i to type __m128i.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi256_si128)

// This intrinsic is only used for compilation and does not generate any
// instructions, thus it has zero latency.

pub fn _mm256_castsi256_si128(a: __m256i) -> __m128i {
    BitVec::from_fn(|i| a[i])
}

/// Casts vector of type __m128i to type __m256i;
/// the upper 128 bits of the result are undefined.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi128_si256)

// This intrinsic is only used for compilation and does not generate any
// instructions, thus it has zero latency.

pub fn _mm256_castsi128_si256(a: __m128i) -> __m256i {
    let a = BitVec::to_i64x2(a);
    let undefined = i64x2::from_fn(|_| 0);
    let dst: i64x4 = simd_shuffle(a, undefined, [0, 1, 2, 2]);
    BitVec::from_i64x4(dst)
}

/// Sets packed __m256i returned vector with the supplied values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_m128i)

pub fn _mm256_set_m128i(hi: __m128i, lo: __m128i) -> __m256i {
    BitVec::from_fn(|i| if i < 128 { lo[i] } else { hi[i - 128] })
}
