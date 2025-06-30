use super::types::*;

use crate::abstractions::bitvec::{int_vec_interp::*, BitVec};

pub fn _mm_set1_epi16(a: i16) -> __m128i {
    i16x8::from_fn(|_| a).into()
}

pub fn _mm_set_epi32(e3: i32, e2: i32, e1: i32, e0: i32) -> __m128i {
    i32x4::from_fn(|i| match i {
        0 => e0,
        1 => e1,
        2 => e2,
        3 => e3,
        _ => unreachable!(),
    })
    .into()
}

pub fn _mm_add_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let b = BitVec::to_i16x8(b);
    i16x8::from_fn(|i| a[i].wrapping_add(b[i])).into()
}

pub fn _mm_sub_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let b = BitVec::to_i16x8(b);

    i16x8::from_fn(|i| a[i].wrapping_sub(b[i])).into()
}

pub fn _mm_mullo_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let b = BitVec::to_i16x8(b);
    i16x8::from_fn(|i| (a[i].overflowing_mul(b[i]).0)).into()
}

pub fn _mm_mulhi_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let b = BitVec::to_i16x8(b);
    i16x8::from_fn(|i| (((a[i] as i32) * (b[i] as i32) >> 16) as i16)).into()
}

pub fn _mm_srli_epi64<const IMM8: i32>(a: __m128i) -> __m128i {
    let a = BitVec::to_i64x2(a);
    i64x2::from_fn(|i| {
        let imm8 = IMM8.rem_euclid(256);
        if imm8 > 63 {
            0
        } else {
            ((a[i] as u64) >> imm8) as i64
        }
    })
    .into()
}

pub fn _mm_packs_epi16(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i16x8(a);
    let b = BitVec::to_i16x8(b);
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
    .into()
}

pub fn _mm_movemask_epi8(a: __m128i) -> i32 {
    let a = BitVec::to_i8x16(a);

    let a0 = if a[0] < 0 { 1 } else { 0 };
    let a1 = if a[1] < 0 { 2 } else { 0 };
    let a2 = if a[2] < 0 { 4 } else { 0 };
    let a3 = if a[3] < 0 { 8 } else { 0 };
    let a4 = if a[4] < 0 { 16 } else { 0 };
    let a5 = if a[5] < 0 { 32 } else { 0 };
    let a6 = if a[6] < 0 { 64 } else { 0 };
    let a7 = if a[7] < 0 { 128 } else { 0 };
    let a8 = if a[8] < 0 { 256 } else { 0 };
    let a9 = if a[9] < 0 { 512 } else { 0 };
    let a10 = if a[10] < 0 { 1024 } else { 0 };
    let a11 = if a[11] < 0 { 2048 } else { 0 };
    let a12 = if a[12] < 0 { 4096 } else { 0 };
    let a13 = if a[13] < 0 { 8192 } else { 0 };
    let a14 = if a[14] < 0 { 16384 } else { 0 };
    let a15 = if a[15] < 0 { 32768 } else { 0 };

    a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15
}
