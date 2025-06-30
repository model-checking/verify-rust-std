use super::types::*;

use crate::abstractions::{
    bit::Bit,
    bitvec::{int_vec_interp::*, BitVec},
};

pub fn _mm256_set1_epi32(x: i32) -> __m256i {
    i32x8::from_fn(|_| x).into()
}

pub fn _mm256_setzero_si256() -> __m256i {
    BitVec::from_fn(|_| Bit::Zero)
}

pub fn _mm256_set_m128i(hi: __m128i, lo: __m128i) -> __m256i {
    BitVec::from_fn(|i| if i < 128 { lo[i] } else { hi[i - 128] })
}

pub fn _mm256_set1_epi16(a: i16) -> __m256i {
    i16x16::from_fn(|_| a).into()
}

pub fn _mm256_castsi256_ps(a: __m256i) -> __m256 {
    a
}

pub fn _mm256_castps_si256(a: __m256) -> __m256i {
    a
}

pub fn _mm256_movemask_ps(a: __m256) -> i32 {
    let a = BitVec::to_i32x8(a);
    let a0: i32 = if a[0] < 0 { 1 } else { 0 };
    let a1 = if a[1] < 0 { 2 } else { 0 };
    let a2 = if a[2] < 0 { 4 } else { 0 };
    let a3 = if a[3] < 0 { 8 } else { 0 };
    let a4 = if a[4] < 0 { 16 } else { 0 };
    let a5 = if a[5] < 0 { 32 } else { 0 };
    let a6 = if a[6] < 0 { 64 } else { 0 };
    let a7 = if a[7] < 0 { 128 } else { 0 };
    a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7
}

pub fn _mm256_testz_si256(a: BitVec<256>, b: BitVec<256>) -> i32 {
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

pub fn _mm256_castsi128_si256(a: __m128i) -> __m256i {
    BitVec::from_fn(|i| if i < 128 { a[i] } else { Bit::Zero })
}

pub fn _mm256_blendv_ps(a: __m256, b: __m256, mask: __m256) -> __m256 {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);
    let mask = BitVec::to_i32x8(mask);
    i32x8::from_fn(|i| if mask[i] < 0 { b[i] } else { a[i] }).into()
}

pub fn _mm256_set1_epi64x(a: i64) -> __m256i {
    i64x4::from_fn(|_| a).into()
}

pub fn _mm256_set_epi64x(e3: i64, e2: i64, e1: i64, e0: i64) -> __m256i {
    i64x4::from_fn(|i| match i {
        0 => e0,
        1 => e1,
        2 => e2,
        3 => e3,
        _ => unreachable!(),
    })
    .into()
}
