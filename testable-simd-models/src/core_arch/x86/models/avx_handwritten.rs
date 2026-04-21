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

pub fn ptestz256(a: i64x4, b: i64x4) -> i32 {
    let c = i64x4::from_fn(|i| a[i] & b[i]);
    if c == i64x4::ZERO() {
        1
    } else {
        0
    }
}

pub fn ptestc256(a: i64x4, b: i64x4) -> i32 {
    let c = i64x4::from_fn(|i| !a[i] & b[i]);
    if c == i64x4::ZERO() {
        1
    } else {
        0
    }
}
