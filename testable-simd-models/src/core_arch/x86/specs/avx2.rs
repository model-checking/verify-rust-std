use super::types::*;

use crate::abstractions::{
    bit::Bit,
    bitvec::{int_vec_interp::*, BitVec},
};

pub fn _mm256_mul_epi32(x: __m256i, y: __m256i) -> __m256i {
    let x = BitVec::to_i32x8(x);
    let y = BitVec::to_i32x8(y);
    i64x4::from_fn(|i| (x[i * 2] as i64) * (y[i * 2] as i64)).into()
}

pub fn _mm256_bsrli_epi128<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i128x2(a);
    let a = i128x2::from_fn(|i| {
        let tmp = IMM8 % 256;
        let tmp = tmp % 16;
        ((a[i] as u128) >> (tmp * 8)) as i128
    });
    BitVec::from_i128x2(a)
}

pub fn _mm256_sub_epi32(x: __m256i, y: __m256i) -> __m256i {
    let x = BitVec::to_i32x8(x);
    let y = BitVec::to_i32x8(y);
    i32x8::from_fn(|i| x[i].wrapping_sub(y[i])).into()
}

pub fn _mm256_shuffle_epi32<const CONTROL: i32>(x: __m256i) -> __m256i {
    let x = BitVec::to_i32x8(x);
    let indexes = u64x4::from_fn(|i| ((CONTROL >> i * 2) % 4) as u64);
    i32x8::from_fn(|i| {
        if i < 4 {
            x[indexes[i]]
        } else {
            x[4 + indexes[i - 4]]
        }
    })
    .into()
}

pub fn _mm256_blend_epi32<const CONTROL: i32>(x: __m256i, y: __m256i) -> __m256i {
    let x = BitVec::to_i32x8(x);
    let y = BitVec::to_i32x8(y);
    i32x8::from_fn(|i| if (CONTROL >> i) % 2 == 0 { x[i] } else { y[i] }).into()
}

pub fn _mm256_add_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);

    i32x8::from_fn(|i| a[i].wrapping_add(b[i])).into()
}

pub fn _mm256_add_epi64(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i64x4(a);
    let b = BitVec::to_i64x4(b);

    i64x4::from_fn(|i| a[i].wrapping_add(b[i])).into()
}

pub fn _mm256_abs_epi32(a: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    i32x8::from_fn(|i| if a[i] == i32::MIN { a[i] } else { a[i].abs() }).into()
}

pub fn _mm256_sub_epi16(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let b = BitVec::to_i16x16(b);

    i16x16::from_fn(|i| a[i].wrapping_sub(b[i])).into()
}

pub fn _mm256_cmpgt_epi16(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let b = BitVec::to_i16x16(b);

    i16x16::from_fn(|i| if a[i] > b[i] { -1 } else { 0 }).into()
}

pub fn _mm256_cmpgt_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);

    i32x8::from_fn(|i| if a[i] > b[i] { -1 } else { 0 }).into()
}

pub fn _mm256_sign_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);

    i32x8::from_fn(|i| {
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
    .into()
}

pub fn _mm256_mullo_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);

    i32x8::from_fn(|i| (a[i].overflowing_mul(b[i]).0)).into()
}

pub fn _mm256_mul_epu32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u32x8(a);
    let b = BitVec::to_u32x8(b);
    u64x4::from_fn(|i| (a[i * 2] as u64) * (b[i * 2] as u64)).into()
}

pub fn _mm256_and_si256(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_fn(|i| match (a[i], b[i]) {
        (Bit::One, Bit::One) => Bit::One,
        _ => Bit::Zero,
    })
}

pub fn _mm256_or_si256(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_fn(|i| match (a[i], b[i]) {
        (Bit::Zero, Bit::Zero) => Bit::Zero,
        _ => Bit::One,
    })
}

pub fn _mm256_xor_si256(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_fn(|i| match (a[i], b[i]) {
        (Bit::Zero, Bit::Zero) => Bit::Zero,
        (Bit::One, Bit::One) => Bit::Zero,
        _ => Bit::One,
    })
}

pub fn _mm256_srai_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    i16x16::from_fn(|i| {
        let imm8 = IMM8.rem_euclid(256);
        if imm8 > 15 {
            if a[i] < 0 {
                -1
            } else {
                0
            }
        } else {
            a[i] >> imm8
        }
    })
    .into()
}

pub fn _mm256_srai_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    i32x8::from_fn(|i| {
        let imm8 = IMM8.rem_euclid(256);
        if imm8 > 31 {
            if a[i] < 0 {
                -1
            } else {
                0
            }
        } else {
            a[i] >> imm8
        }
    })
    .into()
}

pub fn _mm256_srli_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    i16x16::from_fn(|i| {
        let imm8 = IMM8.rem_euclid(256);
        if imm8 > 15 {
            0
        } else {
            ((a[i] as u16) >> imm8) as i16
        }
    })
    .into()
}

pub fn _mm256_srli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    i32x8::from_fn(|i| {
        let imm8 = IMM8.rem_euclid(256);
        if imm8 > 31 {
            0
        } else {
            ((a[i] as u32) >> imm8) as i32
        }
    })
    .into()
}

pub fn _mm256_slli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    i32x8::from_fn(|i| {
        let imm8 = IMM8.rem_euclid(256);
        if imm8 > 31 {
            0
        } else {
            ((a[i] as u32) << imm8) as i32
        }
    })
    .into()
}

pub fn _mm256_permute4x64_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i64x4(a);
    let indexes = u64x4::from_fn(|i| ((IMM8 >> i * 2) % 4) as u64);
    i64x4::from_fn(|i| a[indexes[i]]).into()
}

pub fn _mm256_unpackhi_epi64(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i64x4(a);
    let b = BitVec::to_i64x4(b);
    i64x4::from_fn(|i| match i {
        0 => a[1],
        1 => b[1],
        2 => a[3],
        3 => b[3],
        _ => unreachable!(),
    })
    .into()
}

pub fn _mm256_unpacklo_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);
    i32x8::from_fn(|i| match i {
        0 => a[0],
        1 => b[0],
        2 => a[1],
        3 => b[1],
        4 => a[4],
        5 => b[4],
        6 => a[5],
        7 => b[5],
        _ => unreachable!(),
    })
    .into()
}

pub fn _mm256_unpackhi_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);
    i32x8::from_fn(|i| match i {
        0 => a[2],
        1 => b[2],
        2 => a[3],
        3 => b[3],
        4 => a[6],
        5 => b[6],
        6 => a[7],
        7 => b[7],
        _ => unreachable!(),
    })
    .into()
}

pub fn _mm256_cvtepi16_epi32(a: __m128i) -> __m256i {
    let a = BitVec::to_i16x8(a);
    i32x8::from_fn(|i| a[i] as i32).into()
}

pub fn _mm256_packs_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);
    i16x16::from_fn(|i| {
        if i < 4 {
            if a[i] > (i16::MAX as i32) {
                i16::MAX
            } else if a[i] < (i16::MIN as i32) {
                i16::MIN
            } else {
                a[i] as i16
            }
        } else if i < 8 {
            if b[i - 4] > (i16::MAX as i32) {
                i16::MAX
            } else if b[i - 4] < (i16::MIN as i32) {
                i16::MIN
            } else {
                b[i - 4] as i16
            }
        } else if i < 12 {
            if a[i - 4] > (i16::MAX as i32) {
                i16::MAX
            } else if a[i - 4] < (i16::MIN as i32) {
                i16::MIN
            } else {
                a[i - 4] as i16
            }
        } else {
            if b[i - 8] > (i16::MAX as i32) {
                i16::MAX
            } else if b[i - 8] < (i16::MIN as i32) {
                i16::MIN
            } else {
                b[i - 8] as i16
            }
        }
    })
    .into()
}

pub fn _mm256_blend_epi16<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let b = BitVec::to_i16x16(b);
    i16x16::from_fn(|i| {
        if (IMM8 >> (i % 8)) % 2 == 0 {
            a[i]
        } else {
            b[i]
        }
    })
    .into()
}

pub fn _mm256_inserti128_si256<const IMM1: i32>(a: __m256i, b: __m128i) -> __m256i {
    let a = BitVec::to_i128x2(a);
    let b = BitVec::to_i128x1(b);
    i128x2::from_fn(|i| {
        if IMM1 % 2 == 0 {
            match i {
                0 => b[0],
                1 => a[1],
                _ => unreachable!(),
            }
        } else {
            match i {
                0 => a[0],
                1 => b[0],
                _ => unreachable!(),
            }
        }
    })
    .into()
}

pub fn _mm256_srlv_epi64(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i64x4(a);
    let b = BitVec::to_i64x4(b);
    i64x4::from_fn(|i| {
        if b[i] > 63 || b[i] < 0 {
            0
        } else {
            ((a[i] as u64) >> b[i]) as i64
        }
    })
    .into()
}

pub fn _mm_sllv_epi32(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i32x4(a);
    let b = BitVec::to_i32x4(b);
    i32x4::from_fn(|i| {
        if b[i] > 31 || b[i] < 0 {
            0
        } else {
            ((a[i] as u32) << b[i]) as i32
        }
    })
    .into()
}

pub fn _mm256_slli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i64x4(a);
    i64x4::from_fn(|i| {
        let imm8 = IMM8 % 256;
        if imm8 > 63 {
            0
        } else {
            ((a[i] as u64) << imm8) as i64
        }
    })
    .into()
}

pub fn _mm256_andnot_si256(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_fn(|i| match (a[i], b[i]) {
        (Bit::Zero, Bit::One) => Bit::One,
        _ => Bit::Zero,
    })
}

pub fn _mm256_unpacklo_epi64(a: i64x4, b: i64x4) -> i64x4 {
    i64x4::from_fn(|i| match i {
        0 => a[0],
        1 => b[0],
        2 => a[2],
        3 => b[2],
        _ => unreachable!(),
    })
}

pub fn _mm256_permute2x128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i128x2(a);
    let b = BitVec::to_i128x2(b);
    i128x2::from_fn(|i| {
        let control = IMM8 >> (i * 4);
        if (control >> 3) % 2 == 1 {
            0
        } else {
            match control % 4 {
                0 => a[0],
                1 => a[1],
                2 => b[0],
                3 => b[1],
                _ => unreachable!(),
            }
        }
    })
    .into()
}
