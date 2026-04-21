use super::types::*;
use crate::abstractions::simd::*;

pub fn vaba_s16(a: int16x4_t, b: int16x4_t, c: int16x4_t) -> int16x4_t {
    simd_add(a, vabd_s16(b, c))
}

pub fn vaba_s32(a: int32x2_t, b: int32x2_t, c: int32x2_t) -> int32x2_t {
    simd_add(a, vabd_s32(b, c))
}

pub fn vaba_s8(a: int8x8_t, b: int8x8_t, c: int8x8_t) -> int8x8_t {
    simd_add(a, vabd_s8(b, c))
}

pub fn vaba_u16(a: uint16x4_t, b: uint16x4_t, c: uint16x4_t) -> uint16x4_t {
    simd_add(a, vabd_u16(b, c))
}

pub fn vaba_u32(a: uint32x2_t, b: uint32x2_t, c: uint32x2_t) -> uint32x2_t {
    simd_add(a, vabd_u32(b, c))
}

pub fn vaba_u8(a: uint8x8_t, b: uint8x8_t, c: uint8x8_t) -> uint8x8_t {
    simd_add(a, vabd_u8(b, c))
}

pub fn vabal_u8(a: uint16x8_t, b: uint8x8_t, c: uint8x8_t) -> uint16x8_t {
    let d: uint8x8_t = vabd_u8(b, c);
    simd_add(a, simd_cast(d))
}

pub fn vabal_u16(a: uint32x4_t, b: uint16x4_t, c: uint16x4_t) -> uint32x4_t {
    let d: uint16x4_t = vabd_u16(b, c);
    simd_add(a, simd_cast(d))
}

pub fn vabal_u32(a: uint64x2_t, b: uint32x2_t, c: uint32x2_t) -> uint64x2_t {
    let d: uint32x2_t = vabd_u32(b, c);
    simd_add(a, simd_cast(d))
}

pub fn vabaq_s16(a: int16x8_t, b: int16x8_t, c: int16x8_t) -> int16x8_t {
    simd_add(a, vabdq_s16(b, c))
}

pub fn vabaq_s32(a: int32x4_t, b: int32x4_t, c: int32x4_t) -> int32x4_t {
    simd_add(a, vabdq_s32(b, c))
}

pub fn vabaq_s8(a: int8x16_t, b: int8x16_t, c: int8x16_t) -> int8x16_t {
    simd_add(a, vabdq_s8(b, c))
}

pub fn vabaq_u16(a: uint16x8_t, b: uint16x8_t, c: uint16x8_t) -> uint16x8_t {
    simd_add(a, vabdq_u16(b, c))
}

pub fn vabaq_u32(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t) -> uint32x4_t {
    simd_add(a, vabdq_u32(b, c))
}

pub fn vabaq_u8(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> uint8x16_t {
    simd_add(a, vabdq_u8(b, c))
}

pub fn vabd_s8(a: int8x8_t, b: int8x8_t) -> int8x8_t {
    simd_abs_diff(a, b)
}

pub fn vabdq_s8(a: int8x16_t, b: int8x16_t) -> int8x16_t {
    simd_abs_diff(a, b)
}

pub fn vabd_s16(a: int16x4_t, b: int16x4_t) -> int16x4_t {
    simd_abs_diff(a, b)
}

pub fn vabdq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    simd_abs_diff(a, b)
}

pub fn vabd_s32(a: int32x2_t, b: int32x2_t) -> int32x2_t {
    simd_abs_diff(a, b)
}

pub fn vabdq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    simd_abs_diff(a, b)
}

pub fn vabd_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    simd_abs_diff(a, b)
}

pub fn vabdq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    simd_abs_diff(a, b)
}

pub fn vabd_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    simd_abs_diff(a, b)
}

pub fn vabdq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    simd_abs_diff(a, b)
}

pub fn vabd_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    simd_abs_diff(a, b)
}

pub fn vabdq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    simd_abs_diff(a, b)
}

pub fn vabdl_u8(a: uint8x8_t, b: uint8x8_t) -> uint16x8_t {
    simd_cast(vabd_u8(a, b))
}

pub fn vabdl_u16(a: uint16x4_t, b: uint16x4_t) -> uint32x4_t {
    simd_cast(vabd_u16(a, b))
}

pub fn vabdl_u32(a: uint32x2_t, b: uint32x2_t) -> uint64x2_t {
    simd_cast(vabd_u32(a, b))
}

pub fn vabs_s8(a: int8x8_t) -> int8x8_t {
    simd_abs(a)
}

pub fn vabsq_s8(a: int8x16_t) -> int8x16_t {
    simd_abs(a)
}

pub fn vabs_s16(a: int16x4_t) -> int16x4_t {
    simd_abs(a)
}

pub fn vabsq_s16(a: int16x8_t) -> int16x8_t {
    simd_abs(a)
}

pub fn vabs_s32(a: int32x2_t) -> int32x2_t {
    simd_abs(a)
}

pub fn vabsq_s32(a: int32x4_t) -> int32x4_t {
    simd_abs(a)
}

pub fn vadd_s16(a: int16x4_t, b: int16x4_t) -> int16x4_t {
    simd_add(a, b)
}

pub fn vadd_s32(a: int32x2_t, b: int32x2_t) -> int32x2_t {
    simd_add(a, b)
}

pub fn vadd_s8(a: int8x8_t, b: int8x8_t) -> int8x8_t {
    simd_add(a, b)
}

pub fn vadd_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    simd_add(a, b)
}

pub fn vadd_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    simd_add(a, b)
}

pub fn vadd_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    simd_add(a, b)
}

pub fn vaddq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    simd_add(a, b)
}

pub fn vaddq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    simd_add(a, b)
}

pub fn vaddq_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    simd_add(a, b)
}

pub fn vaddq_s8(a: int8x16_t, b: int8x16_t) -> int8x16_t {
    simd_add(a, b)
}

pub fn vaddq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    simd_add(a, b)
}

pub fn vaddq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    simd_add(a, b)
}

pub fn vaddq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    simd_add(a, b)
}

pub fn vaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    simd_add(a, b)
}

pub fn vaddhn_high_s16(r: int8x8_t, a: int16x8_t, b: int16x8_t) -> int8x16_t {
    let x = simd_cast(simd_shr(simd_add(a, b), int16x8_t::splat(8)));
    simd_shuffle(r, x, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])
}

pub fn vaddhn_high_s32(r: int16x4_t, a: int32x4_t, b: int32x4_t) -> int16x8_t {
    let x = simd_cast(simd_shr(simd_add(a, b), int32x4_t::splat(16)));
    simd_shuffle(r, x, [0, 1, 2, 3, 4, 5, 6, 7])
}

pub fn vaddhn_high_s64(r: int32x2_t, a: int64x2_t, b: int64x2_t) -> int32x4_t {
    let x = simd_cast(simd_shr(simd_add(a, b), int64x2_t::splat(32)));
    simd_shuffle(r, x, [0, 1, 2, 3])
}

pub fn vaddhn_high_u16(r: uint8x8_t, a: uint16x8_t, b: uint16x8_t) -> uint8x16_t {
    let x = simd_cast(simd_shr(simd_add(a, b), uint16x8_t::splat(8)));
    simd_shuffle(r, x, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])
}

pub fn vaddhn_high_u32(r: uint16x4_t, a: uint32x4_t, b: uint32x4_t) -> uint16x8_t {
    let x = simd_cast(simd_shr(simd_add(a, b), uint32x4_t::splat(16)));
    simd_shuffle(r, x, [0, 1, 2, 3, 4, 5, 6, 7])
}

pub fn vaddhn_high_u64(r: uint32x2_t, a: uint64x2_t, b: uint64x2_t) -> uint32x4_t {
    let x = simd_cast(simd_shr(simd_add(a, b), uint64x2_t::splat(32)));
    simd_shuffle(r, x, [0, 1, 2, 3])
}

pub fn vaddhn_s16(a: int16x8_t, b: int16x8_t) -> int8x8_t {
    simd_cast(simd_shr(simd_add(a, b), int16x8_t::splat(8)))
}

pub fn vaddhn_s32(a: int32x4_t, b: int32x4_t) -> int16x4_t {
    simd_cast(simd_shr(simd_add(a, b), int32x4_t::splat(16)))
}

pub fn vaddhn_s64(a: int64x2_t, b: int64x2_t) -> int32x2_t {
    simd_cast(simd_shr(simd_add(a, b), int64x2_t::splat(32)))
}

pub fn vaddhn_u16(a: uint16x8_t, b: uint16x8_t) -> uint8x8_t {
    simd_cast(simd_shr(simd_add(a, b), uint16x8_t::splat(8)))
}

pub fn vaddhn_u32(a: uint32x4_t, b: uint32x4_t) -> uint16x4_t {
    simd_cast(simd_shr(simd_add(a, b), uint32x4_t::splat(16)))
}

pub fn vaddhn_u64(a: uint64x2_t, b: uint64x2_t) -> uint32x2_t {
    simd_cast(simd_shr(simd_add(a, b), uint64x2_t::splat(32)))
}

pub fn vaddl_high_s16(a: int16x8_t, b: int16x8_t) -> int32x4_t {
    let a: int16x4_t = simd_shuffle(a, a, [4, 5, 6, 7]);
    let b: int16x4_t = simd_shuffle(b, b, [4, 5, 6, 7]);
    let a: int32x4_t = simd_cast(a);
    let b: int32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_high_s32(a: int32x4_t, b: int32x4_t) -> int64x2_t {
    let a: int32x2_t = simd_shuffle(a, a, [2, 3]);
    let b: int32x2_t = simd_shuffle(b, b, [2, 3]);
    let a: int64x2_t = simd_cast(a);
    let b: int64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_high_s8(a: int8x16_t, b: int8x16_t) -> int16x8_t {
    let a: int8x8_t = simd_shuffle(a, a, [8, 9, 10, 11, 12, 13, 14, 15]);
    let b: int8x8_t = simd_shuffle(b, b, [8, 9, 10, 11, 12, 13, 14, 15]);
    let a: int16x8_t = simd_cast(a);
    let b: int16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_high_u16(a: uint16x8_t, b: uint16x8_t) -> uint32x4_t {
    let a: uint16x4_t = simd_shuffle(a, a, [4, 5, 6, 7]);
    let b: uint16x4_t = simd_shuffle(b, b, [4, 5, 6, 7]);
    let a: uint32x4_t = simd_cast(a);
    let b: uint32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_high_u32(a: uint32x4_t, b: uint32x4_t) -> uint64x2_t {
    let a: uint32x2_t = simd_shuffle(a, a, [2, 3]);
    let b: uint32x2_t = simd_shuffle(b, b, [2, 3]);
    let a: uint64x2_t = simd_cast(a);
    let b: uint64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_high_u8(a: uint8x16_t, b: uint8x16_t) -> uint16x8_t {
    let a: uint8x8_t = simd_shuffle(a, a, [8, 9, 10, 11, 12, 13, 14, 15]);
    let b: uint8x8_t = simd_shuffle(b, b, [8, 9, 10, 11, 12, 13, 14, 15]);
    let a: uint16x8_t = simd_cast(a);
    let b: uint16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_s16(a: int16x4_t, b: int16x4_t) -> int32x4_t {
    let a: int32x4_t = simd_cast(a);
    let b: int32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_s32(a: int32x2_t, b: int32x2_t) -> int64x2_t {
    let a: int64x2_t = simd_cast(a);
    let b: int64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_s8(a: int8x8_t, b: int8x8_t) -> int16x8_t {
    let a: int16x8_t = simd_cast(a);
    let b: int16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_u16(a: uint16x4_t, b: uint16x4_t) -> uint32x4_t {
    let a: uint32x4_t = simd_cast(a);
    let b: uint32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_u32(a: uint32x2_t, b: uint32x2_t) -> uint64x2_t {
    let a: uint64x2_t = simd_cast(a);
    let b: uint64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddl_u8(a: uint8x8_t, b: uint8x8_t) -> uint16x8_t {
    let a: uint16x8_t = simd_cast(a);
    let b: uint16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_high_s16(a: int32x4_t, b: int16x8_t) -> int32x4_t {
    let b: int16x4_t = simd_shuffle(b, b, [4, 5, 6, 7]);
    let b: int32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_high_s32(a: int64x2_t, b: int32x4_t) -> int64x2_t {
    let b: int32x2_t = simd_shuffle(b, b, [2, 3]);
    let b: int64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_high_s8(a: int16x8_t, b: int8x16_t) -> int16x8_t {
    let b: int8x8_t = simd_shuffle(b, b, [8, 9, 10, 11, 12, 13, 14, 15]);
    let b: int16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_high_u16(a: uint32x4_t, b: uint16x8_t) -> uint32x4_t {
    let b: uint16x4_t = simd_shuffle(b, b, [4, 5, 6, 7]);
    let b: uint32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_high_u32(a: uint64x2_t, b: uint32x4_t) -> uint64x2_t {
    let b: uint32x2_t = simd_shuffle(b, b, [2, 3]);
    let b: uint64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_high_u8(a: uint16x8_t, b: uint8x16_t) -> uint16x8_t {
    let b: uint8x8_t = simd_shuffle(b, b, [8, 9, 10, 11, 12, 13, 14, 15]);
    let b: uint16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_s16(a: int32x4_t, b: int16x4_t) -> int32x4_t {
    let b: int32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_s32(a: int64x2_t, b: int32x2_t) -> int64x2_t {
    let b: int64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_s8(a: int16x8_t, b: int8x8_t) -> int16x8_t {
    let b: int16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_u16(a: uint32x4_t, b: uint16x4_t) -> uint32x4_t {
    let b: uint32x4_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_u32(a: uint64x2_t, b: uint32x2_t) -> uint64x2_t {
    let b: uint64x2_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vaddw_u8(a: uint16x8_t, b: uint8x8_t) -> uint16x8_t {
    let b: uint16x8_t = simd_cast(b);
    simd_add(a, b)
}

pub fn vand_s8(a: int8x8_t, b: int8x8_t) -> int8x8_t {
    simd_and(a, b)
}

pub fn vandq_s8(a: int8x16_t, b: int8x16_t) -> int8x16_t {
    simd_and(a, b)
}

pub fn vand_s16(a: int16x4_t, b: int16x4_t) -> int16x4_t {
    simd_and(a, b)
}

pub fn vandq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    simd_and(a, b)
}

pub fn vand_s32(a: int32x2_t, b: int32x2_t) -> int32x2_t {
    simd_and(a, b)
}

pub fn vandq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    simd_and(a, b)
}

pub fn vand_s64(a: int64x1_t, b: int64x1_t) -> int64x1_t {
    simd_and(a, b)
}

pub fn vandq_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    simd_and(a, b)
}

pub fn vand_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    simd_and(a, b)
}

pub fn vandq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    simd_and(a, b)
}

pub fn vand_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    simd_and(a, b)
}

pub fn vandq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    simd_and(a, b)
}

pub fn vand_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    simd_and(a, b)
}

pub fn vandq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    simd_and(a, b)
}

pub fn vand_u64(a: uint64x1_t, b: uint64x1_t) -> uint64x1_t {
    simd_and(a, b)
}

pub fn vandq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    simd_and(a, b)
}

pub fn vbic_s16(a: int16x4_t, b: int16x4_t) -> int16x4_t {
    let c = int16x4_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbic_s32(a: int32x2_t, b: int32x2_t) -> int32x2_t {
    let c = int32x2_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbic_s64(a: int64x1_t, b: int64x1_t) -> int64x1_t {
    let c = int64x1_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbic_s8(a: int8x8_t, b: int8x8_t) -> int8x8_t {
    let c = int8x8_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbicq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    let c = int16x8_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbicq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    let c = int32x4_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbicq_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    let c = int64x2_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbicq_s8(a: int8x16_t, b: int8x16_t) -> int8x16_t {
    let c = int8x16_t::splat(-1);
    simd_and(simd_xor(b, c), a)
}

pub fn vbic_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    let c = int16x4_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbic_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    let c = int32x2_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbic_u64(a: uint64x1_t, b: uint64x1_t) -> uint64x1_t {
    let c = int64x1_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbic_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    let c = int8x8_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbicq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    let c = int16x8_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbicq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let c = int32x4_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbicq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    let c = int64x2_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbicq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    let c = int8x16_t::splat(-1);
    simd_and(simd_xor(b, simd_cast(c)), a)
}

pub fn vbsl_s16(a: uint16x4_t, b: int16x4_t, c: int16x4_t) -> int16x4_t {
    let not = int16x4_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbsl_s32(a: uint32x2_t, b: int32x2_t, c: int32x2_t) -> int32x2_t {
    let not = int32x2_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbsl_s64(a: uint64x1_t, b: int64x1_t, c: int64x1_t) -> int64x1_t {
    let not = int64x1_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbsl_s8(a: uint8x8_t, b: int8x8_t, c: int8x8_t) -> int8x8_t {
    let not = int8x8_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbslq_s16(a: uint16x8_t, b: int16x8_t, c: int16x8_t) -> int16x8_t {
    let not = int16x8_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbslq_s32(a: uint32x4_t, b: int32x4_t, c: int32x4_t) -> int32x4_t {
    let not = int32x4_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbslq_s64(a: uint64x2_t, b: int64x2_t, c: int64x2_t) -> int64x2_t {
    let not = int64x2_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbslq_s8(a: uint8x16_t, b: int8x16_t, c: int8x16_t) -> int8x16_t {
    let not = int8x16_t::splat(-1);
    simd_cast(simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), simd_cast(c)),
    ))
}

pub fn vbsl_u16(a: uint16x4_t, b: uint16x4_t, c: uint16x4_t) -> uint16x4_t {
    let not = int16x4_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vbsl_u32(a: uint32x2_t, b: uint32x2_t, c: uint32x2_t) -> uint32x2_t {
    let not = int32x2_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vbsl_u64(a: uint64x1_t, b: uint64x1_t, c: uint64x1_t) -> uint64x1_t {
    let not = int64x1_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vbsl_u8(a: uint8x8_t, b: uint8x8_t, c: uint8x8_t) -> uint8x8_t {
    let not = int8x8_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vbslq_u16(a: uint16x8_t, b: uint16x8_t, c: uint16x8_t) -> uint16x8_t {
    let not = int16x8_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vbslq_u32(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t) -> uint32x4_t {
    let not = int32x4_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vbslq_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    let not = int64x2_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vbslq_u8(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t) -> uint8x16_t {
    let not = int8x16_t::splat(-1);
    simd_or(
        simd_and(a, simd_cast(b)),
        simd_and(simd_xor(a, simd_cast(not)), c),
    )
}

pub fn vceq_s8(a: int8x8_t, b: int8x8_t) -> uint8x8_t {
    simd_cast(simd_eq(a, b))
}

pub fn vceqq_s8(a: int8x16_t, b: int8x16_t) -> uint8x16_t {
    simd_cast(simd_eq(a, b))
}

pub fn vceq_s16(a: int16x4_t, b: int16x4_t) -> uint16x4_t {
    simd_cast(simd_eq(a, b))
}

pub fn vceqq_s16(a: int16x8_t, b: int16x8_t) -> uint16x8_t {
    simd_cast(simd_eq(a, b))
}

pub fn vceq_s32(a: int32x2_t, b: int32x2_t) -> uint32x2_t {
    simd_cast(simd_eq(a, b))
}

pub fn vceqq_s32(a: int32x4_t, b: int32x4_t) -> uint32x4_t {
    simd_cast(simd_eq(a, b))
}

pub fn vceq_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    simd_eq(a, b)
}

pub fn vceqq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    simd_eq(a, b)
}

pub fn vceq_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    simd_eq(a, b)
}

pub fn vceqq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    simd_eq(a, b)
}

pub fn vceq_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    simd_eq(a, b)
}

pub fn vceqq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    simd_eq(a, b)
}

pub fn vcge_s8(a: int8x8_t, b: int8x8_t) -> uint8x8_t {
    simd_cast(simd_ge(a, b))
}

pub fn vcgeq_s8(a: int8x16_t, b: int8x16_t) -> uint8x16_t {
    simd_cast(simd_ge(a, b))
}

pub fn vcge_s16(a: int16x4_t, b: int16x4_t) -> uint16x4_t {
    simd_cast(simd_ge(a, b))
}

pub fn vcgeq_s16(a: int16x8_t, b: int16x8_t) -> uint16x8_t {
    simd_cast(simd_ge(a, b))
}

pub fn vcge_s32(a: int32x2_t, b: int32x2_t) -> uint32x2_t {
    simd_cast(simd_ge(a, b))
}

pub fn vcgeq_s32(a: int32x4_t, b: int32x4_t) -> uint32x4_t {
    simd_cast(simd_ge(a, b))
}

pub fn vcge_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    simd_ge(a, b)
}

pub fn vcgeq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    simd_ge(a, b)
}

pub fn vcge_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    simd_ge(a, b)
}

pub fn vcgeq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    simd_ge(a, b)
}

pub fn vcge_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    simd_ge(a, b)
}

pub fn vcgeq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    simd_ge(a, b)
}

pub fn vcgt_s8(a: int8x8_t, b: int8x8_t) -> uint8x8_t {
    simd_cast(simd_gt(a, b))
}

pub fn vcgtq_s8(a: int8x16_t, b: int8x16_t) -> uint8x16_t {
    simd_cast(simd_gt(a, b))
}

pub fn vcgt_s16(a: int16x4_t, b: int16x4_t) -> uint16x4_t {
    simd_cast(simd_gt(a, b))
}

pub fn vcgtq_s16(a: int16x8_t, b: int16x8_t) -> uint16x8_t {
    simd_cast(simd_gt(a, b))
}

pub fn vcgt_s32(a: int32x2_t, b: int32x2_t) -> uint32x2_t {
    simd_cast(simd_gt(a, b))
}

pub fn vcgtq_s32(a: int32x4_t, b: int32x4_t) -> uint32x4_t {
    simd_cast(simd_gt(a, b))
}

pub fn vcgt_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    simd_gt(a, b)
}

pub fn vcgtq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    simd_gt(a, b)
}

pub fn vcgt_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    simd_gt(a, b)
}

pub fn vcgtq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    simd_gt(a, b)
}

pub fn vcgt_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    simd_gt(a, b)
}

pub fn vcgtq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    simd_gt(a, b)
}

pub fn vcle_s8(a: int8x8_t, b: int8x8_t) -> uint8x8_t {
    simd_cast(simd_le(a, b))
}

pub fn vcleq_s8(a: int8x16_t, b: int8x16_t) -> uint8x16_t {
    simd_cast(simd_le(a, b))
}

pub fn vcle_s16(a: int16x4_t, b: int16x4_t) -> uint16x4_t {
    simd_cast(simd_le(a, b))
}

pub fn vcleq_s16(a: int16x8_t, b: int16x8_t) -> uint16x8_t {
    simd_cast(simd_le(a, b))
}

pub fn vcle_s32(a: int32x2_t, b: int32x2_t) -> uint32x2_t {
    simd_cast(simd_le(a, b))
}

pub fn vcleq_s32(a: int32x4_t, b: int32x4_t) -> uint32x4_t {
    simd_cast(simd_le(a, b))
}

pub fn vcle_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x8_t {
    simd_le(a, b)
}

pub fn vcleq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    simd_le(a, b)
}

pub fn vcle_u16(a: uint16x4_t, b: uint16x4_t) -> uint16x4_t {
    simd_le(a, b)
}

pub fn vcleq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    simd_le(a, b)
}

pub fn vcle_u32(a: uint32x2_t, b: uint32x2_t) -> uint32x2_t {
    simd_le(a, b)
}

pub fn vcleq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    simd_le(a, b)
}