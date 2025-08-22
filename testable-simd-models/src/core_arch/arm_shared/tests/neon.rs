#[cfg(test)]
use super::upstream;
use crate::abstractions::funarr::FunArray;
use crate::helpers::test::HasRandom;
/// Derives tests for a given intrinsics. Test that a given intrinsics and its model compute the same thing over random values (1000 by default).
macro_rules! mk {
    ($([$N:literal])?$name:ident$({$(<$($c:literal),*>),*})?($($x:ident : $ty:ident),*)) => {
        #[test]
        fn $name() {
            #[allow(unused)]
            const N: usize = {
                let n: usize = 1000;
                $(let n: usize = $N;)?
                    n
            };
            mk!(@[N]$name$($(<$($c),*>)*)?($($x : $ty),*));
        }
    };
    (@[$N:ident]$name:ident$(<$($c:literal),*>)?($($x:ident : $ty:ident),*)) => {
        for _ in 0..$N {
            $(let $x = $ty::random();)*
                assert_eq!(super::super::models::neon::$name$(::<$($c,)*>)?($($x.into(),)*), unsafe {
                    FunArray::from(upstream::$name$(::<$($c,)*>)?($($x.into(),)*)).into()
                });
        }
    };
    (@[$N:ident]$name:ident<$($c1:literal),*>$(<$($c:literal),*>)*($($x:ident : $ty:ident),*)) => {
        let one = || {
            mk!(@[$N]$name<$($c1),*>($($x : $ty),*));
        };
        one();
        mk!(@[$N]$name$(<$($c),*>)*($($x : $ty),*));
    }

}

use super::types::*;
mk!(vaba_s16(a: int16x4_t, b: int16x4_t, c: int16x4_t));
mk!(vaba_s32(a: int32x2_t, b: int32x2_t, c: int32x2_t));
mk!(vaba_s8(a: int8x8_t, b: int8x8_t, c: int8x8_t));
mk!(vaba_u16(a: uint16x4_t, b: uint16x4_t, c: uint16x4_t));
mk!(vaba_u32(a: uint32x2_t, b: uint32x2_t, c: uint32x2_t));
mk!(vaba_u8(a: uint8x8_t, b: uint8x8_t, c: uint8x8_t));
mk!(vabal_u8(a: uint16x8_t, b: uint8x8_t, c: uint8x8_t));
mk!(vabal_u16(a: uint32x4_t, b: uint16x4_t, c: uint16x4_t));
mk!(vabal_u32(a: uint64x2_t, b: uint32x2_t, c: uint32x2_t));
mk!(vabaq_s16(a: int16x8_t, b: int16x8_t, c: int16x8_t));
mk!(vabaq_s32(a: int32x4_t, b: int32x4_t, c: int32x4_t));
mk!(vabaq_s8(a: int8x16_t, b: int8x16_t, c: int8x16_t));
mk!(vabaq_u16(a: uint16x8_t, b: uint16x8_t, c: uint16x8_t));
mk!(vabaq_u32(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t));
mk!(vabaq_u8(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t));
mk!(vabd_s8(a: int8x8_t, b: int8x8_t));
mk!(vabdq_s8(a: int8x16_t, b: int8x16_t));
mk!(vabd_s16(a: int16x4_t, b: int16x4_t));
mk!(vabdq_s16(a: int16x8_t, b: int16x8_t));
mk!(vabd_s32(a: int32x2_t, b: int32x2_t));
mk!(vabdq_s32(a: int32x4_t, b: int32x4_t));
mk!(vabd_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vabdq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vabd_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vabdq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vabd_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vabdq_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vabdl_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vabdl_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vabdl_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vabs_s8(a: int8x8_t));
mk!(vabsq_s8(a: int8x16_t));
mk!(vabs_s16(a: int16x4_t));
mk!(vabsq_s16(a: int16x8_t));
mk!(vabs_s32(a: int32x2_t));
mk!(vabsq_s32(a: int32x4_t));
mk!(vadd_s16(a: int16x4_t, b: int16x4_t));
mk!(vadd_s32(a: int32x2_t, b: int32x2_t));
mk!(vadd_s8(a: int8x8_t, b: int8x8_t));
mk!(vadd_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vadd_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vadd_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vaddq_s16(a: int16x8_t, b: int16x8_t));
mk!(vaddq_s32(a: int32x4_t, b: int32x4_t));
mk!(vaddq_s64(a: int64x2_t, b: int64x2_t));
mk!(vaddq_s8(a: int8x16_t, b: int8x16_t));
mk!(vaddq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vaddq_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vaddq_u64(a: uint64x2_t, b: uint64x2_t));
mk!(vaddq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vaddhn_high_s16(r: int8x8_t, a: int16x8_t, b: int16x8_t));
mk!(vaddhn_high_s32(r: int16x4_t, a: int32x4_t, b: int32x4_t));
mk!(vaddhn_high_s64(r: int32x2_t, a: int64x2_t, b: int64x2_t));
mk!(vaddhn_high_u16(r: uint8x8_t, a: uint16x8_t, b: uint16x8_t));
mk!(vaddhn_high_u32(r: uint16x4_t, a: uint32x4_t, b: uint32x4_t));
mk!(vaddhn_high_u64(r: uint32x2_t, a: uint64x2_t, b: uint64x2_t));
mk!(vaddhn_s16(a: int16x8_t, b: int16x8_t));
mk!(vaddhn_s32(a: int32x4_t, b: int32x4_t));
mk!(vaddhn_s64(a: int64x2_t, b: int64x2_t));
mk!(vaddhn_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vaddhn_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vaddhn_u64(a: uint64x2_t, b: uint64x2_t));
mk!(vaddl_high_s16(a: int16x8_t, b: int16x8_t));
mk!(vaddl_high_s32(a: int32x4_t, b: int32x4_t));
mk!(vaddl_high_s8(a: int8x16_t, b: int8x16_t));
mk!(vaddl_high_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vaddl_high_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vaddl_high_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vaddl_s16(a: int16x4_t, b: int16x4_t));
mk!(vaddl_s32(a: int32x2_t, b: int32x2_t));
mk!(vaddl_s8(a: int8x8_t, b: int8x8_t));
mk!(vaddl_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vaddl_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vaddl_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vaddw_high_s16(a: int32x4_t, b: int16x8_t));
mk!(vaddw_high_s32(a: int64x2_t, b: int32x4_t));
mk!(vaddw_high_s8(a: int16x8_t, b: int8x16_t));
mk!(vaddw_high_u16(a: uint32x4_t, b: uint16x8_t));
mk!(vaddw_high_u32(a: uint64x2_t, b: uint32x4_t));
mk!(vaddw_high_u8(a: uint16x8_t, b: uint8x16_t));
mk!(vaddw_s16(a: int32x4_t, b: int16x4_t));
mk!(vaddw_s32(a: int64x2_t, b: int32x2_t));
mk!(vaddw_s8(a: int16x8_t, b: int8x8_t));
mk!(vaddw_u16(a: uint32x4_t, b: uint16x4_t));
mk!(vaddw_u32(a: uint64x2_t, b: uint32x2_t));
mk!(vaddw_u8(a: uint16x8_t, b: uint8x8_t));
mk!(vand_s8(a: int8x8_t, b: int8x8_t));
mk!(vandq_s8(a: int8x16_t, b: int8x16_t));
mk!(vand_s16(a: int16x4_t, b: int16x4_t));
mk!(vandq_s16(a: int16x8_t, b: int16x8_t));
mk!(vand_s32(a: int32x2_t, b: int32x2_t));
mk!(vandq_s32(a: int32x4_t, b: int32x4_t));
mk!(vand_s64(a: int64x1_t, b: int64x1_t));
mk!(vandq_s64(a: int64x2_t, b: int64x2_t));
mk!(vand_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vandq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vand_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vandq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vand_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vandq_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vand_u64(a: uint64x1_t, b: uint64x1_t));
mk!(vandq_u64(a: uint64x2_t, b: uint64x2_t));
mk!(vbic_s16(a: int16x4_t, b: int16x4_t));
mk!(vbic_s32(a: int32x2_t, b: int32x2_t));
mk!(vbic_s8(a: int8x8_t, b: int8x8_t));
mk!(vbicq_s16(a: int16x8_t, b: int16x8_t));
mk!(vbicq_s32(a: int32x4_t, b: int32x4_t));
mk!(vbicq_s64(a: int64x2_t, b: int64x2_t));
mk!(vbicq_s8(a: int8x16_t, b: int8x16_t));
mk!(vbic_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vbic_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vbic_u64(a: uint64x1_t, b: uint64x1_t));
mk!(vbic_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vbicq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vbicq_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vbicq_u64(a: uint64x2_t, b: uint64x2_t));
mk!(vbicq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vbsl_s16(a: uint16x4_t, b: int16x4_t, c: int16x4_t));
mk!(vbsl_s32(a: uint32x2_t, b: int32x2_t, c: int32x2_t));
mk!(vbsl_s64(a: uint64x1_t, b: int64x1_t, c: int64x1_t));
mk!(vbsl_s8(a: uint8x8_t, b: int8x8_t, c: int8x8_t));
mk!(vbslq_s16(a: uint16x8_t, b: int16x8_t, c: int16x8_t));
mk!(vbslq_s32(a: uint32x4_t, b: int32x4_t, c: int32x4_t));
mk!(vbslq_s64(a: uint64x2_t, b: int64x2_t, c: int64x2_t));
mk!(vbslq_s8(a: uint8x16_t, b: int8x16_t, c: int8x16_t));
mk!(vbsl_u16(a: uint16x4_t, b: uint16x4_t, c: uint16x4_t));
mk!(vbsl_u32(a: uint32x2_t, b: uint32x2_t, c: uint32x2_t));
mk!(vbsl_u64(a: uint64x1_t, b: uint64x1_t, c: uint64x1_t));
mk!(vbsl_u8(a: uint8x8_t, b: uint8x8_t, c: uint8x8_t));
mk!(vbslq_u16(a: uint16x8_t, b: uint16x8_t, c: uint16x8_t));
mk!(vbslq_u32(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t));
mk!(vbslq_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t));
mk!(vbslq_u8(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t));
mk!(vceq_s8(a: int8x8_t, b: int8x8_t));
mk!(vceqq_s8(a: int8x16_t, b: int8x16_t));
mk!(vceq_s16(a: int16x4_t, b: int16x4_t));
mk!(vceqq_s16(a: int16x8_t, b: int16x8_t));
mk!(vceq_s32(a: int32x2_t, b: int32x2_t));
mk!(vceqq_s32(a: int32x4_t, b: int32x4_t));
mk!(vceq_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vceqq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vceq_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vceqq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vceq_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vceqq_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vcge_s8(a: int8x8_t, b: int8x8_t));
mk!(vcgeq_s8(a: int8x16_t, b: int8x16_t));
mk!(vcge_s16(a: int16x4_t, b: int16x4_t));
mk!(vcgeq_s16(a: int16x8_t, b: int16x8_t));
mk!(vcge_s32(a: int32x2_t, b: int32x2_t));
mk!(vcgeq_s32(a: int32x4_t, b: int32x4_t));
mk!(vcge_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vcgeq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vcge_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vcgeq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vcge_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vcgeq_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vcgt_s8(a: int8x8_t, b: int8x8_t));
mk!(vcgtq_s8(a: int8x16_t, b: int8x16_t));
mk!(vcgt_s16(a: int16x4_t, b: int16x4_t));
mk!(vcgtq_s16(a: int16x8_t, b: int16x8_t));
mk!(vcgt_s32(a: int32x2_t, b: int32x2_t));
mk!(vcgtq_s32(a: int32x4_t, b: int32x4_t));
mk!(vcgt_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vcgtq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vcgt_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vcgtq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vcgt_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vcgtq_u32(a: uint32x4_t, b: uint32x4_t));
mk!(vcle_s8(a: int8x8_t, b: int8x8_t));
mk!(vcleq_s8(a: int8x16_t, b: int8x16_t));
mk!(vcle_s16(a: int16x4_t, b: int16x4_t));
mk!(vcleq_s16(a: int16x8_t, b: int16x8_t));
mk!(vcle_s32(a: int32x2_t, b: int32x2_t));
mk!(vcleq_s32(a: int32x4_t, b: int32x4_t));
mk!(vcle_u8(a: uint8x8_t, b: uint8x8_t));
mk!(vcleq_u8(a: uint8x16_t, b: uint8x16_t));
mk!(vcle_u16(a: uint16x4_t, b: uint16x4_t));
mk!(vcleq_u16(a: uint16x8_t, b: uint16x8_t));
mk!(vcle_u32(a: uint32x2_t, b: uint32x2_t));
mk!(vcleq_u32(a: uint32x4_t, b: uint32x4_t));
