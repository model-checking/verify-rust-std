use super::types::*;
use super::upstream;
use crate::abstractions::bitvec::BitVec;
use crate::helpers::test::HasRandom;

macro_rules! assert_feq {
    ($lhs:expr, $rhs:expr) => {
        assert!(($lhs.is_nan() && $rhs.is_nan()) || $lhs == $rhs)
    };
}

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
                assert_eq!(super::super::models::avx::$name$(::<$($c,)*>)?($($x.into(),)*), unsafe {
                    BitVec::from(upstream::$name$(::<$($c,)*>)?($($x.into(),)*)).into()
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
mk!(_mm256_blendv_ps(a: __m256, b: __m256, c: __m256));

#[test]
fn _mm256_movemask_ps() {
    let n = 1000;

    for _ in 0..n {
        let a: BitVec<256> = BitVec::random();
        assert_eq!(
            super::super::models::avx::_mm256_movemask_ps(a.into()),
            unsafe { upstream::_mm256_movemask_ps(a.into()) },
            "Failed with input value: {:?}",
            a
        );
    }
}

#[test]
fn _mm256_movemask_pd() {
    let n = 1000;

    for _ in 0..n {
        let a: BitVec<256> = BitVec::random();
        assert_eq!(
            super::super::models::avx::_mm256_movemask_pd(a.into()),
            unsafe { upstream::_mm256_movemask_pd(a.into()) },
            "Failed with input value: {:?}",
            a
        );
    }
}

#[test]
fn _mm256_testz_si256() {
    let n = 1000;

    for _ in 0..n {
        let a: BitVec<256> = BitVec::random();
        let b: BitVec<256> = BitVec::random();
        assert_eq!(
            super::super::models::avx::_mm256_testz_si256(a.into(), b.into()),
            unsafe { upstream::_mm256_testz_si256(a.into(), b.into()) },
            "Failed with input values: {:?}, {:?}",
            a,
            b
        );
    }
}

#[test]
fn _mm256_testc_si256() {
    let n = 1000;

    for _ in 0..n {
        let a: BitVec<256> = BitVec::random();
        let b: BitVec<256> = BitVec::random();
        assert_eq!(
            super::super::models::avx::_mm256_testc_si256(a.into(), b.into()),
            unsafe { upstream::_mm256_testc_si256(a.into(), b.into()) },
            "Failed with input values: {:?}, {:?}",
            a,
            b
        );
    }
}

#[test]
fn _mm256_cvtsd_f64() {
    let n = 1000;

    for _ in 0..n {
        let a: BitVec<256> = BitVec::random();
        assert_feq!(
            super::super::models::avx::_mm256_cvtsd_f64(a.into()),
            unsafe { upstream::_mm256_cvtsd_f64(a.into()) }
        );
    }
}

#[test]
fn _mm256_cvtsi256_si32() {
    let n = 1000;

    for _ in 0..n {
        let a: BitVec<256> = BitVec::random();
        assert_eq!(
            super::super::models::avx::_mm256_cvtsi256_si32(a.into()),
            unsafe { upstream::_mm256_cvtsi256_si32(a.into()) },
            "Failed with input value: {:?}",
            a
        );
    }
}

#[test]
fn _mm256_cvtss_f32() {
    let n = 1000;

    for _ in 0..n {
        let a: BitVec<256> = BitVec::random();
        assert_feq!(
            super::super::models::avx::_mm256_cvtss_f32(a.into()),
            unsafe { upstream::_mm256_cvtss_f32(a.into()) }
        );
    }
}

mk!(_mm256_setzero_ps());
mk!(_mm256_setzero_si256());
mk!(_mm256_set_epi8(
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
    e31: i8
));
mk!(_mm256_set_epi16(
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
    e15: i16
));
mk!(_mm256_set_epi32(
    e0: i32,
    e1: i32,
    e2: i32,
    e3: i32,
    e4: i32,
    e5: i32,
    e6: i32,
    e7: i32
));
mk!(_mm256_set_epi64x(a: i64, b: i64, c: i64, d: i64));
mk!(_mm256_set1_epi8(a: i8));
mk!(_mm256_set1_epi16(a: i16));
mk!(_mm256_set1_epi32(a: i32));
mk!(_mm256_set1_epi64x(a: i64));
mk!(_mm256_set_pd(a: f64, b: f64, c: f64, d: f64));
mk!(_mm256_set_ps(a: f32, b: f32, c: f32, d: f32, e: f32, f: f32, g: f32, h: f32));
mk!(_mm256_setr_pd(a: f64, b: f64, c: f64, d: f64));
mk!(_mm256_setr_ps(a: f32, b: f32, c: f32, d: f32, e: f32, f: f32, g: f32, h: f32));
mk!(_mm256_setr_epi64x(a: i64, b: i64, c: i64, d: i64));
mk!(_mm256_set1_pd(a: f64));
mk!(_mm256_set1_ps(a: f32));

mk!(_mm256_and_pd(a: __m256d, b: __m256d));
mk!(_mm256_and_ps(a: __m256, b: __m256));
mk!(_mm256_or_pd(a: __m256d, b: __m256d));
mk!(_mm256_or_ps(a: __m256, b: __m256));
mk!(_mm256_andnot_pd(a: __m256d, b: __m256d));
mk!(_mm256_andnot_ps(a: __m256, b: __m256));
mk!(_mm256_blendv_pd(a: __m256d, b: __m256d, c: __m256d));
mk!(_mm256_xor_pd(a: __m256d, b: __m256d));
mk!(_mm256_xor_ps(a: __m256, b: __m256));
mk!(_mm256_cvtepi32_pd(a: __m128i));
mk!(_mm256_cvtepi32_ps(a: __m256i));
mk!(_mm256_cvtpd_ps(a: __m256d));
mk!(_mm256_cvtps_pd(a: __m128));
mk!(_mm256_movehdup_ps(a: __m256));
mk!(_mm256_moveldup_ps(a: __m256));
mk!(_mm256_movedup_pd(a: __m256d));
mk!(_mm256_unpackhi_pd(a: __m256d, b: __m256d));
mk!(_mm256_unpackhi_ps(a: __m256, b: __m256));
mk!(_mm256_unpacklo_pd(a: __m256d, b: __m256d));
mk!(_mm256_unpacklo_ps(a: __m256, b: __m256));
mk!(_mm256_setzero_pd());
mk!(_mm256_castpd_ps(a: __m256d));
mk!(_mm256_castps_pd(a: __m256));
mk!(_mm256_castps_si256(a: __m256));
mk!(_mm256_castsi256_ps(a: __m256i));
mk!(_mm256_castpd_si256(a: __m256d));
mk!(_mm256_castsi256_pd(a: __m256i));
mk!(_mm256_castps256_ps128(a: __m256));
mk!(_mm256_castpd256_pd128(a: __m256d));
mk!(_mm256_castsi256_si128(a: __m256i));
mk!(_mm256_castps128_ps256(a: __m128));
mk!(_mm256_castpd128_pd256(a: __m128d));
mk!(_mm256_castsi128_si256(a: __m128i));
mk!(_mm256_zextps128_ps256(a: __m128));
mk!(_mm256_zextsi128_si256(a: __m128i));
mk!(_mm256_zextpd128_pd256(a: __m128d));
mk!(_mm256_undefined_ps());
mk!(_mm256_undefined_pd());
mk!(_mm256_undefined_si256());
mk!(_mm256_set_m128(hi: __m128, lo: __m128));
mk!(_mm256_set_m128d(hi: __m128d, lo: __m128d));
mk!(_mm256_set_m128i(hi: __m128i, lo: __m128i));
mk!(_mm256_setr_m128(lo: __m128, hi: __m128));
mk!(_mm256_setr_m128d(lo: __m128d, hi: __m128d));
mk!(_mm256_setr_m128i(lo: __m128i, hi: __m128i));
