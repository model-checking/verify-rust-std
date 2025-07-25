use super::types::*;
use super::upstream;
use crate::abstractions::bitvec::BitVec;
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
            unsafe { upstream::_mm256_movemask_ps(a.into()) }
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
            unsafe { upstream::_mm256_testz_si256(a.into(), b.into()) }
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
