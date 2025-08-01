//! Models of SIMD compiler intrinsics.
//!
//! Operations are defined on FunArrs.

use crate::abstractions::{bit::*, bitvec::*, funarr::*};
use std::convert::*;
use std::ops::*;

#[allow(dead_code)]
/// Derives interpretations functions, and type synonyms.
macro_rules! interpretations {
($n:literal; $($name:ident [$ty:ty; $m:literal]),*) => {
        $(
    #[doc = concat!(stringify!($ty), " vectors of size ", stringify!($m))]
    #[allow(non_camel_case_types)]
    pub type $name = FunArray<$m, $ty>;
    pastey::paste! {
                const _: ()  = {
        impl BitVec<$n> {
                        #[doc = concat!("Conversion from ", stringify!($ty), " vectors of size ", stringify!($m), "to  bit vectors of size ", stringify!($n))]
                        pub fn [< from_ $name >](iv: $name) -> BitVec<$n> {
            let vec: Vec<$ty> = iv.as_vec();
            Self::from_slice(&vec[..], <$ty>::BITS as u32)
                        }
                        #[doc = concat!("Conversion from bit vectors of size ", stringify!($n), " to ", stringify!($ty), " vectors of size ", stringify!($m))]
                        pub fn [< to_ $name >](bv: BitVec<$n>) -> $name {
            let vec: Vec<$ty> = bv.to_vec();
            $name::from_fn(|i| vec[i as usize])
                        }
                        #[doc = concat!("Conversion from bit vectors of size ", stringify!($n), " to ", stringify!($ty), " vectors of size ", stringify!($m))]
                        pub fn [< as_ $name >](self) -> $name {
            let vec: Vec<$ty> = self.to_vec();
            $name::from_fn(|i| vec[i as usize])
                        }


        }


        impl From<BitVec<$n>> for $name {
                        fn from(bv: BitVec<$n>) -> Self {
            BitVec::[< to_ $name >](bv)
                        }
        }

        impl From<$name> for BitVec<$n> {
                        fn from(iv: $name) -> Self {
            BitVec::[< from_ $name >](iv)
                        }
        }

        impl $name {

            pub fn splat(value: $ty) -> Self {
            FunArray::from_fn(|_| value)
            }
        }
                };
    }
        )*
};
}

interpretations!(256; i32x8 [i32; 8], i64x4 [i64; 4], i16x16 [i16; 16], i128x2 [i128; 2], i8x32 [i8; 32],
            u32x8 [u32; 8], u64x4 [u64; 4], u16x16 [u16; 16], u8x32 [u8; 32], f32x8 [f32; 8], f64x4 [f64; 4]);
interpretations!(128; i32x4 [i32; 4], i64x2 [i64; 2], i16x8 [i16; 8], i128x1 [i128; 1], i8x16 [i8; 16],
            u32x4 [u32; 4], u64x2 [u64; 2], u16x8 [u16; 8], u8x16 [u8; 16], f32x4 [f32; 4], f64x2 [f64; 2]);

interpretations!(512; u32x16 [u32; 16], u16x32 [u16; 32], i32x16 [i32; 16], i16x32 [i16; 32]);
interpretations!(64; i64x1 [i64; 1], i32x2 [i32; 2], i16x4 [i16; 4], i8x8 [i8; 8], u64x1 [u64; 1], u32x2 [u32; 2],u16x4 [u16; 4], u8x8 [u8; 8], f32x2 [f32; 2], f64x1 [f64; 1]);
interpretations!(32; i8x4 [i8; 4], u8x4 [u8; 4]);

/// Inserts an element into a vector, returning the updated vector.
///
/// # Safety
///
/// `idx` must be in-bounds of the vector, ie. idx < N
pub fn simd_insert<const N: u32, T: Copy>(x: FunArray<N, T>, idx: u32, val: T) -> FunArray<N, T> {
    FunArray::from_fn(|i| if i == idx { val } else { x[i] })
}

/// Extracts an element from a vector.
///
/// # Safety
///
/// `idx` must be in-bounds of the vector, ie. idx < N
pub fn simd_extract<const N: u32, T: Clone>(x: FunArray<N, T>, idx: u32) -> T {
    x.get(idx).clone()
}

/// Adds two vectors elementwise with wrapping on overflow/underflow.
pub fn simd_add<const N: u32, T: MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| x[i].wrapping_add(y[i]))
}

/// Subtracts `rhs` from `lhs` elementwise with wrapping on overflow/underflow.
pub fn simd_sub<const N: u32, T: MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| x[i].wrapping_sub(y[i]))
}

/// Multiplies two vectors elementwise with wrapping on overflow/underflow.
pub fn simd_mul<const N: u32, T: MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| x[i].overflowing_mul(y[i]))
}

/// Produces the elementwise absolute values.
/// For vectors of unsigned integers it returns the vector untouched.
/// If the element is the minimum value of a signed integer, it returns the element as is.
pub fn simd_abs<const N: u32, T: MachineInteger + Copy>(x: FunArray<N, T>) -> FunArray<N, T> {
    FunArray::from_fn(|i| x[i].wrapping_abs())
}

/// Produces the elementwise absolute difference of two vectors.
/// Note: Absolute difference in this case is simply the element with the smaller value subtracted from the element with the larger value, with overflow/underflow.
/// For example, if the elements are i8, the absolute difference of 255 and -2 is -255.
pub fn simd_abs_diff<const N: u32, T: MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| x[i].wrapping_abs_diff(y[i]))
}

/// Shifts vector left elementwise, with UB on overflow.
///
/// # Safety
///
/// Each element of `rhs` must be less than `<int>::BITS`.
pub fn simd_shl<const N: u32, T: Shl + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, <T as Shl>::Output> {
    FunArray::from_fn(|i| x[i] << y[i])
}

/// Shifts vector right elementwise, with UB on overflow.
///
/// Shifts `lhs` right by `rhs`, shifting in sign bits for signed types.
///
/// # Safety
///
/// Each element of `rhs` must be less than `<int>::BITS`.

pub fn simd_shr<const N: u32, T: Shr + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, <T as Shr>::Output> {
    FunArray::from_fn(|i| x[i] >> y[i])
}

/// "Ands" vectors elementwise.

pub fn simd_and<const N: u32, T: BitAnd + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, <T as BitAnd>::Output> {
    FunArray::from_fn(|i| x[i] & y[i])
}

/// "Ors" vectors elementwise.

pub fn simd_or<const N: u32, T: BitOr + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, <T as BitOr>::Output> {
    FunArray::from_fn(|i| x[i] | y[i])
}

/// "Exclusive ors" vectors elementwise.

pub fn simd_xor<const N: u32, T: BitXor + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, <T as BitXor>::Output> {
    FunArray::from_fn(|i| x[i] ^ y[i])
}

pub trait CastsFrom<T> {
    fn cast(a: T) -> Self;
}
pub trait TruncateFrom<T> {
    /// Truncates into [`Self`] from a larger integer
    fn truncate_from(v: T) -> Self;
}

macro_rules! from_impls{
    ($([$ty1:ty, $ty2: ty]),*) => {
        $(
	    impl CastsFrom<$ty2> for $ty1 {
		fn cast(a: $ty2) -> $ty1 {
		    a as $ty1
		}
	    }
	)*
    };
}
macro_rules! truncate_from_order {
    ($t:ty, $($from:ty),+) => {
        $(
        impl TruncateFrom<$from> for $t {
            #[inline]
            fn truncate_from(v: $from) -> $t { v as $t }
        }
        )*
        truncate_from_order!($($from),+);
    };

    ($t:ty) => {};
}
truncate_from_order!(u8, u16, u32, u64, u128);
truncate_from_order!(i8, i16, i32, i64, i128);

macro_rules! truncate_from_impls{
    ($([$ty1:ty, $ty2: ty]),*) => {
        $(
	    impl CastsFrom<$ty2> for $ty1 {
		fn cast(a: $ty2) -> $ty1 {
		    <$ty1>::truncate_from(a)
		}
	    }
	)*
    };
}

macro_rules! symm_impls{
    ($([$ty1:ty, $ty2: ty]),*) => {
        $(
	    impl CastsFrom<$ty2> for $ty1 {
		fn cast(a: $ty2) -> $ty1 {
		    a as $ty1
		}
	    }
	    impl CastsFrom<$ty1> for $ty2 {
		fn cast(a: $ty1) -> $ty2 {
		    a as $ty2
		}
	    }
	)*
    };
}
macro_rules! self_impls{
    ($($ty1:ty),*) => {
        $(
	    impl CastsFrom<$ty1> for $ty1 {
		fn cast(a: $ty1) -> $ty1 {
		    a
		}
	    }

	)*
    };
}
from_impls!(
    [u16, u8],
    [u32, u8],
    [u32, u16],
    [u64, u8],
    [u64, u16],
    [u64, u32],
    [u128, u8],
    [u128, u16],
    [u128, u32],
    [u128, u64],
    [i16, i8],
    [i32, i8],
    [i32, i16],
    [i64, i8],
    [i64, i16],
    [i64, i32],
    [i128, i8],
    [i128, i16],
    [i128, i32],
    [i128, i64],
    [f64, u32],
    [f64, i32],
    [f32, u32],
    [f32, i32],
    [f32, f64],
    [f64, f32]
);
truncate_from_impls!(
    [u8, u16],
    [u8, u32],
    [u16, u32],
    [u8, u64],
    [u16, u64],
    [u32, u64],
    [u8, u128],
    [u16, u128],
    [u32, u128],
    [u64, u128],
    [i8, i16],
    [i8, i32],
    [i16, i32],
    [i8, i64],
    [i16, i64],
    [i32, i64],
    [i8, i128],
    [i16, i128],
    [i32, i128],
    [i64, i128]
);

symm_impls!([u8, i8], [u16, i16], [u32, i32], [u64, i64], [u128, i128]);

self_impls!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

// Would like to do the below instead of using the above macros, but currently this is an active issue in Rust (#31844)
// impl <T,U> CastsFrom<T> for U
// where
//     U : From<T> {
//     fn cast(a: T) -> U {
// 	U::from(a)
//     }
// }

// impl <T,U> CastsFrom<T> for U
// where
//     U : TruncateFrom<T> {
//     fn cast(a: T) -> U {
// 	U::truncate_from(a)
//     }
// }

/// Numerically casts a vector, elementwise.
///
/// Casting can only happen between two integers of the same signedness.
///
/// When casting from a wider number to a smaller number, the higher bits are removed.
/// Otherwise, it extends the number, following signedness.
pub fn simd_cast<const N: u32, T1: Copy, T2: CastsFrom<T1>>(x: FunArray<N, T1>) -> FunArray<N, T2> {
    FunArray::from_fn(|i| T2::cast(x[i]))
}

/// Negates a vector elementwise.
///
/// Rust panics for `-<int>::Min` due to overflow, but here, it just returns the element as is.

pub fn simd_neg<const N: u32, T: From<<T as Neg>::Output> + MachineInteger + Eq + Neg + Copy>(
    x: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| {
        if x[i] == T::MIN {
            T::MIN
        } else {
            T::from(-x[i])
        }
    })
}
/// Tests elementwise equality of two vectors.
///
/// Returns `0` (all zeros) for false and `!0` (all ones) for true.

pub fn simd_eq<const N: u32, T: Eq + MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| if x[i] == y[i] { T::ONES } else { T::ZEROS })
}

/// Tests elementwise inequality equality of two vectors.
///
/// Returns `0` (all zeros) for false and `!0` (all ones) for true.

pub fn simd_ne<const N: u32, T: Eq + MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| if x[i] != y[i] { T::ONES } else { T::ZEROS })
}

/// Tests if `x` is less than `y`, elementwise.
///
/// Returns `0` (all zeros) for false and `!0` (all ones) for true.

pub fn simd_lt<const N: u32, T: Ord + MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| if x[i] < y[i] { T::ONES } else { T::ZEROS })
}

/// Tests if `x` is less than or equal to `y`, elementwise.
///
/// Returns `0` (all zeros) for false and `!0` (all ones) for true.

pub fn simd_le<const N: u32, T: Ord + MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| if x[i] <= y[i] { T::ONES } else { T::ZEROS })
}

/// Tests if `x` is greater than `y`, elementwise.
///
/// Returns `0` (all zeros) for false and `!0` (all ones) for true.

pub fn simd_gt<const N: u32, T: Ord + MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| if x[i] > y[i] { T::ONES } else { T::ZEROS })
}

/// Tests if `x` is greater than or equal to `y`, elementwise.
///
/// Returns `0` (all zeros) for false and `!0` (all ones) for true.

pub fn simd_ge<const N: u32, T: Ord + MachineInteger + Copy>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| if x[i] >= y[i] { T::ONES } else { T::ZEROS })
}

/// Shuffles two vectors by the indices in idx.
///
/// For safety, `N2 <= N1 + N3` must hold.
pub fn simd_shuffle<T: Copy, const N1: u32, const N2: usize, const N3: u32>(
    x: FunArray<N1, T>,
    y: FunArray<N1, T>,
    idx: [u32; N2],
) -> FunArray<N3, T> {
    FunArray::from_fn(|i| {
        let i = idx[i as usize];
        if i < N1 {
            x[i]
        } else {
            y[i - N1]
        }
    })
}

/// Adds two vectors elementwise, with saturation.

pub fn simd_saturating_add<T: MachineInteger + Copy, const N: u32>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| x[i].saturating_add(y[i]))
}

/// Subtracts `y` from `x` elementwise, with saturation.

pub fn simd_saturating_sub<T: MachineInteger + Copy, const N: u32>(
    x: FunArray<N, T>,
    y: FunArray<N, T>,
) -> FunArray<N, T> {
    FunArray::from_fn(|i| x[i].saturating_sub(y[i]))
}

/// Truncates an integer vector to a bitmask.
/// Macro for that expands to an expression which is equivalent to truncating an integer vector to a bitmask, as it would on little endian systems.
///
/// The macro takes 3 arguments.
/// The first is the highest index of the vector.
/// The second is the vector itself, which should just contain `0` and `!0`.
/// The third is the type to which the truncation happens, which should be atleast as wide as the number of elements in the vector.
///
/// Thus for example, to truncate the vector,
/// `let a : i32 = [!0, 0, 0, 0, 0, 0, 0, 0, !0, !0, 0, 0, 0, 0, !0, 0]`
/// to u16, you would call,
/// `simd_bitmask_little!(15, a, u16)`
/// to get,
/// `0b0100001100000001u16`
///
/// # Safety
/// The second argument must be a vector of signed integer types.
/// The length of the vector must be 64 at most.

// The numbers in here are powers of 2. If it is needed to extend the length of the vector, simply add more cases in the same manner.
// The reason for doing this is that the expression becomes easier to work with when compiled for a proof assistant.
macro_rules! simd_bitmask_little {
    (63, $a:ident, $ty:ty) => {
        9223372036854775808 * ((if $a[63] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(62, $a, $ty)
    };
    (62, $a:ident, $ty:ty) => {
        4611686018427387904 * ((if $a[62] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(61, $a, $ty)
    };
    (61, $a:ident, $ty:ty) => {
        2305843009213693952 * ((if $a[61] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(60, $a, $ty)
    };
    (60, $a:ident, $ty:ty) => {
        1152921504606846976 * ((if $a[60] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(59, $a, $ty)
    };
    (59, $a:ident, $ty:ty) => {
        576460752303423488 * ((if $a[59] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(58, $a, $ty)
    };
    (58, $a:ident, $ty:ty) => {
        288230376151711744 * ((if $a[58] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(57, $a, $ty)
    };
    (57, $a:ident, $ty:ty) => {
        144115188075855872 * ((if $a[57] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(56, $a, $ty)
    };
    (56, $a:ident, $ty:ty) => {
        72057594037927936 * ((if $a[56] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(55, $a, $ty)
    };
    (55, $a:ident, $ty:ty) => {
        36028797018963968 * ((if $a[55] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(54, $a, $ty)
    };
    (54, $a:ident, $ty:ty) => {
        18014398509481984 * ((if $a[54] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(53, $a, $ty)
    };
    (53, $a:ident, $ty:ty) => {
        9007199254740992 * ((if $a[53] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(52, $a, $ty)
    };
    (52, $a:ident, $ty:ty) => {
        4503599627370496 * ((if $a[52] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(51, $a, $ty)
    };
    (51, $a:ident, $ty:ty) => {
        2251799813685248 * ((if $a[51] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(50, $a, $ty)
    };
    (50, $a:ident, $ty:ty) => {
        1125899906842624 * ((if $a[50] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(49, $a, $ty)
    };
    (49, $a:ident, $ty:ty) => {
        562949953421312 * ((if $a[49] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(48, $a, $ty)
    };
    (48, $a:ident, $ty:ty) => {
        281474976710656 * ((if $a[48] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(47, $a, $ty)
    };
    (47, $a:ident, $ty:ty) => {
        140737488355328 * ((if $a[47] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(46, $a, $ty)
    };
    (46, $a:ident, $ty:ty) => {
        70368744177664 * ((if $a[46] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(45, $a, $ty)
    };
    (45, $a:ident, $ty:ty) => {
        35184372088832 * ((if $a[45] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(44, $a, $ty)
    };
    (44, $a:ident, $ty:ty) => {
        17592186044416 * ((if $a[44] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(43, $a, $ty)
    };
    (43, $a:ident, $ty:ty) => {
        8796093022208 * ((if $a[43] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(42, $a, $ty)
    };
    (42, $a:ident, $ty:ty) => {
        4398046511104 * ((if $a[42] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(41, $a, $ty)
    };
    (41, $a:ident, $ty:ty) => {
        2199023255552 * ((if $a[41] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(40, $a, $ty)
    };
    (40, $a:ident, $ty:ty) => {
        1099511627776 * ((if $a[40] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_little!(39, $a, $ty)
    };
    (39, $a:ident, $ty:ty) => {
        549755813888 * ((if $a[39] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(38, $a, $ty)
    };
    (38, $a:ident, $ty:ty) => {
        274877906944 * ((if $a[38] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(37, $a, $ty)
    };
    (37, $a:ident, $ty:ty) => {
        137438953472 * ((if $a[37] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(36, $a, $ty)
    };
    (36, $a:ident, $ty:ty) => {
        68719476736 * ((if $a[36] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(35, $a, $ty)
    };
    (35, $a:ident, $ty:ty) => {
        34359738368 * ((if $a[35] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(34, $a, $ty)
    };
    (34, $a:ident, $ty:ty) => {
        17179869184 * ((if $a[34] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(33, $a, $ty)
    };
    (33, $a:ident, $ty:ty) => {
        8589934592 * ((if $a[33] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(32, $a, $ty)
    };
    (32, $a:ident, $ty:ty) => {
        4294967296 * ((if $a[32] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(31, $a, $ty)
    };
    (31, $a:ident, $ty:ty) => {
        2147483648 * ((if $a[31] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(30, $a, $ty)
    };
    (30, $a:ident, $ty:ty) => {
        1073741824 * ((if $a[30] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(29, $a, $ty)
    };
    (29, $a:ident, $ty:ty) => {
        536870912 * ((if $a[29] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(28, $a, $ty)
    };
    (28, $a:ident, $ty:ty) => {
        268435456 * ((if $a[28] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(27, $a, $ty)
    };
    (27, $a:ident, $ty:ty) => {
        134217728 * ((if $a[27] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(26, $a, $ty)
    };
    (26, $a:ident, $ty:ty) => {
        67108864 * ((if $a[26] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(25, $a, $ty)
    };
    (25, $a:ident, $ty:ty) => {
        33554432 * ((if $a[25] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(24, $a, $ty)
    };
    (24, $a:ident, $ty:ty) => {
        16777216 * ((if $a[24] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(23, $a, $ty)
    };
    (23, $a:ident, $ty:ty) => {
        8388608 * ((if $a[23] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(22, $a, $ty)
    };
    (22, $a:ident, $ty:ty) => {
        4194304 * ((if $a[22] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(21, $a, $ty)
    };
    (21, $a:ident, $ty:ty) => {
        2097152 * ((if $a[21] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(20, $a, $ty)
    };
    (20, $a:ident, $ty:ty) => {
        1048576 * ((if $a[20] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(19, $a, $ty)
    };
    (19, $a:ident, $ty:ty) => {
        524288 * ((if $a[19] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(18, $a, $ty)
    };
    (18, $a:ident, $ty:ty) => {
        262144 * ((if $a[18] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(17, $a, $ty)
    };
    (17, $a:ident, $ty:ty) => {
        131072 * ((if $a[17] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(16, $a, $ty)
    };
    (16, $a:ident, $ty:ty) => {
        65536 * ((if $a[16] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(15, $a, $ty)
    };
    (15, $a:ident, $ty:ty) => {
        32768 * ((if $a[15] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(14, $a, $ty)
    };
    (14, $a:ident, $ty:ty) => {
        16384 * ((if $a[14] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(13, $a, $ty)
    };
    (13, $a:ident, $ty:ty) => {
        8192 * ((if $a[13] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(12, $a, $ty)
    };
    (12, $a:ident, $ty:ty) => {
        4096 * ((if $a[12] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(11, $a, $ty)
    };
    (11, $a:ident, $ty:ty) => {
        2048 * ((if $a[11] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(10, $a, $ty)
    };
    (10, $a:ident, $ty:ty) => {
        1024 * ((if $a[10] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(9, $a, $ty)
    };
    (9, $a:ident, $ty:ty) => {
        512 * ((if $a[9] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(8, $a, $ty)
    };
    (8, $a:ident, $ty:ty) => {
        256 * ((if $a[8] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(7, $a, $ty)
    };
    (7, $a:ident, $ty:ty) => {
        128 * ((if $a[7] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(6, $a, $ty)
    };
    (6, $a:ident, $ty:ty) => {
        64 * ((if $a[6] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(5, $a, $ty)
    };
    (5, $a:ident, $ty:ty) => {
        32 * ((if $a[5] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(4, $a, $ty)
    };
    (4, $a:ident, $ty:ty) => {
        16 * ((if $a[4] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(3, $a, $ty)
    };
    (3, $a:ident, $ty:ty) => {
        8 * ((if $a[3] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(2, $a, $ty)
    };
    (2, $a:ident, $ty:ty) => {
        4 * ((if $a[2] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(1, $a, $ty)
    };
    (1, $a:ident, $ty:ty) => {
        2 * ((if $a[1] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_little!(0, $a, $ty)
    };
    (0, $a:ident, $ty:ty) => {
        ((if $a[0] < 0 { 1 } else { 0 }) as $ty)
    };
}
pub(crate) use simd_bitmask_little;

/// Truncates an integer vector to a bitmask.
/// Macro for that expands to an expression which is equivalent to truncating an integer vector to a bitmask, as it would on big endian systems.
///
/// The macro takes 3 arguments.
/// The first is the highest index of the vector.
/// The second is the vector itself, which should just contain `0` and `!0`.
/// The third is the type to which the truncation happens, which should be atleast as wide as the number of elements in the vector.
///
/// Thus for example, to truncate the vector,
/// `let a : i32 = [!0, 0, 0, 0, 0, 0, 0, 0, !0, !0, 0, 0, 0, 0, !0, 0]`
/// to u16, you would call,
/// `simd_bitmask_big!(15, a, u16)`
/// to get,
/// `0b1000000011000010u16`
///
/// # Safety
/// The second argument must be a vector of signed integer types.

#[allow(unused)]
macro_rules! simd_bitmask_big {
    (63, $a:ident, $ty:ty) => {
        1 * ((if $a[63] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(62, $a, $ty)
    };
    (62, $a:ident, $ty:ty) => {
        2 * ((if $a[62] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(61, $a, $ty)
    };
    (61, $a:ident, $ty:ty) => {
        4 * ((if $a[61] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(60, $a, $ty)
    };
    (60, $a:ident, $ty:ty) => {
        8 * ((if $a[60] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(59, $a, $ty)
    };
    (59, $a:ident, $ty:ty) => {
        16 * ((if $a[59] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(58, $a, $ty)
    };
    (58, $a:ident, $ty:ty) => {
        32 * ((if $a[58] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(57, $a, $ty)
    };
    (57, $a:ident, $ty:ty) => {
        64 * ((if $a[57] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(56, $a, $ty)
    };
    (56, $a:ident, $ty:ty) => {
        128 * ((if $a[56] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(55, $a, $ty)
    };
    (55, $a:ident, $ty:ty) => {
        256 * ((if $a[55] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(54, $a, $ty)
    };
    (54, $a:ident, $ty:ty) => {
        512 * ((if $a[54] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(53, $a, $ty)
    };
    (53, $a:ident, $ty:ty) => {
        1024 * ((if $a[53] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(52, $a, $ty)
    };
    (52, $a:ident, $ty:ty) => {
        2048 * ((if $a[52] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(51, $a, $ty)
    };
    (51, $a:ident, $ty:ty) => {
        4096 * ((if $a[51] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(50, $a, $ty)
    };
    (50, $a:ident, $ty:ty) => {
        8192 * ((if $a[50] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(49, $a, $ty)
    };
    (49, $a:ident, $ty:ty) => {
        16384 * ((if $a[49] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(48, $a, $ty)
    };
    (48, $a:ident, $ty:ty) => {
        32768 * ((if $a[48] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(47, $a, $ty)
    };
    (47, $a:ident, $ty:ty) => {
        65536 * ((if $a[47] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(46, $a, $ty)
    };
    (46, $a:ident, $ty:ty) => {
        131072 * ((if $a[46] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(45, $a, $ty)
    };
    (45, $a:ident, $ty:ty) => {
        262144 * ((if $a[45] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(44, $a, $ty)
    };
    (44, $a:ident, $ty:ty) => {
        524288 * ((if $a[44] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(43, $a, $ty)
    };
    (43, $a:ident, $ty:ty) => {
        1048576 * ((if $a[43] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(42, $a, $ty)
    };
    (42, $a:ident, $ty:ty) => {
        2097152 * ((if $a[42] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(41, $a, $ty)
    };
    (41, $a:ident, $ty:ty) => {
        4194304 * ((if $a[41] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(40, $a, $ty)
    };
    (40, $a:ident, $ty:ty) => {
        8388608 * ((if $a[40] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(39, $a, $ty)
    };
    (39, $a:ident, $ty:ty) => {
        16777216 * ((if $a[39] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(38, $a, $ty)
    };
    (38, $a:ident, $ty:ty) => {
        33554432 * ((if $a[38] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(37, $a, $ty)
    };
    (37, $a:ident, $ty:ty) => {
        67108864 * ((if $a[37] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(36, $a, $ty)
    };
    (36, $a:ident, $ty:ty) => {
        134217728 * ((if $a[36] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(35, $a, $ty)
    };
    (35, $a:ident, $ty:ty) => {
        268435456 * ((if $a[35] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(34, $a, $ty)
    };
    (34, $a:ident, $ty:ty) => {
        536870912 * ((if $a[34] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(33, $a, $ty)
    };
    (33, $a:ident, $ty:ty) => {
        1073741824 * ((if $a[33] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(32, $a, $ty)
    };
    (32, $a:ident, $ty:ty) => {
        2147483648 * ((if $a[32] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(31, $a, $ty)
    };
    (31, $a:ident, $ty:ty) => {
        4294967296 * ((if $a[31] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(30, $a, $ty)
    };
    (30, $a:ident, $ty:ty) => {
        8589934592 * ((if $a[30] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(29, $a, $ty)
    };
    (29, $a:ident, $ty:ty) => {
        17179869184 * ((if $a[29] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(28, $a, $ty)
    };
    (28, $a:ident, $ty:ty) => {
        34359738368 * ((if $a[28] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(27, $a, $ty)
    };
    (27, $a:ident, $ty:ty) => {
        68719476736 * ((if $a[27] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(26, $a, $ty)
    };
    (26, $a:ident, $ty:ty) => {
        137438953472 * ((if $a[26] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(25, $a, $ty)
    };
    (25, $a:ident, $ty:ty) => {
        274877906944 * ((if $a[25] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(24, $a, $ty)
    };
    (24, $a:ident, $ty:ty) => {
        549755813888 * ((if $a[24] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(23, $a, $ty)
    };
    (23, $a:ident, $ty:ty) => {
        1099511627776 * ((if $a[23] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(22, $a, $ty)
    };
    (22, $a:ident, $ty:ty) => {
        2199023255552 * ((if $a[22] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(21, $a, $ty)
    };
    (21, $a:ident, $ty:ty) => {
        4398046511104 * ((if $a[21] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(20, $a, $ty)
    };
    (20, $a:ident, $ty:ty) => {
        8796093022208 * ((if $a[20] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(19, $a, $ty)
    };
    (19, $a:ident, $ty:ty) => {
        17592186044416 * ((if $a[19] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(18, $a, $ty)
    };
    (18, $a:ident, $ty:ty) => {
        35184372088832 * ((if $a[18] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(17, $a, $ty)
    };
    (17, $a:ident, $ty:ty) => {
        70368744177664 * ((if $a[17] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(16, $a, $ty)
    };
    (16, $a:ident, $ty:ty) => {
        140737488355328 * ((if $a[16] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(15, $a, $ty)
    };
    (15, $a:ident, $ty:ty) => {
        281474976710656 * ((if $a[15] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(14, $a, $ty)
    };
    (14, $a:ident, $ty:ty) => {
        562949953421312 * ((if $a[14] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(13, $a, $ty)
    };
    (13, $a:ident, $ty:ty) => {
        1125899906842624 * ((if $a[13] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(12, $a, $ty)
    };
    (12, $a:ident, $ty:ty) => {
        2251799813685248 * ((if $a[12] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(11, $a, $ty)
    };
    (11, $a:ident, $ty:ty) => {
        4503599627370496 * ((if $a[11] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(10, $a, $ty)
    };
    (10, $a:ident, $ty:ty) => {
        9007199254740992 * ((if $a[10] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(9, $a, $ty)
    };
    (9, $a:ident, $ty:ty) => {
        18014398509481984 * ((if $a[9] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(8, $a, $ty)
    };
    (8, $a:ident, $ty:ty) => {
        36028797018963968 * ((if $a[8] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(7, $a, $ty)
    };
    (7, $a:ident, $ty:ty) => {
        72057594037927936 * ((if $a[7] < 0 { 1 } else { 0 }) as $ty) + simd_bitmask_big!(6, $a, $ty)
    };
    (6, $a:ident, $ty:ty) => {
        144115188075855872 * ((if $a[6] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(5, $a, $ty)
    };
    (5, $a:ident, $ty:ty) => {
        288230376151711744 * ((if $a[5] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(4, $a, $ty)
    };
    (4, $a:ident, $ty:ty) => {
        576460752303423488 * ((if $a[4] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(3, $a, $ty)
    };
    (3, $a:ident, $ty:ty) => {
        1152921504606846976 * ((if $a[3] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(2, $a, $ty)
    };
    (2, $a:ident, $ty:ty) => {
        2305843009213693952 * ((if $a[2] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(1, $a, $ty)
    };
    (1, $a:ident, $ty:ty) => {
        4611686018427387904 * ((if $a[1] < 0 { 1 } else { 0 }) as $ty)
            + simd_bitmask_big!(0, $a, $ty)
    };
    (0, $a:ident, $ty:ty) => {
        9223372036854775808 * ((if $a[0] < 0 { 1 } else { 0 }) as $ty)
    };
}
#[allow(unused)]
pub(crate) use simd_bitmask_big;

/// Selects elements from a mask.
///
/// For each element, if the corresponding value in `mask` is `!0`, select the element from
/// `if_true`.  If the corresponding value in `mask` is `0`, select the element from
/// `if_false`.
///
/// # Safety
/// `mask` must only contain `0` and `!0`.

pub fn simd_select<const N: u32, T1: Eq + MachineInteger, T2: Copy>(
    mask: FunArray<N, T1>,
    if_true: FunArray<N, T2>,
    if_false: FunArray<N, T2>,
) -> FunArray<N, T2> {
    FunArray::from_fn(|i| {
        if mask[i] == T1::ONES {
            if_true[i]
        } else {
            if_false[i]
        }
    })
}
