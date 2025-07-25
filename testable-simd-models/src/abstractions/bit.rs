//! # Bit Manipulation and Machine Integer Utilities
//!
//! This module provides utilities for working with individual bits and machine integer types.
//! It defines a [`Bit`] enum to represent a single bit (`0` or `1`) along with convenient
//! conversion implementations between `Bit`, [`bool`], and various primitive integer types.
//!
//! In addition, the module introduces the [`MachineInteger`] trait which abstracts over
//! integer types, providing associated constants:
//!
//! - `BITS`: The size of the integer type in bits.
//! - `SIGNED`: A flag indicating whether the type is signed.
//!
//! The [`Bit`] type includes methods for extracting the value of a specific bit from an integer.
//! For example, [`Bit::of_int`] returns the bit at a given position for a provided integer,
//! handling both positive and negative values (assuming a two's complement representation).
//!
//! # Examples
//!
//! ```rust
//! use testable_simd_models::abstractions::bit::{Bit, MachineInteger};
//!
//! // Extract the 3rd bit (0-indexed) from an integer.
//! let bit = Bit::of_int(42, 2);
//! println!("The extracted bit is: {:?}", bit);
//!
//! // Convert Bit to a primitive integer type.
//! let num: u8 = bit.into();
//! println!("As an integer: {}", num);
//! ```
//!
//! [`bool`]: https://doc.rust-lang.org/std/primitive.bool.html
//! [`Bit::of_int`]: enum.Bit.html#method.of_int

/// Represent a bit: `0` or `1`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Bit {
    Zero,
    One,
}
impl std::ops::BitAnd for Bit {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        match self {
            Bit::Zero => Bit::Zero,
            Bit::One => rhs,
        }
    }
}

impl std::ops::BitOr for Bit {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        match self {
            Bit::Zero => rhs,
            Bit::One => Bit::One,
        }
    }
}

impl std::ops::BitXor for Bit {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Bit::Zero, Bit::Zero) => Bit::Zero,
            (Bit::One, Bit::One) => Bit::Zero,
            _ => Bit::One,
        }
    }
}

impl std::ops::Neg for Bit {
    type Output = Self;
    fn neg(self) -> Self {
        match self {
            Bit::One => Bit::Zero,
            Bit::Zero => Bit::One,
        }
    }
}
macro_rules! generate_from_bit_impls {
    ($($ty:ident),*) => {
        $(impl From<Bit> for $ty {
            fn from(bit: Bit) -> Self {
                bool::from(bit) as $ty
            }
        })*
    };
}
generate_from_bit_impls!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

impl From<Bit> for bool {
    fn from(bit: Bit) -> Self {
        match bit {
            Bit::Zero => false,
            Bit::One => true,
        }
    }
}

impl From<bool> for Bit {
    fn from(b: bool) -> Bit {
        match b {
            false => Bit::Zero,
            true => Bit::One,
        }
    }
}

/// A trait for types that represent machine integers.
pub trait MachineInteger {
    /// The size of this integer type in bits.
    fn bits() -> u32;

    /// The signedness of this integer type.
    const SIGNED: bool;
    /// Element of the integer type with every bit as 0.
    const ZEROS: Self;
    /// Element of the integer type with every bit as 1.
    const ONES: Self;
    /// Minimum value of the integer type.
    const MIN: Self;
    /// Maximum value of the integer type.
    const MAX: Self;

    /// Implements functionality for `simd_add` in `crate::abstractions::simd`.
    fn wrapping_add(self, rhs: Self) -> Self;
    /// Implements functionality for `simd_sub` in `crate::abstractions::simd`.
    fn wrapping_sub(self, rhs: Self) -> Self;
    /// Implements functionality for `simd_mul` in `crate::abstractions::simd`.
    fn overflowing_mul(self, rhs: Self) -> Self;
    /// Implements functionality for `simd_saturating_add` in `crate::abstractions::simd`.
    fn saturating_add(self, rhs: Self) -> Self;
    /// Implements functionality for `simd_saturating_sub` in `crate::abstractions::simd`.
    fn saturating_sub(self, rhs: Self) -> Self;
    /// Implements functionality for `simd_abs_diff` in `crate::abstractions::simd`.
    fn absolute_diff(self, rhs: Self) -> Self;
    /// Implements functionality for `simd_abs` in `crate::abstractions::simd`.
    fn absolute_val(self) -> Self;
}

macro_rules! generate_imachine_integer_impls {
    ($($ty:ident),*) => {
        $(
	    impl MachineInteger for $ty {
		const SIGNED: bool = true;
		const ZEROS: $ty = 0;
		const ONES: $ty = -1;
		const MIN: $ty = $ty::MIN;
		const MAX: $ty = $ty::MAX;
		fn bits() -> u32 { $ty::BITS }
		fn wrapping_add(self, rhs: Self) -> Self { self.wrapping_add(rhs) }
		fn wrapping_sub(self, rhs: Self) -> Self { self.wrapping_sub(rhs) }
		fn overflowing_mul(self, rhs: Self) -> Self { self.overflowing_mul(rhs).0 }
		fn saturating_add(self, rhs: Self) -> Self { self.saturating_add(rhs)}
		fn saturating_sub(self, rhs: Self) -> Self { self.saturating_sub(rhs) }
		fn absolute_diff(self, rhs: Self) -> Self {if self > rhs {$ty::wrapping_sub(self, rhs)} else {$ty::wrapping_sub(rhs, self)}}
		fn absolute_val(self) -> Self {if self == $ty::MIN {self} else {self.abs()}}
            })*
    };
}

macro_rules! generate_umachine_integer_impls {
    ($($ty:ident),*) => {
        $(
	    impl MachineInteger for $ty {
		const SIGNED: bool = false;
		const ZEROS: $ty = 0;
		const ONES: $ty = $ty::MAX;
		const MIN: $ty = $ty::MIN;
		const MAX: $ty = $ty::MAX;


		fn bits() -> u32 { $ty::BITS }
		fn wrapping_add(self, rhs: Self) -> Self { self.wrapping_add(rhs) }
		fn wrapping_sub(self, rhs: Self) -> Self { self.wrapping_sub(rhs) }
		fn overflowing_mul(self, rhs: Self) -> Self { self.overflowing_mul(rhs).0 }
		fn saturating_add(self, rhs: Self) -> Self { self.saturating_add(rhs)}
		fn saturating_sub(self, rhs: Self) -> Self { self.saturating_sub(rhs)}
		fn absolute_diff(self, rhs: Self) -> Self {if self > rhs {self - rhs} else {rhs - self}}
		fn absolute_val(self) -> Self {self}
        })*
    };
}
generate_imachine_integer_impls!(i8, i16, i32, i64, i128);
generate_umachine_integer_impls!(u8, u16, u32, u64, u128);

impl Bit {
    fn of_raw_int(x: u128, nth: u32) -> Self {
        if x / 2u128.pow(nth) % 2 == 1 {
            Self::One
        } else {
            Self::Zero
        }
    }

    pub fn of_int<T: Into<i128> + MachineInteger>(x: T, nth: u32) -> Bit {
        let x: i128 = x.into();
        if x >= 0 {
            Self::of_raw_int(x as u128, nth)
        } else {
            Self::of_raw_int((2i128.pow(T::bits()) + x) as u128, nth)
        }
    }
}
