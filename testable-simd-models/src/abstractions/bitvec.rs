//! This module provides a specification-friendly bit vector type.
use super::bit::{Bit, MachineNumeric};
use super::funarr::*;

use std::fmt::Formatter;

/// A fixed-size bit vector type.
///
/// `BitVec<N>` is a specification-friendly, fixed-length bit vector that internally
/// stores an array of [`Bit`] values, where each `Bit` represents a single binary digit (0 or 1).
///
/// This type provides several utility methods for constructing and converting bit vectors:
///
/// The [`Debug`] implementation for `BitVec` pretty-prints the bits in groups of eight,
/// making the bit pattern more human-readable. The type also implements indexing,
/// allowing for easy access to individual bits.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct BitVec<const N: u32>(FunArray<N, Bit>);

impl<const N: u32> BitVec<N> {
    #[allow(non_snake_case)]
    pub fn ZERO() -> Self {
        Self::from_fn(|_| Bit::Zero)
    }
}

/// Pretty prints a bit slice by group of 8
fn bit_slice_to_string(bits: &[Bit]) -> String {
    bits.iter()
        .map(|bit| match bit {
            Bit::Zero => '0',
            Bit::One => '1',
        })
        .collect::<Vec<_>>()
        .chunks(8)
        .map(|bits| bits.iter().collect::<String>())
        .map(|s| format!("{s} "))
        .collect::<String>()
        .trim()
        .into()
}

impl<const N: u32> core::fmt::Debug for BitVec<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", bit_slice_to_string(&self.0.as_vec()))
    }
}

impl<const N: u32> core::ops::Index<u32> for BitVec<N> {
    type Output = Bit;
    fn index(&self, index: u32) -> &Self::Output {
        self.0.get(index)
    }
}

/// Convert a bit slice into an unsigned number.

fn u128_int_from_bit_slice(bits: &[Bit]) -> u128 {
    bits.iter()
        .enumerate()
        .map(|(i, bit)| u128::from(*bit) << i)
        .sum::<u128>()
}

/// Convert a bit slice into a machine integer of type `T`.
fn int_from_bit_slice<T: MachineNumeric + Copy>(bits: &[Bit]) -> T {
    debug_assert!(bits.len() <= T::BITS as usize);
    let result = if T::SIGNED {
        let is_negative = matches!(bits[T::BITS as usize - 1], Bit::One);
        let s = u128_int_from_bit_slice(&bits[0..T::BITS as usize - 1]) as i128;
        if is_negative {
            s + (-2i128).pow(T::BITS - 1)
        } else {
            s
        }
    } else {
        u128_int_from_bit_slice(bits) as i128
    };
    T::from_u128(result as u128)
}
impl<const N: u32> BitVec<N> {
    /// Constructor for BitVec. `BitVec::<N>::from_fn` constructs a bitvector out of a function that takes usizes smaller than `N` and produces bits.
    pub fn from_fn<F: Fn(u32) -> Bit>(f: F) -> Self {
        Self(FunArray::from_fn(f))
    }
    /// Convert a slice of machine integers where only the `d` least significant bits are relevant.
    pub fn from_slice<T: MachineNumeric + Copy>(x: &[T], d: u32) -> Self {
        Self::from_fn(|i| Bit::nth_bit::<T>(x[(i / d) as usize], (i % d) as usize))
    }

    /// Construct a BitVec out of a machine integer.
    pub fn from_int<T: MachineNumeric + Copy>(n: T) -> Self {
        Self::from_slice::<T>(&[n], T::BITS as u32)
    }

    /// Convert a BitVec into a machine integer of type `T`.
    pub fn to_int<T: MachineNumeric + Copy>(self) -> T {
        int_from_bit_slice(&self.0.as_vec())
    }

    /// Convert a BitVec into a vector of machine integers of type `T`.
    pub fn to_vec<T: MachineNumeric + Copy>(&self) -> Vec<T> {
        self.0
            .as_vec()
            .chunks(T::BITS as usize)
            .map(int_from_bit_slice)
            .collect()
    }
}

impl<const N: u32> BitVec<N> {
    pub fn chunked_shift<const CHUNK: u32, const SHIFTS: u32>(
        self,
        shl: FunArray<SHIFTS, i128>,
    ) -> BitVec<N> {
        fn chunked_shift<const N: u32, const CHUNK: u32, const SHIFTS: u32>(
            bitvec: BitVec<N>,
            shl: FunArray<SHIFTS, i128>,
        ) -> BitVec<N> {
            BitVec::from_fn(|i| {
                let nth_bit = i % CHUNK;
                let nth_chunk = i / CHUNK;
                let shift: i128 = if nth_chunk < SHIFTS {
                    shl[nth_chunk]
                } else {
                    0
                };
                let local_index = (nth_bit as i128).wrapping_sub(shift);
                if local_index < CHUNK as i128 && local_index >= 0 {
                    let local_index = local_index as u32;
                    bitvec[nth_chunk * CHUNK + local_index]
                } else {
                    Bit::Zero
                }
            })
        }
        chunked_shift::<N, CHUNK, SHIFTS>(self, shl)
    }

    /// Folds over the array, accumulating a result.
    ///
    /// # Arguments
    /// * `init` - The initial value of the accumulator.
    /// * `f` - A function combining the accumulator and each element.
    pub fn fold<A>(&self, init: A, f: fn(A, Bit) -> A) -> A {
        self.0.fold(init, f)
    }
}
