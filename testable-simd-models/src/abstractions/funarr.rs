//! This module implements a fixed-size array wrapper with functional semantics
//! which are used in formulating abstractions.

use crate::abstractions::bit::MachineNumeric;

/// `FunArray<N, T>` represents an array of `T` values of length `N`, where `N` is a compile-time constant.
/// Internally, it uses a fixed-length array of `Option<T>` with a maximum capacity of 512 elements.
/// Unused elements beyond `N` are filled with `None`.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct FunArray<const N: u32, T>([Option<T>; 512]);

impl<const N: u32, T> FunArray<N, T> {
    /// Gets a reference to the element at index `i`.
    pub fn get(&self, i: u32) -> &T {
        self.0[i as usize].as_ref().unwrap()
    }
    /// Constructor for FunArray. `FunArray<N,T>::from_fn` constructs a funarray out of a function that takes usizes smaller than `N` and produces an element of type T.
    pub fn from_fn<F: Fn(u32) -> T>(f: F) -> Self {
        // let vec = (0..N).map(f).collect();
        let arr = core::array::from_fn(|i| {
            if (i as u32) < N {
                Some(f(i as u32))
            } else {
                None
            }
        });
        Self(arr)
    }

    /// Converts the `FunArray` into a `Vec<T>`.
    pub fn as_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.0[0..(N as usize)]
            .iter()
            .cloned()
            .map(|x| x.unwrap())
            .collect()
    }

    /// Folds over the array, accumulating a result.
    ///
    /// # Arguments
    /// * `init` - The initial value of the accumulator.
    /// * `f` - A function combining the accumulator and each element.
    pub fn fold<A>(&self, mut init: A, f: fn(A, T) -> A) -> A
    where
        T: Clone,
    {
        for i in 0..N {
            init = f(init, self[i].clone());
        }
        init
    }
}

impl<const N: u32, T: MachineNumeric> FunArray<N, T> {
    #[allow(non_snake_case)]
    pub fn ZERO() -> Self {
        Self::from_fn(|_| T::ZEROS)
    }
}

impl<const N: u32, T: Clone> TryFrom<Vec<T>> for FunArray<N, T> {
    type Error = ();
    fn try_from(v: Vec<T>) -> Result<Self, ()> {
        if (v.len() as u32) < N {
            Err(())
        } else {
            Ok(Self::from_fn(|i| v[i as usize].clone()))
        }
    }
}

impl<const N: u32, T: core::fmt::Debug + Clone> core::fmt::Debug for FunArray<N, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.as_vec())
    }
}

impl<const N: u32, T> core::ops::Index<u32> for FunArray<N, T> {
    type Output = T;

    fn index(&self, index: u32) -> &Self::Output {
        self.get(index)
    }
}

impl<T: Copy> FunArray<1, T> {
    pub fn new(x: T) -> Self {
        let v = [x];
        Self::from_fn(|i| v[i as usize])
    }
}

impl<T: Copy> FunArray<2, T> {
    pub fn new(x0: T, x1: T) -> Self {
        let v = [x0, x1];
        Self::from_fn(|i| v[i as usize])
    }
}

impl<T: Copy> FunArray<4, T> {
    pub fn new(x0: T, x1: T, x2: T, x3: T) -> Self {
        let v = [x0, x1, x2, x3];
        Self::from_fn(|i| v[i as usize])
    }
}

impl<T: Copy> FunArray<8, T> {
    pub fn new(x0: T, x1: T, x2: T, x3: T, x4: T, x5: T, x6: T, x7: T) -> Self {
        let v = [x0, x1, x2, x3, x4, x5, x6, x7];
        Self::from_fn(|i| v[i as usize])
    }
}

impl<T: Copy> FunArray<16, T> {
    pub fn new(
        x0: T,
        x1: T,
        x2: T,
        x3: T,
        x4: T,
        x5: T,
        x6: T,
        x7: T,
        x8: T,
        x9: T,
        x10: T,
        x11: T,
        x12: T,
        x13: T,
        x14: T,
        x15: T,
    ) -> Self {
        let v = [
            x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
        ];
        Self::from_fn(|i| v[i as usize])
    }
}

impl<T: Copy> FunArray<32, T> {
    pub fn new(
        x0: T,
        x1: T,
        x2: T,
        x3: T,
        x4: T,
        x5: T,
        x6: T,
        x7: T,
        x8: T,
        x9: T,
        x10: T,
        x11: T,
        x12: T,
        x13: T,
        x14: T,
        x15: T,
        x16: T,
        x17: T,
        x18: T,
        x19: T,
        x20: T,
        x21: T,
        x22: T,
        x23: T,
        x24: T,
        x25: T,
        x26: T,
        x27: T,
        x28: T,
        x29: T,
        x30: T,
        x31: T,
    ) -> Self {
        let v = [
            x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18,
            x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31,
        ];
        Self::from_fn(|i| v[i as usize])
    }
}
