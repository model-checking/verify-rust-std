//! This module implements a fixed-size array wrapper with functional semantics
//! which are used in formulating abstractions.

/// `FunArray<N, T>` represents an array of `T` values of length `N`, where `N` is a compile-time constant.
/// Internally, it uses a fixed-length array of `Option<T>` with a maximum capacity of 512 elements.
/// Unused elements beyond `N` are filled with `None`.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct FunArray<const N: u64, T>([Option<T>; 512]);

impl<const N: u64, T> FunArray<N, T> {
    /// Gets a reference to the element at index `i`.
    pub fn get(&self, i: u64) -> &T {
        self.0[i as usize].as_ref().unwrap()
    }
    /// Constructor for FunArray. `FunArray<N,T>::from_fn` constructs a funarray out of a function that takes usizes smaller than `N` and produces an element of type T.
    pub fn from_fn<F: Fn(u64) -> T>(f: F) -> Self {
        // let vec = (0..N).map(f).collect();
        let arr = core::array::from_fn(|i| {
            if (i as u64) < N {
                Some(f(i as u64))
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

impl<const N: u64, T: Clone> TryFrom<Vec<T>> for FunArray<N, T> {
    type Error = ();
    fn try_from(v: Vec<T>) -> Result<Self, ()> {
        if (v.len() as u64) < N {
            Err(())
        } else {
            Ok(Self::from_fn(|i| v[i as usize].clone()))
        }
    }
}

impl<const N: u64, T: core::fmt::Debug + Clone> core::fmt::Debug for FunArray<N, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.as_vec())
    }
}

impl<const N: u64, T> core::ops::Index<u64> for FunArray<N, T> {
    type Output = T;

    fn index(&self, index: u64) -> &Self::Output {
        self.get(index)
    }
}
