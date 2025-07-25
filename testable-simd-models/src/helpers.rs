#[cfg(test)]
pub mod test {
    use crate::abstractions::{bit::Bit, bitvec::BitVec, funarr::FunArray};
    use rand::prelude::*;

    /// Helper trait to generate random values
    pub trait HasRandom {
        fn random() -> Self;
    }
    macro_rules! mk_has_random {
        ($($ty:ty),*) => {
            $(impl HasRandom for $ty {
                fn random() -> Self {
                    let mut rng = rand::rng();
                    rng.random()
                }
            })*
        };
    }

    mk_has_random!(bool);
    mk_has_random!(i8, i16, i32, i64, i128);
    mk_has_random!(u8, u16, u32, u64, u128);

    impl HasRandom for isize {
        fn random() -> Self {
            i128::random() as isize
        }
    }
    impl HasRandom for usize {
        fn random() -> Self {
            i128::random() as usize
        }
    }

    impl HasRandom for Bit {
        fn random() -> Self {
            crate::abstractions::bit::Bit::from(bool::random())
        }
    }
    impl<const N: u64> HasRandom for BitVec<N> {
        fn random() -> Self {
            Self::from_fn(|_| Bit::random())
        }
    }

    impl<const N: u64, T: HasRandom> HasRandom for FunArray<N, T> {
        fn random() -> Self {
            FunArray::from_fn(|_| T::random())
        }
    }
}

#[cfg(test)]
pub use test::*;
