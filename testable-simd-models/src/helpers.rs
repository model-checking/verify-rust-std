#[cfg(test)]
pub mod test {
    use crate::abstractions::{bit::Bit, bitvec::BitVec, funarr::FunArray};
    use rand::prelude::*;
    use std::sync::{LazyLock, Mutex};

    static RNG: LazyLock<Mutex<StdRng>> = LazyLock::new(|| {
        let seed = rand::rng().random();
        println!("\nRandomness seed set to: {:?}", seed);
        Mutex::new(StdRng::from_seed(seed))
    });

    /// Helper trait to generate random values
    pub trait HasRandom {
        fn random() -> Self;
    }
    macro_rules! mk_has_random {
        ($($ty:ty),*) => {
            $(impl HasRandom for $ty {
                fn random() -> Self {
                    RNG.lock().unwrap().random()
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

    impl HasRandom for f32 {
        fn random() -> Self {
            u32::random() as f32
        }
    }

    impl HasRandom for f64 {
        fn random() -> Self {
            u64::random() as f64
        }
    }

    impl HasRandom for Bit {
        fn random() -> Self {
            crate::abstractions::bit::Bit::from(bool::random())
        }
    }
    impl<const N: u32> HasRandom for BitVec<N> {
        fn random() -> Self {
            Self::from_fn(|_| Bit::random())
        }
    }

    impl<const N: u32, T: HasRandom> HasRandom for FunArray<N, T> {
        fn random() -> Self {
            FunArray::from_fn(|_| T::random())
        }
    }
}

#[cfg(test)]
pub use test::*;
