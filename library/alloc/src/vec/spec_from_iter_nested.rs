use core::iter::TrustedLen;
#[cfg(kani)]
use core::kani;
use core::{cmp, ptr};

use super::{SpecExtend, Vec};
use crate::raw_vec::RawVec;

/// Another specialization trait for Vec::from_iter
/// necessary to manually prioritize overlapping specializations
/// see [`SpecFromIter`](super::SpecFromIter) for details.
pub(super) trait SpecFromIterNested<T, I> {
    fn from_iter(iter: I) -> Self;
}

impl<T, I> SpecFromIterNested<T, I> for Vec<T>
where
    I: Iterator<Item = T>,
{
    default fn from_iter(mut iterator: I) -> Self {
        // Unroll the first iteration, as the vector is going to be
        // expanded on this iteration in every case when the iterable is not
        // empty, but the loop in extend_desugared() is not going to see the
        // vector being full in the few subsequent loop iterations.
        // So we get better branch prediction.
        let mut vector = match iterator.next() {
            None => return Vec::new(),
            Some(element) => {
                let (lower, _) = iterator.size_hint();
                let initial_capacity =
                    cmp::max(RawVec::<T>::MIN_NON_ZERO_CAP, lower.saturating_add(1));
                let mut vector = Vec::with_capacity(initial_capacity);
                unsafe {
                    // SAFETY: We requested capacity at least 1
                    ptr::write(vector.as_mut_ptr(), element);
                    vector.set_len(1);
                }
                vector
            }
        };
        // must delegate to spec_extend() since extend() itself delegates
        // to spec_from for empty Vecs
        <Vec<T> as SpecExtend<T, I>>::spec_extend(&mut vector, iterator);
        vector
    }
}

impl<T, I> SpecFromIterNested<T, I> for Vec<T>
where
    I: TrustedLen<Item = T>,
{
    fn from_iter(iterator: I) -> Self {
        let mut vector = match iterator.size_hint() {
            (_, Some(upper)) => Vec::with_capacity(upper),
            // TrustedLen contract guarantees that `size_hint() == (_, None)` means that there
            // are more than `usize::MAX` elements.
            // Since the previous branch would eagerly panic if the capacity is too large
            // (via `with_capacity`) we do the same here.
            _ => panic!("capacity overflow"),
        };
        // reuse extend specialization for TrustedLen
        vector.spec_extend(iterator);
        vector
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::super::Vec;
    use super::super::kani_vec_harness_helpers::*;
    use super::*;

    // Harness for `SpecFromIterNested::from_iter`
    macro_rules! gen_from_iter_default_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            #[kani::unwind(72)]
            pub fn $name() {
                let len = kani::any_where(|len: &usize| *len <= 64);
                let iter = UnderreportingIter::<$ty>::new(len);
                let vector = <Vec<$ty> as SpecFromIterNested<$ty, _>>::from_iter(iter);
                assert!(
                    vector.len() == len,
                    "SpecFromIterNested: resulting Vec has the wrong length"
                );
                assert!(
                    vector.capacity() >= vector.len(),
                    "SpecFromIterNested: resulting Vec has insufficient capacity"
                );
                if core::mem::size_of::<$ty>() != 0 {
                    let initial_capacity = core::cmp::max(RawVec::<$ty>::MIN_NON_ZERO_CAP, 1);
                    kani::cover(
                        len > initial_capacity,
                        "SpecFromIterNested: extend_desugared growth path",
                    );
                }
            }
        };
    }

    gen_from_iter_default_harness!(harness_from_iter_default_u8, u8);
    gen_from_iter_default_harness!(harness_from_iter_default_u64, u64);
    gen_from_iter_default_harness!(harness_from_iter_default_unit, ());
    gen_from_iter_default_harness!(harness_from_iter_default_array, [u8; 4]);
    gen_from_iter_default_harness!(harness_from_iter_default_bool, bool);
    gen_from_iter_default_harness!(harness_from_iter_default_al16, Al16);
}
