use core::iter::TrustedLen;
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
mod verify {
    use core::kani;

    use super::SpecFromIterNested;
    use crate::vec::Vec;

    // from_iter (default, non-TrustedLen): unroll first + with_capacity(MIN_NON_ZERO_CAP=8)
    // + spec_extend the rest. A from_fn (non-TrustedLen) source <= 4 stays under cap 8,
    // so no reallocation fires here; the growth branch routes through extend_desugared
    // (a Challenge 23 target) and exceeds the CI-standard object-bits 12 budget at
    // larger sizes (measured). Real body; postcondition checks the produced length.
    #[kani::proof]
    #[kani::unwind(8)]
    fn check_from_iter_default_u8() {
        let n: usize = kani::any();
        kani::assume(n <= 4);
        kani::cover(n == 4, "non-vacuity: the max-length source is reachable");
        let mut i = 0usize;
        let iter = core::iter::from_fn(move || {
            if i < n {
                i += 1;
                Some(kani::any::<u8>())
            } else {
                None
            }
        });
        let v: Vec<u8> = <Vec<u8> as SpecFromIterNested<u8, _>>::from_iter(iter);
        assert!(v.len() == n);
    }
}
