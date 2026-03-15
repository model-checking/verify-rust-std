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
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::kani;

    use super::*;

    const MAX_LEN: usize = 3;

    fn any_vec<T: kani::Arbitrary, const N: usize>() -> Vec<T> {
        let arr: [T; N] = kani::Arbitrary::any_array();
        let mut v = Vec::from(arr);
        let new_len: usize = kani::any();
        kani::assume(new_len <= v.len());
        v.truncate(new_len);
        v
    }

    macro_rules! check_spec_from_iter_nested_with_ty {
        ($mod_name:ident, $ty:ty) => {
            mod $mod_name {
                use super::*;

                // The default SpecFromIterNested::from_iter delegates to
                // extend_desugared via SpecExtend. We test it by passing
                // a regular iterator (vec's IntoIter is NOT TrustedLen for
                // this path, so we use a .map() to strip TrustedLen).
                #[kani::proof]
                fn check_from_iter_nested_default() {
                    let v: Vec<$ty> = any_vec::<$ty, MAX_LEN>();
                    let orig_len = v.len();
                    // .map(|x| x) strips TrustedLen, forcing the default impl
                    let iter = v.into_iter().map(|x| x);
                    let result: Vec<$ty> =
                        <Vec<$ty> as SpecFromIterNested<$ty, _>>::from_iter(iter);
                    assert!(result.len() == orig_len);
                }
            }
        };
    }

    check_spec_from_iter_nested_with_ty!(verify_from_iter_nested_u8, u8);
    check_spec_from_iter_nested_with_ty!(verify_from_iter_nested_unit, ());
    check_spec_from_iter_nested_with_ty!(verify_from_iter_nested_char, char);
    check_spec_from_iter_nested_with_ty!(verify_from_iter_nested_tup, (char, u8));
}
