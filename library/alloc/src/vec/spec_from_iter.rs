use core::mem::ManuallyDrop;
use core::ptr::{self};

use super::{IntoIter, SpecExtend, SpecFromIterNested, Vec};

/// Specialization trait used for Vec::from_iter
///
/// ## The delegation graph:
///
/// ```text
/// +-------------+
/// |FromIterator |
/// +-+-----------+
///   |
///   v
/// +-+---------------------------------+  +---------------------+
/// |SpecFromIter                    +---->+SpecFromIterNested   |
/// |where I:                        |  |  |where I:             |
/// |  Iterator (default)------------+  |  |  Iterator (default) |
/// |  vec::IntoIter                 |  |  |  TrustedLen         |
/// |  InPlaceCollect--(fallback to)-+  |  +---------------------+
/// +-----------------------------------+
/// ```
pub(super) trait SpecFromIter<T, I> {
    fn from_iter(iter: I) -> Self;
}

impl<T, I> SpecFromIter<T, I> for Vec<T>
where
    I: Iterator<Item = T>,
{
    default fn from_iter(iterator: I) -> Self {
        SpecFromIterNested::from_iter(iterator)
    }
}

impl<T> SpecFromIter<T, IntoIter<T>> for Vec<T> {
    fn from_iter(iterator: IntoIter<T>) -> Self {
        // A common case is passing a vector into a function which immediately
        // re-collects into a vector. We can short circuit this if the IntoIter
        // has not been advanced at all.
        // When it has been advanced We can also reuse the memory and move the data to the front.
        // But we only do so when the resulting Vec wouldn't have more unused capacity
        // than creating it through the generic FromIterator implementation would. That limitation
        // is not strictly necessary as Vec's allocation behavior is intentionally unspecified.
        // But it is a conservative choice.
        let has_advanced = iterator.buf != iterator.ptr;
        if !has_advanced || iterator.len() >= iterator.cap / 2 {
            unsafe {
                let it = ManuallyDrop::new(iterator);
                if has_advanced {
                    ptr::copy(it.ptr.as_ptr(), it.buf.as_ptr(), it.len());
                }
                return Vec::from_parts(it.buf, it.len(), it.cap);
            }
        }

        let mut vec = Vec::new();
        // must delegate to spec_extend() since extend() itself delegates
        // to spec_from for empty Vecs
        vec.spec_extend(iterator);
        vec
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

    macro_rules! check_spec_from_iter_with_ty {
        ($mod_name:ident, $ty:ty) => {
            mod $mod_name {
                use super::*;

                // Tests SpecFromIter for IntoIter (the specialized path)
                #[kani::proof]
                fn check_from_iter_into_iter() {
                    let v: Vec<$ty> = any_vec::<$ty, MAX_LEN>();
                    let orig_len = v.len();
                    let iter = v.into_iter();
                    let result: Vec<$ty> =
                        <Vec<$ty> as SpecFromIter<$ty, IntoIter<$ty>>>::from_iter(iter);
                    assert!(result.len() == orig_len);
                }

                // Tests SpecFromIter for IntoIter after advancing
                #[kani::proof]
                fn check_from_iter_into_iter_advanced() {
                    let v: Vec<$ty> = any_vec::<$ty, MAX_LEN>();
                    let orig_len = v.len();
                    let mut iter = v.into_iter();
                    let skip: usize = kani::any();
                    kani::assume(skip <= orig_len);
                    let _ = iter.advance_by(skip);
                    let remaining = orig_len - skip;
                    let result: Vec<$ty> =
                        <Vec<$ty> as SpecFromIter<$ty, IntoIter<$ty>>>::from_iter(iter);
                    assert!(result.len() == remaining);
                }
            }
        };
    }

    check_spec_from_iter_with_ty!(verify_spec_from_iter_u8, u8);
    check_spec_from_iter_with_ty!(verify_spec_from_iter_unit, ());
    check_spec_from_iter_with_ty!(verify_spec_from_iter_char, char);
    check_spec_from_iter_with_ty!(verify_spec_from_iter_tup, (char, u8));
}
