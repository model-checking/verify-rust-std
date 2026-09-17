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
mod verify {
    use core::kani;

    use super::SpecFromIter;
    use crate::vec::{IntoIter, Vec};

    // from_iter (IntoIter specialization): reuse-allocation path (from_parts /
    // ptr::copy-to-front) — object-light, no reallocation. Real body,
    // symbolic-length source; postcondition checks length and element value
    // at a symbolic index.
    #[kani::proof]
    #[kani::unwind(8)]
    fn check_from_iter_intoiter_u8() {
        let arr: [u8; 64] = kani::any();
        let s = kani::slice::any_slice_of_array(&arr);
        let n = s.len();
        let src: IntoIter<u8> = s.to_vec().into_iter();
        let v: Vec<u8> = <Vec<u8> as SpecFromIter<u8, IntoIter<u8>>>::from_iter(src);
        assert!(v.len() == n);
        if n > 0 {
            let j: usize = kani::any();
            kani::assume(j < n);
            assert!(v[j] == s[j]);
        }
    }
}
