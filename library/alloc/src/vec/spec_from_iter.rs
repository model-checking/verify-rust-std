#[cfg(kani)]
use core::kani;
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
    use super::super::kani_vec_harness_helpers::*;
    use super::*;

    // Harnesses for `SpecFromIter::from_iter` with `IntoIter`
    macro_rules! gen_from_iter_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let expected_len = iter.len();
                let original_cap = iter.cap;
                let original_buf = iter.buf;
                let has_advanced = iter.buf != iter.ptr;
                // Mirrors the specialization's allocation-reuse condition.
                let should_reuse = !has_advanced || expected_len >= original_cap / 2;
                let vec = <Vec<$ty> as SpecFromIter<$ty, IntoIter<$ty>>>::from_iter(iter);
                assert!(
                    vec.len() == expected_len,
                    "SpecFromIter<IntoIter>: resulting Vec has the wrong length"
                );
                assert!(
                    vec.capacity() >= vec.len(),
                    "SpecFromIter<IntoIter>: resulting Vec has insufficient capacity"
                );
                if should_reuse {
                    assert!(
                        vec.as_ptr() == original_buf.as_ptr(),
                        "SpecFromIter<IntoIter>: reusable allocation was not preserved"
                    );
                    assert!(
                        vec.capacity() == original_cap,
                        "SpecFromIter<IntoIter>: reused allocation has the wrong capacity"
                    );
                }
                kani::cover(!has_advanced, "SpecFromIter<IntoIter>: direct allocation reuse");
                if core::mem::size_of::<$ty>() != 0 {
                    kani::cover(
                        has_advanced && expected_len >= original_cap / 2,
                        "SpecFromIter<IntoIter>: compact and reuse allocation",
                    );
                    kani::cover(
                        has_advanced && expected_len > 0 && expected_len >= original_cap / 2,
                        "SpecFromIter<IntoIter>: non-empty overlapping copy",
                    );
                    kani::cover(
                        has_advanced && expected_len < original_cap / 2,
                        "SpecFromIter<IntoIter>: fallback to SpecExtend",
                    );
                }
                kani::cover(expected_len == 0, "SpecFromIter<IntoIter>: empty remaining iterator");
                kani::cover(
                    expected_len > 0,
                    "SpecFromIter<IntoIter>: non-empty remaining iterator",
                );
            }
        };
    }

    gen_from_iter_harness!(harness_from_iter_u8, u8);
    gen_from_iter_harness!(harness_from_iter_u64, u64);
    gen_from_iter_harness!(harness_from_iter_unit, ());
    gen_from_iter_harness!(harness_from_iter_array, [u8; 4]);
    gen_from_iter_harness!(harness_from_iter_bool, bool);
    gen_from_iter_harness!(harness_from_iter_al16, Al16);
}
