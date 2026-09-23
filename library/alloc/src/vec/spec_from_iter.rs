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

    // Harness for `SpecFromIter::from_iter`
    macro_rules! gen_from_iter_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let vec = verifier_nondet_vec::<$ty>();
                // Convert the Vec into its owning iterator
                let mut iter = vec.into_iter();
                // Optionally consume one element before collecting the remaining iterator
                // to cover both the advanced and unadvanced IntoIter cases
                if kani::any::<bool>() {
                    let _ = iter.next();
                }
                // Collect the remaining IntoIter through the FromIterator specialization
                let _ = <Vec<$ty> as SpecFromIter<$ty, IntoIter<$ty>>>::from_iter(iter);
            }
        };
    }

    gen_from_iter_harness!(harness_from_iter_u8, u8);
    gen_from_iter_harness!(harness_from_iter_u16, u16);
    gen_from_iter_harness!(harness_from_iter_u32, u32);
    gen_from_iter_harness!(harness_from_iter_u64, u64);
    gen_from_iter_harness!(harness_from_iter_u128, u128);
    gen_from_iter_harness!(harness_from_iter_usize, usize);
    gen_from_iter_harness!(harness_from_iter_i8, i8);
    gen_from_iter_harness!(harness_from_iter_i16, i16);
    gen_from_iter_harness!(harness_from_iter_i32, i32);
    gen_from_iter_harness!(harness_from_iter_i64, i64);
    gen_from_iter_harness!(harness_from_iter_i128, i128);
    gen_from_iter_harness!(harness_from_iter_isize, isize);
    gen_from_iter_harness!(harness_from_iter_unit, ());
    gen_from_iter_harness!(harness_from_iter_array, [u8; 4]);
}
