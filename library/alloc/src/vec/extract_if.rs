#[cfg(kani)]
use core::kani;
use core::ops::{Range, RangeBounds};
use core::{fmt, ptr, slice};

use super::Vec;
use crate::alloc::{Allocator, Global};

/// An iterator which uses a closure to determine if an element should be removed.
///
/// This struct is created by [`Vec::extract_if`].
/// See its documentation for more.
///
/// # Example
///
/// ```
/// let mut v = vec![0, 1, 2];
/// let iter: std::vec::ExtractIf<'_, _, _> = v.extract_if(.., |x| *x % 2 == 0);
/// ```
#[stable(feature = "extract_if", since = "1.87.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ExtractIf<
    'a,
    T,
    F,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    vec: &'a mut Vec<T, A>,
    /// The index of the item that will be inspected by the next call to `next`.
    idx: usize,
    /// Elements at and beyond this point will be retained. Must be equal or smaller than `old_len`.
    end: usize,
    /// The number of items that have been drained (removed) thus far.
    del: usize,
    /// The original length of `vec` prior to draining.
    old_len: usize,
    /// The filter test predicate.
    pred: F,
}

impl<'a, T, F, A: Allocator> ExtractIf<'a, T, F, A> {
    pub(super) fn new<R: RangeBounds<usize>>(vec: &'a mut Vec<T, A>, pred: F, range: R) -> Self {
        let old_len = vec.len();
        let Range { start, end } = slice::range(range, ..old_len);

        // Guard against the vec getting leaked (leak amplification)
        unsafe {
            vec.set_len(0);
        }
        ExtractIf { vec, idx: start, del: 0, end, old_len, pred }
    }

    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn allocator(&self) -> &A {
        self.vec.allocator()
    }
}

#[stable(feature = "extract_if", since = "1.87.0")]
impl<T, F, A: Allocator> Iterator for ExtractIf<'_, T, F, A>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        #[cfg(kani)]
        let is_zst = core::mem::size_of::<T>() == 0;
        #[cfg(kani)]
        let base = self.vec.as_mut_ptr();
        #[cfg(kani)]
        let capacity = self.vec.capacity();
        #[cfg(kani)]
        let mut cur = base;
        #[cfg(kani)]
        let modified_items = if is_zst {
            ptr::slice_from_raw_parts(core::ptr::null::<T>(), 0)
        } else {
            ptr::slice_from_raw_parts(base, self.old_len)
        };
        #[cfg(kani)]
        let modified_items_mut = if is_zst {
            ptr::slice_from_raw_parts_mut(core::ptr::null_mut::<T>(), 0)
        } else {
            ptr::slice_from_raw_parts_mut(base, self.old_len)
        };
        #[cfg(kani)]
        kani::assume(kani::mem::can_write(modified_items_mut));

        #[cfg_attr(kani, kani::loop_invariant(
            (is_zst || self.old_len <= capacity)
                && self.idx <= self.end
                && self.end <= self.old_len
                && self.del <= self.idx
                && kani::mem::can_write(modified_items_mut)
        ))]
        #[cfg_attr(kani, kani::loop_modifies(
            &self.idx,
            &self.del,
            &cur,
            modified_items
        ))]
        while self.idx < self.end {
            let i = self.idx;
            // SAFETY:
            //  We know that `i < self.end` from the if guard and that `self.end <= self.old_len` from
            //  the validity of `Self`. Therefore `i` points to an element within `vec`.
            //
            //  Additionally, the i-th element is valid because each element is visited at most once
            //  and it is the first time we access vec[i].
            //
            //  Note: we can't use `vec.get_unchecked_mut(i)` here since the precondition for that
            //  function is that i < vec.len(), but we've set vec's length to zero.
            #[cfg(kani)]
            {
                kani::assume(i < self.old_len && i < capacity);
                kani::assume(kani::mem::can_write(unsafe { base.add(i) }));
            }
            #[cfg(kani)]
            {
                cur = unsafe { base.add(i) };
            }
            #[cfg(not(kani))]
            let cur = unsafe { &mut *self.vec.as_mut_ptr().add(i) };
            #[cfg(kani)]
            let drained = (self.pred)(unsafe { &mut *cur });
            #[cfg(not(kani))]
            let drained = (self.pred)(cur);
            // Update the index *after* the predicate is called. If the index
            // is updated prior and the predicate panics, the element at this
            // index would be leaked.
            self.idx += 1;
            if drained {
                self.del += 1;
                // SAFETY: We never touch this element again after returning it.
                return Some(unsafe { ptr::read(cur) });
            } else if self.del > 0 {
                // SAFETY: `self.del` > 0, so the hole slot must not overlap with current element.
                // We use copy for move, and never touch this element again.
                unsafe {
                    let hole = i - self.del;
                    #[cfg(kani)]
                    kani::assume(hole < i);
                    #[cfg(kani)]
                    let hole_slot = base.add(hole);
                    #[cfg(not(kani))]
                    let hole_slot = self.vec.as_mut_ptr().add(hole);
                    ptr::copy_nonoverlapping(cur, hole_slot, 1);
                }
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.end - self.idx))
    }
}

#[stable(feature = "extract_if", since = "1.87.0")]
impl<T, F, A: Allocator> Drop for ExtractIf<'_, T, F, A> {
    fn drop(&mut self) {
        if self.del > 0 {
            // SAFETY: Trailing unchecked items must be valid since we never touch them.
            unsafe {
                ptr::copy(
                    self.vec.as_ptr().add(self.idx),
                    self.vec.as_mut_ptr().add(self.idx - self.del),
                    self.old_len - self.idx,
                );
            }
        }
        // SAFETY: After filling holes, all items are in contiguous memory.
        unsafe {
            self.vec.set_len(self.old_len - self.del);
        }
    }
}

#[stable(feature = "extract_if", since = "1.87.0")]
impl<T, F, A> fmt::Debug for ExtractIf<'_, T, F, A>
where
    T: fmt::Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let peek = if self.idx < self.end { self.vec.get(self.idx) } else { None };
        f.debug_struct("ExtractIf").field("peek", &peek).finish_non_exhaustive()
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::super::kani_vec_harness_helpers::*;
    use super::*;

    // Harnesses for ExtractIf::next()
    macro_rules! gen_extract_if_next_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_bounded_vec::<$ty>();
                // Choose a non-deterministic in-bounds extraction range
                let start = kani::any_where(|i: &usize| *i <= vec.len());
                let end = kani::any_where(|j: &usize| start <= *j && *j <= vec.len());
                // Create an ExtractIf iterator with a non-deterministic predicate
                let mut iter = vec.extract_if(start..end, |_x| kani::any::<bool>());
                // Advance the ExtractIf iterator by one element if one is selected
                let _ = iter.next();
            }
        };
    }

    gen_extract_if_next_harness!(harness_extract_if_next_u8, u8);
    gen_extract_if_next_harness!(harness_extract_if_next_u16, u16);
    gen_extract_if_next_harness!(harness_extract_if_next_u32, u32);
    gen_extract_if_next_harness!(harness_extract_if_next_u64, u64);
    gen_extract_if_next_harness!(harness_extract_if_next_u128, u128);
    gen_extract_if_next_harness!(harness_extract_if_next_usize, usize);
    gen_extract_if_next_harness!(harness_extract_if_next_i8, i8);
    gen_extract_if_next_harness!(harness_extract_if_next_i16, i16);
    gen_extract_if_next_harness!(harness_extract_if_next_i32, i32);
    gen_extract_if_next_harness!(harness_extract_if_next_i64, i64);
    gen_extract_if_next_harness!(harness_extract_if_next_i128, i128);
    gen_extract_if_next_harness!(harness_extract_if_next_isize, isize);
    gen_extract_if_next_harness!(harness_extract_if_next_unit, ());
    gen_extract_if_next_harness!(harness_extract_if_next_array, [u8; 4]);
}
