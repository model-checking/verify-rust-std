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
#[must_use = "iterators are lazy and do nothing unless consumed; \
    use `retain_mut` or `extract_if().for_each(drop)` to remove and discard elements"]
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
            let cur = unsafe { &mut *self.vec.as_mut_ptr().add(i) };
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
                    let hole_slot = self.vec.as_mut_ptr().add(i - self.del);
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
        let peek = if self.idx < self.end {
            // This has to use pointer arithmetic as `self.vec[self.idx]` or
            // `self.vec.get_unchecked(self.idx)` wouldn't work since we
            // temporarily set the length of `self.vec` to zero.
            //
            // SAFETY:
            // Since `self.idx` is smaller than `self.end` and `self.end` is
            // smaller than `self.old_len`, `idx` is valid for indexing the
            // buffer. Also, per the invariant of `self.idx`, this element
            // has not been inspected/moved out yet.
            Some(unsafe { &*self.vec.as_ptr().add(self.idx) })
        } else {
            None
        };
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
            // Bounded for now due to a Kani loop-contract limitation with reborrowed
            // loop-local `&mut T` values. An unbounded proof is being investigated.
            #[kani::proof]
            #[kani::unwind(12)]
            pub fn $name() {
                let backing: [$ty; 8] = kani::any();
                let mut vec = kani::slice::any_slice_of_array(&backing).to_vec();
                let old_len = vec.len();
                let start = kani::any_where(|start: &usize| *start <= old_len);
                let end = kani::any_where(|end: &usize| start <= *end && *end <= old_len);
                let mut iter = vec.extract_if(start..end, |_x| kani::any::<bool>());
                assert!(
                    iter.idx == start,
                    "ExtractIf::next: initial index does not match range start"
                );
                assert!(iter.end == end, "ExtractIf::next: stored range end is incorrect");
                assert!(iter.del == 0, "ExtractIf::next: deletion count is not initially zero");
                assert!(iter.old_len == old_len, "ExtractIf::next: original length is incorrect");
                let first_some = iter.next().is_some();
                let idx_after_first = iter.idx;
                assert!(
                    iter.idx >= start && iter.idx <= end,
                    "ExtractIf::next: first call left idx outside the extraction range"
                );
                assert!(
                    iter.del == first_some as usize,
                    "ExtractIf::next: deletion count after first call is incorrect"
                );
                if !first_some {
                    assert!(
                        iter.idx == end,
                        "ExtractIf::next: None did not exhaust the extraction range"
                    );
                }
                let second_some = iter.next().is_some();
                let idx_after_second = iter.idx;
                let removed = first_some as usize + second_some as usize;
                assert!(
                    iter.idx >= idx_after_first && iter.idx <= end,
                    "ExtractIf::next: second call moved idx incorrectly"
                );
                assert!(
                    iter.del == removed,
                    "ExtractIf::next: deletion count does not match returned elements"
                );
                if !second_some {
                    assert!(
                        iter.idx == end,
                        "ExtractIf::next: second None did not exhaust the extraction range"
                    );
                }
                if !first_some {
                    assert!(
                        !second_some,
                        "ExtractIf::next: produced an element after already returning None"
                    );
                }
                kani::cover(start == end && !first_some, "ExtractIf::next: empty extraction range");
                kani::cover(
                    start < end && first_some,
                    "ExtractIf::next: first call removes an element",
                );
                kani::cover(
                    start < end && !first_some,
                    "ExtractIf::next: first call scans to the end",
                );
                kani::cover(first_some && second_some, "ExtractIf::next: two successive removals");
                kani::cover(
                    first_some && idx_after_second > idx_after_first + second_some as usize,
                    "ExtractIf::next: hole-shift path is reachable",
                );
                drop(iter);
                assert!(
                    vec.len() == old_len - removed,
                    "ExtractIf::next: dropping ExtractIf restored the wrong Vec length"
                );
            }
        };
    }

    gen_extract_if_next_harness!(harness_extract_if_next_u8, u8);
    gen_extract_if_next_harness!(harness_extract_if_next_u64, u64);
    gen_extract_if_next_harness!(harness_extract_if_next_unit, ());
    gen_extract_if_next_harness!(harness_extract_if_next_array, [u8; 4]);
    gen_extract_if_next_harness!(harness_extract_if_next_bool, bool);
}
