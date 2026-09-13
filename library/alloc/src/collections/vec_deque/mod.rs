//! A double-ended queue (deque) implemented with a growable ring buffer.
//!
//! This queue has *O*(1) amortized inserts and removals from both ends of the
//! container. It also has *O*(1) indexing like a vector. The contained elements
//! are not required to be copyable, and the queue will be sendable if the
//! contained type is sendable.

#![stable(feature = "rust1", since = "1.0.0")]

#[cfg(not(no_global_oom_handling))]
use core::clone::TrivialClone;
use core::cmp::{self, Ordering};
use core::hash::{Hash, Hasher};
use core::iter::{ByRefSized, repeat_n, repeat_with};
// This is used in a bunch of intra-doc links.
// FIXME: For some reason, `#[cfg(doc)]` wasn't sufficient, resulting in
// failures in linkchecker even though rustdoc built the docs just fine.
#[allow(unused_imports)]
use core::mem;
use core::mem::{ManuallyDrop, SizedTypeProperties};
use core::ops::{Index, IndexMut, Range, RangeBounds};
use core::{fmt, ptr, slice};

use safety::{ensures, requires};

#[cfg(kani)]
use crate::alloc::Layout;
use crate::alloc::{Allocator, Global};
use crate::collections::{TryReserveError, TryReserveErrorKind};
use crate::raw_vec::RawVec;
use crate::vec::Vec;

#[macro_use]
mod macros;

#[stable(feature = "drain", since = "1.6.0")]
pub use self::drain::Drain;

mod drain;

#[unstable(feature = "vec_deque_extract_if", issue = "147750")]
pub use self::extract_if::ExtractIf;

mod extract_if;

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::iter_mut::IterMut;

mod iter_mut;

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::into_iter::IntoIter;

mod into_iter;

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::iter::Iter;

mod iter;

use self::spec_extend::{SpecExtend, SpecExtendFront};

mod spec_extend;

use self::spec_from_iter::SpecFromIter;

mod spec_from_iter;

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "deque_extend_front", issue = "146975")]
pub use self::splice::Splice;

#[cfg(not(no_global_oom_handling))]
mod splice;

#[cfg(test)]
mod tests;

#[cfg(kani)]
use core::kani;

/// A double-ended queue implemented with a growable ring buffer.
///
/// The "default" usage of this type as a queue is to use [`push_back`] to add to
/// the queue, and [`pop_front`] to remove from the queue. [`extend`] and [`append`]
/// push onto the back in this manner, and iterating over `VecDeque` goes front
/// to back.
///
/// A `VecDeque` with a known list of items can be initialized from an array:
///
/// ```
/// use std::collections::VecDeque;
///
/// let deq = VecDeque::from([-1, 0, 1]);
/// ```
///
/// Since `VecDeque` is a ring buffer, its elements are not necessarily contiguous
/// in memory. If you want to access the elements as a single slice, such as for
/// efficient sorting, you can use [`make_contiguous`]. It rotates the `VecDeque`
/// so that its elements do not wrap, and returns a mutable slice to the
/// now-contiguous element sequence.
///
/// [`push_back`]: VecDeque::push_back
/// [`pop_front`]: VecDeque::pop_front
/// [`extend`]: VecDeque::extend
/// [`append`]: VecDeque::append
/// [`make_contiguous`]: VecDeque::make_contiguous
#[cfg_attr(not(test), rustc_diagnostic_item = "VecDeque")]
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_insignificant_dtor]
pub struct VecDeque<
    T,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    // `self[0]`, if it exists, is `buf[head]`.
    // `head < buf.capacity()`, unless `buf.capacity() == 0` when `head == 0`.
    head: usize,
    // the number of initialized elements, starting from the one at `head` and potentially wrapping around.
    // if `len == 0`, the exact value of `head` is unimportant.
    // if `T` is zero-Sized, then `self.len <= usize::MAX`, otherwise `self.len <= isize::MAX as usize`.
    len: usize,
    buf: RawVec<T, A>,
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone, A: Allocator + Clone> Clone for VecDeque<T, A> {
    fn clone(&self) -> Self {
        let mut deq = Self::with_capacity_in(self.len(), self.allocator().clone());
        deq.extend(self.iter().cloned());
        deq
    }

    /// Overwrites the contents of `self` with a clone of the contents of `source`.
    ///
    /// This method is preferred over simply assigning `source.clone()` to `self`,
    /// as it avoids reallocation if possible.
    fn clone_from(&mut self, source: &Self) {
        self.clear();
        self.extend(source.iter().cloned());
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<#[may_dangle] T, A: Allocator> Drop for VecDeque<T, A> {
    fn drop(&mut self) {
        /// Runs the destructor for all items in the slice when it gets dropped (normally or
        /// during unwinding).
        struct Dropper<'a, T>(&'a mut [T]);

        impl<'a, T> Drop for Dropper<'a, T> {
            fn drop(&mut self) {
                unsafe {
                    ptr::drop_in_place(self.0);
                }
            }
        }

        let (front, back) = self.as_mut_slices();
        unsafe {
            let _back_dropper = Dropper(back);
            // use drop for [T]
            ptr::drop_in_place(front);
        }
        // RawVec handles deallocation
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Default for VecDeque<T> {
    /// Creates an empty deque.
    #[inline]
    fn default() -> VecDeque<T> {
        VecDeque::new()
    }
}

impl<T, A: Allocator> VecDeque<T, A> {
    /// Marginally more convenient
    #[inline]
    fn ptr(&self) -> *mut T {
        self.buf.ptr()
    }

    /// Structural invariant of a `VecDeque` (see the field comments on the struct):
    /// `len <= capacity()` and `head < capacity()` unless the capacity is zero, in which
    /// case `head == 0`. Only used by the verification contracts below and by `mod verify`.
    #[cfg(kani)]
    fn invariant_holds(&self) -> bool {
        self.len <= self.capacity()
            && (self.head < self.capacity() || (self.capacity() == 0 && self.head == 0))
    }

    /// The physical slots `off..off + n` as a slice pointer, for `modifies` clauses. An empty
    /// range is represented by a null slice so that a dangling or one-past-the-end base pointer
    /// never has to be checked for writability. Only used by the verification contracts.
    #[cfg(kani)]
    fn slots(&self, off: usize, n: usize) -> *mut [T] {
        if n == 0 || T::IS_ZST {
            ptr::slice_from_raw_parts_mut(ptr::null_mut(), 0)
        } else {
            ptr::slice_from_raw_parts_mut(unsafe { self.ptr().add(off) }, n)
        }
    }

    /// The whole physical buffer as a slice pointer, for `modifies` clauses.
    #[cfg(kani)]
    fn all_slots(&self) -> *mut [T] {
        self.slots(0, self.capacity())
    }

    /// Appends an element to the buffer.
    ///
    /// # Safety
    ///
    /// May only be called if `deque.len() < deque.capacity()`
    #[inline]
    #[requires(self.invariant_holds() && self.len < self.capacity())]
    #[ensures(|_| self.len == old(self.len) + 1 && self.invariant_holds())]
    #[cfg_attr(kani, kani::modifies(&self.len, self.slots(self.to_physical_idx(self.len), 1)))]
    unsafe fn push_unchecked(&mut self, element: T) {
        // SAFETY: Because of the precondition, it's guaranteed that there is space
        // in the logical array after the last element.
        unsafe { self.buffer_write(self.to_physical_idx(self.len), element) };
        // This can't overflow because `deque.len() < deque.capacity() <= usize::MAX`.
        self.len += 1;
    }

    /// Prepends an element to the buffer.
    ///
    /// # Safety
    ///
    /// May only be called if `deque.len() < deque.capacity()`
    #[inline]
    unsafe fn push_front_unchecked(&mut self, element: T) {
        self.head = self.wrap_sub(self.head, 1);
        // SAFETY: Because of the precondition, it's guaranteed that there is space
        // in the logical array before the first element (where self.head is now).
        unsafe { self.buffer_write(self.head, element) };
        // This can't overflow because `deque.len() < deque.capacity() <= usize::MAX`.
        self.len += 1;
    }

    /// Moves an element out of the buffer
    ///
    /// # Safety
    ///
    /// `off < self.capacity()` and slot `off` must hold an initialized `T`. The value is moved
    /// out: the caller must ensure the slot is no longer considered initialized afterwards.
    #[inline]
    #[requires(off < self.capacity() && core::ub_checks::can_dereference(unsafe { self.ptr().add(off) }))]
    unsafe fn buffer_read(&mut self, off: usize) -> T {
        unsafe { ptr::read(self.ptr().add(off)) }
    }

    /// Writes an element into the buffer, moving it and returning a pointer to it.
    /// # Safety
    ///
    /// May only be called if `off < self.capacity()`.
    #[inline]
    #[requires(off < self.capacity() && core::ub_checks::can_write(unsafe { self.ptr().add(off) }))]
    #[ensures(|result| core::ptr::eq(*result, old(unsafe { self.ptr().add(off) })))]
    #[cfg_attr(kani, kani::modifies(self.slots(off, 1)))]
    unsafe fn buffer_write(&mut self, off: usize, value: T) -> &mut T {
        unsafe {
            let ptr = self.ptr().add(off);
            ptr::write(ptr, value);
            &mut *ptr
        }
    }

    /// Returns a slice pointer into the buffer.
    /// `range` must lie inside `0..self.capacity()`.
    #[inline]
    #[requires(range.start <= range.end && range.end <= self.capacity())]
    #[ensures(|result| result.len() == old(range.end) - old(range.start)
        && core::ptr::eq(*result as *const T, unsafe { self.ptr().add(old(range.start)) }))]
    unsafe fn buffer_range(&self, range: Range<usize>) -> *mut [T] {
        unsafe {
            ptr::slice_from_raw_parts_mut(self.ptr().add(range.start), range.end - range.start)
        }
    }

    /// Returns `true` if the buffer is at full capacity.
    #[inline]
    fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    /// Returns the index in the underlying buffer for a given logical element
    /// index + addend.
    #[inline]
    fn wrap_add(&self, idx: usize, addend: usize) -> usize {
        wrap_index(idx.wrapping_add(addend), self.capacity())
    }

    #[inline]
    fn to_physical_idx(&self, idx: usize) -> usize {
        self.wrap_add(self.head, idx)
    }

    /// Returns the index in the underlying buffer for a given logical element
    /// index - subtrahend.
    #[inline]
    fn wrap_sub(&self, idx: usize, subtrahend: usize) -> usize {
        wrap_index(idx.wrapping_sub(subtrahend).wrapping_add(self.capacity()), self.capacity())
    }

    /// Get source, destination and count (like the arguments to [`ptr::copy_nonoverlapping`])
    /// for copying `count` values from index `src` to index `dst`.
    /// One of the ranges can wrap around the physical buffer, for this reason 2 triples are returned.
    ///
    /// Use of the word "ranges" specifically refers to `src..src + count` and `dst..dst + count`.
    ///
    /// # Safety
    ///
    /// - Ranges must not overlap: `src.abs_diff(dst) >= count`.
    /// - Ranges must be in bounds of the logical buffer: `src + count <= self.capacity()` and `dst + count <= self.capacity()`.
    /// - `head` must be in bounds: `head < self.capacity()`.
    #[cfg(not(no_global_oom_handling))]
    unsafe fn nonoverlapping_ranges(
        &mut self,
        src: usize,
        dst: usize,
        count: usize,
        head: usize,
    ) -> [(*const T, *mut T, usize); 2] {
        // "`src` and `dst` must be at least as far apart as `count`"
        debug_assert!(
            src.abs_diff(dst) >= count,
            "`src` and `dst` must not overlap. src={src} dst={dst} count={count}",
        );
        debug_assert!(
            src.max(dst) + count <= self.capacity(),
            "ranges must be in bounds. src={src} dst={dst} count={count} cap={}",
            self.capacity(),
        );

        let wrapped_src = self.wrap_add(head, src);
        let wrapped_dst = self.wrap_add(head, dst);

        let room_after_src = self.capacity() - wrapped_src;
        let room_after_dst = self.capacity() - wrapped_dst;

        let src_wraps = room_after_src < count;
        let dst_wraps = room_after_dst < count;

        // Wrapping occurs if `capacity` is contained within `wrapped_src..wrapped_src + count` or `wrapped_dst..wrapped_dst + count`.
        // Since these two ranges must not overlap as per the safety invariants of this function, only one range can wrap.
        debug_assert!(
            !(src_wraps && dst_wraps),
            "BUG: at most one of src and dst can wrap. src={src} dst={dst} count={count} cap={}",
            self.capacity(),
        );

        unsafe {
            let ptr = self.ptr();
            let src_ptr = ptr.add(wrapped_src);
            let dst_ptr = ptr.add(wrapped_dst);

            if src_wraps {
                [
                    (src_ptr, dst_ptr, room_after_src),
                    (ptr, dst_ptr.add(room_after_src), count - room_after_src),
                ]
            } else if dst_wraps {
                [
                    (src_ptr, dst_ptr, room_after_dst),
                    (src_ptr.add(room_after_dst), ptr, count - room_after_dst),
                ]
            } else {
                [
                    (src_ptr, dst_ptr, count),
                    // null pointers are fine as long as the count is 0
                    (ptr::null(), ptr::null_mut(), 0),
                ]
            }
        }
    }

    /// Copies a contiguous block of memory len long from src to dst
    ///
    /// # Safety
    ///
    /// `src + len <= self.capacity()` and `dst + len <= self.capacity()`.
    #[inline]
    #[requires(len <= self.capacity() && src <= self.capacity() - len && dst <= self.capacity() - len)]
    #[ensures(|_| self.head == old(self.head) && self.len == old(self.len))]
    #[cfg_attr(kani, kani::modifies(self.slots(dst, len)))]
    unsafe fn copy(&mut self, src: usize, dst: usize, len: usize) {
        debug_assert!(
            dst + len <= self.capacity(),
            "cpy dst={} src={} len={} cap={}",
            dst,
            src,
            len,
            self.capacity()
        );
        debug_assert!(
            src + len <= self.capacity(),
            "cpy dst={} src={} len={} cap={}",
            dst,
            src,
            len,
            self.capacity()
        );
        unsafe {
            ptr::copy(self.ptr().add(src), self.ptr().add(dst), len);
        }
    }

    /// Copies a contiguous block of memory len long from src to dst
    ///
    /// # Safety
    ///
    /// `src + len <= self.capacity()`, `dst + len <= self.capacity()` and the two ranges
    /// must not overlap: `src.abs_diff(dst) >= len`.
    #[inline]
    #[requires(len <= self.capacity() && src <= self.capacity() - len && dst <= self.capacity() - len)]
    #[requires(src.abs_diff(dst) >= len)]
    #[ensures(|_| self.head == old(self.head) && self.len == old(self.len))]
    #[cfg_attr(kani, kani::modifies(self.slots(dst, len)))]
    unsafe fn copy_nonoverlapping(&mut self, src: usize, dst: usize, len: usize) {
        debug_assert!(
            dst + len <= self.capacity(),
            "cno dst={} src={} len={} cap={}",
            dst,
            src,
            len,
            self.capacity()
        );
        debug_assert!(
            src + len <= self.capacity(),
            "cno dst={} src={} len={} cap={}",
            dst,
            src,
            len,
            self.capacity()
        );
        unsafe {
            ptr::copy_nonoverlapping(self.ptr().add(src), self.ptr().add(dst), len);
        }
    }

    /// Copies a potentially wrapping block of memory len long from src to dest.
    /// (abs(dst - src) + len) must be no larger than capacity() (There must be at
    /// most one continuous overlapping region between src and dest).
    ///
    /// # Safety
    ///
    /// `src` and `dst` must be physical indices (`< self.capacity()`, or both `0` when the
    /// capacity is `0`) and `min(src.abs_diff(dst), self.capacity() - src.abs_diff(dst)) + len`
    /// must not exceed `self.capacity()`.
    #[requires(self.invariant_holds()
        && ((src < self.capacity() && dst < self.capacity()) || (src == 0 && dst == 0))
        && cmp::min(src.abs_diff(dst), self.capacity() - src.abs_diff(dst))
            .checked_add(len)
            .is_some_and(|end| end <= self.capacity()))]
    #[ensures(|_| self.head == old(self.head) && self.len == old(self.len))]
    #[cfg_attr(kani, kani::modifies(self.all_slots()))]
    unsafe fn wrap_copy(&mut self, src: usize, dst: usize, len: usize) {
        debug_assert!(
            cmp::min(src.abs_diff(dst), self.capacity() - src.abs_diff(dst)) + len
                <= self.capacity(),
            "wrc dst={} src={} len={} cap={}",
            dst,
            src,
            len,
            self.capacity()
        );

        // If T is a ZST, don't do any copying.
        if T::IS_ZST || src == dst || len == 0 {
            return;
        }

        let dst_after_src = self.wrap_sub(dst, src) < len;

        let src_pre_wrap_len = self.capacity() - src;
        let dst_pre_wrap_len = self.capacity() - dst;
        let src_wraps = src_pre_wrap_len < len;
        let dst_wraps = dst_pre_wrap_len < len;

        match (dst_after_src, src_wraps, dst_wraps) {
            (_, false, false) => {
                // src doesn't wrap, dst doesn't wrap
                //
                //        S . . .
                // 1 [_ _ A A B B C C _]
                // 2 [_ _ A A A A B B _]
                //            D . . .
                //
                unsafe {
                    self.copy(src, dst, len);
                }
            }
            (false, false, true) => {
                // dst before src, src doesn't wrap, dst wraps
                //
                //    S . . .
                // 1 [A A B B _ _ _ C C]
                // 2 [A A B B _ _ _ A A]
                // 3 [B B B B _ _ _ A A]
                //    . .           D .
                //
                unsafe {
                    self.copy(src, dst, dst_pre_wrap_len);
                    self.copy(src + dst_pre_wrap_len, 0, len - dst_pre_wrap_len);
                }
            }
            (true, false, true) => {
                // src before dst, src doesn't wrap, dst wraps
                //
                //              S . . .
                // 1 [C C _ _ _ A A B B]
                // 2 [B B _ _ _ A A B B]
                // 3 [B B _ _ _ A A A A]
                //    . .           D .
                //
                unsafe {
                    self.copy(src + dst_pre_wrap_len, 0, len - dst_pre_wrap_len);
                    self.copy(src, dst, dst_pre_wrap_len);
                }
            }
            (false, true, false) => {
                // dst before src, src wraps, dst doesn't wrap
                //
                //    . .           S .
                // 1 [C C _ _ _ A A B B]
                // 2 [C C _ _ _ B B B B]
                // 3 [C C _ _ _ B B C C]
                //              D . . .
                //
                unsafe {
                    self.copy(src, dst, src_pre_wrap_len);
                    self.copy(0, dst + src_pre_wrap_len, len - src_pre_wrap_len);
                }
            }
            (true, true, false) => {
                // src before dst, src wraps, dst doesn't wrap
                //
                //    . .           S .
                // 1 [A A B B _ _ _ C C]
                // 2 [A A A A _ _ _ C C]
                // 3 [C C A A _ _ _ C C]
                //    D . . .
                //
                unsafe {
                    self.copy(0, dst + src_pre_wrap_len, len - src_pre_wrap_len);
                    self.copy(src, dst, src_pre_wrap_len);
                }
            }
            (false, true, true) => {
                // dst before src, src wraps, dst wraps
                //
                //    . . .         S .
                // 1 [A B C D _ E F G H]
                // 2 [A B C D _ E G H H]
                // 3 [A B C D _ E G H A]
                // 4 [B C C D _ E G H A]
                //    . .         D . .
                //
                debug_assert!(dst_pre_wrap_len > src_pre_wrap_len);
                let delta = dst_pre_wrap_len - src_pre_wrap_len;
                unsafe {
                    self.copy(src, dst, src_pre_wrap_len);
                    self.copy(0, dst + src_pre_wrap_len, delta);
                    self.copy(delta, 0, len - dst_pre_wrap_len);
                }
            }
            (true, true, true) => {
                // src before dst, src wraps, dst wraps
                //
                //    . .         S . .
                // 1 [A B C D _ E F G H]
                // 2 [A A B D _ E F G H]
                // 3 [H A B D _ E F G H]
                // 4 [H A B D _ E F F G]
                //    . . .         D .
                //
                debug_assert!(src_pre_wrap_len > dst_pre_wrap_len);
                let delta = src_pre_wrap_len - dst_pre_wrap_len;
                unsafe {
                    self.copy(0, delta, len - src_pre_wrap_len);
                    self.copy(self.capacity() - delta, 0, delta);
                    self.copy(src, dst, dst_pre_wrap_len);
                }
            }
        }
    }

    /// Copies all values from `src` to `dst`, wrapping around if needed.
    /// Assumes capacity is sufficient.
    ///
    /// # Safety
    ///
    /// `dst <= self.capacity()` and `src.len() <= self.capacity()`.
    #[inline]
    #[requires(dst <= self.capacity() && src.len() <= self.capacity())]
    #[ensures(|_| self.head == old(self.head) && self.len == old(self.len))]
    #[cfg_attr(kani, kani::modifies(self.all_slots()))]
    unsafe fn copy_slice(&mut self, dst: usize, src: &[T]) {
        debug_assert!(src.len() <= self.capacity());
        let head_room = self.capacity() - dst;
        if src.len() <= head_room {
            unsafe {
                ptr::copy_nonoverlapping(src.as_ptr(), self.ptr().add(dst), src.len());
            }
        } else {
            let (left, right) = src.split_at(head_room);
            unsafe {
                ptr::copy_nonoverlapping(left.as_ptr(), self.ptr().add(dst), left.len());
                ptr::copy_nonoverlapping(right.as_ptr(), self.ptr(), right.len());
            }
        }
    }

    /// Copies all values from `src` to `dst` in reversed order, wrapping around if needed.
    /// Assumes capacity is sufficient.
    /// Equivalent to calling [`VecDeque::copy_slice`] with a [reversed](https://doc.rust-lang.org/std/primitive.slice.html#method.reverse) slice.
    #[inline]
    unsafe fn copy_slice_reversed(&mut self, dst: usize, src: &[T]) {
        /// # Safety
        ///
        /// See [`ptr::copy_nonoverlapping`].
        unsafe fn copy_nonoverlapping_reversed<T>(src: *const T, dst: *mut T, count: usize) {
            for i in 0..count {
                unsafe { ptr::copy_nonoverlapping(src.add(count - 1 - i), dst.add(i), 1) };
            }
        }

        debug_assert!(src.len() <= self.capacity());
        let head_room = self.capacity() - dst;
        if src.len() <= head_room {
            unsafe {
                copy_nonoverlapping_reversed(src.as_ptr(), self.ptr().add(dst), src.len());
            }
        } else {
            let (left, right) = src.split_at(src.len() - head_room);
            unsafe {
                copy_nonoverlapping_reversed(right.as_ptr(), self.ptr().add(dst), right.len());
                copy_nonoverlapping_reversed(left.as_ptr(), self.ptr(), left.len());
            }
        }
    }

    /// Writes all values from `iter` to `dst`.
    ///
    /// # Safety
    ///
    /// Assumes no wrapping around happens.
    /// Assumes capacity is sufficient.
    ///
    /// # Safety
    ///
    /// `iter` must yield at most `self.capacity() - dst` items. The contract below expresses
    /// this through the iterator's upper `size_hint`, which is exact for the `TrustedLen`
    /// iterators every caller passes.
    #[inline]
    #[requires(self.write_iter_precondition(dst, iter.size_hint().1, *written))]
    #[ensures(|_| old(*written) <= *written
        && *written - old(*written) <= old(iter.size_hint().1.unwrap_or(0)))]
    #[cfg_attr(kani, kani::modifies(written, self.slots(dst, iter.size_hint().1.unwrap_or(0))))]
    unsafe fn write_iter(
        &mut self,
        dst: usize,
        iter: impl Iterator<Item = T>,
        written: &mut usize,
    ) {
        #[cfg(not(kani))]
        iter.enumerate().for_each(|(i, element)| unsafe {
            self.buffer_write(dst + i, element);
            *written += 1;
        });
        // Under Kani the very same iteration is spelled as an explicit loop (see
        // `write_iter_loop`) so that a loop contract can be attached; loop contracts cannot be
        // attached to the closure-driven `for_each`. The statement above is also compiled
        // under Kani, byte for byte, as `write_iter_for_each`, and checked against this
        // function's contract for bounded iterator lengths (`verify::bounded_evidence`).
        #[cfg(kani)]
        unsafe {
            self.write_iter_loop(dst, iter, written)
        }
    }

    /// The precondition of [`Self::write_iter`]'s contract as one predicate, so that the
    /// contract replacement in `mod verify` (`write_iter_contract_replacement`) asserts exactly
    /// the clause the contract requires. Only used by the verification contracts and by
    /// `mod verify`.
    #[cfg(kani)]
    fn write_iter_precondition(&self, dst: usize, upper: Option<usize>, written: usize) -> bool {
        upper.is_some_and(|hi| {
            dst.checked_add(hi).is_some_and(|end| end <= self.capacity())
                && written.checked_add(hi).is_some()
        })
    }

    /// The shipped statement of [`Self::write_iter`] (its `#[cfg(not(kani))]` body), byte for
    /// byte, as a Kani-visible sibling: `verify::bounded_evidence` substitutes it for
    /// `write_iter_loop` to check the shipped text against `write_iter`'s contract, bounded in
    /// the iterator length. It must stay byte-identical to that statement; diff the two when
    /// editing either.
    #[cfg(kani)]
    #[inline]
    unsafe fn write_iter_for_each(
        &mut self,
        dst: usize,
        iter: impl Iterator<Item = T>,
        written: &mut usize,
    ) {
        iter.enumerate().for_each(|(i, element)| unsafe {
            self.buffer_write(dst + i, element);
            *written += 1;
        });
    }

    /// The iteration of [`Self::write_iter`] transcribed into the form Kani's loop contracts
    /// accept: `iter` is driven with `next()`, every element is written to `dst + i` and
    /// counted, exactly as the shipped `for_each` statement does; nothing is skipped,
    /// synthesized or forgotten. `write_iter`'s contract proof (`check_write_iter_*` in
    /// `mod verify`) runs this transcription unbounded; `verify::bounded_evidence` checks the
    /// shipped statement itself ([`Self::write_iter_for_each`]) against the same contract,
    /// bounded in the iterator length.
    ///
    /// Why a transcription: the shipped loop is inside `Iterator::for_each` → `Enumerate::fold`
    /// → `I::fold` (core), where no loop contract can be attached, and `Enumerate::fold` keeps
    /// its index in a closure that a loop contract lower down could neither name nor re-pin
    /// after havocking. The transcription relies on `Iterator`'s documented equivalence between
    /// `fold` and repeated `next()`. Its loop-contract proof is a partial-correctness proof
    /// (Kani's loop contracts assume termination); termination follows from the exact
    /// `size_hint` of the `TrustedLen` iterators every caller passes. `loop_decreases` is not
    /// used because at the pinned Kani it conflicts with an explicit `loop_modifies`.
    ///
    /// Callers of `write_iter` whose iterator is reused after the call (the wrapping branch of
    /// `write_iter_wrapping`, which passes `Take<ByRefSized<&mut I>>`) are verified with this
    /// helper replaced by `write_iter`'s contract plus the consumption of the iterator
    /// (`verify::write_iter_contract_replacement`), because a loop contract cannot survive the
    /// havocking of that reference-carrying adapter.
    #[cfg(kani)]
    #[inline]
    unsafe fn write_iter_loop(
        &mut self,
        dst: usize,
        iter: impl Iterator<Item = T>,
        written: &mut usize,
    ) {
        let bound = iter.size_hint().1.unwrap_or(0);
        let written_on_entry = *written;
        let mut iter = iter;
        let mut i = 0;
        #[safety::loop_invariant(i <= bound
            && *written == written_on_entry + i
            && iter.size_hint().1 == Some(bound - i))]
        #[kani::loop_modifies(&raw mut *written, &i, &iter, self.slots(dst, bound))]
        loop {
            let Some(element) = iter.next() else { break };
            unsafe {
                self.buffer_write(dst + i, element);
            }
            *written += 1;
            i += 1;
        }
    }

    /// Writes all values from `iter` to `dst`, wrapping
    /// at the end of the buffer and returns the number
    /// of written values.
    ///
    /// # Safety
    ///
    /// Assumes that `iter` yields at most `len` items.
    /// Assumes capacity is sufficient.
    ///
    /// # Safety
    ///
    /// `dst <= self.capacity()`, `self.len + len <= self.capacity()` and `iter` yields at most
    /// `len` items (expressed through its upper `size_hint`, exact for `TrustedLen` callers).
    #[requires(self.invariant_holds() && dst <= self.capacity() && len <= self.capacity() - self.len)]
    #[requires(iter.size_hint().1.is_some_and(|hi| hi <= len))]
    #[ensures(|written| *written <= len && self.len == old(self.len) + *written && self.invariant_holds())]
    #[cfg_attr(kani, kani::modifies(
        &self.len,
        self.slots(dst, cmp::min(len, self.capacity() - dst)),
        self.slots(0, len.saturating_sub(self.capacity() - dst))
    ))]
    unsafe fn write_iter_wrapping(
        &mut self,
        dst: usize,
        mut iter: impl Iterator<Item = T>,
        len: usize,
    ) -> usize {
        struct Guard<'a, T, A: Allocator> {
            deque: &'a mut VecDeque<T, A>,
            written: usize,
        }

        impl<'a, T, A: Allocator> Drop for Guard<'a, T, A> {
            fn drop(&mut self) {
                self.deque.len += self.written;
            }
        }

        let head_room = self.capacity() - dst;

        let mut guard = Guard { deque: self, written: 0 };

        if head_room >= len {
            unsafe { guard.deque.write_iter(dst, iter, &mut guard.written) };
        } else {
            unsafe {
                guard.deque.write_iter(
                    dst,
                    ByRefSized(&mut iter).take(head_room),
                    &mut guard.written,
                );
                guard.deque.write_iter(0, iter, &mut guard.written)
            };
        }

        guard.written
    }

    /// Frobs the head and tail sections around to handle the fact that we
    /// just reallocated. Unsafe because it trusts old_capacity.
    ///
    /// # Safety
    ///
    /// `old_capacity` must be the capacity the elements were laid out for before the
    /// reallocation: `self.len <= old_capacity <= self.capacity()` and `self.head` must be a
    /// valid physical index for it (`self.head < old_capacity`, or `0` if it was `0`).
    #[inline]
    #[requires(self.len <= old_capacity && old_capacity <= self.capacity())]
    #[requires(self.head < old_capacity || self.head == 0)]
    #[ensures(|_| self.len == old(self.len) && self.invariant_holds())]
    #[cfg_attr(kani, kani::modifies(&self.head, self.all_slots()))]
    unsafe fn handle_capacity_increase(&mut self, old_capacity: usize) {
        let new_capacity = self.capacity();
        debug_assert!(new_capacity >= old_capacity);

        // Move the shortest contiguous section of the ring buffer
        //
        // H := head
        // L := last element (`self.to_physical_idx(self.len - 1)`)
        //
        //    H             L
        //   [o o o o o o o o ]
        //    H             L
        // A [o o o o o o o o . . . . . . . . ]
        //        L H
        //   [o o o o o o o o ]
        //          H             L
        // B [. . . o o o o o o o o . . . . . ]
        //              L H
        //   [o o o o o o o o ]
        //              L                 H
        // C [o o o o o o . . . . . . . . o o ]

        // can't use is_contiguous() because the capacity is already updated.
        if self.head <= old_capacity - self.len {
            // A
            // Nop
        } else {
            let head_len = old_capacity - self.head;
            let tail_len = self.len - head_len;
            if head_len > tail_len && new_capacity - old_capacity >= tail_len {
                // B
                unsafe {
                    self.copy_nonoverlapping(0, old_capacity, tail_len);
                }
            } else {
                // C
                let new_head = new_capacity - head_len;
                unsafe {
                    // can't use copy_nonoverlapping here, because if e.g. head_len = 2
                    // and new_capacity = old_capacity + 1, then the heads overlap.
                    self.copy(self.head, new_head, head_len);
                }
                self.head = new_head;
            }
        }
        debug_assert!(self.head < self.capacity() || self.capacity() == 0);
    }

    /// Creates an iterator which uses a closure to determine if an element in the range should be removed.
    ///
    /// If the closure returns `true`, the element is removed from the deque and yielded. If the closure
    /// returns `false`, or panics, the element remains in the deque and will not be yielded.
    ///
    /// Only elements that fall in the provided range are considered for extraction, but any elements
    /// after the range will still have to be moved if any element has been extracted.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without iterating
    /// or the iteration short-circuits, then the remaining elements will be retained.
    /// Use `extract_if().for_each(drop)` if you do not need the returned iterator,
    /// or [`retain_mut`] with a negated predicate if you also do not need to restrict the range.
    ///
    /// [`retain_mut`]: VecDeque::retain_mut
    ///
    /// Using this method is equivalent to the following code:
    ///
    /// ```
    /// #![feature(vec_deque_extract_if)]
    /// # use std::collections::VecDeque;
    /// # let some_predicate = |x: &mut i32| { *x % 2 == 1 };
    /// # let mut deq: VecDeque<_> = (0..10).collect();
    /// # let mut deq2 = deq.clone();
    /// # let range = 1..5;
    /// let mut i = range.start;
    /// let end_items = deq.len() - range.end;
    /// # let mut extracted = vec![];
    ///
    /// while i < deq.len() - end_items {
    ///     if some_predicate(&mut deq[i]) {
    ///         let val = deq.remove(i).unwrap();
    ///         // your code here
    /// #         extracted.push(val);
    ///     } else {
    ///         i += 1;
    ///     }
    /// }
    ///
    /// # let extracted2: Vec<_> = deq2.extract_if(range, some_predicate).collect();
    /// # assert_eq!(deq, deq2);
    /// # assert_eq!(extracted, extracted2);
    /// ```
    ///
    /// But `extract_if` is easier to use. `extract_if` is also more efficient,
    /// because it can backshift the elements of the array in bulk.
    ///
    /// The iterator also lets you mutate the value of each element in the
    /// closure, regardless of whether you choose to keep or remove it.
    ///
    /// # Panics
    ///
    /// If `range` is out of bounds.
    ///
    /// # Examples
    ///
    /// Splitting a deque into even and odd values, reusing the original deque:
    ///
    /// ```
    /// #![feature(vec_deque_extract_if)]
    /// use std::collections::VecDeque;
    ///
    /// let mut numbers = VecDeque::from([1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15]);
    ///
    /// let evens = numbers.extract_if(.., |x| *x % 2 == 0).collect::<VecDeque<_>>();
    /// let odds = numbers;
    ///
    /// assert_eq!(evens, VecDeque::from([2, 4, 6, 8, 14]));
    /// assert_eq!(odds, VecDeque::from([1, 3, 5, 9, 11, 13, 15]));
    /// ```
    ///
    /// Using the range argument to only process a part of the deque:
    ///
    /// ```
    /// #![feature(vec_deque_extract_if)]
    /// use std::collections::VecDeque;
    ///
    /// let mut items = VecDeque::from([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 1, 2]);
    /// let ones = items.extract_if(7.., |x| *x == 1).collect::<VecDeque<_>>();
    /// assert_eq!(items, VecDeque::from([0, 0, 0, 0, 0, 0, 0, 2, 2, 2]));
    /// assert_eq!(ones.len(), 3);
    /// ```
    #[unstable(feature = "vec_deque_extract_if", issue = "147750")]
    pub fn extract_if<F, R>(&mut self, range: R, filter: F) -> ExtractIf<'_, T, F, A>
    where
        F: FnMut(&mut T) -> bool,
        R: RangeBounds<usize>,
    {
        ExtractIf::new(self, filter, range)
    }
}

impl<T> VecDeque<T> {
    /// Creates an empty deque.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<u32> = VecDeque::new();
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_deque_new", since = "1.68.0")]
    #[must_use]
    pub const fn new() -> VecDeque<T> {
        // FIXME(const-hack): This should just be `VecDeque::new_in(Global)` once that hits stable.
        VecDeque { head: 0, len: 0, buf: RawVec::new() }
    }

    /// Creates an empty deque with space for at least `capacity` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<u32> = VecDeque::with_capacity(10);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> VecDeque<T> {
        Self::with_capacity_in(capacity, Global)
    }

    /// Creates an empty deque with space for at least `capacity` elements.
    ///
    /// # Errors
    ///
    /// Returns an error if the capacity exceeds `isize::MAX` _bytes_,
    /// or if the allocator reports allocation failure.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![feature(try_with_capacity)]
    /// # #[allow(unused)]
    /// # fn example() -> Result<(), std::collections::TryReserveError> {
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<u32> = VecDeque::try_with_capacity(10)?;
    /// # Ok(()) }
    /// ```
    #[inline]
    #[unstable(feature = "try_with_capacity", issue = "91913")]
    pub fn try_with_capacity(capacity: usize) -> Result<VecDeque<T>, TryReserveError> {
        Ok(VecDeque { head: 0, len: 0, buf: RawVec::try_with_capacity_in(capacity, Global)? })
    }
}

impl<T, A: Allocator> VecDeque<T, A> {
    /// Creates an empty deque.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<u32> = VecDeque::new();
    /// ```
    #[inline]
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub const fn new_in(alloc: A) -> VecDeque<T, A> {
        VecDeque { head: 0, len: 0, buf: RawVec::new_in(alloc) }
    }

    /// Creates an empty deque with space for at least `capacity` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<u32> = VecDeque::with_capacity(10);
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> VecDeque<T, A> {
        VecDeque { head: 0, len: 0, buf: RawVec::with_capacity_in(capacity, alloc) }
    }

    /// Creates a `VecDeque` from a raw allocation, when the initialized
    /// part of that allocation forms a *contiguous* subslice thereof.
    ///
    /// For use by `vec::IntoIter::into_vecdeque`
    ///
    /// # Safety
    ///
    /// All the usual requirements on the allocated memory like in
    /// `Vec::from_raw_parts_in`, but takes a *range* of elements that are
    /// initialized rather than only supporting `0..len`.  Requires that
    /// `initialized.start` ≤ `initialized.end` ≤ `capacity`.
    #[inline]
    #[cfg(not(test))]
    ///
    /// In addition, `initialized.start` must be a valid `head`, i.e. `initialized.start <
    /// capacity` unless the range is `0..0`: the resulting deque uses `head` unwrapped (e.g.
    /// `pop_front` reads slot `head` directly), so `head == capacity` reads past the buffer.
    /// (`vec::IntoIter::into_vecdeque` currently violates this for an exhausted iterator whose
    /// `Vec` had `capacity == len`; see rust-lang/rust#162452.)
    #[requires(initialized.start <= initialized.end && initialized.end <= capacity)]
    #[requires(initialized.start < capacity || initialized.start == 0)]
    #[requires(Layout::array::<T>(capacity).is_ok())]
    #[requires(T::IS_ZST || capacity == 0
        || core::ub_checks::can_write(ptr::slice_from_raw_parts_mut(ptr, capacity)))]
    #[ensures(|result| result.head == old(initialized.start)
        && result.len == old(initialized.end) - old(initialized.start)
        && result.invariant_holds()
        && (T::IS_ZST || result.capacity() == capacity))]
    pub(crate) unsafe fn from_contiguous_raw_parts_in(
        ptr: *mut T,
        initialized: Range<usize>,
        capacity: usize,
        alloc: A,
    ) -> Self {
        debug_assert!(initialized.start <= initialized.end);
        debug_assert!(initialized.end <= capacity);

        // SAFETY: Our safety precondition guarantees the range length won't wrap,
        // and that the allocation is valid for use in `RawVec`.
        unsafe {
            VecDeque {
                head: initialized.start,
                len: initialized.end.unchecked_sub(initialized.start),
                buf: RawVec::from_raw_parts_in(ptr, capacity, alloc),
            }
        }
    }

    /// Provides a reference to the element at the given index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// buf.push_back(6);
    /// assert_eq!(buf.get(1), Some(&4));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            let idx = self.to_physical_idx(index);
            unsafe { Some(&*self.ptr().add(idx)) }
        } else {
            None
        }
    }

    /// Provides a mutable reference to the element at the given index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// buf.push_back(6);
    /// assert_eq!(buf[1], 4);
    /// if let Some(elem) = buf.get_mut(1) {
    ///     *elem = 7;
    /// }
    /// assert_eq!(buf[1], 7);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            let idx = self.to_physical_idx(index);
            unsafe { Some(&mut *self.ptr().add(idx)) }
        } else {
            None
        }
    }

    /// Swaps elements at indices `i` and `j`.
    ///
    /// `i` and `j` may be equal.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if either index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// assert_eq!(buf, [3, 4, 5]);
    /// buf.swap(0, 2);
    /// assert_eq!(buf, [5, 4, 3]);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn swap(&mut self, i: usize, j: usize) {
        assert!(i < self.len());
        assert!(j < self.len());
        let ri = self.to_physical_idx(i);
        let rj = self.to_physical_idx(j);
        unsafe { ptr::swap(self.ptr().add(ri), self.ptr().add(rj)) }
    }

    /// Returns the number of elements the deque can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let buf: VecDeque<i32> = VecDeque::with_capacity(10);
    /// assert!(buf.capacity() >= 10);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn capacity(&self) -> usize {
        if T::IS_ZST { usize::MAX } else { self.buf.capacity() }
    }

    /// Reserves the minimum capacity for at least `additional` more elements to be inserted in the
    /// given deque. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore
    /// capacity can not be relied upon to be precisely minimal. Prefer [`reserve`] if future
    /// insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<i32> = [1].into();
    /// buf.reserve_exact(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    ///
    /// [`reserve`]: VecDeque::reserve
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve_exact(&mut self, additional: usize) {
        let new_cap = self.len.checked_add(additional).expect("capacity overflow");
        let old_cap = self.capacity();

        if new_cap > old_cap {
            self.buf.reserve_exact(self.len, additional);
            unsafe {
                self.handle_capacity_increase(old_cap);
            }
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// deque. The collection may reserve more space to speculatively avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<i32> = [1].into();
    /// buf.reserve(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[cfg_attr(not(test), rustc_diagnostic_item = "vecdeque_reserve")]
    pub fn reserve(&mut self, additional: usize) {
        let new_cap = self.len.checked_add(additional).expect("capacity overflow");
        let old_cap = self.capacity();

        if new_cap > old_cap {
            // we don't need to reserve_exact(), as the size doesn't have
            // to be a power of 2.
            self.buf.reserve(self.len, additional);
            unsafe {
                self.handle_capacity_increase(old_cap);
            }
        }
    }

    /// Tries to reserve the minimum capacity for at least `additional` more elements to
    /// be inserted in the given deque. After calling `try_reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional` if
    /// it returns `Ok(())`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: VecDeque::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows `usize`, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::TryReserveError;
    /// use std::collections::VecDeque;
    ///
    /// fn process_data(data: &[u32]) -> Result<VecDeque<u32>, TryReserveError> {
    ///     let mut output = VecDeque::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM(Out-Of-Memory) in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[stable(feature = "try_reserve", since = "1.57.0")]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let new_cap =
            self.len.checked_add(additional).ok_or(TryReserveErrorKind::CapacityOverflow)?;
        let old_cap = self.capacity();

        if new_cap > old_cap {
            self.buf.try_reserve_exact(self.len, additional)?;
            unsafe {
                self.handle_capacity_increase(old_cap);
            }
        }
        Ok(())
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given deque. The collection may reserve more space to speculatively avoid
    /// frequent reallocations. After calling `try_reserve`, capacity will be
    /// greater than or equal to `self.len() + additional` if it returns
    /// `Ok(())`. Does nothing if capacity is already sufficient. This method
    /// preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows `usize`, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::TryReserveError;
    /// use std::collections::VecDeque;
    ///
    /// fn process_data(data: &[u32]) -> Result<VecDeque<u32>, TryReserveError> {
    ///     let mut output = VecDeque::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[stable(feature = "try_reserve", since = "1.57.0")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let new_cap =
            self.len.checked_add(additional).ok_or(TryReserveErrorKind::CapacityOverflow)?;
        let old_cap = self.capacity();

        if new_cap > old_cap {
            self.buf.try_reserve(self.len, additional)?;
            unsafe {
                self.handle_capacity_increase(old_cap);
            }
        }
        Ok(())
    }

    /// Shrinks the capacity of the deque as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// deque that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::with_capacity(15);
    /// buf.extend(0..4);
    /// assert_eq!(buf.capacity(), 15);
    /// buf.shrink_to_fit();
    /// assert!(buf.capacity() >= 4);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }

    /// Shrinks the capacity of the deque with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::with_capacity(15);
    /// buf.extend(0..4);
    /// assert_eq!(buf.capacity(), 15);
    /// buf.shrink_to(6);
    /// assert!(buf.capacity() >= 6);
    /// buf.shrink_to(0);
    /// assert!(buf.capacity() >= 4);
    /// ```
    #[stable(feature = "shrink_to", since = "1.56.0")]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let target_cap = min_capacity.max(self.len);

        // never shrink ZSTs
        if T::IS_ZST || self.capacity() <= target_cap {
            return;
        }

        // There are three cases of interest:
        //   All elements are out of desired bounds
        //   Elements are contiguous, and tail is out of desired bounds
        //   Elements are discontiguous
        //
        // At all other times, element positions are unaffected.

        // `head` and `len` are at most `isize::MAX` and `target_cap < self.capacity()`, so nothing can
        // overflow.
        let tail_outside = (target_cap + 1..=self.capacity()).contains(&(self.head + self.len));
        // Used in the drop guard below.
        let old_head = self.head;

        if self.len == 0 {
            self.head = 0;
        } else if self.head >= target_cap && tail_outside {
            // Head and tail are both out of bounds, so copy all of them to the front.
            //
            //  H := head
            //  L := last element
            //                    H           L
            //   [. . . . . . . . o o o o o o o . ]
            //    H           L
            //   [o o o o o o o . ]
            unsafe {
                // nonoverlapping because `self.head >= target_cap >= self.len`.
                self.copy_nonoverlapping(self.head, 0, self.len);
            }
            self.head = 0;
        } else if self.head < target_cap && tail_outside {
            // Head is in bounds, tail is out of bounds.
            // Copy the overflowing part to the beginning of the
            // buffer. This won't overlap because `target_cap >= self.len`.
            //
            //  H := head
            //  L := last element
            //          H           L
            //   [. . . o o o o o o o . . . . . . ]
            //      L   H
            //   [o o . o o o o o ]
            let len = self.head + self.len - target_cap;
            unsafe {
                self.copy_nonoverlapping(target_cap, 0, len);
            }
        } else if !self.is_contiguous() {
            // The head slice is at least partially out of bounds, tail is in bounds.
            // Copy the head backwards so it lines up with the target capacity.
            // This won't overlap because `target_cap >= self.len`.
            //
            //  H := head
            //  L := last element
            //            L                   H
            //   [o o o o o . . . . . . . . . o o ]
            //            L   H
            //   [o o o o o . o o ]
            let head_len = self.capacity() - self.head;
            let new_head = target_cap - head_len;
            unsafe {
                // can't use `copy_nonoverlapping()` here because the new and old
                // regions for the head might overlap.
                self.copy(self.head, new_head, head_len);
            }
            self.head = new_head;
        }

        struct Guard<'a, T, A: Allocator> {
            deque: &'a mut VecDeque<T, A>,
            old_head: usize,
            target_cap: usize,
        }

        impl<T, A: Allocator> Drop for Guard<'_, T, A> {
            #[cold]
            fn drop(&mut self) {
                unsafe {
                    // SAFETY: This is only called if `buf.shrink_to_fit` unwinds,
                    // which is the only time it's safe to call `abort_shrink`.
                    self.deque.abort_shrink(self.old_head, self.target_cap)
                }
            }
        }

        let guard = Guard { deque: self, old_head, target_cap };

        guard.deque.buf.shrink_to_fit(target_cap);

        // Don't drop the guard if we didn't unwind.
        mem::forget(guard);

        debug_assert!(self.head < self.capacity() || self.capacity() == 0);
        debug_assert!(self.len <= self.capacity());
    }

    /// Reverts the deque back into a consistent state in case `shrink_to` failed.
    /// This is necessary to prevent UB if the backing allocator returns an error
    /// from `shrink` and `handle_alloc_error` subsequently unwinds (see #123369).
    ///
    /// `old_head` refers to the head index before `shrink_to` was called. `target_cap`
    /// is the capacity that it was trying to shrink to.
    ///
    /// # Safety
    ///
    /// Must only be called in the state `shrink_to` leaves behind when `buf.shrink_to_fit`
    /// unwinds: `self.len <= target_cap <= self.capacity()`, `self.head <= target_cap`,
    /// `old_head < self.capacity()`, and either the elements are contiguous within
    /// `target_cap` or the head slice `self.head..target_cap` fits back at `old_head`.
    #[requires(self.invariant_holds() && self.len <= target_cap && target_cap <= self.capacity())]
    #[requires(self.head <= target_cap && old_head < self.capacity())]
    #[requires(self.head <= target_cap - self.len
        || old_head.checked_add(target_cap - self.head).is_some_and(|end| end <= self.capacity()))]
    #[ensures(|_| self.len == old(self.len) && self.invariant_holds())]
    #[cfg_attr(kani, kani::modifies(&self.head, self.all_slots()))]
    unsafe fn abort_shrink(&mut self, old_head: usize, target_cap: usize) {
        // Moral equivalent of self.head + self.len <= target_cap. Won't overflow
        // because `self.len <= target_cap`.
        if self.head <= target_cap - self.len {
            // The deque's buffer is contiguous, so no need to copy anything around.
            return;
        }

        // `shrink_to` already copied the head to fit into the new capacity, so this won't overflow.
        let head_len = target_cap - self.head;
        // `self.head > target_cap - self.len` => `self.len > target_cap - self.head =: head_len` so this must be positive.
        let tail_len = self.len - head_len;

        if tail_len <= cmp::min(head_len, self.capacity() - target_cap) {
            // There's enough spare capacity to copy the tail to the back (because `tail_len < self.capacity() - target_cap`),
            // and copying the tail should be cheaper than copying the head (because `tail_len <= head_len`).

            unsafe {
                // The old tail and the new tail can't overlap because the head slice lies between them. The
                // head slice ends at `target_cap`, so that's where we copy to.
                self.copy_nonoverlapping(0, target_cap, tail_len);
            }
        } else {
            // Either there's not enough spare capacity to make the deque contiguous, or the head is shorter than the tail
            // (and therefore hopefully cheaper to copy).
            unsafe {
                // The old and the new head slice can overlap, so we can't use `copy_nonoverlapping` here.
                self.copy(self.head, old_head, head_len);
                self.head = old_head;
            }
        }
    }

    /// Shortens the deque, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater or equal to the deque's current length, this has
    /// no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, [5, 10, 15]);
    /// buf.truncate(1);
    /// assert_eq!(buf, [5]);
    /// ```
    #[stable(feature = "deque_extras", since = "1.16.0")]
    pub fn truncate(&mut self, len: usize) {
        /// Runs the destructor for all items in the slice when it gets dropped (normally or
        /// during unwinding).
        struct Dropper<'a, T>(&'a mut [T]);

        impl<'a, T> Drop for Dropper<'a, T> {
            fn drop(&mut self) {
                unsafe {
                    ptr::drop_in_place(self.0);
                }
            }
        }

        // Safe because:
        //
        // * Any slice passed to `drop_in_place` is valid; the second case has
        //   `len <= front.len()` and returning on `len > self.len()` ensures
        //   `begin <= back.len()` in the first case
        // * The head of the VecDeque is moved before calling `drop_in_place`,
        //   so no value is dropped twice if `drop_in_place` panics
        unsafe {
            if len >= self.len {
                return;
            }

            let (front, back) = self.as_mut_slices();
            if len > front.len() {
                let begin = len - front.len();
                let drop_back = back.get_unchecked_mut(begin..) as *mut _;
                self.len = len;
                ptr::drop_in_place(drop_back);
            } else {
                let drop_back = back as *mut _;
                let drop_front = front.get_unchecked_mut(len..) as *mut _;
                self.len = len;

                // Make sure the second half is dropped even when a destructor
                // in the first one panics.
                let _back_dropper = Dropper(&mut *drop_back);
                ptr::drop_in_place(drop_front);
            }
        }
    }

    /// Shortens the deque, keeping the last `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater or equal to the deque's current length, this has
    /// no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![feature(vec_deque_truncate_front)]
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_front(5);
    /// buf.push_front(10);
    /// buf.push_front(15);
    /// assert_eq!(buf, [15, 10, 5]);
    /// assert_eq!(buf.as_slices(), (&[15, 10, 5][..], &[][..]));
    /// buf.truncate_front(1);
    /// assert_eq!(buf.as_slices(), (&[5][..], &[][..]));
    /// ```
    #[unstable(feature = "vec_deque_truncate_front", issue = "140667")]
    pub fn truncate_front(&mut self, len: usize) {
        /// Runs the destructor for all items in the slice when it gets dropped (normally or
        /// during unwinding).
        struct Dropper<'a, T>(&'a mut [T]);

        impl<'a, T> Drop for Dropper<'a, T> {
            fn drop(&mut self) {
                unsafe {
                    ptr::drop_in_place(self.0);
                }
            }
        }

        unsafe {
            if len >= self.len {
                // No action is taken
                return;
            }

            let (front, back) = self.as_mut_slices();
            if len > back.len() {
                // The 'back' slice remains unchanged.
                // front.len() + back.len() == self.len, so 'end' is non-negative
                // and end < front.len()
                let end = front.len() - (len - back.len());
                let drop_front = front.get_unchecked_mut(..end) as *mut _;
                self.head += end;
                self.len = len;
                ptr::drop_in_place(drop_front);
            } else {
                let drop_front = front as *mut _;
                // 'end' is non-negative by the condition above
                let end = back.len() - len;
                let drop_back = back.get_unchecked_mut(..end) as *mut _;
                self.head = self.to_physical_idx(self.len - len);
                self.len = len;

                // Make sure the second half is dropped even when a destructor
                // in the first one panics.
                let _back_dropper = Dropper(&mut *drop_back);
                ptr::drop_in_place(drop_front);
            }
        }
    }

    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn allocator(&self) -> &A {
        self.buf.allocator()
    }

    /// Returns a front-to-back iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// let b: &[_] = &[&5, &3, &4];
    /// let c: Vec<&i32> = buf.iter().collect();
    /// assert_eq!(&c[..], b);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[cfg_attr(not(test), rustc_diagnostic_item = "vecdeque_iter")]
    pub fn iter(&self) -> Iter<'_, T> {
        let (a, b) = self.as_slices();
        Iter::new(a.iter(), b.iter())
    }

    /// Returns a front-to-back iterator that returns mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// for num in buf.iter_mut() {
    ///     *num = *num - 2;
    /// }
    /// let b: &[_] = &[&mut 3, &mut 1, &mut 2];
    /// assert_eq!(&buf.iter_mut().collect::<Vec<&mut i32>>()[..], b);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        let (a, b) = self.as_mut_slices();
        IterMut::new(a.iter_mut(), b.iter_mut())
    }

    /// Returns a pair of slices which contain, in order, the contents of the
    /// deque.
    ///
    /// If [`make_contiguous`] was previously called, all elements of the
    /// deque will be in the first slice and the second slice will be empty.
    /// Otherwise, the exact split point depends on implementation details
    /// and is not guaranteed.
    ///
    /// [`make_contiguous`]: VecDeque::make_contiguous
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::new();
    ///
    /// deque.push_back(0);
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let expected = [0, 1, 2];
    /// let (front, back) = deque.as_slices();
    /// assert_eq!(&expected[..front.len()], front);
    /// assert_eq!(&expected[front.len()..], back);
    ///
    /// deque.push_front(10);
    /// deque.push_front(9);
    ///
    /// let expected = [9, 10, 0, 1, 2];
    /// let (front, back) = deque.as_slices();
    /// assert_eq!(&expected[..front.len()], front);
    /// assert_eq!(&expected[front.len()..], back);
    /// ```
    #[inline]
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        let (a_range, b_range) = self.slice_ranges(.., self.len);
        // SAFETY: `slice_ranges` always returns valid ranges into
        // the physical buffer.
        unsafe { (&*self.buffer_range(a_range), &*self.buffer_range(b_range)) }
    }

    /// Returns a pair of slices which contain, in order, the contents of the
    /// deque.
    ///
    /// If [`make_contiguous`] was previously called, all elements of the
    /// deque will be in the first slice and the second slice will be empty.
    /// Otherwise, the exact split point depends on implementation details
    /// and is not guaranteed.
    ///
    /// [`make_contiguous`]: VecDeque::make_contiguous
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::new();
    ///
    /// deque.push_back(0);
    /// deque.push_back(1);
    ///
    /// deque.push_front(10);
    /// deque.push_front(9);
    ///
    /// // Since the split point is not guaranteed, we may need to update
    /// // either slice.
    /// let mut update_nth = |index: usize, val: u32| {
    ///     let (front, back) = deque.as_mut_slices();
    ///     if index > front.len() - 1 {
    ///         back[index - front.len()] = val;
    ///     } else {
    ///         front[index] = val;
    ///     }
    /// };
    ///
    /// update_nth(0, 42);
    /// update_nth(2, 24);
    ///
    /// let v: Vec<_> = deque.into();
    /// assert_eq!(v, [42, 10, 24, 1]);
    /// ```
    #[inline]
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        let (a_range, b_range) = self.slice_ranges(.., self.len);
        // SAFETY: `slice_ranges` always returns valid ranges into
        // the physical buffer.
        unsafe { (&mut *self.buffer_range(a_range), &mut *self.buffer_range(b_range)) }
    }

    /// Returns the number of elements in the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::new();
    /// assert_eq!(deque.len(), 0);
    /// deque.push_back(1);
    /// assert_eq!(deque.len(), 1);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("length", "size")]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::new();
    /// assert!(deque.is_empty());
    /// deque.push_front(1);
    /// assert!(!deque.is_empty());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Given a range into the logical buffer of the deque, this function
    /// return two ranges into the physical buffer that correspond to
    /// the given range. The `len` parameter should usually just be `self.len`;
    /// the reason it's passed explicitly is that if the deque is wrapped in
    /// a `Drain`, then `self.len` is not actually the length of the deque.
    ///
    /// # Safety
    ///
    /// This function is always safe to call. For the resulting ranges to be valid
    /// ranges into the physical buffer, the caller must ensure that the result of
    /// calling `slice::range(range, ..len)` represents a valid range into the
    /// logical buffer, and that all elements in that range are initialized.
    fn slice_ranges<R>(&self, range: R, len: usize) -> (Range<usize>, Range<usize>)
    where
        R: RangeBounds<usize>,
    {
        let Range { start, end } = slice::range(range, ..len);
        let len = end - start;

        if len == 0 {
            (0..0, 0..0)
        } else {
            // `slice::range` guarantees that `start <= end <= len`.
            // because `len != 0`, we know that `start < end`, so `start < len`
            // and the indexing is valid.
            let wrapped_start = self.to_physical_idx(start);

            // this subtraction can never overflow because `wrapped_start` is
            // at most `self.capacity()` (and if `self.capacity != 0`, then `wrapped_start` is strictly less
            // than `self.capacity`).
            let head_len = self.capacity() - wrapped_start;

            if head_len >= len {
                // we know that `len + wrapped_start <= self.capacity <= usize::MAX`, so this addition can't overflow
                (wrapped_start..wrapped_start + len, 0..0)
            } else {
                // can't overflow because of the if condition
                let tail_len = len - head_len;
                (wrapped_start..self.capacity(), 0..tail_len)
            }
        }
    }

    /// Creates an iterator that covers the specified range in the deque.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and past the length of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<_> = [1, 2, 3].into();
    /// let range = deque.range(2..).copied().collect::<VecDeque<_>>();
    /// assert_eq!(range, [3]);
    ///
    /// // A full range covers all contents
    /// let all = deque.range(..);
    /// assert_eq!(all.len(), 3);
    /// ```
    #[inline]
    #[stable(feature = "deque_range", since = "1.51.0")]
    pub fn range<R>(&self, range: R) -> Iter<'_, T>
    where
        R: RangeBounds<usize>,
    {
        let (a_range, b_range) = self.slice_ranges(range, self.len);
        // SAFETY: The ranges returned by `slice_ranges`
        // are valid ranges into the physical buffer, so
        // it's ok to pass them to `buffer_range` and
        // dereference the result.
        let a = unsafe { &*self.buffer_range(a_range) };
        let b = unsafe { &*self.buffer_range(b_range) };
        Iter::new(a.iter(), b.iter())
    }

    /// Creates an iterator that covers the specified mutable range in the deque.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and past the length of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque: VecDeque<_> = [1, 2, 3].into();
    /// for v in deque.range_mut(2..) {
    ///   *v *= 2;
    /// }
    /// assert_eq!(deque, [1, 2, 6]);
    ///
    /// // A full range covers all contents
    /// for v in deque.range_mut(..) {
    ///   *v *= 2;
    /// }
    /// assert_eq!(deque, [2, 4, 12]);
    /// ```
    #[inline]
    #[stable(feature = "deque_range", since = "1.51.0")]
    pub fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>
    where
        R: RangeBounds<usize>,
    {
        let (a_range, b_range) = self.slice_ranges(range, self.len);
        // SAFETY: The ranges returned by `slice_ranges`
        // are valid ranges into the physical buffer, so
        // it's ok to pass them to `buffer_range` and
        // dereference the result.
        let a = unsafe { &mut *self.buffer_range(a_range) };
        let b = unsafe { &mut *self.buffer_range(b_range) };
        IterMut::new(a.iter_mut(), b.iter_mut())
    }

    /// Removes the specified range from the deque in bulk, returning all
    /// removed elements as an iterator. If the iterator is dropped before
    /// being fully consumed, it drops the remaining removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the queue to optimize
    /// its implementation.
    ///
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and past the length of the deque.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`mem::forget`], for example), the deque may have lost and leaked
    /// elements arbitrarily, including elements outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque: VecDeque<_> = [1, 2, 3].into();
    /// let drained = deque.drain(2..).collect::<VecDeque<_>>();
    /// assert_eq!(drained, [3]);
    /// assert_eq!(deque, [1, 2]);
    ///
    /// // A full range clears all contents, like `clear()` does
    /// deque.drain(..);
    /// assert!(deque.is_empty());
    /// ```
    #[inline]
    #[stable(feature = "drain", since = "1.6.0")]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // When the Drain is first created, the source deque is shortened to
        // make sure no uninitialized or moved-from elements are accessible at
        // all if the Drain's destructor never gets to run.
        //
        // Drain will ptr::read out the values to remove.
        // When finished, the remaining data will be copied back to cover the hole,
        // and the head/tail values will be restored correctly.
        //
        let Range { start, end } = slice::range(range, ..self.len);
        let drain_start = start;
        let drain_len = end - start;

        // The deque's elements are parted into three segments:
        // * 0  -> drain_start
        // * drain_start -> drain_start+drain_len
        // * drain_start+drain_len -> self.len
        //
        // H = self.head; T = self.head+self.len; t = drain_start+drain_len; h = drain_head
        //
        // We store drain_start as self.len, and drain_len and self.len as
        // drain_len and orig_len respectively on the Drain. This also
        // truncates the effective array such that if the Drain is leaked, we
        // have forgotten about the potentially moved values after the start of
        // the drain.
        //
        //        H   h   t   T
        // [. . . o o x x o o . . .]
        //
        // "forget" about the values after the start of the drain until after
        // the drain is complete and the Drain destructor is run.

        unsafe { Drain::new(self, drain_start, drain_len) }
    }

    /// Creates a splicing iterator that replaces the specified range in the deque with the given
    /// `replace_with` iterator and yields the removed items. `replace_with` does not need to be the
    /// same length as `range`.
    ///
    /// `range` is removed even if the `Splice` iterator is not consumed before it is dropped.
    ///
    /// It is unspecified how many elements are removed from the deque if the `Splice` value is
    /// leaked.
    ///
    /// The input iterator `replace_with` is only consumed when the `Splice` value is dropped.
    ///
    /// This is optimal if:
    ///
    /// * The tail (elements in the deque after `range`) is empty,
    /// * or `replace_with` yields fewer or equal elements than `range`'s length
    /// * or the lower bound of its `size_hint()` is exact.
    ///
    /// Otherwise, a temporary vector is allocated and the tail is moved twice.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and past the length of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![feature(deque_extend_front)]
    /// # use std::collections::VecDeque;
    ///
    /// let mut v = VecDeque::from(vec![1, 2, 3, 4]);
    /// let new = [7, 8, 9];
    /// let u: Vec<_> = v.splice(1..3, new).collect();
    /// assert_eq!(v, [1, 7, 8, 9, 4]);
    /// assert_eq!(u, [2, 3]);
    /// ```
    ///
    /// Using `splice` to insert new items into a vector efficiently at a specific position
    /// indicated by an empty range:
    ///
    /// ```
    /// # #![feature(deque_extend_front)]
    /// # use std::collections::VecDeque;
    ///
    /// let mut v = VecDeque::from(vec![1, 5]);
    /// let new = [2, 3, 4];
    /// v.splice(1..1, new);
    /// assert_eq!(v, [1, 2, 3, 4, 5]);
    /// ```
    #[unstable(feature = "deque_extend_front", issue = "146975")]
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> Splice<'_, I::IntoIter, A>
    where
        R: RangeBounds<usize>,
        I: IntoIterator<Item = T>,
    {
        Splice { drain: self.drain(range), replace_with: replace_with.into_iter() }
    }

    /// Clears the deque, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::new();
    /// deque.push_back(1);
    /// deque.clear();
    /// assert!(deque.is_empty());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
        // Not strictly necessary, but leaves things in a more consistent/predictable state.
        self.head = 0;
    }

    /// Returns `true` if the deque contains an element equal to the
    /// given value.
    ///
    /// This operation is *O*(*n*).
    ///
    /// Note that if you have a sorted `VecDeque`, [`binary_search`] may be faster.
    ///
    /// [`binary_search`]: VecDeque::binary_search
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque: VecDeque<u32> = VecDeque::new();
    ///
    /// deque.push_back(0);
    /// deque.push_back(1);
    ///
    /// assert_eq!(deque.contains(&1), true);
    /// assert_eq!(deque.contains(&10), false);
    /// ```
    #[stable(feature = "vec_deque_contains", since = "1.12.0")]
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        let (a, b) = self.as_slices();
        a.contains(x) || b.contains(x)
    }

    /// Provides a reference to the front element, or `None` if the deque is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.front(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.front(), Some(&1));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("first")]
    pub fn front(&self) -> Option<&T> {
        self.get(0)
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.front_mut(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.front_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.front(), Some(&9));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.get_mut(0)
    }

    /// Provides a reference to the back element, or `None` if the deque is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.back(), Some(&2));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("last")]
    pub fn back(&self) -> Option<&T> {
        self.get(self.len.wrapping_sub(1))
    }

    /// Provides a mutable reference to the back element, or `None` if the
    /// deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.back_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.back(), Some(&9));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.get_mut(self.len.wrapping_sub(1))
    }

    /// Removes the first element and returns it, or `None` if the deque is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// d.push_back(1);
    /// d.push_back(2);
    ///
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            let old_head = self.head;
            self.head = self.to_physical_idx(1);
            self.len -= 1;
            unsafe {
                core::hint::assert_unchecked(self.len < self.capacity());
                Some(self.buffer_read(old_head))
            }
        }
    }

    /// Removes the last element from the deque and returns it, or `None` if
    /// it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// assert_eq!(buf.pop_back(), None);
    /// buf.push_back(1);
    /// buf.push_back(3);
    /// assert_eq!(buf.pop_back(), Some(3));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.len -= 1;
            unsafe {
                core::hint::assert_unchecked(self.len < self.capacity());
                Some(self.buffer_read(self.to_physical_idx(self.len)))
            }
        }
    }

    /// Removes and returns the first element from the deque if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the deque
    /// is empty (the predicate will not be called in that case).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque: VecDeque<i32> = vec![0, 1, 2, 3, 4].into();
    /// let pred = |x: &mut i32| *x % 2 == 0;
    ///
    /// assert_eq!(deque.pop_front_if(pred), Some(0));
    /// assert_eq!(deque, [1, 2, 3, 4]);
    /// assert_eq!(deque.pop_front_if(pred), None);
    /// ```
    #[stable(feature = "vec_deque_pop_if", since = "1.93.0")]
    pub fn pop_front_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        let first = self.front_mut()?;
        if predicate(first) { self.pop_front() } else { None }
    }

    /// Removes and returns the last element from the deque if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the deque
    /// is empty (the predicate will not be called in that case).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque: VecDeque<i32> = vec![0, 1, 2, 3, 4].into();
    /// let pred = |x: &mut i32| *x % 2 == 0;
    ///
    /// assert_eq!(deque.pop_back_if(pred), Some(4));
    /// assert_eq!(deque, [0, 1, 2, 3]);
    /// assert_eq!(deque.pop_back_if(pred), None);
    /// ```
    #[stable(feature = "vec_deque_pop_if", since = "1.93.0")]
    pub fn pop_back_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        let last = self.back_mut()?;
        if predicate(last) { self.pop_back() } else { None }
    }

    /// Prepends an element to the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::new();
    /// d.push_front(1);
    /// d.push_front(2);
    /// assert_eq!(d.front(), Some(&2));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn push_front(&mut self, value: T) {
        let _ = self.push_front_mut(value);
    }

    /// Prepends an element to the deque, returning a reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::from([1, 2, 3]);
    /// let x = d.push_front_mut(8);
    /// *x -= 1;
    /// assert_eq!(d.front(), Some(&7));
    /// ```
    #[stable(feature = "push_mut", since = "CURRENT_RUSTC_VERSION")]
    #[must_use = "if you don't need a reference to the value, use `VecDeque::push_front` instead"]
    pub fn push_front_mut(&mut self, value: T) -> &mut T {
        if self.is_full() {
            self.grow();
        }

        self.head = self.wrap_sub(self.head, 1);
        self.len += 1;
        // SAFETY: We know that self.head is within range of the deque.
        unsafe { self.buffer_write(self.head, value) }
    }

    /// Appends an element to the back of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(1);
    /// buf.push_back(3);
    /// assert_eq!(3, *buf.back().unwrap());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("push", "put", "append")]
    pub fn push_back(&mut self, value: T) {
        let _ = self.push_back_mut(value);
    }

    /// Appends an element to the back of the deque, returning a reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut d = VecDeque::from([1, 2, 3]);
    /// let x = d.push_back_mut(9);
    /// *x += 1;
    /// assert_eq!(d.back(), Some(&10));
    /// ```
    #[stable(feature = "push_mut", since = "CURRENT_RUSTC_VERSION")]
    #[must_use = "if you don't need a reference to the value, use `VecDeque::push_back` instead"]
    pub fn push_back_mut(&mut self, value: T) -> &mut T {
        if self.is_full() {
            self.grow();
        }

        let len = self.len;
        self.len += 1;
        unsafe { self.buffer_write(self.to_physical_idx(len), value) }
    }

    /// Prepends all contents of the iterator to the front of the deque.
    /// The order of the contents is preserved.
    ///
    /// To get behavior like [`append`][VecDeque::append] where elements are moved
    /// from the other collection to this one, use `self.prepend(other.drain(..))`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(deque_extend_front)]
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::from([4, 5, 6]);
    /// deque.prepend([1, 2, 3]);
    /// assert_eq!(deque, [1, 2, 3, 4, 5, 6]);
    /// ```
    ///
    /// Move values between collections like [`append`][VecDeque::append] does but prepend to the front:
    ///
    /// ```
    /// #![feature(deque_extend_front)]
    /// use std::collections::VecDeque;
    ///
    /// let mut deque1 = VecDeque::from([4, 5, 6]);
    /// let mut deque2 = VecDeque::from([1, 2, 3]);
    /// deque1.prepend(deque2.drain(..));
    /// assert_eq!(deque1, [1, 2, 3, 4, 5, 6]);
    /// assert!(deque2.is_empty());
    /// ```
    #[unstable(feature = "deque_extend_front", issue = "146975")]
    #[track_caller]
    pub fn prepend<I: IntoIterator<Item = T, IntoIter: DoubleEndedIterator>>(&mut self, other: I) {
        self.extend_front(other.into_iter().rev())
    }

    /// Prepends all contents of the iterator to the front of the deque,
    /// as if [`push_front`][VecDeque::push_front] was called repeatedly with
    /// the values yielded by the iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(deque_extend_front)]
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::from([4, 5, 6]);
    /// deque.extend_front([3, 2, 1]);
    /// assert_eq!(deque, [1, 2, 3, 4, 5, 6]);
    /// ```
    ///
    /// This behaves like [`push_front`][VecDeque::push_front] was called repeatedly:
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque = VecDeque::from([4, 5, 6]);
    /// for v in [3, 2, 1] {
    ///     deque.push_front(v);
    /// }
    /// assert_eq!(deque, [1, 2, 3, 4, 5, 6]);
    /// ```
    #[unstable(feature = "deque_extend_front", issue = "146975")]
    #[track_caller]
    pub fn extend_front<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        <Self as SpecExtendFront<T, I::IntoIter>>::spec_extend_front(self, iter.into_iter());
    }

    #[inline]
    fn is_contiguous(&self) -> bool {
        // Do the calculation like this to avoid overflowing if len + head > usize::MAX
        self.head <= self.capacity() - self.len
    }

    /// Removes an element from anywhere in the deque and returns it,
    /// replacing it with the first element.
    ///
    /// This does not preserve ordering, but is *O*(1).
    ///
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// assert_eq!(buf.swap_remove_front(0), None);
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// assert_eq!(buf.swap_remove_front(2), Some(3));
    /// assert_eq!(buf, [2, 1]);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        let length = self.len;
        if index < length && index != 0 {
            self.swap(index, 0);
        } else if index >= length {
            return None;
        }
        self.pop_front()
    }

    /// Removes an element from anywhere in the deque and returns it,
    /// replacing it with the last element.
    ///
    /// This does not preserve ordering, but is *O*(1).
    ///
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// assert_eq!(buf.swap_remove_back(0), None);
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, [1, 2, 3]);
    ///
    /// assert_eq!(buf.swap_remove_back(0), Some(1));
    /// assert_eq!(buf, [3, 2]);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        let length = self.len;
        if length > 0 && index < length - 1 {
            self.swap(index, length - 1);
        } else if index >= length {
            return None;
        }
        self.pop_back()
    }

    /// Inserts an element at `index` within the deque, shifting all elements
    /// with indices greater than or equal to `index` towards the back.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if `index` is strictly greater than the deque's length.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut vec_deque = VecDeque::new();
    /// vec_deque.push_back('a');
    /// vec_deque.push_back('b');
    /// vec_deque.push_back('c');
    /// assert_eq!(vec_deque, &['a', 'b', 'c']);
    ///
    /// vec_deque.insert(1, 'd');
    /// assert_eq!(vec_deque, &['a', 'd', 'b', 'c']);
    ///
    /// vec_deque.insert(4, 'e');
    /// assert_eq!(vec_deque, &['a', 'd', 'b', 'c', 'e']);
    /// ```
    #[stable(feature = "deque_extras_15", since = "1.5.0")]
    pub fn insert(&mut self, index: usize, value: T) {
        let _ = self.insert_mut(index, value);
    }

    /// Inserts an element at `index` within the deque, shifting all elements
    /// with indices greater than or equal to `index` towards the back, and
    /// returning a reference to it.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if `index` is strictly greater than the deque's length.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut vec_deque = VecDeque::from([1, 2, 3]);
    ///
    /// let x = vec_deque.insert_mut(1, 5);
    /// *x += 7;
    /// assert_eq!(vec_deque, &[1, 12, 2, 3]);
    /// ```
    #[stable(feature = "push_mut", since = "CURRENT_RUSTC_VERSION")]
    #[must_use = "if you don't need a reference to the value, use `VecDeque::insert` instead"]
    pub fn insert_mut(&mut self, index: usize, value: T) -> &mut T {
        assert!(index <= self.len(), "index out of bounds");

        if self.is_full() {
            self.grow();
        }

        let k = self.len - index;
        if k < index {
            // `index + 1` can't overflow, because if index was usize::MAX, then either the
            // assert would've failed, or the deque would've tried to grow past usize::MAX
            // and panicked.
            unsafe {
                // see `remove()` for explanation why this wrap_copy() call is safe.
                self.wrap_copy(self.to_physical_idx(index), self.to_physical_idx(index + 1), k);
                self.len += 1;
                self.buffer_write(self.to_physical_idx(index), value)
            }
        } else {
            let old_head = self.head;
            self.head = self.wrap_sub(self.head, 1);
            unsafe {
                self.wrap_copy(old_head, self.head, index);
                self.len += 1;
                self.buffer_write(self.to_physical_idx(index), value)
            }
        }
    }

    /// Removes and returns the element at `index` from the deque.
    /// Whichever end is closer to the removal point will be moved to make
    /// room, and all the affected elements will be moved to new positions.
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back('a');
    /// buf.push_back('b');
    /// buf.push_back('c');
    /// assert_eq!(buf, ['a', 'b', 'c']);
    ///
    /// assert_eq!(buf.remove(1), Some('b'));
    /// assert_eq!(buf, ['a', 'c']);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("delete", "take")]
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if self.len <= index {
            return None;
        }

        let wrapped_idx = self.to_physical_idx(index);

        let elem = unsafe { Some(self.buffer_read(wrapped_idx)) };

        let k = self.len - index - 1;
        // safety: due to the nature of the if-condition, whichever wrap_copy gets called,
        // its length argument will be at most `self.len / 2`, so there can't be more than
        // one overlapping area.
        if k < index {
            unsafe { self.wrap_copy(self.wrap_add(wrapped_idx, 1), wrapped_idx, k) };
            self.len -= 1;
        } else {
            let old_head = self.head;
            self.head = self.to_physical_idx(1);
            unsafe { self.wrap_copy(old_head, self.head, index) };
            self.len -= 1;
        }

        elem
    }

    /// Splits the deque into two at the given index.
    ///
    /// Returns a newly allocated `VecDeque`. `self` contains elements `[0, at)`,
    /// and the returned deque contains elements `[at, len)`.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = ['a', 'b', 'c'].into();
    /// let buf2 = buf.split_off(1);
    /// assert_eq!(buf, ['a']);
    /// assert_eq!(buf2, ['b', 'c']);
    /// ```
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    #[stable(feature = "split_off", since = "1.4.0")]
    pub fn split_off(&mut self, at: usize) -> Self
    where
        A: Clone,
    {
        let len = self.len;
        assert!(at <= len, "`at` out of bounds");

        let other_len = len - at;
        let mut other = VecDeque::with_capacity_in(other_len, self.allocator().clone());

        let (first_half, second_half) = self.as_slices();
        let first_len = first_half.len();
        let second_len = second_half.len();

        unsafe {
            if at < first_len {
                // `at` lies in the first half.
                let amount_in_first = first_len - at;

                ptr::copy_nonoverlapping(first_half.as_ptr().add(at), other.ptr(), amount_in_first);

                // just take all of the second half.
                ptr::copy_nonoverlapping(
                    second_half.as_ptr(),
                    other.ptr().add(amount_in_first),
                    second_len,
                );
            } else {
                // `at` lies in the second half, need to factor in the elements we skipped
                // in the first half.
                let offset = at - first_len;
                let amount_in_second = second_len - offset;
                ptr::copy_nonoverlapping(
                    second_half.as_ptr().add(offset),
                    other.ptr(),
                    amount_in_second,
                );
            }
        }

        // Cleanup where the ends of the buffers are
        self.len = at;
        other.len = other_len;

        other
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new number of elements in self overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = [1, 2].into();
    /// let mut buf2: VecDeque<_> = [3, 4].into();
    /// buf.append(&mut buf2);
    /// assert_eq!(buf, [1, 2, 3, 4]);
    /// assert_eq!(buf2, []);
    /// ```
    #[inline]
    #[stable(feature = "append", since = "1.4.0")]
    pub fn append(&mut self, other: &mut Self) {
        if T::IS_ZST {
            self.len = self.len.checked_add(other.len).expect("capacity overflow");
            other.len = 0;
            other.head = 0;
            return;
        }

        self.reserve(other.len);
        unsafe {
            let (left, right) = other.as_slices();
            self.copy_slice(self.to_physical_idx(self.len), left);
            // no overflow, because self.capacity() >= old_cap + left.len() >= self.len + left.len()
            self.copy_slice(self.to_physical_idx(self.len + left.len()), right);
        }
        // SAFETY: Update pointers after copying to avoid leaving doppelganger
        // in case of panics.
        self.len += other.len;
        // Now that we own its values, forget everything in `other`.
        other.len = 0;
        other.head = 0;
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns false.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.extend(1..5);
    /// buf.retain(|&x| x % 2 == 0);
    /// assert_eq!(buf, [2, 4]);
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.extend(1..6);
    ///
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// buf.retain(|_| *iter.next().unwrap());
    /// assert_eq!(buf, [2, 3, 5]);
    /// ```
    #[stable(feature = "vec_deque_retain", since = "1.4.0")]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&mut e)` returns false.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.extend(1..5);
    /// buf.retain_mut(|x| if *x % 2 == 0 {
    ///     *x += 1;
    ///     true
    /// } else {
    ///     false
    /// });
    /// assert_eq!(buf, [3, 5]);
    /// ```
    #[stable(feature = "vec_retain_mut", since = "1.61.0")]
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.len;
        let mut idx = 0;
        let mut cur = 0;

        // Stage 1: All values are retained.
        #[safety::loop_invariant(cur <= len && idx <= cur)]
        #[cfg_attr(kani, kani::loop_modifies(&cur, &idx, self.all_slots()))]
        while cur < len {
            if !f(&mut self[cur]) {
                cur += 1;
                break;
            }
            cur += 1;
            idx += 1;
        }
        // Stage 2: Swap retained value into current idx.
        #[safety::loop_invariant(cur <= len && idx <= cur)]
        #[cfg_attr(kani, kani::loop_modifies(&cur, &idx, self.all_slots()))]
        while cur < len {
            if !f(&mut self[cur]) {
                cur += 1;
                continue;
            }

            self.swap(idx, cur);
            cur += 1;
            idx += 1;
        }
        // Stage 3: Truncate all values after idx.
        if cur != idx {
            self.truncate(idx);
        }
    }

    // Double the buffer size. This method is inline(never), so we expect it to only
    // be called in cold paths.
    // This may panic or abort
    #[inline(never)]
    fn grow(&mut self) {
        // Extend or possibly remove this assertion when valid use-cases for growing the
        // buffer without it being full emerge
        debug_assert!(self.is_full());
        let old_cap = self.capacity();
        self.buf.grow_one();
        unsafe {
            self.handle_capacity_increase(old_cap);
        }
        debug_assert!(!self.is_full());
    }

    /// Modifies the deque in-place so that `len()` is equal to `new_len`,
    /// either by removing excess elements from the back or by appending
    /// elements generated by calling `generator` to the back.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, [5, 10, 15]);
    ///
    /// buf.resize_with(5, Default::default);
    /// assert_eq!(buf, [5, 10, 15, 0, 0]);
    ///
    /// buf.resize_with(2, || unreachable!());
    /// assert_eq!(buf, [5, 10]);
    ///
    /// let mut state = 100;
    /// buf.resize_with(5, || { state += 1; state });
    /// assert_eq!(buf, [5, 10, 101, 102, 103]);
    /// ```
    #[stable(feature = "vec_resize_with", since = "1.33.0")]
    pub fn resize_with(&mut self, new_len: usize, generator: impl FnMut() -> T) {
        let len = self.len;

        if new_len > len {
            self.extend(repeat_with(generator).take(new_len - len))
        } else {
            self.truncate(new_len);
        }
    }

    /// Rearranges the internal storage of this deque so it is one contiguous
    /// slice, which is then returned.
    ///
    /// This method does not allocate and does not change the order of the
    /// inserted elements. As it returns a mutable slice, this can be used to
    /// sort a deque.
    ///
    /// Once the internal storage is contiguous, the [`as_slices`] and
    /// [`as_mut_slices`] methods will return the entire contents of the
    /// deque in a single slice.
    ///
    /// [`as_slices`]: VecDeque::as_slices
    /// [`as_mut_slices`]: VecDeque::as_mut_slices
    ///
    /// # Examples
    ///
    /// Sorting the content of a deque.
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::with_capacity(15);
    ///
    /// buf.push_back(2);
    /// buf.push_back(1);
    /// buf.push_front(3);
    ///
    /// // sorting the deque
    /// buf.make_contiguous().sort();
    /// assert_eq!(buf.as_slices(), (&[1, 2, 3] as &[_], &[] as &[_]));
    ///
    /// // sorting it in reverse order
    /// buf.make_contiguous().sort_by(|a, b| b.cmp(a));
    /// assert_eq!(buf.as_slices(), (&[3, 2, 1] as &[_], &[] as &[_]));
    /// ```
    ///
    /// Getting immutable access to the contiguous slice.
    ///
    /// ```rust
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    ///
    /// buf.push_back(2);
    /// buf.push_back(1);
    /// buf.push_front(3);
    ///
    /// buf.make_contiguous();
    /// if let (slice, &[]) = buf.as_slices() {
    ///     // we can now be sure that `slice` contains all elements of the deque,
    ///     // while still having immutable access to `buf`.
    ///     assert_eq!(buf.len(), slice.len());
    ///     assert_eq!(slice, &[3, 2, 1] as &[_]);
    /// }
    /// ```
    #[stable(feature = "deque_make_contiguous", since = "1.48.0")]
    pub fn make_contiguous(&mut self) -> &mut [T] {
        if T::IS_ZST {
            self.head = 0;
        }

        if self.is_contiguous() {
            unsafe { return slice::from_raw_parts_mut(self.ptr().add(self.head), self.len) }
        }

        let &mut Self { head, len, .. } = self;
        let ptr = self.ptr();
        let cap = self.capacity();

        let free = cap - len;
        let head_len = cap - head;
        let tail = len - head_len;
        let tail_len = tail;

        if free >= head_len {
            // there is enough free space to copy the head in one go,
            // this means that we first shift the tail backwards, and then
            // copy the head to the correct position.
            //
            // from: DEFGH....ABC
            // to:   ABCDEFGH....
            unsafe {
                self.copy(0, head_len, tail_len);
                // ...DEFGH.ABC
                self.copy_nonoverlapping(head, 0, head_len);
                // ABCDEFGH....
            }

            self.head = 0;
        } else if free >= tail_len {
            // there is enough free space to copy the tail in one go,
            // this means that we first shift the head forwards, and then
            // copy the tail to the correct position.
            //
            // from: FGH....ABCDE
            // to:   ...ABCDEFGH.
            unsafe {
                self.copy(head, tail, head_len);
                // FGHABCDE....
                self.copy_nonoverlapping(0, tail + head_len, tail_len);
                // ...ABCDEFGH.
            }

            self.head = tail;
        } else {
            // `free` is smaller than both `head_len` and `tail_len`.
            // the general algorithm for this first moves the slices
            // right next to each other and then uses `slice::rotate`
            // to rotate them into place:
            //
            // initially:   HIJK..ABCDEFG
            // step 1:      ..HIJKABCDEFG
            // step 2:      ..ABCDEFGHIJK
            //
            // or:
            //
            // initially:   FGHIJK..ABCDE
            // step 1:      FGHIJKABCDE..
            // step 2:      ABCDEFGHIJK..

            // pick the shorter of the 2 slices to reduce the amount
            // of memory that needs to be moved around.
            if head_len > tail_len {
                // tail is shorter, so:
                //  1. copy tail forwards
                //  2. rotate used part of the buffer
                //  3. update head to point to the new beginning (which is just `free`)

                unsafe {
                    // if there is no free space in the buffer, then the slices are already
                    // right next to each other and we don't need to move any memory.
                    if free != 0 {
                        // because we only move the tail forward as much as there's free space
                        // behind it, we don't overwrite any elements of the head slice, and
                        // the slices end up right next to each other.
                        self.copy(0, free, tail_len);
                    }

                    // We just copied the tail right next to the head slice,
                    // so all of the elements in the range are initialized
                    let slice = &mut *self.buffer_range(free..self.capacity());

                    // because the deque wasn't contiguous, we know that `tail_len < self.len == slice.len()`,
                    // so this will never panic.
                    slice.rotate_left(tail_len);

                    // the used part of the buffer now is `free..self.capacity()`, so set
                    // `head` to the beginning of that range.
                    self.head = free;
                }
            } else {
                // head is shorter so:
                //  1. copy head backwards
                //  2. rotate used part of the buffer
                //  3. update head to point to the new beginning (which is the beginning of the buffer)

                unsafe {
                    // if there is no free space in the buffer, then the slices are already
                    // right next to each other and we don't need to move any memory.
                    if free != 0 {
                        // copy the head slice to lie right behind the tail slice.
                        self.copy(self.head, tail_len, head_len);
                    }

                    // because we copied the head slice so that both slices lie right
                    // next to each other, all the elements in the range are initialized.
                    let slice = &mut *self.buffer_range(0..self.len);

                    // because the deque wasn't contiguous, we know that `head_len < self.len == slice.len()`
                    // so this will never panic.
                    slice.rotate_right(head_len);

                    // the used part of the buffer now is `0..self.len`, so set
                    // `head` to the beginning of that range.
                    self.head = 0;
                }
            }
        }

        unsafe { slice::from_raw_parts_mut(ptr.add(self.head), self.len) }
    }

    /// Rotates the double-ended queue `n` places to the left.
    ///
    /// Equivalently,
    /// - Rotates item `n` into the first position.
    /// - Pops the first `n` items and pushes them to the end.
    /// - Rotates `len() - n` places to the right.
    ///
    /// # Panics
    ///
    /// If `n` is greater than `len()`. Note that `n == len()`
    /// does _not_ panic and is a no-op rotation.
    ///
    /// # Complexity
    ///
    /// Takes `*O*(min(n, len() - n))` time and no extra space.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = (0..10).collect();
    ///
    /// buf.rotate_left(3);
    /// assert_eq!(buf, [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
    ///
    /// for i in 1..10 {
    ///     assert_eq!(i * 3 % 10, buf[0]);
    ///     buf.rotate_left(3);
    /// }
    /// assert_eq!(buf, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// ```
    #[stable(feature = "vecdeque_rotate", since = "1.36.0")]
    pub fn rotate_left(&mut self, n: usize) {
        assert!(n <= self.len());
        let k = self.len - n;
        if n <= k {
            unsafe { self.rotate_left_inner(n) }
        } else {
            unsafe { self.rotate_right_inner(k) }
        }
    }

    /// Rotates the double-ended queue `n` places to the right.
    ///
    /// Equivalently,
    /// - Rotates the first item into position `n`.
    /// - Pops the last `n` items and pushes them to the front.
    /// - Rotates `len() - n` places to the left.
    ///
    /// # Panics
    ///
    /// If `n` is greater than `len()`. Note that `n == len()`
    /// does _not_ panic and is a no-op rotation.
    ///
    /// # Complexity
    ///
    /// Takes `*O*(min(n, len() - n))` time and no extra space.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf: VecDeque<_> = (0..10).collect();
    ///
    /// buf.rotate_right(3);
    /// assert_eq!(buf, [7, 8, 9, 0, 1, 2, 3, 4, 5, 6]);
    ///
    /// for i in 1..10 {
    ///     assert_eq!(0, buf[i * 3 % 10]);
    ///     buf.rotate_right(3);
    /// }
    /// assert_eq!(buf, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// ```
    #[stable(feature = "vecdeque_rotate", since = "1.36.0")]
    pub fn rotate_right(&mut self, n: usize) {
        assert!(n <= self.len());
        let k = self.len - n;
        if n <= k {
            unsafe { self.rotate_right_inner(n) }
        } else {
            unsafe { self.rotate_left_inner(k) }
        }
    }

    // SAFETY: the following two methods require that the rotation amount
    // be less than half the length of the deque.
    //
    // `wrap_copy` requires that `min(x, capacity() - x) + copy_len <= capacity()`,
    // but then `min` is never more than half the capacity, regardless of x,
    // so it's sound to call here because we're calling with something
    // less than half the length, which is never above half the capacity.

    #[requires(self.invariant_holds() && mid <= self.len / 2)]
    #[ensures(|_| self.len == old(self.len) && self.invariant_holds())]
    #[cfg_attr(kani, kani::modifies(&self.head, self.all_slots()))]
    unsafe fn rotate_left_inner(&mut self, mid: usize) {
        debug_assert!(mid * 2 <= self.len());
        unsafe {
            self.wrap_copy(self.head, self.to_physical_idx(self.len), mid);
        }
        self.head = self.to_physical_idx(mid);
    }

    #[requires(self.invariant_holds() && k <= self.len / 2)]
    #[ensures(|_| self.len == old(self.len) && self.invariant_holds())]
    #[cfg_attr(kani, kani::modifies(&self.head, self.all_slots()))]
    unsafe fn rotate_right_inner(&mut self, k: usize) {
        debug_assert!(k * 2 <= self.len());
        self.head = self.wrap_sub(self.head, k);
        unsafe {
            self.wrap_copy(self.to_physical_idx(self.len), self.head, k);
        }
    }

    /// Binary searches this `VecDeque` for a given element.
    /// If the `VecDeque` is not sorted, the returned result is unspecified and
    /// meaningless.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// See also [`binary_search_by`], [`binary_search_by_key`], and [`partition_point`].
    ///
    /// [`binary_search_by`]: VecDeque::binary_search_by
    /// [`binary_search_by_key`]: VecDeque::binary_search_by_key
    /// [`partition_point`]: VecDeque::partition_point
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a
    /// uniquely determined position; the second and third are not
    /// found; the fourth could match any position in `[1, 4]`.
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
    ///
    /// assert_eq!(deque.binary_search(&13),  Ok(9));
    /// assert_eq!(deque.binary_search(&4),   Err(7));
    /// assert_eq!(deque.binary_search(&100), Err(13));
    /// let r = deque.binary_search(&1);
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    ///
    /// If you want to insert an item to a sorted deque, while maintaining
    /// sort order, consider using [`partition_point`]:
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
    /// let num = 42;
    /// let idx = deque.partition_point(|&x| x <= num);
    /// // If `num` is unique, `s.partition_point(|&x| x < num)` (with `<`) is equivalent to
    /// // `s.binary_search(&num).unwrap_or_else(|x| x)`, but using `<=` may allow `insert`
    /// // to shift less elements.
    /// deque.insert(idx, num);
    /// assert_eq!(deque, &[0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
    /// ```
    #[stable(feature = "vecdeque_binary_search", since = "1.54.0")]
    #[inline]
    pub fn binary_search(&self, x: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|e| e.cmp(x))
    }

    /// Binary searches this `VecDeque` with a comparator function.
    ///
    /// The comparator function should return an order code that indicates
    /// whether its argument is `Less`, `Equal` or `Greater` the desired
    /// target.
    /// If the `VecDeque` is not sorted or if the comparator function does not
    /// implement an order consistent with the sort order of the underlying
    /// `VecDeque`, the returned result is unspecified and meaningless.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// See also [`binary_search`], [`binary_search_by_key`], and [`partition_point`].
    ///
    /// [`binary_search`]: VecDeque::binary_search
    /// [`binary_search_by_key`]: VecDeque::binary_search_by_key
    /// [`partition_point`]: VecDeque::partition_point
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a
    /// uniquely determined position; the second and third are not
    /// found; the fourth could match any position in `[1, 4]`.
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
    ///
    /// assert_eq!(deque.binary_search_by(|x| x.cmp(&13)),  Ok(9));
    /// assert_eq!(deque.binary_search_by(|x| x.cmp(&4)),   Err(7));
    /// assert_eq!(deque.binary_search_by(|x| x.cmp(&100)), Err(13));
    /// let r = deque.binary_search_by(|x| x.cmp(&1));
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    #[stable(feature = "vecdeque_binary_search", since = "1.54.0")]
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        let (front, back) = self.as_slices();
        let cmp_back = back.first().map(|elem| f(elem));

        if let Some(Ordering::Equal) = cmp_back {
            Ok(front.len())
        } else if let Some(Ordering::Less) = cmp_back {
            back.binary_search_by(f).map(|idx| idx + front.len()).map_err(|idx| idx + front.len())
        } else {
            front.binary_search_by(f)
        }
    }

    /// Binary searches this `VecDeque` with a key extraction function.
    ///
    /// Assumes that the deque is sorted by the key, for instance with
    /// [`make_contiguous().sort_by_key()`] using the same key extraction function.
    /// If the deque is not sorted by the key, the returned result is
    /// unspecified and meaningless.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// See also [`binary_search`], [`binary_search_by`], and [`partition_point`].
    ///
    /// [`make_contiguous().sort_by_key()`]: VecDeque::make_contiguous
    /// [`binary_search`]: VecDeque::binary_search
    /// [`binary_search_by`]: VecDeque::binary_search_by
    /// [`partition_point`]: VecDeque::partition_point
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements in a slice of pairs sorted by
    /// their second elements. The first is found, with a uniquely
    /// determined position; the second and third are not found; the
    /// fourth could match any position in `[1, 4]`.
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<_> = [(0, 0), (2, 1), (4, 1), (5, 1),
    ///          (3, 1), (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
    ///          (1, 21), (2, 34), (4, 55)].into();
    ///
    /// assert_eq!(deque.binary_search_by_key(&13, |&(a, b)| b),  Ok(9));
    /// assert_eq!(deque.binary_search_by_key(&4, |&(a, b)| b),   Err(7));
    /// assert_eq!(deque.binary_search_by_key(&100, |&(a, b)| b), Err(13));
    /// let r = deque.binary_search_by_key(&1, |&(a, b)| b);
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    #[stable(feature = "vecdeque_binary_search", since = "1.54.0")]
    #[inline]
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> B,
        B: Ord,
    {
        self.binary_search_by(|k| f(k).cmp(b))
    }

    /// Returns the index of the partition point according to the given predicate
    /// (the index of the first element of the second partition).
    ///
    /// The deque is assumed to be partitioned according to the given predicate.
    /// This means that all elements for which the predicate returns true are at the start of the deque
    /// and all elements for which the predicate returns false are at the end.
    /// For example, `[7, 15, 3, 5, 4, 12, 6]` is partitioned under the predicate `x % 2 != 0`
    /// (all odd numbers are at the start, all even at the end).
    ///
    /// If the deque is not partitioned, the returned result is unspecified and meaningless,
    /// as this method performs a kind of binary search.
    ///
    /// See also [`binary_search`], [`binary_search_by`], and [`binary_search_by_key`].
    ///
    /// [`binary_search`]: VecDeque::binary_search
    /// [`binary_search_by`]: VecDeque::binary_search_by
    /// [`binary_search_by_key`]: VecDeque::binary_search_by_key
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deque: VecDeque<_> = [1, 2, 3, 3, 5, 6, 7].into();
    /// let i = deque.partition_point(|&x| x < 5);
    ///
    /// assert_eq!(i, 4);
    /// assert!(deque.iter().take(i).all(|&x| x < 5));
    /// assert!(deque.iter().skip(i).all(|&x| !(x < 5)));
    /// ```
    ///
    /// If you want to insert an item to a sorted deque, while maintaining
    /// sort order:
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
    /// let num = 42;
    /// let idx = deque.partition_point(|&x| x < num);
    /// deque.insert(idx, num);
    /// assert_eq!(deque, &[0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
    /// ```
    #[stable(feature = "vecdeque_binary_search", since = "1.54.0")]
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        let (front, back) = self.as_slices();

        if let Some(true) = back.first().map(|v| pred(v)) {
            back.partition_point(pred) + front.len()
        } else {
            front.partition_point(pred)
        }
    }
}

impl<T: Clone, A: Allocator> VecDeque<T, A> {
    /// Modifies the deque in-place so that `len()` is equal to new_len,
    /// either by removing excess elements from the back or by appending clones of `value`
    /// to the back.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let mut buf = VecDeque::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, [5, 10, 15]);
    ///
    /// buf.resize(2, 0);
    /// assert_eq!(buf, [5, 10]);
    ///
    /// buf.resize(5, 20);
    /// assert_eq!(buf, [5, 10, 20, 20, 20]);
    /// ```
    #[stable(feature = "deque_extras", since = "1.16.0")]
    pub fn resize(&mut self, new_len: usize, value: T) {
        if new_len > self.len() {
            let extra = new_len - self.len();
            self.extend(repeat_n(value, extra))
        } else {
            self.truncate(new_len);
        }
    }

    /// Clones the elements at the range `src` and appends them to the end.
    ///
    /// # Panics
    ///
    /// Panics if the starting index is greater than the end index
    /// or if either index is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(deque_extend_front)]
    /// use std::collections::VecDeque;
    ///
    /// let mut characters = VecDeque::from(['a', 'b', 'c', 'd', 'e']);
    /// characters.extend_from_within(2..);
    /// assert_eq!(characters, ['a', 'b', 'c', 'd', 'e', 'c', 'd', 'e']);
    ///
    /// let mut numbers = VecDeque::from([0, 1, 2, 3, 4]);
    /// numbers.extend_from_within(..2);
    /// assert_eq!(numbers, [0, 1, 2, 3, 4, 0, 1]);
    ///
    /// let mut strings = VecDeque::from([String::from("hello"), String::from("world"), String::from("!")]);
    /// strings.extend_from_within(1..=2);
    /// assert_eq!(strings, ["hello", "world", "!", "world", "!"]);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "deque_extend_front", issue = "146975")]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
    {
        let range = slice::range(src, ..self.len());
        self.reserve(range.len());

        // SAFETY:
        // - `slice::range` guarantees that the given range is valid for indexing self
        // - at least `range.len()` additional space is available
        unsafe {
            self.spec_extend_from_within(range);
        }
    }

    /// Clones the elements at the range `src` and prepends them to the front.
    ///
    /// # Panics
    ///
    /// Panics if the starting index is greater than the end index
    /// or if either index is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(deque_extend_front)]
    /// use std::collections::VecDeque;
    ///
    /// let mut characters = VecDeque::from(['a', 'b', 'c', 'd', 'e']);
    /// characters.prepend_from_within(2..);
    /// assert_eq!(characters, ['c', 'd', 'e', 'a', 'b', 'c', 'd', 'e']);
    ///
    /// let mut numbers = VecDeque::from([0, 1, 2, 3, 4]);
    /// numbers.prepend_from_within(..2);
    /// assert_eq!(numbers, [0, 1, 0, 1, 2, 3, 4]);
    ///
    /// let mut strings = VecDeque::from([String::from("hello"), String::from("world"), String::from("!")]);
    /// strings.prepend_from_within(1..=2);
    /// assert_eq!(strings, ["world", "!", "hello", "world", "!"]);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "deque_extend_front", issue = "146975")]
    pub fn prepend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
    {
        let range = slice::range(src, ..self.len());
        self.reserve(range.len());

        // SAFETY:
        // - `slice::range` guarantees that the given range is valid for indexing self
        // - at least `range.len()` additional space is available
        unsafe {
            self.spec_prepend_from_within(range);
        }
    }
}

/// Associated functions have the following preconditions:
///
/// - `src` needs to be a valid range: `src.start <= src.end <= self.len()`.
/// - The buffer must have enough spare capacity: `self.capacity() - self.len() >= src.len()`.
#[cfg(not(no_global_oom_handling))]
trait SpecExtendFromWithin {
    unsafe fn spec_extend_from_within(&mut self, src: Range<usize>);

    unsafe fn spec_prepend_from_within(&mut self, src: Range<usize>);
}

#[cfg(not(no_global_oom_handling))]
impl<T: Clone, A: Allocator> SpecExtendFromWithin for VecDeque<T, A> {
    default unsafe fn spec_extend_from_within(&mut self, src: Range<usize>) {
        let dst = self.len();
        let count = src.end - src.start;
        let src = src.start;

        unsafe {
            // SAFETY:
            // - Ranges do not overlap: src entirely spans initialized values, dst entirely spans uninitialized values.
            // - Ranges are in bounds: guaranteed by the caller.
            let ranges = self.nonoverlapping_ranges(src, dst, count, self.head);

            // `len` is updated after every clone to prevent leaking and
            // leave the deque in the right state when a clone implementation panics

            for (src, dst, count) in ranges {
                for offset in 0..count {
                    dst.add(offset).write((*src.add(offset)).clone());
                    self.len += 1;
                }
            }
        }
    }

    default unsafe fn spec_prepend_from_within(&mut self, src: Range<usize>) {
        let dst = 0;
        let count = src.end - src.start;
        let src = src.start + count;

        let new_head = self.wrap_sub(self.head, count);
        let cap = self.capacity();

        unsafe {
            // SAFETY:
            // - Ranges do not overlap: src entirely spans initialized values, dst entirely spans uninitialized values.
            // - Ranges are in bounds: guaranteed by the caller.
            let ranges = self.nonoverlapping_ranges(src, dst, count, new_head);

            // Cloning is done in reverse because we prepend to the front of the deque,
            // we can't get holes in the *logical* buffer.
            // `head` and `len` are updated after every clone to prevent leaking and
            // leave the deque in the right state when a clone implementation panics

            // Clone the first range
            let (src, dst, count) = ranges[1];
            for offset in (0..count).rev() {
                dst.add(offset).write((*src.add(offset)).clone());
                self.head -= 1;
                self.len += 1;
            }

            // Clone the second range
            let (src, dst, count) = ranges[0];
            let mut iter = (0..count).rev();
            if let Some(offset) = iter.next() {
                dst.add(offset).write((*src.add(offset)).clone());
                // After the first clone of the second range, wrap `head` around
                if self.head == 0 {
                    self.head = cap;
                }
                self.head -= 1;
                self.len += 1;

                // Continue like normal
                for offset in iter {
                    dst.add(offset).write((*src.add(offset)).clone());
                    self.head -= 1;
                    self.len += 1;
                }
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: TrivialClone, A: Allocator> SpecExtendFromWithin for VecDeque<T, A> {
    unsafe fn spec_extend_from_within(&mut self, src: Range<usize>) {
        let dst = self.len();
        let count = src.end - src.start;
        let src = src.start;

        unsafe {
            // SAFETY:
            // - Ranges do not overlap: src entirely spans initialized values, dst entirely spans uninitialized values.
            // - Ranges are in bounds: guaranteed by the caller.
            let ranges = self.nonoverlapping_ranges(src, dst, count, self.head);
            for (src, dst, count) in ranges {
                ptr::copy_nonoverlapping(src, dst, count);
            }
        }

        // SAFETY:
        // - The elements were just initialized by `copy_nonoverlapping`
        self.len += count;
    }

    unsafe fn spec_prepend_from_within(&mut self, src: Range<usize>) {
        let dst = 0;
        let count = src.end - src.start;
        let src = src.start + count;

        let new_head = self.wrap_sub(self.head, count);

        unsafe {
            // SAFETY:
            // - Ranges do not overlap: src entirely spans initialized values, dst entirely spans uninitialized values.
            // - Ranges are in bounds: guaranteed by the caller.
            let ranges = self.nonoverlapping_ranges(src, dst, count, new_head);
            for (src, dst, count) in ranges {
                ptr::copy_nonoverlapping(src, dst, count);
            }
        }

        // SAFETY:
        // - The elements were just initialized by `copy_nonoverlapping`
        self.head = new_head;
        self.len += count;
    }
}

/// Returns the index in the underlying buffer for a given logical element index.
#[inline]
fn wrap_index(logical_index: usize, capacity: usize) -> usize {
    debug_assert!(
        (logical_index == 0 && capacity == 0)
            || logical_index < capacity
            || (logical_index - capacity) < capacity
    );
    if logical_index >= capacity { logical_index - capacity } else { logical_index }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: PartialEq, A: Allocator> PartialEq for VecDeque<T, A> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len() {
            return false;
        }
        let (sa, sb) = self.as_slices();
        let (oa, ob) = other.as_slices();
        if sa.len() == oa.len() {
            sa == oa && sb == ob
        } else if sa.len() < oa.len() {
            // Always divisible in three sections, for example:
            // self:  [a b c|d e f]
            // other: [0 1 2 3|4 5]
            // front = 3, mid = 1,
            // [a b c] == [0 1 2] && [d] == [3] && [e f] == [4 5]
            let front = sa.len();
            let mid = oa.len() - front;

            let (oa_front, oa_mid) = oa.split_at(front);
            let (sb_mid, sb_back) = sb.split_at(mid);
            debug_assert_eq!(sa.len(), oa_front.len());
            debug_assert_eq!(sb_mid.len(), oa_mid.len());
            debug_assert_eq!(sb_back.len(), ob.len());
            sa == oa_front && sb_mid == oa_mid && sb_back == ob
        } else {
            let front = oa.len();
            let mid = sa.len() - front;

            let (sa_front, sa_mid) = sa.split_at(front);
            let (ob_mid, ob_back) = ob.split_at(mid);
            debug_assert_eq!(sa_front.len(), oa.len());
            debug_assert_eq!(sa_mid.len(), ob_mid.len());
            debug_assert_eq!(sb.len(), ob_back.len());
            sa_front == oa && sa_mid == ob_mid && sb == ob_back
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Eq, A: Allocator> Eq for VecDeque<T, A> {}

__impl_slice_eq1! { [] VecDeque<T, A>, Vec<U, A>, }
__impl_slice_eq1! { [] VecDeque<T, A>, &[U], }
__impl_slice_eq1! { [] VecDeque<T, A>, &mut [U], }
__impl_slice_eq1! { [const N: usize] VecDeque<T, A>, [U; N], }
__impl_slice_eq1! { [const N: usize] VecDeque<T, A>, &[U; N], }
__impl_slice_eq1! { [const N: usize] VecDeque<T, A>, &mut [U; N], }

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: PartialOrd, A: Allocator> PartialOrd for VecDeque<T, A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Ord, A: Allocator> Ord for VecDeque<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Hash, A: Allocator> Hash for VecDeque<T, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_length_prefix(self.len);
        // It's not possible to use Hash::hash_slice on slices
        // returned by as_slices method as their length can vary
        // in otherwise identical deques.
        //
        // Hasher only guarantees equivalence for the exact same
        // set of calls to its methods.
        self.iter().for_each(|elem| elem.hash(state));
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> Index<usize> for VecDeque<T, A> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        self.get(index).expect("Out of bounds access")
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> IndexMut<usize> for VecDeque<T, A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index).expect("Out of bounds access")
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> FromIterator<T> for VecDeque<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> VecDeque<T> {
        SpecFromIter::spec_from_iter(iter.into_iter())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> IntoIterator for VecDeque<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Consumes the deque into a front-to-back iterator yielding elements by
    /// value.
    fn into_iter(self) -> IntoIter<T, A> {
        IntoIter::new(self)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, A: Allocator> IntoIterator for &'a VecDeque<T, A> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, A: Allocator> IntoIterator for &'a mut VecDeque<T, A> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> Extend<T> for VecDeque<T, A> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        <Self as SpecExtend<T, I::IntoIter>>::spec_extend(self, iter.into_iter());
    }

    #[inline]
    fn extend_one(&mut self, elem: T) {
        self.push_back(elem);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    #[inline]
    unsafe fn extend_one_unchecked(&mut self, item: T) {
        // SAFETY: Our preconditions ensure the space has been reserved, and `extend_reserve` is implemented correctly.
        unsafe {
            self.push_unchecked(item);
        }
    }
}

#[stable(feature = "extend_ref", since = "1.2.0")]
impl<'a, T: 'a + Copy, A: Allocator> Extend<&'a T> for VecDeque<T, A> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.spec_extend(iter.into_iter());
    }

    #[inline]
    fn extend_one(&mut self, &elem: &'a T) {
        self.push_back(elem);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    #[inline]
    unsafe fn extend_one_unchecked(&mut self, &item: &'a T) {
        // SAFETY: Our preconditions ensure the space has been reserved, and `extend_reserve` is implemented correctly.
        unsafe {
            self.push_unchecked(item);
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for VecDeque<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[stable(feature = "vecdeque_vec_conversions", since = "1.10.0")]
impl<T, A: Allocator> From<Vec<T, A>> for VecDeque<T, A> {
    /// Turn a [`Vec<T>`] into a [`VecDeque<T>`].
    ///
    /// [`Vec<T>`]: crate::vec::Vec
    /// [`VecDeque<T>`]: crate::collections::VecDeque
    ///
    /// This conversion is guaranteed to run in *O*(1) time
    /// and to not re-allocate the `Vec`'s buffer or allocate
    /// any additional memory.
    #[inline]
    fn from(other: Vec<T, A>) -> Self {
        let (ptr, len, cap, alloc) = other.into_raw_parts_with_alloc();
        Self { head: 0, len, buf: unsafe { RawVec::from_raw_parts_in(ptr, cap, alloc) } }
    }
}

#[stable(feature = "vecdeque_vec_conversions", since = "1.10.0")]
impl<T, A: Allocator> From<VecDeque<T, A>> for Vec<T, A> {
    /// Turn a [`VecDeque<T>`] into a [`Vec<T>`].
    ///
    /// [`Vec<T>`]: crate::vec::Vec
    /// [`VecDeque<T>`]: crate::collections::VecDeque
    ///
    /// This never needs to re-allocate, but does need to do *O*(*n*) data movement if
    /// the circular buffer doesn't happen to be at the beginning of the allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// // This one is *O*(1).
    /// let deque: VecDeque<_> = (1..5).collect();
    /// let ptr = deque.as_slices().0.as_ptr();
    /// let vec = Vec::from(deque);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// assert_eq!(vec.as_ptr(), ptr);
    ///
    /// // This one needs data rearranging.
    /// let mut deque: VecDeque<_> = (1..5).collect();
    /// deque.push_front(9);
    /// deque.push_front(8);
    /// let ptr = deque.as_slices().1.as_ptr();
    /// let vec = Vec::from(deque);
    /// assert_eq!(vec, [8, 9, 1, 2, 3, 4]);
    /// assert_eq!(vec.as_ptr(), ptr);
    /// ```
    fn from(mut other: VecDeque<T, A>) -> Self {
        other.make_contiguous();

        unsafe {
            let other = ManuallyDrop::new(other);
            let buf = other.buf.ptr();
            let len = other.len();
            let cap = other.capacity();
            let alloc = ptr::read(other.allocator());

            if other.head != 0 {
                ptr::copy(buf.add(other.head), buf, len);
            }
            Vec::from_raw_parts_in(buf, len, cap, alloc)
        }
    }
}

#[stable(feature = "std_collections_from_array", since = "1.56.0")]
impl<T, const N: usize> From<[T; N]> for VecDeque<T> {
    /// Converts a `[T; N]` into a `VecDeque<T>`.
    ///
    /// ```
    /// use std::collections::VecDeque;
    ///
    /// let deq1 = VecDeque::from([1, 2, 3, 4]);
    /// let deq2: VecDeque<_> = [1, 2, 3, 4].into();
    /// assert_eq!(deq1, deq2);
    /// ```
    fn from(arr: [T; N]) -> Self {
        let mut deq = VecDeque::with_capacity(N);
        let arr = ManuallyDrop::new(arr);
        if !<T>::IS_ZST {
            // SAFETY: VecDeque::with_capacity ensures that there is enough capacity.
            unsafe {
                ptr::copy_nonoverlapping(arr.as_ptr(), deq.ptr(), N);
            }
        }
        deq.head = 0;
        deq.len = N;
        deq
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Kani proofs for Challenge 25.
    //!
    //! # Method
    //!
    //! Every harness starts from [`any_deque`]: a real allocation of symbolic capacity, a
    //! symbolic `head` over every physical index and a symbolic `len` (so both the contiguous
    //! and the wrapped ring layout are explored), with exactly the logical range initialized.
    //! There is no `kani::unwind` and no length constant in any proof; the only bound on sizes
    //! is CBMC's object model (`MAX_ALLOCATION_BYTES`). The 13 unsafe functions carry
    //! `#[requires]`/`#[ensures]`/`kani::modifies` contracts checked by `proof_for_contract`
    //! harnesses; the 30 safe functions have `#[kani::proof]` harnesses. Loops are discharged
    //! with loop contracts (`retain_mut`, `write_iter_loop`).
    //!
    //! # Element shapes (generic `T`)
    //!
    //! Kani rejects a `#[kani::proof]` on a generic function, so each harness body is written
    //! once for arbitrary `T` and instantiated over element *shapes* chosen to cover every
    //! property of `T` that the code observes. `VecDeque<T>` is parametric in `T` except through
    //! `size_of`/`align_of` (allocation and pointer arithmetic), `T::IS_ZST` (the branches that
    //! skip the buffer), moves of opaque values, and the drop glue `ptr::drop_in_place::<[T]>`
    //! in `truncate`, `drain` and `Drop for VecDeque`; it never branches on `needs_drop` or on
    //! element values (the only value-dependent code is the user closures, which the harnesses
    //! make nondeterministic).
    //!
    //! | shape | size | align | `needs_drop` / non-`Copy` | validity invariant |
    //! |---|---|---|---|---|
    //! | `()` | 0 | 1 | no | no |
    //! | `u8` | 1 | 1 | no | no |
    //! | `bool` | 1 | 1 | no | yes (`0`/`1`) |
    //! | `[u8; 3]` | 3 | 1 | no | no |
    //! | `u64` | 8 | 8 | no | no |
    //! | [`Al16`] | 16 | 16 | no | no |
    //! | [`WithDrop`] | 1 | 1 | yes | no |
    //!
    //! `u8`, `u64` and `()` instantiate every harness (plus `[u8; 3]` on the cheap ones);
    //! `bool`, `Al16` and `WithDrop` instantiate the harnesses whose targets exercise their
    //! property (see the instantiation lists). For `WithDrop` the unbounded harnesses cover
    //! every target that drops at most single elements; the slice drop glue
    //! (`drop_in_place::<[T]>`, a compiler-generated loop that cannot carry a loop contract) is
    //! checked bounded (`len <= 4`) in [`bounded_evidence`]. Generators write pre-existing
    //! elements with one symbolic byte per region (a valid bit pattern of the shape,
    //! [`Shape::any_fill`]); elements that enter through the API are per-element `kani::any()`.
    //! Representative shapes are the closest Kani can come to the challenge's "no
    //! monomorphization" clause.
    //!
    //! # Stubs and the `write_iter` transcription
    //!
    //! Everything a harness assumes about a callee is either its verified contract or one of
    //! the items below, each with the harness that checks what it hides:
    //!
    //! | replacement | replaces | asserts | over-approximates | evidence | residual argument |
    //! |---|---|---|---|---|---|
    //! | `write_iter_loop` (cfg(kani) body of `write_iter`) | the shipped `for_each` statement | — | — (transcription) | `bounded_evidence::bounded_write_iter_shipped_text_*` runs the shipped statement (`write_iter_for_each`) against the same contract, `n <= 4` | `Iterator::fold` ≡ repeated `next()`; see `write_iter_loop`'s doc for why no loop contract can reach the shipped loop |
    //! | [`VecDeque::write_iter_contract_replacement`] (and its `_drop` variant for `resize_with`) | `write_iter_loop` | `write_iter`'s precondition, via `write_iter_precondition` | `write_iter`'s `modifies` region gets an arbitrary fill; `written += hi`; iterator advanced by `hi` | `bounded_write_iter_wrapping_shipped_text_u8` (the branch with the shipped statement iterating) and `bounded_replacement_advance_by_matches_next_u8` (`advance_by(hi)` ≡ `hi` × `next()`) | exact-`hi` = `TrustedLen` exactness (asserted `lo == hi`) |
    //! | [`stub_ptr_rotate`] (`check_make_contiguous_*` only) | `core::slice::rotate::ptr_rotate` | its documented precondition (range writable) | leaves memory untouched | `bounded_evidence::bounded_rotate_permutes_range_u8`: the real `rotate_left`/`rotate_right` on ranges of every length and amount up to eight, symbolic contents, guard bytes — exactly the rotated sequence, nothing else written | a rotation only permutes initialized slots; `make_contiguous` does nothing value-dependent afterwards |
    //!
    //! Loop-contract proofs are partial-correctness proofs at the pinned Kani (termination is
    //! assumed); the loops involved terminate by the exact `size_hint` of `TrustedLen`
    //! iterators (`write_iter_loop`) and by `cur` reaching `len` (`retain_mut`).
    //!
    //! # Kani limitations at the pinned version (`152c6a8`)
    //!
    //! 1. `stub_verified` on a contract whose `modifies` names a slice ICEs (kani#3682; the fix,
    //!    kani#4749, is 92 commits after the pin), and `kani::stub` of a contracted function is
    //!    rejected (kani#4591). Hence the contract-free `write_iter_loop` is the stub target.
    //!    Even with kani#4749, `stub_verified(write_iter)` would not prove the wrapping branch:
    //!    the generated replacement drops the by-value `Take<ByRefSized<&mut I>>` unconsumed,
    //!    so the second call would see the whole iterator again (see
    //!    `write_iter_contract_replacement`).
    //! 2. A loop contract cannot survive the havocking of a loop-carried adapter holding a
    //!    `&mut` (`Take<ByRefSized<&mut I>>`): its private fields cannot be re-pinned.
    //! 3. A stub must be a method when the original is one: signatures are compared by the
    //!    position of their own generic parameters.
    //! 4. CBMC aborts on a `loop_modifies` target that is a zero-sized closure (kani#4786), so
    //!    `retain_mut`'s loop contracts do not list the predicate.
    //! 5. `loop_decreases` cannot be combined with an explicit `loop_modifies`.
    //! 6. `-Z uninit-checks` and `-Z valid-value-checks` are not enabled by CI (the former
    //!    rejects alloc at this pin, kani#3300); reading uninitialized memory and invalid values
    //!    are therefore only excluded by construction (initialized ranges, valid fills).

    use core::iter::TrustedLen;
    use core::marker::PhantomData;
    use core::mem::SizedTypeProperties;
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering::Relaxed;
    use core::{cmp, kani, ptr};

    use crate::alloc::Layout;
    use crate::collections::VecDeque;
    use crate::vec::Vec;

    // ---------------------------------------------------------------------------------------
    // Element shapes
    // ---------------------------------------------------------------------------------------

    /// An element type the generic harness bodies are instantiated with (see the shape matrix
    /// in the module documentation). `any_fill` is the byte the generators write into every
    /// byte of a pre-existing element; it must be a valid bit pattern for `Self`, which is why
    /// types with a validity invariant override it.
    pub(super) trait Shape: kani::Arbitrary {
        fn any_fill() -> u8 {
            kani::any()
        }
    }

    impl Shape for u8 {}
    impl Shape for u64 {}
    impl Shape for [u8; 3] {}
    impl Shape for () {}

    /// Validity invariant: only the bit patterns `0` and `1` are valid.
    impl Shape for bool {
        fn any_fill() -> u8 {
            kani::any_where(|b: &u8| *b <= 1)
        }
    }

    /// Alignment larger than any primitive's (`align_of == size_of == 16`).
    #[derive(kani::Arbitrary)]
    #[repr(align(16))]
    pub(super) struct Al16(u8);
    impl Shape for Al16 {}

    /// Number of `WithDrop` destructors that have run. Reset by the harnesses that assert on it
    /// (`bounded_evidence`); the other harnesses only require that no destructor runs on an
    /// uninitialized or already-moved slot, which Kani's memory checks enforce.
    pub(super) static DROPS: AtomicUsize = AtomicUsize::new(0);

    /// `needs_drop` (and therefore non-`Copy`, move-only) element: its destructor counts itself
    /// and reads its payload.
    #[derive(kani::Arbitrary)]
    pub(super) struct WithDrop(u8);
    impl Drop for WithDrop {
        fn drop(&mut self) {
            DROPS.fetch_add(1, Relaxed);
            core::hint::black_box(self.0);
        }
    }
    impl Shape for WithDrop {}

    /// Ends a harness that owns `deque`. For shapes without a destructor the deque is dropped,
    /// exercising `Drop for VecDeque` (whose `ptr::drop_in_place::<[T]>` is then a no-op). For
    /// `needs_drop` shapes it is leaked: `drop_in_place::<[T]>` is a compiler-generated loop of
    /// symbolic length that cannot carry a loop contract, so the drop-glue paths are checked
    /// separately, bounded, in `bounded_evidence`.
    pub(super) fn finish<T, A: crate::alloc::Allocator>(deque: VecDeque<T, A>) {
        if core::mem::needs_drop::<T>() { core::mem::forget(deque) } else { drop(deque) }
    }

    /// A non-vacuity witness for a path through the ring buffer. Zero-sized element types never
    /// touch the buffer (every such path is excluded by `T::IS_ZST` checks in the code), so the
    /// witness is only meaningful, and only required, for sized `T`. (A macro rather than a
    /// function because Kani needs the message to be a literal at the `cover` call site.)
    macro_rules! cover_buffer_path {
        ($t:ty, $cond:expr, $msg:literal) => {
            kani::cover(<$t>::IS_ZST || $cond, $msg)
        };
    }

    // ---------------------------------------------------------------------------------------
    // Symbolic deque generator
    // ---------------------------------------------------------------------------------------

    /// Upper bound, in bytes, on the size of the backing allocation. This is not a bound of
    /// the proof: it mirrors CBMC's memory model, whose objects are addressed with
    /// `64 - object_bits` offset bits (`--object-bits 12` in `scripts/run-kani.sh`), so a single
    /// allocation cannot exceed 2^51 bytes in the model. Every `cap` whose allocation fits the
    /// model is explored; the bound only excludes allocations no real machine could back either.
    const MAX_ALLOCATION_BYTES: usize = 1 << 48;

    /// Builds an arbitrary `VecDeque<T>` with symbolic capacity, symbolic `head` and symbolic
    /// `len`, backed by a real allocation of that capacity.
    ///
    /// * `cap` is only restricted by the layout precondition `RawVec` itself imposes
    ///   (`Layout::array::<T>(cap).is_ok()`); there is no length bound.
    /// * `head` ranges over every valid physical index and `len` over `0..=cap`, so both the
    ///   contiguous (`head + len <= cap`) and the wrapped (`head + len > cap`) ring layouts are
    ///   explored (see the `kani::cover` witnesses).
    /// * Exactly the logical range `head..head + len` (wrapping at `cap`) is initialized, every
    ///   byte with the shape's arbitrary valid fill byte (`Shape::any_fill`); slots outside it
    ///   stay uninitialized. `VecDeque<T>` never branches on element values (the only
    ///   value-dependent code is the user closures, which the harnesses make nondeterministic,
    ///   and the elements `AnyIter` yields are per-element `kani::any()`), so one symbolic byte
    ///   per initialized region loses nothing.
    pub(super) fn any_deque<T: Shape>() -> VecDeque<T> {
        let requested: usize = kani::any();
        kani::assume(Layout::array::<T>(requested).is_ok());
        kani::assume(
            requested
                .checked_mul(core::mem::size_of::<T>())
                .is_some_and(|b| b <= MAX_ALLOCATION_BYTES),
        );
        let mut deque = VecDeque::<T>::with_capacity(requested);
        let cap = deque.capacity();
        let head: usize = if cap == 0 { 0 } else { kani::any_where(|h: &usize| *h < cap) };
        let len: usize = kani::any_where(|l: &usize| *l <= cap);
        if !T::IS_ZST && len > 0 {
            let fill: u8 = T::any_fill();
            let head_room = cap - head;
            unsafe {
                if len <= head_room {
                    ptr::write_bytes(deque.ptr().add(head), fill, len);
                } else {
                    ptr::write_bytes(deque.ptr().add(head), fill, head_room);
                    ptr::write_bytes(deque.ptr(), fill, len - head_room);
                }
            }
        }
        deque.head = head;
        deque.len = len;
        kani::cover(len > cap - head, "generator: wrapped ring layout is reachable");
        kani::cover(len > 0 && len <= cap - head, "generator: contiguous layout is reachable");
        kani::cover(len == cap && cap > 1, "generator: full deque is reachable");
        cover_buffer_path!(T, cap == 0, "generator: zero-capacity deque is reachable");
        deque
    }

    /// Reads a symbolic logical index of `deque` so that the slot is actually dereferenced
    /// after the operation under test.
    pub(super) fn touch<T>(deque: &VecDeque<T>) {
        let i: usize = kani::any();
        if let Some(elem) = deque.get(i) {
            core::mem::forget(unsafe { ptr::read(elem) });
        }
        assert!(deque.invariant_holds());
    }

    /// A harness iterator yielding exactly `remaining` arbitrary elements. It carries no
    /// references, so loop-contract havocking cannot invalidate it, and its `size_hint` is
    /// exact (it is `TrustedLen`, like every iterator the real callers of `write_iter` pass).
    pub(super) struct AnyIter<T> {
        remaining: usize,
        _marker: PhantomData<T>,
    }

    impl<T> AnyIter<T> {
        pub(super) fn new(remaining: usize) -> Self {
            AnyIter { remaining, _marker: PhantomData }
        }
    }

    impl<T: kani::Arbitrary> Iterator for AnyIter<T> {
        type Item = T;

        fn next(&mut self) -> Option<T> {
            if self.remaining == 0 {
                None
            } else {
                self.remaining -= 1;
                Some(kani::any())
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.remaining, Some(self.remaining))
        }

        fn advance_by(&mut self, n: usize) -> Result<(), core::num::NonZero<usize>> {
            let skipped = cmp::min(n, self.remaining);
            self.remaining -= skipped;
            core::num::NonZero::new(n - skipped).map_or(Ok(()), Err)
        }
    }

    impl<T: kani::Arbitrary> ExactSizeIterator for AnyIter<T> {}
    unsafe impl<T: kani::Arbitrary> TrustedLen for AnyIter<T> {}

    // ---------------------------------------------------------------------------------------
    // Contract harnesses (`proof_for_contract`) for the unsafe functions
    // ---------------------------------------------------------------------------------------

    /// Contract replacement for the loop of `VecDeque::write_iter` (`write_iter_loop`), used
    /// when verifying the callers of `write_iter` (`write_iter_wrapping`, `resize_with`).
    /// `write_iter` itself, loop included, is verified against its real body by
    /// `check_write_iter_*`. (Running the real loop inside the callers was tried at the pinned
    /// Kani: the loop contract is then instrumented for the `Take<ByRefSized<&mut _>>`
    /// instance of the wrapping branch as well, and neither `check_resize_with_u8` nor a
    /// direct-branch-only `write_iter_wrapping` harness finished within 20 minutes.)
    ///
    /// This is what `#[kani::stub_verified(write_iter)]` would generate, **plus one step**. It
    /// is written by hand because the pinned Kani (a) ICEs when generating the replacement of a
    /// contract whose `modifies` clause names a slice (model-checking/kani#3682; the fix,
    /// model-checking/kani#4749, postdates the pin) and (b) cannot `kani::stub` a function that
    /// carries a contract (model-checking/kani#4591); hence the contract-free helper is the
    /// stub target. The extra step is `iter.advance_by(hi)`: a pure contract replacement drops
    /// the by-value `Take<ByRefSized<&mut I>>` unconsumed, so the caller's second `write_iter`
    /// call would see the whole iterator again and could write past `len` — the caller's own
    /// `ensures`/`modifies` are only provable with the consumption modelled. This step is what
    /// the loop does (it calls `next()` until `None`, i.e. exactly `hi` times for an exact
    /// hint), and `bounded_evidence::bounded_write_iter_wrapping_shipped_text_u8` runs the
    /// shipped statement on this very adapter stack, bounded, and
    /// `bounded_evidence::bounded_replacement_advance_by_matches_next_u8` checks
    /// `advance_by(hi)` against `hi` calls of `next()` on it.
    ///
    /// What it does: *asserts* the precondition of `write_iter`'s contract — through the same
    /// predicate the contract uses, `write_iter_precondition`, so the two cannot drift — then
    /// models the effect the contract permits: exactly the slots `dst..dst + hi` receive an
    /// arbitrary valid fill (the `modifies` region, `slots(dst, hi)`; one symbolic byte per
    /// region, since no proof reads element values), `*written` grows by `hi`, and the iterator
    /// is advanced by `hi`. Writing exactly `hi` rather than the contract's `<= hi` is the one
    /// assumption beyond the contract; it is the `TrustedLen` exactness every caller relies on
    /// (asserted here as `lo == hi`) and what the loop does with such an iterator.
    ///
    /// It is a method rather than a free function because the pinned Kani compares a stub's
    /// signature with the original's by the position of their *own* generic parameters (the
    /// `impl Iterator` argument here); a free function would put `T` and `A` in those
    /// positions and be rejected ("Cannot stub … Expected type `&mut VecDeque<T, A>` …").
    impl<T: Shape, A: crate::alloc::Allocator> VecDeque<T, A> {
        pub(super) unsafe fn write_iter_contract_replacement(
            &mut self,
            dst: usize,
            mut iter: impl Iterator<Item = T>,
            written: &mut usize,
        ) {
            let (lo, hi) = iter.size_hint();
            kani::assert(
                self.write_iter_precondition(dst, hi, *written),
                "write_iter precondition",
            );
            let hi = hi.unwrap();
            kani::assert(lo == hi, "write_iter callers pass TrustedLen iterators");
            if !T::IS_ZST && hi > 0 {
                unsafe { ptr::write_bytes(self.ptr().add(dst), T::any_fill(), hi) };
            }
            *written += hi;
            // Consume the elements exactly as the real loop does, so that an iterator shared
            // with a later call (`write_iter_wrapping`'s wrapping branch borrows `iter` for the
            // first call and passes it on to the second) reports the right remaining length.
            // `advance_by` is O(1) for the harness iterator and the `Take` / `ByRefSized`
            // adapters the callee wraps it in.
            kani::assert(
                iter.advance_by(hi).is_ok(),
                "write_iter replacement: iterator advanced by hi",
            );
        }

        /// Like [`Self::write_iter_contract_replacement`] but drops the iterator instead of
        /// advancing it. Only valid where the iterator is not observed after the call, i.e. in
        /// the non-wrapping branch of `write_iter_wrapping`; used by the `resize_with`
        /// harnesses, whose `Take<RepeatWith<_>>` iterator cannot be advanced without a loop.
        pub(super) unsafe fn write_iter_contract_replacement_drop(
            &mut self,
            dst: usize,
            iter: impl Iterator<Item = T>,
            written: &mut usize,
        ) {
            let (lo, hi) = iter.size_hint();
            kani::assert(
                self.write_iter_precondition(dst, hi, *written),
                "write_iter precondition",
            );
            let hi = hi.unwrap();
            kani::assert(lo == hi, "write_iter callers pass TrustedLen iterators");
            if !T::IS_ZST && hi > 0 {
                unsafe { ptr::write_bytes(self.ptr().add(dst), T::any_fill(), hi) };
            }
            *written += hi;
            drop(iter);
        }
    }

    fn check_write_iter<T: Shape>() {
        let mut deque = any_deque::<T>();
        let dst: usize = kani::any();
        let n: usize = kani::any();
        let mut written: usize = kani::any();
        let before = written;
        unsafe { deque.write_iter(dst, AnyIter::<T>::new(n), &mut written) };
        assert_eq!(written, before + n);
        kani::cover(n > 1, "write_iter: more than one element written");
        kani::cover(dst > 0 && n > 0, "write_iter: non-zero destination");
        finish(deque);
    }

    fn check_write_iter_wrapping<T: Shape>() {
        let mut deque = any_deque::<T>();
        let dst: usize = kani::any();
        let len: usize = kani::any();
        let n: usize = kani::any();
        let old_len = deque.len;
        let written = unsafe { deque.write_iter_wrapping(dst, AnyIter::<T>::new(n), len) };
        assert!(written <= len);
        assert_eq!(deque.len, old_len + written);
        kani::cover(len > deque.capacity() - dst, "write_iter_wrapping: wrapping branch");
        kani::cover(n > 0 && len <= deque.capacity() - dst, "write_iter_wrapping: direct branch");
        touch(&deque);
        finish(deque);
    }

    fn check_copy<T: Shape>() {
        let mut deque = any_deque::<T>();
        let src: usize = kani::any();
        let dst: usize = kani::any();
        let len: usize = kani::any();
        unsafe { deque.copy(src, dst, len) };
        kani::cover(len > 1 && src.abs_diff(dst) < len, "copy: overlapping ranges");
        kani::cover(len > 1 && src.abs_diff(dst) >= len, "copy: disjoint ranges");
        touch(&deque);
    }

    fn check_copy_nonoverlapping<T: Shape>() {
        let mut deque = any_deque::<T>();
        let src: usize = kani::any();
        let dst: usize = kani::any();
        let len: usize = kani::any();
        unsafe { deque.copy_nonoverlapping(src, dst, len) };
        kani::cover(len > 1, "copy_nonoverlapping: more than one element");
        touch(&deque);
    }

    fn check_wrap_copy<T: Shape>() {
        let mut deque = any_deque::<T>();
        let src: usize = kani::any();
        let dst: usize = kani::any();
        let len: usize = kani::any();
        let cap = deque.capacity();
        unsafe { deque.wrap_copy(src, dst, len) };
        let copying = !T::IS_ZST && cap > 0 && len > 0 && src != dst;
        let dst_after_src = copying && deque.wrap_sub(dst, src) < len;
        let src_wraps = copying && cap - src < len;
        let dst_wraps = copying && cap - dst < len;
        cover_buffer_path!(T, copying && !src_wraps && !dst_wraps, "wrap_copy: (_, false, false)");
        cover_buffer_path!(
            T,
            !dst_after_src && !src_wraps && dst_wraps,
            "wrap_copy: (false, false, true)"
        );
        cover_buffer_path!(
            T,
            dst_after_src && !src_wraps && dst_wraps,
            "wrap_copy: (true, false, true)"
        );
        cover_buffer_path!(
            T,
            !dst_after_src && src_wraps && !dst_wraps,
            "wrap_copy: (false, true, false)"
        );
        cover_buffer_path!(
            T,
            dst_after_src && src_wraps && !dst_wraps,
            "wrap_copy: (true, true, false)"
        );
        cover_buffer_path!(
            T,
            !dst_after_src && src_wraps && dst_wraps,
            "wrap_copy: (false, true, true)"
        );
        cover_buffer_path!(
            T,
            dst_after_src && src_wraps && dst_wraps,
            "wrap_copy: (true, true, true)"
        );
        touch(&deque);
    }

    fn check_buffer_read<T: Shape>() {
        let mut deque = any_deque::<T>();
        let off: usize = kani::any();
        let value = unsafe { deque.buffer_read(off) };
        core::mem::forget(value);
        kani::cover(off > 0, "buffer_read: non-zero offset");
        finish(deque);
    }

    fn check_buffer_write<T: Shape>() {
        let mut deque = any_deque::<T>();
        let off: usize = kani::any();
        let slot = unsafe { deque.buffer_write(off, kani::any()) };
        core::mem::forget(unsafe { ptr::read(slot) });
        kani::cover(off > 0, "buffer_write: non-zero offset");
        finish(deque);
    }

    fn check_push_unchecked<T: Shape>() {
        let mut deque = any_deque::<T>();
        let old_len = deque.len;
        unsafe { deque.push_unchecked(kani::any()) };
        assert_eq!(deque.len, old_len + 1);
        kani::cover(old_len >= deque.capacity() - deque.head, "push_unchecked: wrapped write");
        touch(&deque);
        finish(deque);
    }

    // ---------------------------------------------------------------------------------------
    // Safe-abstraction harnesses (`kani::proof`)
    // ---------------------------------------------------------------------------------------

    /// Abstraction of the *safe* `core::slice::rotate::ptr_rotate` used by
    /// `<[T]>::rotate_left/right`: it checks the callee's documented precondition (the range
    /// `mid - left .. mid + right` must be valid for reading and writing) and otherwise leaves
    /// memory untouched. `make_contiguous` performs no value-dependent operation after the
    /// rotation, and a rotation of a valid slice can only permute valid values, so this
    /// abstraction is sound for the memory-safety proof of `make_contiguous`.
    unsafe fn stub_ptr_rotate<T>(left: usize, mid: *mut T, right: usize) {
        let len = left.checked_add(right).expect("rotate range overflows");
        let start = unsafe { mid.sub(left) };
        assert!(core::ub_checks::can_write(ptr::slice_from_raw_parts_mut(start, len)));
    }

    fn check_make_contiguous<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len;
        let cap = deque.capacity();
        let head = deque.head;
        let wrapped = !T::IS_ZST && len > cap - head;
        let free = cap - len;
        let slice = deque.make_contiguous();
        assert_eq!(slice.len(), len);
        if len > 0 {
            core::mem::forget(unsafe { ptr::read(&slice[len - 1]) });
        }
        assert!(deque.is_contiguous());
        let head_len = cap - head;
        let tail_len = len.wrapping_sub(head_len);
        cover_buffer_path!(
            T,
            wrapped && free >= head_len,
            "make_contiguous: head fits in free space"
        );
        cover_buffer_path!(
            T,
            wrapped && free < head_len && free >= tail_len,
            "make_contiguous: tail fits"
        );
        cover_buffer_path!(
            T,
            wrapped && free < head_len && free < tail_len && head_len > tail_len,
            "make_contiguous: rotate_left"
        );
        cover_buffer_path!(
            T,
            wrapped && free < head_len && free < tail_len && head_len <= tail_len,
            "make_contiguous: rotate_right"
        );
        touch(&deque);
    }

    // ---------------------------------------------------------------------------------------
    // Remaining contract harnesses
    // ---------------------------------------------------------------------------------------

    /// Allocates a deque with symbolic capacity and no elements (`head == len == 0`).
    pub(super) fn any_empty_deque<T>() -> VecDeque<T> {
        let requested: usize = kani::any();
        kani::assume(Layout::array::<T>(requested).is_ok());
        kani::assume(
            requested
                .checked_mul(core::mem::size_of::<T>())
                .is_some_and(|b| b <= MAX_ALLOCATION_BYTES),
        );
        VecDeque::<T>::with_capacity(requested)
    }

    /// Lays out a logical ring of `len` elements starting at `head` inside the first `ring_cap`
    /// slots of `deque`'s buffer (`ring_cap <= deque.capacity()`, `head < ring_cap` unless
    /// `ring_cap == 0`, `len <= ring_cap`): initializes exactly those slots and sets the fields.
    pub(super) fn init_ring<T: Shape>(
        deque: &mut VecDeque<T>,
        ring_cap: usize,
        head: usize,
        len: usize,
    ) {
        assert!(ring_cap <= deque.capacity() && len <= ring_cap);
        assert!(head < ring_cap || (ring_cap == 0 && head == 0));
        if !T::IS_ZST && len > 0 {
            let fill: u8 = T::any_fill();
            let head_room = ring_cap - head;
            unsafe {
                if len <= head_room {
                    ptr::write_bytes(deque.ptr().add(head), fill, len);
                } else {
                    ptr::write_bytes(deque.ptr().add(head), fill, head_room);
                    ptr::write_bytes(deque.ptr(), fill, len - head_room);
                }
            }
        }
        deque.head = head;
        deque.len = len;
    }

    /// A `Vec<T>` of symbolic length whose elements are all initialized.
    pub(super) fn any_vec<T: Shape>() -> Vec<T> {
        let len: usize = kani::any();
        kani::assume(Layout::array::<T>(len).is_ok());
        kani::assume(
            len.checked_mul(core::mem::size_of::<T>()).is_some_and(|b| b <= MAX_ALLOCATION_BYTES),
        );
        let mut vec = Vec::<T>::with_capacity(len);
        if !T::IS_ZST && len > 0 {
            unsafe { ptr::write_bytes(vec.as_mut_ptr(), T::any_fill(), len) };
        }
        unsafe { vec.set_len(len) };
        vec
    }

    fn check_buffer_range<T: Shape>() {
        let deque = any_deque::<T>();
        let start: usize = kani::any();
        let end: usize = kani::any();
        let slice = unsafe { deque.buffer_range(start..end) };
        assert_eq!(slice.len(), end - start);
        assert!(core::ptr::eq(slice as *const T, unsafe { deque.ptr().add(start) }));
        kani::cover(end - start > 1, "buffer_range: more than one slot");
        // `Drop for VecDeque` calls `buffer_range` too; a contract harness must contain a single
        // call to the function under contract, so the (element-free) deque is leaked instead.
        core::mem::forget(deque);
    }

    fn check_copy_slice<T: Shape>() {
        let mut deque = any_deque::<T>();
        let src = any_vec::<T>();
        let dst: usize = kani::any();
        unsafe { deque.copy_slice(dst, &src) };
        kani::cover(src.len() > 0 && src.len() <= deque.capacity() - dst, "copy_slice: no wrap");
        kani::cover(src.len() > deque.capacity() - dst, "copy_slice: wrapping copy");
        touch(&deque);
    }

    fn check_handle_capacity_increase<T: Shape>() {
        let mut deque = any_empty_deque::<T>();
        let new_cap = deque.capacity();
        let old_cap: usize = kani::any_where(|c: &usize| *c <= new_cap);
        let head: usize = if old_cap == 0 { 0 } else { kani::any_where(|h: &usize| *h < old_cap) };
        let len: usize = kani::any_where(|l: &usize| *l <= old_cap);
        init_ring(&mut deque, old_cap, head, len);
        let contiguous = head <= old_cap - len;
        let head_len = old_cap - head;
        let case_b =
            !contiguous && head_len > len - head_len && new_cap - old_cap >= len - head_len;
        unsafe { deque.handle_capacity_increase(old_cap) };
        assert!(deque.is_contiguous() || T::IS_ZST || len > old_cap - head);
        kani::cover(contiguous && len > 0, "handle_capacity_increase: case A (no move)");
        kani::cover(case_b, "handle_capacity_increase: case B (tail moved)");
        kani::cover(!contiguous && !case_b, "handle_capacity_increase: case C (head moved)");
        kani::cover(old_cap == 0, "handle_capacity_increase: from zero capacity");
        touch(&deque);
    }

    fn check_from_contiguous_raw_parts_in<T: Shape>() {
        let vec = any_empty_deque_vec::<T>();
        let (ptr, _, capacity, alloc) = vec.into_raw_parts_with_alloc();
        let start: usize = kani::any();
        let end: usize = kani::any();
        if !T::IS_ZST && start <= end && end <= capacity && end > start {
            unsafe { ptr::write_bytes(ptr.add(start), T::any_fill(), end - start) };
        }
        let deque =
            unsafe { VecDeque::from_contiguous_raw_parts_in(ptr, start..end, capacity, alloc) };
        assert_eq!(deque.len(), end - start);
        // The `initialized.start < capacity || initialized.start == 0` precondition is what
        // keeps `head` a valid physical index. Without it, `capacity..capacity` (which
        // `vec::IntoIter::into_vecdeque` produces for an exhausted iterator whose `Vec` had
        // `capacity == len`) yields `head == capacity`, and a subsequent `push_back` +
        // `pop_front` reads one past the end of the buffer: rust-lang/rust#162452.
        touch(&deque);
        kani::cover(end - start > 1 && start > 0, "from_contiguous_raw_parts_in: interior range");
        kani::cover(
            start == 0 && end == 0 && capacity > 0,
            "from_contiguous_raw_parts_in: empty range",
        );
        finish(deque);
    }

    /// A `Vec<T>` with symbolic capacity and no elements, used to obtain raw parts.
    fn any_empty_deque_vec<T>() -> Vec<T> {
        let requested: usize = kani::any();
        kani::assume(Layout::array::<T>(requested).is_ok());
        kani::assume(
            requested
                .checked_mul(core::mem::size_of::<T>())
                .is_some_and(|b| b <= MAX_ALLOCATION_BYTES),
        );
        Vec::<T>::with_capacity(requested)
    }

    fn check_abort_shrink<T: Shape>() {
        let mut deque = any_empty_deque::<T>();
        let cap = deque.capacity();
        let target_cap: usize = kani::any_where(|c: &usize| *c <= cap);
        let len: usize = kani::any_where(|l: &usize| *l <= target_cap);
        let head: usize = kani::any_where(|h: &usize| *h <= target_cap);
        let old_head: usize = kani::any_where(|h: &usize| *h < cap);
        kani::assume(head < target_cap || len == 0);
        if head < target_cap {
            init_ring(&mut deque, target_cap, head, len);
        } else {
            deque.head = head;
            deque.len = 0;
        }
        let contiguous = head <= target_cap - len;
        let head_len = target_cap - head;
        let tail_len = len.wrapping_sub(head_len);
        let case_b = !contiguous && tail_len <= cmp::min(head_len, cap - target_cap);
        unsafe { deque.abort_shrink(old_head, target_cap) };
        kani::cover(contiguous && len > 0, "abort_shrink: contiguous, nothing to do");
        kani::cover(case_b, "abort_shrink: tail copied to the back");
        kani::cover(!contiguous && !case_b, "abort_shrink: head copied back to old_head");
        touch(&deque);
    }

    fn check_rotate_left_inner<T: Shape>() {
        let mut deque = any_deque::<T>();
        let mid: usize = kani::any();
        unsafe { deque.rotate_left_inner(mid) };
        kani::cover(mid > 1, "rotate_left_inner: rotation by more than one");
        touch(&deque);
    }

    fn check_rotate_right_inner<T: Shape>() {
        let mut deque = any_deque::<T>();
        let k: usize = kani::any();
        unsafe { deque.rotate_right_inner(k) };
        kani::cover(k > 1, "rotate_right_inner: rotation by more than one");
        touch(&deque);
    }

    // ---------------------------------------------------------------------------------------
    // Safe-abstraction harnesses
    // ---------------------------------------------------------------------------------------

    /// `push_*`, `insert`, `reserve*` and `append` may legitimately panic with "capacity
    /// overflow" when the requested capacity cannot be represented; the harnesses assume the
    /// documented non-panicking condition instead (the new capacity fits the allocation model).
    fn assume_can_grow_by<T>(deque: &VecDeque<T>, additional: usize) {
        kani::assume(deque.len().checked_add(additional).is_some_and(|new_len| {
            new_len
                .checked_mul(core::mem::size_of::<T>())
                .is_some_and(|b| b <= MAX_ALLOCATION_BYTES)
                && (!T::IS_ZST || new_len < usize::MAX)
        }));
    }

    fn check_get<T: Shape>() {
        let deque = any_deque::<T>();
        let i: usize = kani::any();
        let elem = deque.get(i);
        assert_eq!(elem.is_some(), i < deque.len());
        if let Some(elem) = elem {
            core::mem::forget(unsafe { ptr::read(elem) });
        }
        kani::cover(i > 0 && i < deque.len(), "get: in-bounds non-front index");
        kani::cover(i >= deque.len(), "get: out-of-bounds index");
        finish(deque);
    }

    fn check_get_mut<T: Shape>() {
        let mut deque = any_deque::<T>();
        let i: usize = kani::any();
        let len = deque.len();
        let elem = deque.get_mut(i);
        assert_eq!(elem.is_some(), i < len);
        if let Some(elem) = elem {
            *elem = kani::any();
        }
        kani::cover(i > 0 && i < len, "get_mut: in-bounds non-front index");
        touch(&deque);
        finish(deque);
    }

    fn check_swap<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let i: usize = kani::any_where(|x: &usize| *x < len);
        let j: usize = kani::any_where(|x: &usize| *x < len);
        deque.swap(i, j);
        kani::cover(i != j, "swap: distinct indices");
        touch(&deque);
        finish(deque);
    }

    fn check_as_slices<T: Shape>() {
        let deque = any_deque::<T>();
        let (a, b) = deque.as_slices();
        assert_eq!(a.len() + b.len(), deque.len());
        if let Some(last) = a.last() {
            core::mem::forget(unsafe { ptr::read(last) });
        }
        if let Some(last) = b.last() {
            core::mem::forget(unsafe { ptr::read(last) });
        }
        kani::cover(!a.is_empty() && !b.is_empty(), "as_slices: both halves non-empty");
    }

    fn check_as_mut_slices<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let (a, b) = deque.as_mut_slices();
        assert_eq!(a.len() + b.len(), len);
        if let Some(last) = a.last_mut() {
            *last = kani::any();
        }
        if let Some(first) = b.first_mut() {
            *first = kani::any();
        }
        kani::cover(!a.is_empty() && !b.is_empty(), "as_mut_slices: both halves non-empty");
        touch(&deque);
    }

    fn any_subrange(len: usize) -> (usize, usize) {
        let start: usize = kani::any_where(|s: &usize| *s <= len);
        let end: usize = kani::any_where(|e: &usize| *e >= start && *e <= len);
        (start, end)
    }

    fn check_range<T: Shape>() {
        let deque = any_deque::<T>();
        let (start, end) = any_subrange(deque.len());
        let mut iter = deque.range(start..end);
        assert_eq!(iter.len(), end - start);
        if let Some(first) = iter.next() {
            core::mem::forget(unsafe { ptr::read(first) });
        }
        if let Some(last) = iter.next_back() {
            core::mem::forget(unsafe { ptr::read(last) });
        }
        kani::cover(end - start > 2, "range: more than two elements");
    }

    fn check_range_mut<T: Shape>() {
        let mut deque = any_deque::<T>();
        let (start, end) = any_subrange(deque.len());
        let mut iter = deque.range_mut(start..end);
        assert_eq!(iter.len(), end - start);
        if let Some(first) = iter.next() {
            *first = kani::any();
        }
        if let Some(last) = iter.next_back() {
            *last = kani::any();
        }
        kani::cover(end - start > 2, "range_mut: more than two elements");
        touch(&deque);
    }

    fn check_drain<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let (start, end) = any_subrange(len);
        let mut drain = deque.drain(start..end);
        let pull_front: bool = kani::any();
        let pull_back: bool = kani::any();
        if pull_front {
            if let Some(elem) = drain.next() {
                core::mem::forget(elem);
            }
        }
        if pull_back {
            if let Some(elem) = drain.next_back() {
                core::mem::forget(elem);
            }
        }
        drop(drain);
        assert_eq!(deque.len(), len - (end - start));
        kani::cover(
            start > 0 && end < len && end > start,
            "drain: interior range (elements moved)",
        );
        kani::cover(start == 0 && end == len && len > 0, "drain: everything drained");
        kani::cover(start > 0 && end == len && end > start, "drain: tail drained");
        kani::cover(start == 0 && end < len && end > 0, "drain: head drained");
        touch(&deque);
    }

    fn check_pop_front<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let elem = deque.pop_front();
        assert_eq!(elem.is_some(), len > 0);
        assert_eq!(deque.len(), len.saturating_sub(1));
        core::mem::forget(elem);
        kani::cover(len > 1, "pop_front: elements remain");
        touch(&deque);
        finish(deque);
    }

    fn check_pop_back<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let elem = deque.pop_back();
        assert_eq!(elem.is_some(), len > 0);
        assert_eq!(deque.len(), len.saturating_sub(1));
        core::mem::forget(elem);
        kani::cover(len > 1, "pop_back: elements remain");
        touch(&deque);
        finish(deque);
    }

    fn check_push_front<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let full = deque.is_full();
        assume_can_grow_by(&deque, 1);
        deque.push_front(kani::any());
        assert_eq!(deque.len(), len + 1);
        cover_buffer_path!(T, full && len > 0, "push_front: buffer grown");
        kani::cover(!full && len > 0, "push_front: no growth");
        touch(&deque);
        finish(deque);
    }

    fn check_push_back<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let full = deque.is_full();
        assume_can_grow_by(&deque, 1);
        deque.push_back(kani::any());
        assert_eq!(deque.len(), len + 1);
        cover_buffer_path!(T, full && len > 0, "push_back: buffer grown");
        kani::cover(!full && len > 0, "push_back: no growth");
        touch(&deque);
        finish(deque);
    }

    fn check_reserve<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let old_cap = deque.capacity();
        let additional: usize = kani::any();
        assume_can_grow_by(&deque, additional);
        deque.reserve(additional);
        assert_eq!(deque.len(), len);
        assert!(deque.capacity() >= len + additional);
        cover_buffer_path!(T, len + additional > old_cap && len > 0, "reserve: buffer grown");
        kani::cover(len + additional <= old_cap, "reserve: no growth");
        touch(&deque);
    }

    fn check_reserve_exact<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let old_cap = deque.capacity();
        let additional: usize = kani::any();
        assume_can_grow_by(&deque, additional);
        deque.reserve_exact(additional);
        assert_eq!(deque.len(), len);
        assert!(deque.capacity() >= len + additional);
        cover_buffer_path!(T, len + additional > old_cap && len > 0, "reserve_exact: buffer grown");
        kani::cover(len + additional <= old_cap, "reserve_exact: no growth");
        touch(&deque);
    }

    fn check_try_reserve<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let old_cap = deque.capacity();
        let additional: usize = kani::any();
        let result = deque.try_reserve(additional);
        assert_eq!(deque.len(), len);
        if result.is_ok() {
            assert!(deque.capacity() >= len + additional);
        }
        cover_buffer_path!(
            T,
            result.is_ok() && len + additional > old_cap && len > 0,
            "try_reserve: buffer grown"
        );
        kani::cover(result.is_err(), "try_reserve: capacity overflow reported");
        touch(&deque);
    }

    fn check_try_reserve_exact<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let old_cap = deque.capacity();
        let additional: usize = kani::any();
        let result = deque.try_reserve_exact(additional);
        assert_eq!(deque.len(), len);
        if result.is_ok() {
            assert!(deque.capacity() >= len + additional);
        }
        cover_buffer_path!(
            T,
            result.is_ok() && len + additional > old_cap && len > 0,
            "try_reserve_exact: buffer grown"
        );
        kani::cover(result.is_err(), "try_reserve_exact: capacity overflow reported");
        touch(&deque);
    }

    fn check_shrink_to<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let head = deque.head;
        let cap = deque.capacity();
        let min_capacity: usize = kani::any();
        let target_cap = cmp::max(min_capacity, len);
        let end = head as u128 + len as u128;
        let tail_outside = target_cap < cap && end > target_cap as u128 && end <= cap as u128;
        deque.shrink_to(min_capacity);
        assert_eq!(deque.len(), len);
        assert!(deque.capacity() >= cmp::min(target_cap, cap));
        let shrinking = !T::IS_ZST && target_cap < cap && len > 0;
        cover_buffer_path!(
            T,
            shrinking && head >= target_cap && tail_outside,
            "shrink_to: all elements moved to front"
        );
        cover_buffer_path!(
            T,
            shrinking && head < target_cap && tail_outside,
            "shrink_to: tail wrapped to front"
        );
        cover_buffer_path!(
            T,
            shrinking && !tail_outside && end > cap as u128,
            "shrink_to: head slice moved back"
        );
        cover_buffer_path!(
            T,
            shrinking && !tail_outside && end <= target_cap as u128,
            "shrink_to: elements untouched"
        );
        touch(&deque);
    }

    fn check_truncate<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let front_len = deque.as_slices().0.len();
        let new_len: usize = kani::any();
        deque.truncate(new_len);
        assert_eq!(deque.len(), cmp::min(len, new_len));
        kani::cover(new_len < len && new_len > front_len, "truncate: cut inside the back slice");
        kani::cover(
            new_len < len && new_len <= front_len && front_len < len,
            "truncate: cut inside the front slice, back dropped",
        );
        kani::cover(new_len >= len, "truncate: no-op");
        touch(&deque);
    }

    fn check_insert<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let full = deque.is_full();
        let index: usize = kani::any_where(|i: &usize| *i <= len);
        assume_can_grow_by(&deque, 1);
        deque.insert(index, kani::any());
        assert_eq!(deque.len(), len + 1);
        kani::cover(len - index < index, "insert: back half shifted");
        kani::cover(len - index >= index && index > 0, "insert: front half shifted");
        cover_buffer_path!(T, full && len > 0, "insert: buffer grown");
        touch(&deque);
    }

    fn check_remove<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let index: usize = kani::any();
        let elem = deque.remove(index);
        assert_eq!(elem.is_some(), index < len);
        assert_eq!(deque.len(), if index < len { len - 1 } else { len });
        core::mem::forget(elem);
        kani::cover(index < len && len - index - 1 < index, "remove: back half shifted");
        kani::cover(
            index < len && len - index - 1 >= index && index > 0,
            "remove: front half shifted",
        );
        touch(&deque);
        finish(deque);
    }

    fn check_split_off<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let first_len = deque.as_slices().0.len();
        let at: usize = kani::any_where(|a: &usize| *a <= len);
        let other = deque.split_off(at);
        assert_eq!(deque.len(), at);
        assert_eq!(other.len(), len - at);
        kani::cover(at < first_len && first_len < len, "split_off: split inside the first half");
        kani::cover(
            at >= first_len && at < len && first_len < len,
            "split_off: split inside the second half",
        );
        touch(&deque);
        touch(&other);
        finish(deque);
        finish(other);
    }

    fn check_append<T: Shape>() {
        let mut deque = any_deque::<T>();
        let mut other = any_deque::<T>();
        let len = deque.len();
        let other_len = other.len();
        let old_cap = deque.capacity();
        assume_can_grow_by(&deque, other_len);
        deque.append(&mut other);
        assert_eq!(deque.len(), len + other_len);
        assert_eq!(other.len(), 0);
        cover_buffer_path!(T, len + other_len > old_cap && other_len > 0, "append: buffer grown");
        kani::cover(len + other_len <= old_cap && other_len > 0 && len > 0, "append: in place");
        touch(&deque);
        touch(&other);
        finish(deque);
        finish(other);
    }

    fn check_retain_mut<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        deque.retain_mut(|elem| {
            let keep: bool = kani::any();
            if keep {
                *elem = kani::any();
            }
            keep
        });
        assert!(deque.len() <= len);
        kani::cover(deque.len() > 0 && deque.len() < len, "retain_mut: some elements removed");
        touch(&deque);
    }

    fn check_grow<T: Shape>() {
        let mut deque = any_deque::<T>();
        kani::assume(deque.is_full());
        let len = deque.len();
        assume_can_grow_by(&deque, 1);
        deque.grow();
        assert_eq!(deque.len(), len);
        assert!(!deque.is_full());
        kani::cover(len > 1, "grow: non-trivial deque");
        touch(&deque);
    }

    /// `resize_with` appends through `extend` → `write_iter_wrapping` with a
    /// `Take<RepeatWith<_>>` iterator. That iterator cannot be advanced without a loop, so the
    /// contract replacement of `write_iter`'s loop can only model calls after which the
    /// iterator is not reused, i.e. the non-wrapping branch of `write_iter_wrapping` (see
    /// `write_iter_contract_replacement_drop`). The two `resize_with` harnesses therefore
    /// restrict the appended elements to not wrap around the end of the buffer, in two
    /// complementary ways; the wrapping write path itself is verified by
    /// `check_write_iter_wrapping_*`.
    ///
    /// Variant 1: arbitrary (possibly wrapped) deque, capacity reserved up front so that the
    /// appended elements fit behind the last element without wrapping.
    fn check_resize_with<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let new_len: usize = kani::any();
        if new_len > len {
            let additional = new_len - len;
            assume_can_grow_by(&deque, additional);
            deque.reserve(additional);
            kani::assume(additional <= deque.capacity() - deque.to_physical_idx(len));
        }
        deque.resize_with(new_len, || kani::any());
        assert_eq!(deque.len(), new_len);
        kani::cover(
            new_len > len && new_len - len > 1 && len > 0 && deque.head > 0,
            "resize_with: grown by more than one",
        );
        kani::cover(new_len < len, "resize_with: truncated");
        touch(&deque);
    }

    /// Variant 2: contiguous deque starting at `head == 0`, so that the growth performed by
    /// `resize_with` itself (`reserve` → `handle_capacity_increase`, case A) keeps the appended
    /// elements from wrapping.
    fn check_resize_with_grow<T: Shape>() {
        let mut deque = any_deque::<T>();
        kani::assume(deque.head == 0);
        let len = deque.len();
        let cap = deque.capacity();
        let new_len: usize = kani::any();
        if new_len > len {
            assume_can_grow_by(&deque, new_len - len);
        }
        deque.resize_with(new_len, || kani::any());
        assert_eq!(deque.len(), new_len);
        cover_buffer_path!(T, new_len > cap && len > 0, "resize_with: buffer grown");
        kani::cover(
            new_len > len && new_len - len > 1 && new_len <= cap,
            "resize_with: appended in place",
        );
        touch(&deque);
    }

    fn check_rotate_left<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let n: usize = kani::any_where(|n: &usize| *n <= len);
        deque.rotate_left(n);
        assert_eq!(deque.len(), len);
        kani::cover(n > 0 && n <= len - n, "rotate_left: via rotate_left_inner");
        kani::cover(n > len - n, "rotate_left: via rotate_right_inner");
        touch(&deque);
    }

    fn check_rotate_right<T: Shape>() {
        let mut deque = any_deque::<T>();
        let len = deque.len();
        let n: usize = kani::any_where(|n: &usize| *n <= len);
        deque.rotate_right(n);
        assert_eq!(deque.len(), len);
        kani::cover(n > 0 && n <= len - n, "rotate_right: via rotate_right_inner");
        kani::cover(n > len - n, "rotate_right: via rotate_left_inner");
        touch(&deque);
    }

    // ---------------------------------------------------------------------------------------
    // Instantiation over element types.
    // ---------------------------------------------------------------------------------------

    macro_rules! contract_harness {
        ($target:ident, $harness:ident, $ty:ty, $name:ident, [$($attr:meta),*]) => {
            #[kani::proof_for_contract(VecDeque::<$ty>::$target)]
            $(#[$attr])*
            fn $name() {
                $harness::<$ty>();
            }
        };
    }

    macro_rules! contract_harnesses {
        ($target:ident, $harness:ident, [$($ty:ty => $name:ident),* $(,)?]) => {
            $( contract_harness!($target, $harness, $ty, $name, []); )*
        };
        ($target:ident, $harness:ident, $attrs:tt, [$($ty:ty => $name:ident),* $(,)?]) => {
            $( contract_harness!($target, $harness, $ty, $name, $attrs); )*
        };
    }

    macro_rules! proof_harness {
        ($harness:ident, $ty:ty, $name:ident, [$($attr:meta),*]) => {
            #[kani::proof]
            $(#[$attr])*
            fn $name() {
                $harness::<$ty>();
            }
        };
    }

    macro_rules! proof_harnesses {
        ($harness:ident, $attrs:tt, [$($ty:ty => $name:ident),* $(,)?]) => {
            $( proof_harness!($harness, $ty, $name, $attrs); )*
        };
    }

    contract_harnesses!(push_unchecked, check_push_unchecked, [u8 => check_push_unchecked_u8, u64 => check_push_unchecked_u64, [u8; 3] => check_push_unchecked_u8x3, () => check_push_unchecked_unit]);
    contract_harnesses!(buffer_read, check_buffer_read, [u8 => check_buffer_read_u8, u64 => check_buffer_read_u64, [u8; 3] => check_buffer_read_u8x3, () => check_buffer_read_unit]);
    contract_harnesses!(buffer_write, check_buffer_write, [u8 => check_buffer_write_u8, u64 => check_buffer_write_u64, [u8; 3] => check_buffer_write_u8x3, () => check_buffer_write_unit]);
    contract_harnesses!(buffer_range, check_buffer_range, [u8 => check_buffer_range_u8, u64 => check_buffer_range_u64, [u8; 3] => check_buffer_range_u8x3, () => check_buffer_range_unit]);
    contract_harnesses!(copy, check_copy, [u8 => check_copy_u8, u64 => check_copy_u64, [u8; 3] => check_copy_u8x3, () => check_copy_unit]);
    contract_harnesses!(copy_nonoverlapping, check_copy_nonoverlapping, [u8 => check_copy_nonoverlapping_u8, u64 => check_copy_nonoverlapping_u64, [u8; 3] => check_copy_nonoverlapping_u8x3, () => check_copy_nonoverlapping_unit]);
    contract_harnesses!(wrap_copy, check_wrap_copy, [u8 => check_wrap_copy_u8, u64 => check_wrap_copy_u64, () => check_wrap_copy_unit]);
    contract_harnesses!(copy_slice, check_copy_slice, [u8 => check_copy_slice_u8, u64 => check_copy_slice_u64, () => check_copy_slice_unit]);
    contract_harnesses!(write_iter, check_write_iter, [u8 => check_write_iter_u8, u64 => check_write_iter_u64, [u8; 3] => check_write_iter_u8x3, () => check_write_iter_unit]);
    contract_harnesses!(
        write_iter_wrapping,
        check_write_iter_wrapping,
        [kani::stub(VecDeque::<u8>::write_iter_loop, VecDeque::<u8>::write_iter_contract_replacement)],
        [u8 => check_write_iter_wrapping_u8]
    );
    contract_harnesses!(
        write_iter_wrapping,
        check_write_iter_wrapping,
        [kani::stub(VecDeque::<u64>::write_iter_loop, VecDeque::<u64>::write_iter_contract_replacement)],
        [u64 => check_write_iter_wrapping_u64]
    );
    contract_harnesses!(
        write_iter_wrapping,
        check_write_iter_wrapping,
        [kani::stub(VecDeque::<()>::write_iter_loop, VecDeque::<()>::write_iter_contract_replacement)],
        [() => check_write_iter_wrapping_unit]
    );
    contract_harnesses!(handle_capacity_increase, check_handle_capacity_increase, [u8 => check_handle_capacity_increase_u8, u64 => check_handle_capacity_increase_u64, () => check_handle_capacity_increase_unit]);
    contract_harnesses!(from_contiguous_raw_parts_in, check_from_contiguous_raw_parts_in, [u8 => check_from_contiguous_raw_parts_in_u8, u64 => check_from_contiguous_raw_parts_in_u64, [u8; 3] => check_from_contiguous_raw_parts_in_u8x3, () => check_from_contiguous_raw_parts_in_unit]);
    contract_harnesses!(abort_shrink, check_abort_shrink, [u8 => check_abort_shrink_u8, u64 => check_abort_shrink_u64, () => check_abort_shrink_unit]);
    contract_harnesses!(rotate_left_inner, check_rotate_left_inner, [u8 => check_rotate_left_inner_u8, u64 => check_rotate_left_inner_u64, () => check_rotate_left_inner_unit]);
    contract_harnesses!(rotate_right_inner, check_rotate_right_inner, [u8 => check_rotate_right_inner_u8, u64 => check_rotate_right_inner_u64, () => check_rotate_right_inner_unit]);

    proof_harnesses!(check_get, [], [u8 => check_get_u8, u64 => check_get_u64, () => check_get_unit]);
    proof_harnesses!(check_get_mut, [], [u8 => check_get_mut_u8, u64 => check_get_mut_u64, () => check_get_mut_unit]);
    proof_harnesses!(check_swap, [], [u8 => check_swap_u8, u64 => check_swap_u64, () => check_swap_unit]);
    proof_harnesses!(check_as_slices, [], [u8 => check_as_slices_u8, u64 => check_as_slices_u64, () => check_as_slices_unit]);
    proof_harnesses!(check_as_mut_slices, [], [u8 => check_as_mut_slices_u8, u64 => check_as_mut_slices_u64, () => check_as_mut_slices_unit]);
    proof_harnesses!(check_range, [], [u8 => check_range_u8, () => check_range_unit]);
    proof_harnesses!(check_range_mut, [], [u8 => check_range_mut_u8, () => check_range_mut_unit]);
    proof_harnesses!(check_drain, [], [u8 => check_drain_u8, () => check_drain_unit]);
    proof_harnesses!(check_pop_front, [], [u8 => check_pop_front_u8, u64 => check_pop_front_u64, () => check_pop_front_unit]);
    proof_harnesses!(check_pop_back, [], [u8 => check_pop_back_u8, u64 => check_pop_back_u64, () => check_pop_back_unit]);
    proof_harnesses!(check_push_front, [], [u8 => check_push_front_u8, u64 => check_push_front_u64, () => check_push_front_unit]);
    proof_harnesses!(check_push_back, [], [u8 => check_push_back_u8, u64 => check_push_back_u64, () => check_push_back_unit]);
    proof_harnesses!(check_reserve, [], [u8 => check_reserve_u8, u64 => check_reserve_u64, () => check_reserve_unit]);
    proof_harnesses!(check_reserve_exact, [], [u8 => check_reserve_exact_u8, () => check_reserve_exact_unit]);
    proof_harnesses!(check_try_reserve, [], [u8 => check_try_reserve_u8, () => check_try_reserve_unit]);
    proof_harnesses!(check_try_reserve_exact, [], [u8 => check_try_reserve_exact_u8, u64 => check_try_reserve_exact_u64, () => check_try_reserve_exact_unit]);
    proof_harnesses!(check_shrink_to, [], [u8 => check_shrink_to_u8, u64 => check_shrink_to_u64, () => check_shrink_to_unit]);
    proof_harnesses!(check_truncate, [], [u8 => check_truncate_u8, u64 => check_truncate_u64, () => check_truncate_unit]);
    proof_harnesses!(check_insert, [], [u8 => check_insert_u8, () => check_insert_unit]);
    proof_harnesses!(check_remove, [], [u8 => check_remove_u8, () => check_remove_unit]);
    proof_harnesses!(check_split_off, [], [u8 => check_split_off_u8, u64 => check_split_off_u64, () => check_split_off_unit]);
    proof_harnesses!(check_append, [], [u8 => check_append_u8, () => check_append_unit]);
    proof_harnesses!(check_retain_mut, [], [u8 => check_retain_mut_u8, () => check_retain_mut_unit]);
    // `grow` is only ever called on a full deque; for a zero-sized `T` that means
    // `len == usize::MAX`, where growing panics with "capacity overflow" by design, so there
    // is no non-panicking ZST instance to verify.
    proof_harnesses!(check_grow, [], [u8 => check_grow_u8]);
    proof_harnesses!(
        check_resize_with,
        [kani::stub(VecDeque::<u8>::write_iter_loop, VecDeque::<u8>::write_iter_contract_replacement_drop)],
        [u8 => check_resize_with_u8]
    );
    proof_harnesses!(
        check_resize_with,
        [kani::stub(VecDeque::<()>::write_iter_loop, VecDeque::<()>::write_iter_contract_replacement_drop)],
        [() => check_resize_with_unit]
    );
    proof_harnesses!(
        check_resize_with_grow,
        [kani::stub(VecDeque::<u8>::write_iter_loop, VecDeque::<u8>::write_iter_contract_replacement_drop)],
        [u8 => check_resize_with_grow_u8]
    );
    proof_harnesses!(
        check_resize_with_grow,
        [kani::stub(VecDeque::<()>::write_iter_loop, VecDeque::<()>::write_iter_contract_replacement_drop)],
        [() => check_resize_with_grow_unit]
    );
    proof_harnesses!(
        check_make_contiguous,
        [kani::stub(core::slice::rotate::ptr_rotate, stub_ptr_rotate)],
        [u8 => check_make_contiguous_u8, () => check_make_contiguous_unit]
    );
    proof_harnesses!(check_rotate_left, [], [u8 => check_rotate_left_u8, () => check_rotate_left_unit]);
    proof_harnesses!(check_rotate_right, [], [u8 => check_rotate_right_u8, () => check_rotate_right_unit]);

    // Additional shapes (see the shape matrix in the module documentation). `WithDrop` goes on
    // the targets that move or read elements and drop at most one at a time; `Al16` and `bool`
    // on the cheap allocation/read paths. The drop-glue paths are in `bounded_evidence`.
    contract_harnesses!(push_unchecked, check_push_unchecked, [WithDrop => check_push_unchecked_withdrop, Al16 => check_push_unchecked_al16, bool => check_push_unchecked_bool]);
    contract_harnesses!(buffer_read, check_buffer_read, [WithDrop => check_buffer_read_withdrop, Al16 => check_buffer_read_al16, bool => check_buffer_read_bool]);
    contract_harnesses!(buffer_write, check_buffer_write, [WithDrop => check_buffer_write_withdrop, Al16 => check_buffer_write_al16]);
    contract_harnesses!(buffer_range, check_buffer_range, [Al16 => check_buffer_range_al16]);
    contract_harnesses!(copy, check_copy, [Al16 => check_copy_al16]);
    contract_harnesses!(copy_nonoverlapping, check_copy_nonoverlapping, [Al16 => check_copy_nonoverlapping_al16]);
    contract_harnesses!(write_iter, check_write_iter, [WithDrop => check_write_iter_withdrop, Al16 => check_write_iter_al16, bool => check_write_iter_bool]);
    contract_harnesses!(
        write_iter_wrapping,
        check_write_iter_wrapping,
        [kani::stub(VecDeque::<WithDrop>::write_iter_loop, VecDeque::<WithDrop>::write_iter_contract_replacement)],
        [WithDrop => check_write_iter_wrapping_withdrop]
    );
    contract_harnesses!(from_contiguous_raw_parts_in, check_from_contiguous_raw_parts_in, [WithDrop => check_from_contiguous_raw_parts_in_withdrop, Al16 => check_from_contiguous_raw_parts_in_al16]);
    proof_harnesses!(check_get, [], [WithDrop => check_get_withdrop, Al16 => check_get_al16, bool => check_get_bool]);
    proof_harnesses!(check_get_mut, [], [WithDrop => check_get_mut_withdrop]);
    proof_harnesses!(check_swap, [], [WithDrop => check_swap_withdrop]);
    proof_harnesses!(check_pop_front, [], [WithDrop => check_pop_front_withdrop, Al16 => check_pop_front_al16, bool => check_pop_front_bool]);
    proof_harnesses!(check_pop_back, [], [WithDrop => check_pop_back_withdrop]);
    proof_harnesses!(check_push_front, [], [WithDrop => check_push_front_withdrop]);
    proof_harnesses!(check_push_back, [], [WithDrop => check_push_back_withdrop, Al16 => check_push_back_al16, bool => check_push_back_bool]);
    proof_harnesses!(check_remove, [], [WithDrop => check_remove_withdrop]);
    proof_harnesses!(check_split_off, [], [WithDrop => check_split_off_withdrop, Al16 => check_split_off_al16]);
    proof_harnesses!(check_append, [], [WithDrop => check_append_withdrop]);
    proof_harnesses!(check_shrink_to, [], [Al16 => check_shrink_to_al16]);

    /// Bounded supplementary evidence.
    ///
    /// None of the harnesses in this module is the proof of any function listed in Challenge
    /// 25. Each is supplementary evidence for one stub, one transcription or one drop-glue path
    /// named in its doc comment, and this module is the only place in `verify` that uses
    /// `#[kani::unwind]`. Every listed function keeps its unbounded harness in the parent
    /// module. No harness here reaches a loop that carries a loop contract except the
    /// `retain_mut` drop-glue one (Kani replaces such loops by their contracts regardless of the
    /// unwind bound, which is fine there: only the drop glue is bounded); the `write_iter`
    /// iteration is exercised through the contract-free `write_iter_for_each`, the shipped
    /// statement.
    mod bounded_evidence {
        use core::iter::ByRefSized;

        use super::*;

        /// Bound on the iterator length / element count of every harness in this module.
        const N: usize = 4;

        // -----------------------------------------------------------------------------------
        // Item 2: the shipped `for_each` statement of `write_iter`
        // -----------------------------------------------------------------------------------

        /// `write_iter`'s contract checked against the shipped `for_each` statement
        /// (`write_iter_for_each`, substituted for `write_iter_loop`), the deque fully
        /// symbolic, the iterator length bounded by `N`.
        fn write_iter_shipped_text<T: Shape>() {
            let mut deque = any_deque::<T>();
            let dst: usize = kani::any();
            let n: usize = kani::any();
            kani::assume(n <= N);
            let mut written: usize = kani::any();
            let before = written;
            unsafe { deque.write_iter(dst, AnyIter::<T>::new(n), &mut written) };
            assert_eq!(written, before + n);
            kani::cover(n == N && dst > 0, "shipped text: N elements written at a non-zero offset");
            finish(deque);
        }

        macro_rules! shipped_text_harness {
            ($ty:ty, $name:ident) => {
                #[kani::proof_for_contract(VecDeque::<$ty>::write_iter)]
                #[kani::stub(VecDeque::<$ty>::write_iter_loop, VecDeque::<$ty>::write_iter_for_each)]
                #[kani::unwind(6)]
                fn $name() {
                    write_iter_shipped_text::<$ty>();
                }
            };
        }
        shipped_text_harness!(u8, bounded_write_iter_shipped_text_u8);
        shipped_text_harness!(u64, bounded_write_iter_shipped_text_u64);
        shipped_text_harness!([u8; 3], bounded_write_iter_shipped_text_u8x3);
        shipped_text_harness!((), bounded_write_iter_shipped_text_unit);
        shipped_text_harness!(WithDrop, bounded_write_iter_shipped_text_withdrop);

        // -----------------------------------------------------------------------------------
        // Item 3: what `write_iter_contract_replacement` adds to `write_iter`'s contract
        // -----------------------------------------------------------------------------------

        /// The wrapping branch of `write_iter_wrapping` with the shipped statement doing the
        /// iteration on the real adapter stack (`Take<ByRefSized<&mut AnyIter>>`, then the
        /// borrowed iterator itself): every element is written exactly once (`written == n`),
        /// which is the consumption `write_iter_contract_replacement` models with
        /// `advance_by(hi)`.
        #[kani::proof_for_contract(VecDeque::<u8>::write_iter_wrapping)]
        #[kani::stub(VecDeque::<u8>::write_iter_loop, VecDeque::<u8>::write_iter_for_each)]
        #[kani::unwind(6)]
        fn bounded_write_iter_wrapping_shipped_text_u8() {
            let mut deque = any_deque::<u8>();
            let dst: usize = kani::any();
            let len: usize = kani::any();
            let n: usize = kani::any();
            kani::assume(n <= N);
            let old_len = deque.len;
            let written = unsafe { deque.write_iter_wrapping(dst, AnyIter::<u8>::new(n), len) };
            assert_eq!(written, n);
            assert_eq!(deque.len, old_len + n);
            kani::cover(
                n > 1 && n > deque.capacity() - dst,
                "shipped text, wrapping branch: both write_iter calls write",
            );
            touch(&deque);
        }

        /// `advance_by(hi)` — the step `write_iter_contract_replacement` adds to the contract —
        /// leaves the borrowed iterator in the same state as `hi` calls of `next()` (what the
        /// loop does), on the adapter stack `write_iter_wrapping` builds and on the bare
        /// iterator, for `hi = size_hint().1` (the value the replacement uses; `Take::next` and
        /// `Take::advance_by` differ only past the hint).
        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_replacement_advance_by_matches_next_u8() {
            let n: usize = kani::any();
            let k: usize = kani::any();
            kani::assume(n <= N && k <= N);
            // The adapter stack of the wrapping branch's first call.
            let mut a = AnyIter::<u8>::new(n);
            let mut b = AnyIter::<u8>::new(n);
            let mut ta = ByRefSized(&mut a).take(k);
            let hi = ta.size_hint().1.unwrap();
            assert_eq!(ta.size_hint().0, hi);
            assert!(ta.advance_by(hi).is_ok());
            let mut tb = ByRefSized(&mut b).take(k);
            let mut steps = 0;
            while let Some(_) = tb.next() {
                steps += 1;
            }
            assert_eq!(steps, hi);
            drop(ta);
            drop(tb);
            assert_eq!(a.size_hint(), b.size_hint());
            assert_eq!(a.size_hint().1, Some(n - hi));
            // The bare iterator (direct branch, and the wrapping branch's second call).
            let mut c = AnyIter::<u8>::new(n);
            let mut d = AnyIter::<u8>::new(n);
            let hi = c.size_hint().1.unwrap();
            assert!(c.advance_by(hi).is_ok());
            let mut steps = 0;
            while let Some(_) = d.next() {
                steps += 1;
            }
            assert_eq!(steps, hi);
            assert_eq!(c.size_hint(), d.size_hint());
            kani::cover(k > 0 && k < n, "Take budget smaller than the iterator");
            kani::cover(k > n, "Take budget larger than the iterator");
        }

        // -----------------------------------------------------------------------------------
        // Item 3: `stub_ptr_rotate`
        // -----------------------------------------------------------------------------------

        /// `<[u8]>::rotate_left` / `rotate_right` — the calls `make_contiguous` makes, hence
        /// `core::slice::rotate::ptr_rotate` — on ranges of every length up to eight and every
        /// rotation amount, with symbolic contents and a symbolic guard byte on each side: the
        /// range holds exactly the rotated sequence afterwards and the guards are untouched,
        /// i.e. `ptr_rotate` permutes the slots of the range and writes nothing else — what
        /// `stub_ptr_rotate` abstracts for `check_make_contiguous_*`. Lengths and amounts are
        /// enumerated rather than symbolic so that `ptr_rotate`'s algorithm selection is
        /// concrete: only the selected, loop-free `ptr_rotate_memmove` is explored (the two
        /// looping algorithms need `min(left, right) > 256` for `u8`, and would otherwise be
        /// unwound although unreachable).
        #[kani::proof]
        #[kani::unwind(10)]
        fn bounded_rotate_permutes_range_u8() {
            const N: usize = 8;
            for len in 0..=N {
                for mid in 0..=len {
                    let mut buf: [u8; N + 2] = kani::any();
                    let before = buf;
                    buf[1..1 + len].rotate_left(mid);
                    for i in 0..len {
                        assert_eq!(buf[1 + i], before[1 + (i + mid) % len]);
                    }
                    assert_eq!(buf[0], before[0]);
                    for i in 1 + len..N + 2 {
                        assert_eq!(buf[i], before[i]);
                    }
                    let mut buf: [u8; N + 2] = kani::any();
                    let before = buf;
                    buf[1..1 + len].rotate_right(mid);
                    for i in 0..len {
                        assert_eq!(buf[1 + (i + mid) % len], before[1 + i]);
                    }
                    assert_eq!(buf[0], before[0]);
                    for i in 1 + len..N + 2 {
                        assert_eq!(buf[i], before[i]);
                    }
                }
            }
            kani::cover(true, "rotate: all lengths and amounts up to 8 enumerated");
        }

        // -----------------------------------------------------------------------------------
        // Item 1: the drop-glue paths, for the `needs_drop` shape
        // -----------------------------------------------------------------------------------

        /// A `VecDeque<WithDrop>` of capacity `<= 8` with `len <= N` elements written in place
        /// (no destructor runs while building), symbolic head, and `DROPS` reset to zero.
        fn small_deque_with_drop() -> VecDeque<WithDrop> {
            const CAP: usize = 8;
            let requested: usize = kani::any();
            kani::assume(requested <= CAP);
            let mut deque = VecDeque::<WithDrop>::with_capacity(requested);
            let cap = deque.capacity();
            kani::assume(cap <= CAP);
            let head: usize = if cap == 0 { 0 } else { kani::any_where(|h: &usize| *h < cap) };
            let len: usize = kani::any_where(|l: &usize| *l <= cmp::min(cap, N));
            for i in 0..len {
                unsafe { ptr::write(deque.ptr().add((head + i) % cap), WithDrop(kani::any())) };
            }
            deque.head = head;
            deque.len = len;
            kani::cover(len > cap - head, "drop glue: wrapped layout");
            DROPS.store(0, Relaxed);
            deque
        }

        /// `truncate` runs the destructor of exactly the removed elements, and `Drop for
        /// VecDeque` those of the remaining ones (`ptr::drop_in_place::<[T]>` on both slices).
        #[kani::proof]
        #[kani::unwind(10)]
        fn bounded_truncate_drop_glue_withdrop() {
            let mut deque = small_deque_with_drop();
            let len = deque.len();
            let new_len: usize = kani::any();
            deque.truncate(new_len);
            let removed = len.saturating_sub(new_len);
            assert_eq!(DROPS.load(Relaxed), removed);
            assert_eq!(deque.len(), len - removed);
            kani::cover(removed > 1 && len > removed, "truncate: several dropped, some remain");
            drop(deque);
            assert_eq!(DROPS.load(Relaxed), len);
        }

        /// `drain` runs the destructor of exactly the drained elements (the ones not pulled out
        /// through `Drain`'s destructor), the rest through `Drop for VecDeque`.
        #[kani::proof]
        #[kani::unwind(10)]
        fn bounded_drain_drop_glue_withdrop() {
            let mut deque = small_deque_with_drop();
            let len = deque.len();
            let (start, end) = any_subrange(len);
            let mut drain = deque.drain(start..end);
            let pulled: bool = kani::any();
            if pulled {
                if let Some(elem) = drain.next() {
                    drop(elem);
                }
            }
            drop(drain);
            assert_eq!(DROPS.load(Relaxed), end - start);
            assert_eq!(deque.len(), len - (end - start));
            kani::cover(
                pulled && end - start > 1 && start > 0 && end < len,
                "drain: one pulled, interior range",
            );
            drop(deque);
            assert_eq!(DROPS.load(Relaxed), len);
        }

        /// `Drop for VecDeque` runs every element's destructor exactly once, for both ring
        /// layouts.
        #[kani::proof]
        #[kani::unwind(10)]
        fn bounded_vecdeque_drop_glue_withdrop() {
            let deque = small_deque_with_drop();
            let len = deque.len();
            let wrapped = len > deque.capacity() - deque.head;
            drop(deque);
            assert_eq!(DROPS.load(Relaxed), len);
            kani::cover(wrapped && len > 1, "Drop for VecDeque: wrapped layout");
        }

        /// `retain_mut` drops exactly the rejected elements (through `truncate`), `Drop for
        /// VecDeque` the kept ones. `retain_mut`'s own loops run under their loop contracts
        /// here as everywhere; the drop glue is what this harness bounds.
        #[kani::proof]
        #[kani::unwind(10)]
        fn bounded_retain_mut_drop_glue_withdrop() {
            let mut deque = small_deque_with_drop();
            let len = deque.len();
            deque.retain_mut(|_| kani::any());
            let kept = deque.len();
            assert_eq!(DROPS.load(Relaxed), len - kept);
            kani::cover(kept > 0 && kept < len, "retain_mut: some dropped, some kept");
            drop(deque);
            assert_eq!(DROPS.load(Relaxed), len);
        }
    }

    #[kani::proof]
    fn check_vecdeque_swap() {
        // The array's length is set to an arbitrary value, which defines its size.
        // In this case, implementing a dynamic array is not possible using any_array
        // The more elements in the array the longer the veification time.
        const ARRAY_LEN: usize = 40;
        let mut arr: [u32; ARRAY_LEN] = kani::Arbitrary::any_array();
        let mut deque: VecDeque<u32> = VecDeque::from(arr);
        let len = deque.len();

        // Generate valid indices within bounds
        let i = kani::any_where(|&x: &usize| x < len);
        let j = kani::any_where(|&x: &usize| x < len);

        // Capture the elements at i and j before the swap
        let elem_i_before = deque[i];
        let elem_j_before = deque[j];

        // Perform the swap
        deque.swap(i, j);

        // Postcondition: Verify elements have swapped places
        assert_eq!(deque[i], elem_j_before);
        assert_eq!(deque[j], elem_i_before);

        // Ensure other elements remain unchanged
        let k = kani::any_where(|&x: &usize| x < len);
        if k != i && k != j {
            assert!(deque[k] == arr[k]);
        }
    }
}
