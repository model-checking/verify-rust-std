use core::iter::{
    FusedIterator, InPlaceIterable, SourceIter, TrustedFused, TrustedLen,
    TrustedRandomAccessNoCoerce,
};
#[cfg(kani)]
use core::kani;
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit, SizedTypeProperties};
use core::num::NonZero;
#[cfg(not(no_global_oom_handling))]
use core::ops::Deref;
use core::panic::UnwindSafe;
use core::ptr::{self, NonNull};
use core::slice::{self};
use core::{array, fmt};

use safety::requires;

#[cfg(not(no_global_oom_handling))]
use super::AsVecIntoIter;
use crate::alloc::{Allocator, Global};
#[cfg(not(no_global_oom_handling))]
use crate::collections::VecDeque;
use crate::raw_vec::RawVec;

macro non_null {
    (mut $place:expr, $t:ident) => {{
        #![allow(unused_unsafe)] // we're sometimes used within an unsafe block
        unsafe { &mut *((&raw mut $place) as *mut NonNull<$t>) }
    }},
    ($place:expr, $t:ident) => {{
        #![allow(unused_unsafe)] // we're sometimes used within an unsafe block
        unsafe { *((&raw const $place) as *const NonNull<$t>) }
    }},
}

/// An iterator that moves out of a vector.
///
/// This `struct` is created by the `into_iter` method on [`Vec`](super::Vec)
/// (provided by the [`IntoIterator`] trait).
///
/// # Example
///
/// ```
/// let v = vec![0, 1, 2];
/// let iter: std::vec::IntoIter<_> = v.into_iter();
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_insignificant_dtor]
pub struct IntoIter<
    T,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    pub(super) buf: NonNull<T>,
    pub(super) phantom: PhantomData<T>,
    pub(super) cap: usize,
    // the drop impl reconstructs a RawVec from buf, cap and alloc
    // to avoid dropping the allocator twice we need to wrap it into ManuallyDrop
    pub(super) alloc: ManuallyDrop<A>,
    pub(super) ptr: NonNull<T>,
    /// If T is a ZST, this is actually ptr+len. This encoding is picked so that
    /// ptr == end is a quick test for the Iterator being empty, that works
    /// for both ZST and non-ZST.
    /// For non-ZSTs the pointer is treated as `NonNull<T>`
    pub(super) end: *const T,
}

// Manually mirroring what `Vec` has,
// because otherwise we get `T: RefUnwindSafe` from `NonNull`.
#[stable(feature = "catch_unwind", since = "1.9.0")]
impl<T: UnwindSafe, A: Allocator + UnwindSafe> UnwindSafe for IntoIter<T, A> {}

#[stable(feature = "vec_intoiter_debug", since = "1.13.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for IntoIter<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
    }
}

impl<T, A: Allocator> IntoIter<T, A> {
    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = vec!['a', 'b', 'c'];
    /// let mut into_iter = vec.into_iter();
    /// assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
    /// let _ = into_iter.next().unwrap();
    /// assert_eq!(into_iter.as_slice(), &['b', 'c']);
    /// ```
    #[stable(feature = "vec_into_iter_as_slice", since = "1.15.0")]
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len()) }
    }

    /// Returns the remaining items of this iterator as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = vec!['a', 'b', 'c'];
    /// let mut into_iter = vec.into_iter();
    /// assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
    /// into_iter.as_mut_slice()[2] = 'z';
    /// assert_eq!(into_iter.next().unwrap(), 'a');
    /// assert_eq!(into_iter.next().unwrap(), 'b');
    /// assert_eq!(into_iter.next().unwrap(), 'z');
    /// ```
    #[stable(feature = "vec_into_iter_as_slice", since = "1.15.0")]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { &mut *self.as_raw_mut_slice() }
    }

    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn allocator(&self) -> &A {
        &self.alloc
    }

    fn as_raw_mut_slice(&mut self) -> *mut [T] {
        ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), self.len())
    }

    /// Drops remaining elements and relinquishes the backing allocation.
    ///
    /// This method guarantees it won't panic before relinquishing the backing
    /// allocation.
    ///
    /// This is roughly equivalent to the following, but more efficient
    ///
    /// ```
    /// # let mut vec = Vec::<u8>::with_capacity(10);
    /// # let ptr = vec.as_mut_ptr();
    /// # let mut into_iter = vec.into_iter();
    /// let mut into_iter = std::mem::replace(&mut into_iter, Vec::new().into_iter());
    /// (&mut into_iter).for_each(drop);
    /// std::mem::forget(into_iter);
    /// # // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// # // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// # drop(unsafe { Vec::<u8>::from_raw_parts(ptr, 0, 10) });
    /// ```
    ///
    /// This method is used by in-place iteration, refer to the vec::in_place_collect
    /// documentation for an overview.
    #[cfg(not(no_global_oom_handling))]
    pub(super) fn forget_allocation_drop_remaining(&mut self) {
        let remaining = self.as_raw_mut_slice();

        // overwrite the individual fields instead of creating a new
        // struct and then overwriting &mut self.
        // this creates less assembly
        self.cap = 0;
        self.buf = RawVec::new().non_null();
        self.ptr = self.buf;
        self.end = self.buf.as_ptr();

        // Dropping the remaining elements can panic, so this needs to be
        // done only after updating the other fields.
        unsafe {
            ptr::drop_in_place(remaining);
        }
    }

    /// Forgets to Drop the remaining elements while still allowing the backing allocation to be freed.
    pub(crate) fn forget_remaining_elements(&mut self) {
        // For the ZST case, it is crucial that we mutate `end` here, not `ptr`.
        // `ptr` must stay aligned, while `end` may be unaligned.
        self.end = self.ptr.as_ptr();
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub(crate) fn into_vecdeque(self) -> VecDeque<T, A> {
        // Keep our `Drop` impl from dropping the elements and the allocator
        let mut this = ManuallyDrop::new(self);

        // SAFETY: This allocation originally came from a `Vec`, so it passes
        // all those checks. We have `this.buf` ≤ `this.ptr` ≤ `this.end`,
        // so the `offset_from_unsigned`s below cannot wrap, and will produce a well-formed
        // range. `end` ≤ `buf + cap`, so the range will be in-bounds.
        // Taking `alloc` is ok because nothing else is going to look at it,
        // since our `Drop` impl isn't going to run so there's no more code.
        unsafe {
            let buf = this.buf.as_ptr();
            let initialized = if T::IS_ZST {
                // All the pointers are the same for ZSTs, so it's fine to
                // say that they're all at the beginning of the "allocation".
                0..this.len()
            } else {
                this.ptr.offset_from_unsigned(this.buf)..this.end.offset_from_unsigned(buf)
            };
            let cap = this.cap;
            let alloc = ManuallyDrop::take(&mut this.alloc);
            VecDeque::from_contiguous_raw_parts_in(buf, initialized, cap, alloc)
        }
    }
}

#[stable(feature = "vec_intoiter_as_ref", since = "1.46.0")]
impl<T, A: Allocator> AsRef<[T]> for IntoIter<T, A> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Send, A: Allocator + Send> Send for IntoIter<T, A> {}
#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync, A: Allocator + Sync> Sync for IntoIter<T, A> {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        let ptr = if T::IS_ZST {
            if self.ptr.as_ptr() == self.end as *mut T {
                return None;
            }
            // `ptr` has to stay where it is to remain aligned, so we reduce the length by 1 by
            // reducing the `end`.
            self.end = self.end.wrapping_byte_sub(1);
            self.ptr
        } else {
            if self.ptr == non_null!(self.end, T) {
                return None;
            }
            let old = self.ptr;
            self.ptr = unsafe { old.add(1) };
            old
        };
        Some(unsafe { ptr.read() })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = if T::IS_ZST {
            self.end.addr().wrapping_sub(self.ptr.as_ptr().addr())
        } else {
            unsafe { non_null!(self.end, T).offset_from_unsigned(self.ptr) }
        };
        (exact, Some(exact))
    }

    #[inline]
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let step_size = self.len().min(n);
        let to_drop = ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), step_size);
        if T::IS_ZST {
            // See `next` for why we sub `end` here.
            self.end = self.end.wrapping_byte_sub(step_size);
        } else {
            // SAFETY: the min() above ensures that step_size is in bounds
            self.ptr = unsafe { self.ptr.add(step_size) };
        }
        // SAFETY: the min() above ensures that step_size is in bounds
        unsafe {
            ptr::drop_in_place(to_drop);
        }
        NonZero::new(n - step_size).map_or(Ok(()), Err)
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn last(mut self) -> Option<T> {
        self.next_back()
    }

    #[inline]
    fn next_chunk<const N: usize>(&mut self) -> Result<[T; N], core::array::IntoIter<T, N>> {
        let mut raw_ary = [const { MaybeUninit::uninit() }; N];

        let len = self.len();

        if T::IS_ZST {
            if len < N {
                self.forget_remaining_elements();
                // Safety: ZSTs can be conjured ex nihilo, only the amount has to be correct
                return Err(unsafe { array::IntoIter::new_unchecked(raw_ary, 0..len) });
            }

            self.end = self.end.wrapping_byte_sub(N);
            // Safety: ditto
            return Ok(unsafe { raw_ary.transpose().assume_init() });
        }

        if len < N {
            // Safety: `len` indicates that this many elements are available and we just checked that
            // it fits into the array.
            unsafe {
                ptr::copy_nonoverlapping(self.ptr.as_ptr(), raw_ary.as_mut_ptr() as *mut T, len);
                self.forget_remaining_elements();
                return Err(array::IntoIter::new_unchecked(raw_ary, 0..len));
            }
        }

        // Safety: `len` is larger than the array size. Copy a fixed amount here to fully initialize
        // the array.
        unsafe {
            ptr::copy_nonoverlapping(self.ptr.as_ptr(), raw_ary.as_mut_ptr() as *mut T, N);
            self.ptr = self.ptr.add(N);
            Ok(raw_ary.transpose().assume_init())
        }
    }

    fn fold<B, F>(mut self, mut accum: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        if T::IS_ZST {
            while self.ptr.as_ptr() != self.end.cast_mut() {
                // SAFETY: we just checked that `self.ptr` is in bounds.
                let tmp = unsafe { self.ptr.read() };
                // See `next` for why we subtract from `end` here.
                self.end = self.end.wrapping_byte_sub(1);
                accum = f(accum, tmp);
            }
        } else {
            // SAFETY: `self.end` can only be null if `T` is a ZST.
            while self.ptr != non_null!(self.end, T) {
                // SAFETY: we just checked that `self.ptr` is in bounds.
                let tmp = unsafe { self.ptr.read() };
                // SAFETY: the maximum this can be is `self.end`.
                // Increment `self.ptr` first to avoid double dropping in the event of a panic.
                self.ptr = unsafe { self.ptr.add(1) };
                accum = f(accum, tmp);
            }
        }
        accum
    }

    fn try_fold<B, F, R>(&mut self, mut accum: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: core::ops::Try<Output = B>,
    {
        if T::IS_ZST {
            while self.ptr.as_ptr() != self.end.cast_mut() {
                // SAFETY: we just checked that `self.ptr` is in bounds.
                let tmp = unsafe { self.ptr.read() };
                // See `next` for why we subtract from `end` here.
                self.end = self.end.wrapping_byte_sub(1);
                accum = f(accum, tmp)?;
            }
        } else {
            // SAFETY: `self.end` can only be null if `T` is a ZST.
            while self.ptr != non_null!(self.end, T) {
                // SAFETY: we just checked that `self.ptr` is in bounds.
                let tmp = unsafe { self.ptr.read() };
                // SAFETY: the maximum this can be is `self.end`.
                // Increment `self.ptr` first to avoid double dropping in the event of a panic.
                self.ptr = unsafe { self.ptr.add(1) };
                accum = f(accum, tmp)?;
            }
        }
        R::from_output(accum)
    }

    #[requires(i < self.len())]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn __iterator_get_unchecked(&mut self, i: usize) -> Self::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: the caller must guarantee that `i` is in bounds of the
        // `Vec<T>`, so `i` cannot overflow an `isize`, and the `self.ptr.add(i)`
        // is guaranteed to pointer to an element of the `Vec<T>` and
        // thus guaranteed to be valid to dereference.
        //
        // Also note the implementation of `Self: TrustedRandomAccess` requires
        // that `T: Copy` so reading elements from the buffer doesn't invalidate
        // them for `Drop`.
        unsafe { self.ptr.add(i).read() }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> DoubleEndedIterator for IntoIter<T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if T::IS_ZST {
            if self.ptr.as_ptr() == self.end as *mut _ {
                return None;
            }
            // See above for why 'ptr.offset' isn't used
            self.end = self.end.wrapping_byte_sub(1);
            // Note that even though this is next_back() we're reading from `self.ptr`, not
            // `self.end`. We track our length using the byte offset from `self.ptr` to `self.end`,
            // so the end pointer may not be suitably aligned for T.
            Some(unsafe { ptr::read(self.ptr.as_ptr()) })
        } else {
            if self.ptr == non_null!(self.end, T) {
                return None;
            }
            unsafe {
                self.end = self.end.sub(1);
                Some(ptr::read(self.end))
            }
        }
    }

    #[inline]
    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let step_size = self.len().min(n);
        if T::IS_ZST {
            // SAFETY: same as for advance_by()
            self.end = self.end.wrapping_byte_sub(step_size);
        } else {
            // SAFETY: same as for advance_by()
            self.end = unsafe { self.end.sub(step_size) };
        }
        let to_drop = if T::IS_ZST {
            // ZST may cause unalignment
            ptr::slice_from_raw_parts_mut(ptr::NonNull::<T>::dangling().as_ptr(), step_size)
        } else {
            ptr::slice_from_raw_parts_mut(self.end as *mut T, step_size)
        };
        // SAFETY: same as for advance_by()
        unsafe {
            ptr::drop_in_place(to_drop);
        }
        NonZero::new(n - step_size).map_or(Ok(()), Err)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> ExactSizeIterator for IntoIter<T, A> {
    fn is_empty(&self) -> bool {
        if T::IS_ZST {
            self.ptr.as_ptr() == self.end as *mut _
        } else {
            self.ptr == non_null!(self.end, T)
        }
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T, A: Allocator> FusedIterator for IntoIter<T, A> {}

#[doc(hidden)]
#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<T, A: Allocator> TrustedFused for IntoIter<T, A> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T, A: Allocator> TrustedLen for IntoIter<T, A> {}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<T, A> Default for IntoIter<T, A>
where
    A: Allocator + Default,
{
    /// Creates an empty `vec::IntoIter`.
    ///
    /// ```
    /// # use std::vec;
    /// let iter: vec::IntoIter<u8> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// assert_eq!(iter.as_slice(), &[]);
    /// ```
    fn default() -> Self {
        super::Vec::new_in(Default::default()).into_iter()
    }
}

#[doc(hidden)]
#[unstable(issue = "none", feature = "std_internals")]
#[rustc_unsafe_specialization_marker]
pub trait NonDrop {}

// T: Copy as approximation for !Drop since get_unchecked does not advance self.ptr
// and thus we can't implement drop-handling
#[unstable(issue = "none", feature = "std_internals")]
impl<T: Copy> NonDrop for T {}

#[doc(hidden)]
#[unstable(issue = "none", feature = "std_internals")]
// TrustedRandomAccess (without NoCoerce) must not be implemented because
// subtypes/supertypes of `T` might not be `NonDrop`
unsafe impl<T, A: Allocator> TrustedRandomAccessNoCoerce for IntoIter<T, A>
where
    T: NonDrop,
{
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "vec_into_iter_clone", since = "1.8.0")]
impl<T: Clone, A: Allocator + Clone> Clone for IntoIter<T, A> {
    fn clone(&self) -> Self {
        self.as_slice().to_vec_in(self.alloc.deref().clone()).into_iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<#[may_dangle] T, A: Allocator> Drop for IntoIter<T, A> {
    fn drop(&mut self) {
        struct DropGuard<'a, T, A: Allocator>(&'a mut IntoIter<T, A>);

        impl<T, A: Allocator> Drop for DropGuard<'_, T, A> {
            fn drop(&mut self) {
                unsafe {
                    // `IntoIter::alloc` is not used anymore after this and will be dropped by RawVec
                    let alloc = ManuallyDrop::take(&mut self.0.alloc);
                    // RawVec handles deallocation
                    let _ = RawVec::from_nonnull_in(self.0.buf, self.0.cap, alloc);
                }
            }
        }

        let guard = DropGuard(self);
        // destroy the remaining elements
        unsafe {
            ptr::drop_in_place(guard.0.as_raw_mut_slice());
        }
        // now `guard` will be dropped and do the rest
    }
}

// In addition to the SAFETY invariants of the following three unsafe traits
// also refer to the vec::in_place_collect module documentation to get an overview
#[unstable(issue = "none", feature = "inplace_iteration")]
#[doc(hidden)]
unsafe impl<T, A: Allocator> InPlaceIterable for IntoIter<T, A> {
    const EXPAND_BY: Option<NonZero<usize>> = NonZero::new(1);
    const MERGE_BY: Option<NonZero<usize>> = NonZero::new(1);
}

#[unstable(issue = "none", feature = "inplace_iteration")]
#[doc(hidden)]
unsafe impl<T, A: Allocator> SourceIter for IntoIter<T, A> {
    type Source = Self;

    #[inline]
    unsafe fn as_inner(&mut self) -> &mut Self::Source {
        self
    }
}

#[cfg(not(no_global_oom_handling))]
unsafe impl<T> AsVecIntoIter for IntoIter<T> {
    type Item = T;

    fn as_into_iter(&mut self) -> &mut IntoIter<Self::Item> {
        self
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::super::Vec;
    use super::super::kani_vec_harness_helpers::*;
    use super::*;

    // Harnesses for IntoIter::as_slice()
    macro_rules! gen_into_iter_as_slice_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let expected_len = iter.len();
                let expected_ptr = iter.ptr.as_ptr();
                let slice = iter.as_slice();
                assert!(
                    slice.len() == expected_len,
                    "as_slice: returned length differs from IntoIter remaining length"
                );
                assert!(
                    slice.as_ptr() == expected_ptr,
                    "as_slice: returned slice starts at the wrong pointer"
                );
                kani::cover(expected_len == 0, "as_slice: empty remaining range");
                kani::cover(expected_len > 0, "as_slice: non-empty remaining range");
            }
        };
    }

    gen_into_iter_as_slice_harness!(harness_into_iter_as_slice_u8, u8);
    gen_into_iter_as_slice_harness!(harness_into_iter_as_slice_u64, u64);
    gen_into_iter_as_slice_harness!(harness_into_iter_as_slice_unit, ());
    gen_into_iter_as_slice_harness!(harness_into_iter_as_slice_array, [u8; 4]);
    gen_into_iter_as_slice_harness!(harness_into_iter_as_slice_bool, bool);
    gen_into_iter_as_slice_harness!(harness_into_iter_as_slice_al16, Al16);

    // Harnesses for IntoIter::as_mut_slice()
    macro_rules! gen_into_iter_as_mut_slice_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let expected_len = iter.len();
                let expected_ptr = iter.ptr.as_ptr();
                let slice = iter.as_mut_slice();
                assert!(
                    slice.len() == expected_len,
                    "as_mut_slice: returned length differs from IntoIter remaining length"
                );
                assert!(
                    slice.as_mut_ptr() == expected_ptr,
                    "as_mut_slice: returned slice starts at the wrong pointer"
                );
                kani::cover(expected_len == 0, "as_mut_slice: empty remaining range");
                kani::cover(expected_len > 0, "as_mut_slice: non-empty remaining range");
            }
        };
    }

    gen_into_iter_as_mut_slice_harness!(harness_into_iter_as_mut_slice_u8, u8);
    gen_into_iter_as_mut_slice_harness!(harness_into_iter_as_mut_slice_u64, u64);
    gen_into_iter_as_mut_slice_harness!(harness_into_iter_as_mut_slice_unit, ());
    gen_into_iter_as_mut_slice_harness!(harness_into_iter_as_mut_slice_array, [u8; 4]);
    gen_into_iter_as_mut_slice_harness!(harness_into_iter_as_mut_slice_bool, bool);
    gen_into_iter_as_mut_slice_harness!(harness_into_iter_as_mut_slice_al16, Al16);

    // Harnesses for IntoIter::forget_allocation_drop_remaining()
    macro_rules! gen_into_iter_forget_allocation_drop_remaining_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                iter.forget_allocation_drop_remaining();
                assert!(
                    iter.len() == 0,
                    "forget_allocation_drop_remaining: iterator is not empty afterwards"
                );
                assert!(
                    iter.cap == 0,
                    "forget_allocation_drop_remaining: capacity was not cleared"
                );
                assert!(
                    iter.ptr == iter.buf,
                    "forget_allocation_drop_remaining: ptr does not equal reset buffer"
                );
                assert!(
                    iter.end == iter.ptr.as_ptr(),
                    "forget_allocation_drop_remaining: end does not equal reset ptr"
                );
                kani::cover(before_len == 0, "forget_allocation_drop_remaining: empty input");
                kani::cover(before_len > 0, "forget_allocation_drop_remaining: non-empty input");
            }
        };
    }

    gen_into_iter_forget_allocation_drop_remaining_harness!(
        harness_into_iter_forget_allocation_drop_remaining_u8,
        u8
    );
    gen_into_iter_forget_allocation_drop_remaining_harness!(
        harness_into_iter_forget_allocation_drop_remaining_u64,
        u64
    );
    gen_into_iter_forget_allocation_drop_remaining_harness!(
        harness_into_iter_forget_allocation_drop_remaining_unit,
        ()
    );
    gen_into_iter_forget_allocation_drop_remaining_harness!(
        harness_into_iter_forget_allocation_drop_remaining_array,
        [u8; 4]
    );
    gen_into_iter_forget_allocation_drop_remaining_harness!(
        harness_into_iter_forget_allocation_drop_remaining_bool,
        bool
    );

    // Harnesses for IntoIter::into_vecdeque()
    macro_rules! gen_into_iter_into_vecdeque_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let expected_len = iter.len();
                let deque = iter.into_vecdeque();
                assert!(
                    deque.len() == expected_len,
                    "into_vecdeque: resulting VecDeque has the wrong length"
                );
                kani::cover(expected_len == 0, "into_vecdeque: empty remaining range");
                kani::cover(expected_len > 0, "into_vecdeque: non-empty remaining range");
            }
        };
    }

    gen_into_iter_into_vecdeque_harness!(harness_into_iter_into_vecdeque_u8, u8);
    gen_into_iter_into_vecdeque_harness!(harness_into_iter_into_vecdeque_u64, u64);
    gen_into_iter_into_vecdeque_harness!(harness_into_iter_into_vecdeque_unit, ());
    gen_into_iter_into_vecdeque_harness!(harness_into_iter_into_vecdeque_array, [u8; 4]);
    gen_into_iter_into_vecdeque_harness!(harness_into_iter_into_vecdeque_bool, bool);

    // Harnesses for IntoIter::next()
    macro_rules! gen_into_iter_next_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                let result = iter.next();
                assert!(
                    result.is_some() == (before_len > 0),
                    "next: Option result does not match whether the iterator was empty"
                );
                assert!(
                    iter.len() == before_len.saturating_sub(1),
                    "next: remaining length is incorrect"
                );
                kani::cover(before_len == 0, "next: empty iterator returns None");
                kani::cover(before_len == 1, "next: consumes the final element");
                kani::cover(before_len > 1, "next: elements remain afterwards");
            }
        };
    }

    gen_into_iter_next_harness!(harness_into_iter_next_u8, u8);
    gen_into_iter_next_harness!(harness_into_iter_next_u64, u64);
    gen_into_iter_next_harness!(harness_into_iter_next_unit, ());
    gen_into_iter_next_harness!(harness_into_iter_next_array, [u8; 4]);
    gen_into_iter_next_harness!(harness_into_iter_next_bool, bool);
    gen_into_iter_next_harness!(harness_into_iter_next_al16, Al16);

    // Harnesses for IntoIter::size_hint()
    macro_rules! gen_into_iter_size_hint_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let expected_len = iter.len();
                let (lower, upper) = iter.size_hint();
                assert!(
                    lower == expected_len,
                    "size_hint: lower bound is not the exact remaining length"
                );
                assert!(
                    upper == Some(expected_len),
                    "size_hint: upper bound is not the exact remaining length"
                );
                assert!(
                    iter.len() == expected_len,
                    "size_hint: querying size_hint modified the iterator"
                );
                kani::cover(expected_len == 0, "size_hint: empty iterator");
                kani::cover(expected_len > 0, "size_hint: non-empty iterator");
            }
        };
    }

    gen_into_iter_size_hint_harness!(harness_into_iter_size_hint_u8, u8);
    gen_into_iter_size_hint_harness!(harness_into_iter_size_hint_u64, u64);
    gen_into_iter_size_hint_harness!(harness_into_iter_size_hint_unit, ());
    gen_into_iter_size_hint_harness!(harness_into_iter_size_hint_array, [u8; 4]);
    gen_into_iter_size_hint_harness!(harness_into_iter_size_hint_bool, bool);

    // Harnesses for IntoIter::advance_by()
    macro_rules! gen_into_iter_advance_by_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                let n: usize = kani::any();
                let expected_step = before_len.min(n);
                let expected_len = before_len - expected_step;
                let result = iter.advance_by(n);
                assert!(iter.len() == expected_len, "advance_by: remaining length is incorrect");
                match result {
                    Ok(()) => {
                        assert!(
                            n <= before_len,
                            "advance_by: returned Ok even though n exceeded the remaining length"
                        );
                    }
                    Err(remaining) => {
                        assert!(
                            n > before_len,
                            "advance_by: returned Err even though n fit in the remaining length"
                        );
                        assert!(
                            remaining.get() == n - before_len,
                            "advance_by: Err contains the wrong unadvanced count"
                        );
                    }
                }
                kani::cover(n == 0, "advance_by: zero requested");
                kani::cover(before_len > 0 && n < before_len, "advance_by: partial advance");
                kani::cover(before_len > 0 && n == before_len, "advance_by: exact exhaustion");
                kani::cover(n > before_len, "advance_by: request exceeds remaining length");
            }
        };
    }

    gen_into_iter_advance_by_harness!(harness_into_iter_advance_by_u8, u8);
    gen_into_iter_advance_by_harness!(harness_into_iter_advance_by_u64, u64);
    gen_into_iter_advance_by_harness!(harness_into_iter_advance_by_unit, ());
    gen_into_iter_advance_by_harness!(harness_into_iter_advance_by_array, [u8; 4]);
    gen_into_iter_advance_by_harness!(harness_into_iter_advance_by_bool, bool);

    // Harnesses for IntoIter::next_chunk()
    macro_rules! gen_into_iter_next_chunk_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                const N: usize = 4;
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                let result = iter.next_chunk::<N>();
                match result {
                    Ok(chunk) => {
                        assert!(
                            before_len >= N,
                            "next_chunk: returned Ok with fewer than N elements"
                        );
                        assert!(
                            chunk.len() == N,
                            "next_chunk: successful chunk has incorrect length"
                        );
                        assert!(
                            iter.len() == before_len - N,
                            "next_chunk: remaining length is incorrect after Ok"
                        );
                    }
                    Err(remainder) => {
                        assert!(
                            before_len < N,
                            "next_chunk: returned Err with at least N elements available"
                        );
                        assert!(
                            remainder.len() == before_len,
                            "next_chunk: Err iterator has incorrect length"
                        );
                        assert!(
                            iter.len() == 0,
                            "next_chunk: source iterator was not exhausted after Err"
                        );
                    }
                }
                kani::cover(before_len == 0, "next_chunk: empty iterator");
                kani::cover(before_len > 0 && before_len < N, "next_chunk: short iterator");
                kani::cover(before_len == N, "next_chunk: exact chunk");
                kani::cover(before_len > N, "next_chunk: elements remain");
            }
        };
    }

    gen_into_iter_next_chunk_harness!(harness_into_iter_next_chunk_u8, u8);
    gen_into_iter_next_chunk_harness!(harness_into_iter_next_chunk_u64, u64);
    gen_into_iter_next_chunk_harness!(harness_into_iter_next_chunk_unit, ());
    gen_into_iter_next_chunk_harness!(harness_into_iter_next_chunk_array, [u8; 4]);
    gen_into_iter_next_chunk_harness!(harness_into_iter_next_chunk_bool, bool);
    gen_into_iter_next_chunk_harness!(harness_into_iter_next_chunk_al16, Al16);

    // Harnesses for IntoIter::fold() non-ZST case
    #[kani::proof]
    #[kani::unwind(72)]
    pub fn harness_into_iter_fold_u8() {
        let backing: [u8; 64] = kani::any();
        // Symbolic prefix length: 0..=64.
        let vec = kani::slice::any_slice_of_array(&backing).to_vec();
        let mut iter = vec.into_iter();
        // Also cover arbitrary reachable front/back iterator states.
        position_into_iter(&mut iter);
        let before_len = iter.len();
        // Count exactly how many elements fold feeds to the closure.
        let count = iter.fold(0usize, |count, _item| count + 1);
        assert!(
            count == before_len,
            "fold: closure was not called exactly once per remaining element"
        );
        kani::cover(before_len == 0, "fold: empty iterator");
        kani::cover(before_len == 1, "fold: one remaining element");
        kani::cover(before_len > 1, "fold: multiple remaining elements");
        kani::cover(before_len == 64, "fold: maximum bounded length");
    }

    // Harnesses for IntoIter::fold() ZST case
    #[kani::proof]
    #[kani::unwind(72)]
    pub fn harness_into_iter_fold_unit() {
        let backing = [(); 64];
        let vec = kani::slice::any_slice_of_array(&backing).to_vec();
        let mut iter = vec.into_iter();
        position_into_iter(&mut iter);

        let before_len = iter.len();
        let count = iter.fold(0usize, |count, _item| count + 1);

        assert!(
            count == before_len,
            "fold ZST: closure was not called exactly once per remaining element"
        );

        kani::cover(before_len == 0, "fold ZST: empty iterator");
        kani::cover(before_len == 1, "fold ZST: one remaining element");
        kani::cover(before_len > 1, "fold ZST: multiple remaining elements");
        kani::cover(before_len == 64, "fold ZST: maximum bounded length");
    }

    // Harnesses for IntoIter::try_fold() non-ZST case
    #[kani::proof]
    #[kani::unwind(72)]
    pub fn harness_into_iter_try_fold_u8() {
        let backing: [u8; 64] = kani::any();
        let vec = kani::slice::any_slice_of_array(&backing).to_vec();
        let mut iter = vec.into_iter();
        position_into_iter(&mut iter);
        let before_len = iter.len();
        let result: Result<usize, usize> = iter.try_fold(0usize, |processed, _item| {
            let processed = processed + 1;
            if kani::any::<bool>() { Err(processed) } else { Ok(processed) }
        });
        let after_len = iter.len();
        assert!(after_len <= before_len, "try_fold: remaining length increased");
        match result {
            Ok(processed) => {
                assert!(
                    processed == before_len,
                    "try_fold: Ok did not process every remaining element"
                );
                assert!(after_len == 0, "try_fold: Ok did not exhaust the iterator");
            }
            Err(processed) => {
                assert!(processed > 0, "try_fold: Err occurred without processing an element");
                assert!(
                    processed <= before_len,
                    "try_fold: processed more elements than were available"
                );
                assert!(
                    after_len == before_len - processed,
                    "try_fold: iterator state does not match consumed elements"
                );
            }
        }
        kani::cover(before_len == 0, "try_fold: empty iterator");
        kani::cover(before_len > 0 && result.is_ok(), "try_fold: successful traversal");
        kani::cover(before_len > 0 && result.is_err(), "try_fold: early termination");
        kani::cover(
            matches!(result, Err(processed) if processed == 1),
            "try_fold: failure on first element",
        );
        kani::cover(
            matches!(result, Err(processed) if processed > 1),
            "try_fold: failure after multiple elements",
        );
    }

    // Harnesses for IntoIter::try_fold() ZST case
    #[kani::proof]
    #[kani::unwind(72)]
    pub fn harness_into_iter_try_fold_unit() {
        let backing = [(); 64];
        let vec = kani::slice::any_slice_of_array(&backing).to_vec();
        let mut iter = vec.into_iter();
        position_into_iter(&mut iter);
        let before_len = iter.len();
        let result: Result<usize, usize> = iter.try_fold(0usize, |processed, _item| {
            let processed = processed + 1;
            if kani::any::<bool>() { Err(processed) } else { Ok(processed) }
        });
        let after_len = iter.len();
        assert!(after_len <= before_len, "try_fold ZST: remaining length increased");
        match result {
            Ok(processed) => {
                assert!(
                    processed == before_len,
                    "try_fold ZST: Ok did not process every remaining element"
                );
                assert!(after_len == 0, "try_fold ZST: Ok did not exhaust the iterator");
            }
            Err(processed) => {
                assert!(processed > 0, "try_fold ZST: Err occurred without processing an element");
                assert!(
                    processed <= before_len,
                    "try_fold ZST: processed more elements than were available"
                );
                assert!(
                    after_len == before_len - processed,
                    "try_fold ZST: iterator state does not match consumed elements"
                );
            }
        }
        kani::cover(before_len == 0, "try_fold ZST: empty iterator");
        kani::cover(before_len > 0 && result.is_ok(), "try_fold ZST: successful traversal");
        kani::cover(before_len > 0 && result.is_err(), "try_fold ZST: early termination");
        kani::cover(
            matches!(result, Err(processed) if processed == 1),
            "try_fold ZST: failure on first element",
        );
        kani::cover(
            matches!(result, Err(processed) if processed > 1),
            "try_fold ZST: failure after multiple elements",
        );
    }

    // Harnesses for IntoIter::__iterator_get_unchecked()
    macro_rules! gen_into_iter_iterator_get_unchecked_harness {
        ($name:ident, $ty:ty) => {
            // `__iterator_get_unchecked` is defined on the generic
            // `Iterator for IntoIter<T, A>` implementation.
            //
            // Kani cannot currently resolve this concrete generic-self
            // instantiation as a `proof_for_contract` target, so this harness
            // verifies the real implementation directly and mirrors its
            // `#[requires(i < self.len())]` precondition with `kani::assume`.
            //
            // TODO: switch to `proof_for_contract` once Kani's generic-self
            // trait-method contract resolution supports this target.
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                let before_ptr = iter.ptr;
                let before_end = iter.end;
                let i: usize = kani::any();
                // Demonstrate that the contract precondition is satisfiable before
                // restricting verification to calls permitted by the contract.
                kani::cover(
                    before_len > 0 && i < before_len,
                    "__iterator_get_unchecked: contract precondition is reachable",
                );
                // Mirrors the method contract:
                // `#[requires(i < self.len())]`.
                kani::assume(i < before_len);
                let expected = iter.as_slice()[i];
                let result = unsafe { iter.__iterator_get_unchecked(i) };
                assert!(result == expected, "__iterator_get_unchecked: returned the wrong element");
                assert!(
                    iter.len() == before_len,
                    "__iterator_get_unchecked: changed the remaining length"
                );
                assert!(
                    iter.ptr == before_ptr,
                    "__iterator_get_unchecked: changed the front pointer"
                );
                assert!(
                    iter.end == before_end,
                    "__iterator_get_unchecked: changed the end pointer"
                );
                kani::cover(i == 0, "__iterator_get_unchecked: first element");
                kani::cover(i == before_len - 1, "__iterator_get_unchecked: last valid element");
                kani::cover(
                    before_len > 2 && i > 0 && i < before_len - 1,
                    "__iterator_get_unchecked: interior element",
                );
            }
        };
    }

    gen_into_iter_iterator_get_unchecked_harness!(harness_into_iter_iterator_get_unchecked_u8, u8);
    gen_into_iter_iterator_get_unchecked_harness!(
        harness_into_iter_iterator_get_unchecked_u64,
        u64
    );
    gen_into_iter_iterator_get_unchecked_harness!(
        harness_into_iter_iterator_get_unchecked_unit,
        ()
    );
    gen_into_iter_iterator_get_unchecked_harness!(
        harness_into_iter_iterator_get_unchecked_array,
        [u8; 4]
    );
    gen_into_iter_iterator_get_unchecked_harness!(
        harness_into_iter_iterator_get_unchecked_bool,
        bool
    );

    // Harnesses for IntoIter::next_back()
    macro_rules! gen_into_iter_next_back_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                let before_ptr = iter.ptr;
                let result = iter.next_back();
                assert!(
                    result.is_some() == (before_len > 0),
                    "next_back: Option result does not match whether the iterator was empty"
                );
                assert!(
                    iter.len() == before_len.saturating_sub(1),
                    "next_back: remaining length is incorrect"
                );
                assert!(iter.ptr == before_ptr, "next_back: changed the front pointer");
                kani::cover(before_len == 0, "next_back: empty iterator returns None");
                kani::cover(before_len == 1, "next_back: consumes the final element");
                kani::cover(before_len > 1, "next_back: elements remain afterwards");
            }
        };
    }

    gen_into_iter_next_back_harness!(harness_into_iter_next_back_u8, u8);
    gen_into_iter_next_back_harness!(harness_into_iter_next_back_u64, u64);
    gen_into_iter_next_back_harness!(harness_into_iter_next_back_unit, ());
    gen_into_iter_next_back_harness!(harness_into_iter_next_back_array, [u8; 4]);
    gen_into_iter_next_back_harness!(harness_into_iter_next_back_bool, bool);
    gen_into_iter_next_back_harness!(harness_into_iter_next_back_al16, Al16);

    // Harnesses for IntoIter::advance_back_by()
    macro_rules! gen_into_iter_advance_back_by_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                let before_ptr = iter.ptr;
                let n: usize = kani::any();
                let expected_step = before_len.min(n);
                let expected_len = before_len - expected_step;
                let result = iter.advance_back_by(n);
                assert!(
                    iter.len() == expected_len,
                    "advance_back_by: remaining length is incorrect"
                );
                assert!(
                    iter.ptr == before_ptr,
                    "advance_back_by: changed the front pointer"
                );
                match result {
                    Ok(()) => {
                        assert!(
                            n <= before_len,
                            "advance_back_by: returned Ok even though n exceeded the remaining length"
                        );
                    }
                    Err(remaining) => {
                        assert!(
                            n > before_len,
                            "advance_back_by: returned Err even though n fit in the remaining length"
                        );
                        assert!(
                            remaining.get() == n - before_len,
                            "advance_back_by: Err contains the wrong unadvanced count"
                        );
                    }
                }
                kani::cover(n == 0, "advance_back_by: zero requested");
                kani::cover(before_len > 0 && n < before_len, "advance_back_by: partial advance");
                kani::cover(before_len > 0 && n == before_len, "advance_back_by: exact exhaustion");
                kani::cover(n > before_len, "advance_back_by: request exceeds remaining length");
            }
        };
    }

    gen_into_iter_advance_back_by_harness!(harness_into_iter_advance_back_by_u8, u8);
    gen_into_iter_advance_back_by_harness!(harness_into_iter_advance_back_by_u64, u64);
    gen_into_iter_advance_back_by_harness!(harness_into_iter_advance_back_by_unit, ());
    gen_into_iter_advance_back_by_harness!(harness_into_iter_advance_back_by_array, [u8; 4]);
    gen_into_iter_advance_back_by_harness!(harness_into_iter_advance_back_by_bool, bool);
    gen_into_iter_advance_back_by_harness!(harness_into_iter_advance_back_by_al16, Al16);

    // Harnesses for IntoIter::drop()
    macro_rules! gen_into_iter_drop_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let before_len = iter.len();
                kani::cover(before_len == 0, "drop: empty iterator");
                kani::cover(before_len > 0, "drop: non-empty iterator");
                drop(iter);
            }
        };
    }

    gen_into_iter_drop_harness!(harness_into_iter_drop_u8, u8);
    gen_into_iter_drop_harness!(harness_into_iter_drop_u64, u64);
    gen_into_iter_drop_harness!(harness_into_iter_drop_unit, ());
    gen_into_iter_drop_harness!(harness_into_iter_drop_array, [u8; 4]);
    gen_into_iter_drop_harness!(harness_into_iter_drop_bool, bool);
    gen_into_iter_drop_harness!(harness_into_iter_drop_al16, Al16);

    mod bounded_evidence {
        //! Supplementary bounded evidence for `needs_drop` behavior.
        //!
        //! The primary `IntoIter::drop` harnesses remain unbounded. Dropping an
        //! `IntoIter<WithDrop>` eventually executes compiler-generated slice drop
        //! glue, which has no source-level loop where a Kani loop contract can be
        //! attached. This module therefore uses bounded unwinding only for that
        //! drop-glue path.
        use super::*;

        fn bounded_with_drop_into_iter() -> IntoIter<WithDrop> {
            let mut vec = verifier_nondet_vec::<WithDrop>();
            // Bound only the compiler-generated slice drop loop.
            let len = kani::any_where(|len: &usize| *len <= 8 && *len <= vec.len());
            vec.len = len;
            vec.into_iter()
        }

        #[kani::proof]
        #[kani::unwind(12)]
        fn bounded_into_iter_drop_with_drop() {
            let iter = bounded_with_drop_into_iter();
            let len = iter.len();
            kani::cover(len == 0, "IntoIter::drop WithDrop: empty iterator");
            kani::cover(len > 0, "IntoIter::drop WithDrop: non-empty iterator");
            kani::cover(len == 8, "IntoIter::drop WithDrop: maximum bounded length");
            drop(iter);
        }
    }
}
