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
mod verify {
    use super::*;
    use crate::vec::Vec;

    // Symbolic-length Vec of u8 (length 0..=N). The backing size (64 for the
    // iterator harnesses) bounds the length; loops below run a symbolic number
    // of iterations up to that bound. Larger backings add solver time without
    // covering new branches. (`kani::vec` is not exposed under verify-std, so
    // the Vec is built via `kani::slice`.)
    fn any_u8_vec<const N: usize>() -> Vec<u8> {
        let arr: [u8; N] = kani::any();
        kani::slice::any_slice_of_array(&arr).to_vec()
    }

    // A Drop-carrying element so drop harnesses exercise real drop glue.
    // Fixed at 4 elements: drop obligations are per-element identical, so a
    // larger vector adds solver time without new proof obligations.
    struct DropToken(u8);
    impl Drop for DropToken {
        fn drop(&mut self) {
            let _ = self.0;
        }
    }

    // fold: verifies the REAL non-ZST body (the `while self.ptr != end`
    // concrete-pointer loop) — no cfg(kani) body substitution. The counting
    // accumulator asserts fold visits exactly `len` elements.
    #[kani::proof]
    #[kani::unwind(72)]
    fn check_into_iter_fold_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        kani::cover(n > 1, "non-vacuity: a multi-element fold is reachable");
        let count = v.into_iter().fold(0usize, |acc, _| acc + 1);
        assert!(count == n);
    }

    // try_fold: REAL body; a symbolic early-exit exercises the `?` short-circuit
    // and the drop of the remaining elements. Postconditions: Ok consumed all;
    // Err consumed at least one.
    #[kani::proof]
    #[kani::unwind(72)]
    fn check_into_iter_try_fold_u8() {
        let mut it = any_u8_vec::<64>().into_iter();
        let n = it.len();
        kani::cover(n > 1, "non-vacuity: a multi-element try_fold is reachable");
        let r: Result<u32, ()> =
            it.try_fold(
                0u32,
                |acc, x| {
                    if kani::any() { Err(()) } else { Ok(acc.wrapping_add(x as u32)) }
                },
            );
        if r.is_ok() {
            assert!(it.len() == 0);
        } else {
            assert!(it.len() < n);
        }
    }

    // try_fold with drop glue: the early exit leaves unconsumed elements whose
    // drop runs via IntoIter's Drop (drop_in_place over the remaining tail) —
    // the double-drop-on-early-exit class the `ptr.add(1)`-before-`f` ordering
    // in the body exists to prevent.
    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_try_fold_droptoken() {
        let mut it = vec![
            DropToken(kani::any()),
            DropToken(kani::any()),
            DropToken(kani::any()),
            DropToken(kani::any()),
        ]
        .into_iter();
        let n = it.len();
        kani::cover(n > 1, "non-vacuity: a multi-element early-exit is reachable");
        let r: Result<u32, ()> =
            it.try_fold(
                0u32,
                |acc, t| {
                    if kani::any() { Err(()) } else { Ok(acc.wrapping_add(t.0 as u32)) }
                },
            );
        if r.is_ok() {
            assert!(it.len() == 0);
        } else {
            assert!(it.len() < n);
        }
        // `it` drops here with its remaining tokens.
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_next_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let first = if n > 0 { Some(v[0]) } else { None };
        let mut it = v.into_iter();
        let r = it.next();
        assert!(r == first);
        assert!(it.len() == n - (r.is_some() as usize));
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_next_back_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let last = if n > 0 { Some(v[n - 1]) } else { None };
        let mut it = v.into_iter();
        let r = it.next_back();
        assert!(r == last);
        assert!(it.len() == n - (r.is_some() as usize));
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_size_hint_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let it = v.into_iter();
        let (lo, hi) = it.size_hint();
        assert!(lo == n);
        assert!(hi == Some(n));
    }

    // unwind 72: covers the <=64 drop loop + NonZero::new's 8-byte zero-check
    #[kani::proof]
    #[kani::unwind(72)]
    fn check_into_iter_advance_by_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let mut it = v.into_iter();
        let k: usize = kani::any();
        let r = it.advance_by(k);
        if k <= n {
            assert!(r.is_ok());
            assert!(it.len() == n - k);
        } else {
            assert!(r.is_err());
            assert!(it.len() == 0);
        }
    }

    #[kani::proof]
    #[kani::unwind(72)]
    fn check_into_iter_advance_back_by_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let mut it = v.into_iter();
        let k: usize = kani::any();
        let r = it.advance_back_by(k);
        if k <= n {
            assert!(r.is_ok());
            assert!(it.len() == n - k);
        } else {
            assert!(r.is_err());
            assert!(it.len() == 0);
        }
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_next_chunk_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let mut it = v.into_iter();
        match it.next_chunk::<2>() {
            Ok(_) => {
                assert!(n >= 2);
                assert!(it.len() == n - 2);
            }
            Err(_) => {
                assert!(n < 2);
                assert!(it.len() == 0);
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_as_slice_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let it = v.into_iter();
        assert!(it.as_slice().len() == n);
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_as_mut_slice_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let mut it = v.into_iter();
        assert!(it.as_mut_slice().len() == n);
    }

    // __iterator_get_unchecked: the #[requires(i < self.len())] + kani::modifies
    // contract already exists on this method. Kani cannot resolve a generic
    // trait-impl method as a proof_for_contract target (kani#1997), so this
    // harness is the mirroring assume-guarded proof: the assume mirrors the
    // #[requires]; the assert checks the read's value against the source slice.
    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_get_unchecked_u8() {
        let arr: [u8; 64] = kani::any();
        let s = kani::slice::any_slice_of_array(&arr);
        let mut it = s.to_vec().into_iter();
        let len = it.len();
        kani::assume(len > 0);
        let i: usize = kani::any();
        kani::assume(i < len);
        kani::cover(i == len - 1, "non-vacuity: the maximal valid index is reachable");
        // SAFETY: i < len mirrors the documented #[requires] precondition.
        let x = unsafe { it.__iterator_get_unchecked(i) };
        assert!(x == s[i]);
    }

    // Drop: destroys the remaining elements (drop_in_place) + RawVec dealloc.
    // vec![..] list form builds the Vec without the reallocation path.
    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_drop_droptoken() {
        let mut it = vec![
            DropToken(kani::any()),
            DropToken(kani::any()),
            DropToken(kani::any()),
            DropToken(kani::any()),
        ]
        .into_iter();
        let _ = it.advance_by(kani::any()); // consume a symbolic prefix
        // `it` drops here: drop_in_place over the symbolic-count remaining + dealloc
    }

    // forget_allocation_drop_remaining: drops remaining elements, keeps the allocation.
    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_forget_allocation_drop_remaining() {
        let mut it = vec![
            DropToken(kani::any()),
            DropToken(kani::any()),
            DropToken(kani::any()),
            DropToken(kani::any()),
        ]
        .into_iter();
        let _ = it.next();
        it.forget_allocation_drop_remaining();
        assert!(it.len() == 0);
    }

    // into_vecdeque: reinterprets the IntoIter allocation as a VecDeque.
    #[kani::proof]
    #[kani::unwind(8)]
    fn check_into_iter_into_vecdeque_u8() {
        let v = any_u8_vec::<64>();
        let n = v.len();
        let it = v.into_iter();
        let dq = it.into_vecdeque();
        assert!(dq.len() == n);
    }

    // --- ZST arm: every method above has a structurally separate `T::IS_ZST`
    // branch (end walks by bytes, ptr frozen). These three harnesses cover that
    // arm for the iteration core; this is branch coverage of distinct pointer
    // arithmetic, not an extra width instantiation. ---

    #[kani::proof]
    #[kani::unwind(72)]
    fn check_into_iter_next_zst() {
        let n: usize = kani::any();
        kani::assume(n <= 64);
        kani::cover(n == 64, "non-vacuity: the full-length ZST case is reachable");
        let v: Vec<()> = vec![(); n];
        let mut it = v.into_iter();
        let r = it.next();
        assert!(r.is_some() == (n > 0));
        assert!(it.len() == n - (r.is_some() as usize));
    }

    #[kani::proof]
    #[kani::unwind(72)]
    fn check_into_iter_fold_zst() {
        let n: usize = kani::any();
        kani::assume(n <= 64);
        kani::cover(n == 64, "non-vacuity: the full-length ZST fold is reachable");
        let v: Vec<()> = vec![(); n];
        let count = v.into_iter().fold(0usize, |acc, _| acc + 1);
        assert!(count == n);
    }

    #[kani::proof]
    #[kani::unwind(72)]
    fn check_into_iter_advance_by_zst() {
        let n: usize = kani::any();
        kani::assume(n <= 64);
        kani::cover(n == 64, "non-vacuity: the full-length ZST advance is reachable");
        let v: Vec<()> = vec![(); n];
        let mut it = v.into_iter();
        let k: usize = kani::any();
        let r = it.advance_by(k);
        if k <= n {
            assert!(r.is_ok());
            assert!(it.len() == n - k);
        } else {
            assert!(r.is_err());
            assert!(it.len() == 0);
        }
    }

    // --- Additive Option-A shape coverage. The per-type harnesses above are
    // unchanged; each helper below is written once for arbitrary T and
    // instantiated over the shapes whose property the method observes. Full
    // conversion of the existing suite is deferred pending the generic-T ruling. ---
    // `DropToken` aliased: this module already has its own local `DropToken`
    // (a distinct, non-Arbitrary type used by the existing drop harnesses above).
    use crate::vec::kani_shapes::{Al16, DropToken as ShapeDropToken, any_vec};

    // next over arbitrary T: reads the first element back (validity + stride)
    // and checks length bookkeeping. Mirrors check_into_iter_next_u8's body.
    fn check_next_shape<T: kani::Arbitrary + Clone + PartialEq, const N: usize>() {
        let v = any_vec::<T, N>();
        let n = v.len();
        let first = if n > 0 { Some(v[0].clone()) } else { None };
        let mut it = v.into_iter();
        let r = it.next();
        assert!(r == first);
        assert!(it.len() == n - (r.is_some() as usize));
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_next_bool() {
        check_next_shape::<bool, 8>();
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_next_al16() {
        check_next_shape::<Al16, 8>();
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_next_droptoken() {
        check_next_shape::<ShapeDropToken, 8>();
    }

    // next_back over arbitrary T: backward move-out — a drop geometry distinct
    // from next and from IntoIter::drop. Mirrors check_into_iter_next_back_u8.
    fn check_next_back_shape<T: kani::Arbitrary + Clone + PartialEq, const N: usize>() {
        let v = any_vec::<T, N>();
        let n = v.len();
        let last = if n > 0 { Some(v[n - 1].clone()) } else { None };
        let mut it = v.into_iter();
        let r = it.next_back();
        assert!(r == last);
        assert!(it.len() == n - (r.is_some() as usize));
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_next_back_droptoken() {
        check_next_back_shape::<ShapeDropToken, 8>();
    }

    // __iterator_get_unchecked over arbitrary Copy T: the assume mirrors the
    // existing #[requires(i < len)]; [u8; 3] adds the odd-stride (non-power-of-
    // two) `add(i)` index arithmetic no other harness exercises. T: Copy is the
    // method's own reach (TrustedRandomAccessNoCoerce requires NonDrop). Mirrors
    // check_into_iter_get_unchecked_u8.
    fn check_get_unchecked_shape<T: kani::Arbitrary + Copy + PartialEq, const N: usize>() {
        let arr: [T; N] = kani::any();
        let s = kani::slice::any_slice_of_array(&arr);
        let mut it = s.to_vec().into_iter();
        let len = it.len();
        kani::assume(len > 0);
        let i: usize = kani::any();
        kani::assume(i < len);
        kani::cover(i == len - 1, "non-vacuity: the maximal valid index is reachable");
        // SAFETY: i < len mirrors the documented #[requires] precondition.
        let x = unsafe { it.__iterator_get_unchecked(i) };
        assert!(x == s[i]);
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn check_into_iter_get_unchecked_arr3() {
        check_get_unchecked_shape::<[u8; 3], 8>();
    }
}
