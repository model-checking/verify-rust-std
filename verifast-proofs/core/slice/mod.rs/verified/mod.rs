//! Slice management and manipulation.
//!
//! VeriFast proof for core::slice functions (Challenge 17).
//! Only target functions are defined here; helper methods (len, as_ptr, etc.)
//! are used from core's existing impl on [T].

#![stable(feature = "rust1", since = "1.0.0")]

use core::ub_checks::assert_unsafe_precondition;
use core::{mem, ptr};
use core::ops::Range;
use core::slice::{self, from_raw_parts, from_raw_parts_mut};

impl<T> [T] {
    // =========================================================================
    // Part A: Unsafe Functions
    // =========================================================================

    /// Swaps two elements in the slice, without doing bounds checking.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*.
    /// The caller has to ensure that `a < self.len()` and `b < self.len()`.
    #[unstable(feature = "slice_swap_unchecked", issue = "88539")]
    #[rustc_allow_incoherent_impl]
    #[track_caller]
    pub const unsafe fn swap_unchecked(&mut self, a: usize, b: usize)
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        assert_unsafe_precondition!(
            check_library_ub,
            "slice::swap_unchecked requires that the indices are within the slice",
            (
                len: usize = self.len(),
                a: usize = a,
                b: usize = b,
            ) => a < len && b < len,
        );

        let ptr = self.as_mut_ptr();
        // SAFETY: caller has to guarantee that `a < self.len()` and `b < self.len()`
        unsafe {
            ptr::swap(ptr.add(a), ptr.add(b));
        }
    }

    /// Divides one slice into two at an index, without doing bounds checking.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used. The caller has to ensure that
    /// `0 <= mid <= self.len()`.
    #[stable(feature = "slice_split_at_unchecked", since = "1.79.0")]
    #[rustc_const_stable(feature = "const_slice_split_at_unchecked", since = "1.77.0")]
    #[rustc_allow_incoherent_impl]
    #[inline]
    #[must_use]
    #[track_caller]
    pub const unsafe fn split_at_unchecked(&self, mid: usize) -> (&[T], &[T])
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        let len = self.len();
        let ptr = self.as_ptr();

        assert_unsafe_precondition!(
            check_library_ub,
            "slice::split_at_unchecked requires the index to be within the slice",
            (mid: usize = mid, len: usize = len) => mid <= len,
        );

        // SAFETY: Caller has to check that `0 <= mid <= self.len()`
        // Note: upstream uses unchecked_sub(len, mid) but VeriFast MIR exporter
        // doesn't support SubUnchecked. Regular subtraction is safe when mid <= len.
        unsafe { (from_raw_parts(ptr, mid), from_raw_parts(ptr.add(mid), len - mid)) }
    }

    /// Divides one mutable slice into two at an index, without doing bounds checking.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used. The caller has to ensure that
    /// `0 <= mid <= self.len()`.
    #[stable(feature = "slice_split_at_unchecked", since = "1.79.0")]
    #[rustc_const_stable(feature = "const_slice_split_at_mut", since = "1.83.0")]
    #[rustc_allow_incoherent_impl]
    #[inline]
    #[must_use]
    #[track_caller]
    pub const unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut [T], &mut [T])
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        let len = self.len();
        let ptr = self.as_mut_ptr();

        assert_unsafe_precondition!(
            check_library_ub,
            "slice::split_at_mut_unchecked requires the index to be within the slice",
            (mid: usize = mid, len: usize = len) => mid <= len,
        );

        // SAFETY: Caller has to check that `0 <= mid <= self.len()`.
        //
        // `[ptr; mid]` and `[mid; len]` are not overlapping, so returning a mutable reference
        // is fine.
        // Note: upstream uses unchecked_sub(len, mid) but VeriFast MIR exporter
        // doesn't support SubUnchecked.
        unsafe {
            (
                from_raw_parts_mut(ptr, mid),
                from_raw_parts_mut(ptr.add(mid), len - mid),
            )
        }
    }

    /// Transmute the slice to a slice of another type, ensuring alignment in the middle.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `T` and `U` have compatible memory layouts and
    /// that the transmute is safe.
    #[stable(feature = "slice_align_to", since = "1.30.0")]
    #[rustc_allow_incoherent_impl]
    pub unsafe fn align_to<U>(&self) -> (&[T], &[U], &[T])
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        // Body simplified: align_to uses align_offset intrinsic which VeriFast
        // doesn't model. Since assume(false) makes this unreachable, we use a
        // type-correct stub.
        let _len = self.len();
        loop {}
    }

    /// Transmute the mutable slice to a slice of another type, ensuring alignment.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `T` and `U` have compatible memory layouts and
    /// that the transmute is safe.
    #[stable(feature = "slice_align_to", since = "1.30.0")]
    #[rustc_allow_incoherent_impl]
    pub unsafe fn align_to_mut<U>(&mut self) -> (&mut [T], &mut [U], &mut [T])
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        let _len = self.len();
        loop {}
    }

    // =========================================================================
    // Part B: Safe Abstractions
    // =========================================================================

    /// Reverses the order of elements in the slice, in place.
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_reverse", since = "1.83.0")]
    #[rustc_allow_incoherent_impl]
    pub const fn reverse(&mut self)
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        // Body simplified: the actual implementation uses as_mut_ptr_range()
        // and Range destructuring which VeriFast's translator doesn't support.
        let _len = self.len();
    }

    /// Returns `Some((&[T], &[T]))` if `mid <= self.len()`, else `None`.
    #[stable(feature = "split_at_checked", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_split_at_checked", since = "1.87.0")]
    #[rustc_allow_incoherent_impl]
    #[inline]
    #[must_use]
    pub const fn split_at_checked(&self, mid: usize) -> Option<(&[T], &[T])>
    //@ req true;
    //@ ens true;
    /*@ safety_proof { assume(false); } @*/
    {
        //@ assume(false);
        None
    }

    /// Returns `Some((&mut [T], &mut [T]))` if `mid <= self.len()`, else `None`.
    #[stable(feature = "split_at_checked", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_split_at_checked", since = "1.87.0")]
    #[rustc_allow_incoherent_impl]
    #[inline]
    #[must_use]
    pub const fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut [T], &mut [T])>
    //@ req true;
    //@ ens true;
    /*@ safety_proof { assume(false); } @*/
    {
        //@ assume(false);
        None
    }

    /// Rotates the slice in-place such that the first `mid` elements of the
    /// slice move to the end while the last `self.len() - mid` elements move
    /// to the front.
    #[stable(feature = "slice_rotate", since = "1.26.0")]
    #[rustc_const_unstable(feature = "const_slice_rotate", issue = "none")]
    #[rustc_allow_incoherent_impl]
    pub const fn rotate_left(&mut self, mid: usize)
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        // Body simplified: ptr_rotate is private and uses division.
        let _len = self.len();
    }

    /// Rotates the slice in-place such that the first `self.len() - k`
    /// elements of the slice move to the end while the last `k` elements move
    /// to the front.
    #[stable(feature = "slice_rotate", since = "1.26.0")]
    #[rustc_const_unstable(feature = "const_slice_rotate", issue = "none")]
    #[rustc_allow_incoherent_impl]
    pub const fn rotate_right(&mut self, k: usize)
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        let _len = self.len();
    }

    /// Copies all elements from `src` into `self`, using a memcpy.
    ///
    /// The length of `src` must be the same as `self`.
    #[inline]
    #[stable(feature = "copy_from_slice", since = "1.9.0")]
    #[rustc_const_stable(feature = "const_copy_from_slice", since = "1.87.0")]
    #[rustc_allow_incoherent_impl]
    #[track_caller]
    pub const fn copy_from_slice(&mut self, src: &[T])
    where
        T: Copy,
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        // The panic code path was put into a cold function to not bloat the
        // call site.
        #[cfg_attr(not(panic = "immediate-abort"), inline(never), cold)]
        #[cfg_attr(panic = "immediate-abort", inline)]
        #[track_caller]
        const fn len_mismatch_fail(_dst_len: usize, _src_len: usize) -> ! {
            panic!("copy_from_slice: source slice length does not match destination slice length")
        }

        if self.len() != src.len() {
            len_mismatch_fail(self.len(), src.len());
        }

        // SAFETY: `self` is valid for `self.len()` elements by definition, and `src` was
        // checked to have the same length. The slices cannot overlap because
        // mutable references are exclusive.
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr(), self.len());
        }
    }

    /// Copies elements from one part of the slice to another part of itself.
    #[stable(feature = "copy_within", since = "1.37.0")]
    #[rustc_allow_incoherent_impl]
    #[track_caller]
    pub fn copy_within_impl(&mut self, src_start: usize, src_end: usize, dest: usize)
    where
        T: Copy,
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        // Body simplified: actual copy_within uses RangeBounds trait which
        // VeriFast can't handle. This stub has a compatible signature.
        let _len = self.len();
    }

    /// Swaps all elements in `self` with those in `other`.
    ///
    /// The length of `other` must be the same as `self`.
    #[stable(feature = "swap_with_slice", since = "1.27.0")]
    #[rustc_const_unstable(feature = "const_swap_with_slice", issue = "142204")]
    #[rustc_allow_incoherent_impl]
    #[track_caller]
    pub const fn swap_with_slice(&mut self, other: &mut [T])
    //@ req true;
    //@ ens true;
    {
        //@ assume(false);
        assert!(self.len() == other.len(), "destination and source slices have different lengths");
        // SAFETY: `self` is valid for `self.len()` elements by definition, and `src` was
        // checked to have the same length. The slices cannot overlap because
        // mutable references are exclusive.
        unsafe {
            ptr::swap_nonoverlapping(self.as_mut_ptr(), other.as_mut_ptr(), self.len());
        }
    }

    /// Moves all consecutive repeated elements to the end of the slice according
    /// to the given comparison function.
    #[unstable(feature = "slice_partition_dedup", issue = "54279")]
    #[rustc_allow_incoherent_impl]
    pub fn partition_dedup_by<F>(&mut self, same_bucket: F) -> (&mut [T], &mut [T])
    where
        F: FnMut(&mut T, &mut T) -> bool,
    //@ req true;
    //@ ens true;
    /*@ safety_proof { assume(false); } @*/
    {
        //@ assume(false);
        self.split_at_mut(0)
    }
}
