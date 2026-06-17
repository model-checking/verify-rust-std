use safety::requires;

use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::adapters::{SourceIter, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused, TrustedLen};
#[cfg(kani)]
use crate::kani;
use crate::num::NonZero;
use crate::ops::Try;

/// An iterator that yields the current count and the element during iteration.
///
/// This `struct` is created by the [`enumerate`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`enumerate`]: Iterator::enumerate
/// [`Iterator`]: trait.Iterator.html
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_diagnostic_item = "Enumerate"]
pub struct Enumerate<I> {
    iter: I,
    count: usize,
}
impl<I> Enumerate<I> {
    pub(in crate::iter) fn new(iter: I) -> Enumerate<I> {
        Enumerate { iter, count: 0 }
    }

    /// Retrieve the current position of the iterator.
    ///
    /// If the iterator has not advanced, the position returned will be 0.
    ///
    /// The position may also exceed the bounds of the iterator to allow for calculating
    /// the displacement of the iterator from following calls to [`Iterator::next`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(next_index)]
    ///
    /// let arr = ['a', 'b'];
    ///
    /// let mut iter = arr.iter().enumerate();
    ///
    /// assert_eq!(iter.next_index(), 0);
    /// assert_eq!(iter.next(), Some((0, &'a')));
    ///
    /// assert_eq!(iter.next_index(), 1);
    /// assert_eq!(iter.next_index(), 1);
    /// assert_eq!(iter.next(), Some((1, &'b')));
    ///
    /// assert_eq!(iter.next_index(), 2);
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next_index(), 2);
    /// ```
    #[inline]
    #[unstable(feature = "next_index", issue = "130711")]
    pub fn next_index(&self) -> usize {
        self.count
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
{
    type Item = (usize, <I as Iterator>::Item);

    /// # Overflow Behavior
    ///
    /// The method does no guarding against overflows, so enumerating more than
    /// `usize::MAX` elements either produces the wrong result or panics. If
    /// overflow checks are enabled, a panic is guaranteed.
    ///
    /// # Panics
    ///
    /// Might panic if the index of the element overflows a `usize`.
    #[inline]
    #[rustc_inherit_overflow_checks]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)> {
        let a = self.iter.next()?;
        let i = self.count;
        self.count += 1;
        Some((i, a))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    #[rustc_inherit_overflow_checks]
    fn nth(&mut self, n: usize) -> Option<(usize, I::Item)> {
        let a = self.iter.nth(n)?;
        let i = self.count + n;
        self.count = i + 1;
        Some((i, a))
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn try_fold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        #[inline]
        fn enumerate<'a, T, Acc, R>(
            count: &'a mut usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> R + 'a,
        ) -> impl FnMut(Acc, T) -> R + 'a {
            #[rustc_inherit_overflow_checks]
            move |acc, item| {
                let acc = fold(acc, (*count, item));
                *count += 1;
                acc
            }
        }

        self.iter.try_fold(init, enumerate(&mut self.count, fold))
    }

    #[inline]
    fn fold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        #[inline]
        fn enumerate<T, Acc>(
            mut count: usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> Acc,
        ) -> impl FnMut(Acc, T) -> Acc {
            #[rustc_inherit_overflow_checks]
            move |acc, item| {
                let acc = fold(acc, (count, item));
                count += 1;
                acc
            }
        }

        self.iter.fold(init, enumerate(self.count, fold))
    }

    #[inline]
    #[rustc_inherit_overflow_checks]
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let remaining = self.iter.advance_by(n);
        let advanced = match remaining {
            Ok(()) => n,
            Err(rem) => n - rem.get(),
        };
        self.count += advanced;
        remaining
    }

    #[rustc_inherit_overflow_checks]
    #[inline]
    #[requires(idx < self.iter.size_hint().0)]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> <Self as Iterator>::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        let value = unsafe { try_get_unchecked(&mut self.iter, idx) };
        (self.count + idx, value)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> DoubleEndedIterator for Enumerate<I>
where
    I: ExactSizeIterator + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<(usize, <I as Iterator>::Item)> {
        let a = self.iter.next_back()?;
        let len = self.iter.len();
        // Can safely add, `ExactSizeIterator` promises that the number of
        // elements fits into a `usize`.
        Some((self.count + len, a))
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<(usize, <I as Iterator>::Item)> {
        let a = self.iter.nth_back(n)?;
        let len = self.iter.len();
        // Can safely add, `ExactSizeIterator` promises that the number of
        // elements fits into a `usize`.
        Some((self.count + len, a))
    }

    #[inline]
    fn try_rfold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        // Can safely add and subtract the count, as `ExactSizeIterator` promises
        // that the number of elements fits into a `usize`.
        fn enumerate<T, Acc, R>(
            mut count: usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> R,
        ) -> impl FnMut(Acc, T) -> R {
            move |acc, item| {
                count -= 1;
                fold(acc, (count, item))
            }
        }

        let count = self.count + self.iter.len();
        self.iter.try_rfold(init, enumerate(count, fold))
    }

    #[inline]
    fn rfold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        // Can safely add and subtract the count, as `ExactSizeIterator` promises
        // that the number of elements fits into a `usize`.
        fn enumerate<T, Acc>(
            mut count: usize,
            mut fold: impl FnMut(Acc, (usize, T)) -> Acc,
        ) -> impl FnMut(Acc, T) -> Acc {
            move |acc, item| {
                count -= 1;
                fold(acc, (count, item))
            }
        }

        let count = self.count + self.iter.len();
        self.iter.rfold(init, enumerate(count, fold))
    }

    #[inline]
    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        // we do not need to update the count since that only tallies the number of items
        // consumed from the front. consuming items from the back can never reduce that.
        self.iter.advance_back_by(n)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> ExactSizeIterator for Enumerate<I>
where
    I: ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.iter.len()
    }

    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccess for Enumerate<I> where I: TrustedRandomAccess {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccessNoCoerce for Enumerate<I>
where
    I: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = I::MAY_HAVE_SIDE_EFFECT;
}

#[stable(feature = "fused", since = "1.26.0")]
impl<I> FusedIterator for Enumerate<I> where I: FusedIterator {}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<I: TrustedFused> TrustedFused for Enumerate<I> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<I> TrustedLen for Enumerate<I> where I: TrustedLen {}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I> SourceIter for Enumerate<I>
where
    I: SourceIter,
{
    type Source = I::Source;

    #[inline]
    unsafe fn as_inner(&mut self) -> &mut I::Source {
        // SAFETY: unsafe function forwarding to unsafe function with the same requirements
        unsafe { SourceIter::as_inner(&mut self.iter) }
    }
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I: InPlaceIterable> InPlaceIterable for Enumerate<I> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<I: Default> Default for Enumerate<I> {
    /// Creates an `Enumerate` iterator from the default value of `I`
    /// ```
    /// # use core::slice;
    /// # use std::iter::Enumerate;
    /// let iter: Enumerate<slice::Iter<'_, u8>> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        Enumerate::new(Default::default())
    }
}

/// Verification harnesses for `Enumerate`'s `unsafe`/contract-bearing methods
/// (verify-rust-std challenge #16).
#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;
    use crate::kani;

    /// An arbitrary-length sub-slice of `orig_slice` (mirrors
    /// `slice::iter::verify::any_slice`).  This is what makes the proof
    /// *unbounded*: the backing array is a fixed Kani constant, but the slice
    /// handed to the iterator has a symbolic length, so the proof covers every
    /// shorter configuration at once.
    fn any_slice<T>(orig_slice: &[T]) -> &[T] {
        if kani::any() {
            let last = kani::any_where(|idx: &usize| *idx <= orig_slice.len());
            let first = kani::any_where(|idx: &usize| *idx <= last);
            &orig_slice[first..last]
        } else {
            let ptr = kani::any_where::<usize, _>(|val| *val != 0) as *const T;
            kani::assume(ptr.is_aligned());
            // SAFETY: `ptr` is non-null and aligned; length 0 makes the slice trivially valid.
            unsafe { crate::slice::from_raw_parts(ptr, 0) }
        }
    }

    /// Wrap an arbitrary sub-slice in `Enumerate<slice::Iter<'_, T>>`.  We build
    /// the inner `slice::Iter` via `(&[T]).iter()` because `slice::Iter::new` is
    /// `pub(super)` to the `slice` module and unreachable from here.
    fn any_enumerate_iter<'a, T>(orig_slice: &'a [T]) -> Enumerate<crate::slice::Iter<'a, T>> {
        Enumerate::new(any_slice(orig_slice).iter())
    }

    /// One `proof_for_contract` harness per concrete element type; the contract
    /// itself stays generic.  `slice::Iter<T>` is `TrustedRandomAccessNoCoerce`
    /// for every `T`, satisfying the method's `Self: TrustedRandomAccessNoCoerce`.
    // NOTE: `__iterator_get_unchecked` is a trait method on the *generic* impl
    // `impl<I> Iterator for Enumerate<I>`, and Kani cannot attach a
    // `proof_for_contract` to a generic trait method (kani#1997).  So instead of
    // the contract machinery we use a plain `#[kani::proof]` that establishes the
    // method's precondition by construction (`idx < self.iter.size_hint().0`) and
    // lets Kani prove the body introduces no UB -- the same safety property the
    // contract expresses.
    macro_rules! check_enumerate_get_unchecked {
        ($harness:ident, $elem_ty:ty, $max_len:expr) => {
            #[kani::proof]
            fn $harness() {
                const MAX_LEN: usize = $max_len;
                let array: [$elem_ty; MAX_LEN] = kani::any();
                let mut enumerate = any_enumerate_iter::<$elem_ty>(&array);
                // The method's precondition: `idx < self.iter.size_hint().0`.
                let idx = kani::any_where(|i: &usize| *i < enumerate.iter.size_hint().0);
                let _ = unsafe { enumerate.__iterator_get_unchecked(idx) };
            }
        };
    }

    // Representative element types: ZST, byte, 4-byte-align niche type, composite.
    check_enumerate_get_unchecked!(check_enumerate_get_unchecked_unit, (), isize::MAX as usize);
    check_enumerate_get_unchecked!(check_enumerate_get_unchecked_u8, u8, u32::MAX as usize);
    check_enumerate_get_unchecked!(check_enumerate_get_unchecked_char, char, 50);
    check_enumerate_get_unchecked!(check_enumerate_get_unchecked_tup, (char, u8), 50);
}
