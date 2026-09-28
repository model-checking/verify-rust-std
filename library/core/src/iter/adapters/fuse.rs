use safety::requires;

use crate::intrinsics;
use crate::iter::adapters::SourceIter;
use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::{
    FusedIterator, TrustedFused, TrustedLen, TrustedRandomAccess, TrustedRandomAccessNoCoerce,
};
#[cfg(kani)]
use crate::kani;
use crate::ops::Try;

/// An iterator that yields `None` forever after the underlying iterator
/// yields `None` once.
///
/// This `struct` is created by [`Iterator::fuse`]. See its documentation
/// for more.
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Fuse<I> {
    // NOTE: for `I: FusedIterator`, we never bother setting `None`, but
    // we still have to be prepared for that state due to variance.
    // See rust-lang/rust#85863
    iter: Option<I>,
}
impl<I> Fuse<I> {
    pub(in crate::iter) fn new(iter: I) -> Fuse<I> {
        Fuse { iter: Some(iter) }
    }

    pub(crate) fn into_inner(self) -> Option<I> {
        self.iter
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<I> FusedIterator for Fuse<I> where I: Iterator {}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<I> TrustedFused for Fuse<I> where I: TrustedFused {}

// Any specialized implementation here is made internal
// to avoid exposing default fns outside this trait.
#[stable(feature = "rust1", since = "1.0.0")]
impl<I> Iterator for Fuse<I>
where
    I: Iterator,
{
    type Item = <I as Iterator>::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        FuseImpl::next(self)
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        FuseImpl::nth(self, n)
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        match self.iter {
            Some(iter) => iter.last(),
            None => None,
        }
    }

    #[inline]
    fn count(self) -> usize {
        match self.iter {
            Some(iter) => iter.count(),
            None => 0,
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.iter {
            Some(ref iter) => iter.size_hint(),
            None => (0, Some(0)),
        }
    }

    #[inline]
    fn try_fold<Acc, Fold, R>(&mut self, acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        FuseImpl::try_fold(self, acc, fold)
    }

    #[inline]
    fn fold<Acc, Fold>(self, mut acc: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        if let Some(iter) = self.iter {
            acc = iter.fold(acc, fold);
        }
        acc
    }

    #[inline]
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        FuseImpl::find(self, predicate)
    }

    #[inline]
    #[requires(self.iter.is_some() && idx < self.iter.as_ref().unwrap().size_hint().0)]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        match self.iter {
            // SAFETY: the caller must uphold the contract for
            // `Iterator::__iterator_get_unchecked`.
            Some(ref mut iter) => unsafe { try_get_unchecked(iter, idx) },
            // SAFETY: the caller asserts there is an item at `i`, so we're not exhausted.
            None => unsafe { intrinsics::unreachable() },
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> DoubleEndedIterator for Fuse<I>
where
    I: DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<<I as Iterator>::Item> {
        FuseImpl::next_back(self)
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<<I as Iterator>::Item> {
        FuseImpl::nth_back(self, n)
    }

    #[inline]
    fn try_rfold<Acc, Fold, R>(&mut self, acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        FuseImpl::try_rfold(self, acc, fold)
    }

    #[inline]
    fn rfold<Acc, Fold>(self, mut acc: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        if let Some(iter) = self.iter {
            acc = iter.rfold(acc, fold);
        }
        acc
    }

    #[inline]
    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        FuseImpl::rfind(self, predicate)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> ExactSizeIterator for Fuse<I>
where
    I: ExactSizeIterator,
{
    fn len(&self) -> usize {
        match self.iter {
            Some(ref iter) => iter.len(),
            None => 0,
        }
    }

    fn is_empty(&self) -> bool {
        match self.iter {
            Some(ref iter) => iter.is_empty(),
            None => true,
        }
    }
}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<I: Default> Default for Fuse<I> {
    /// Creates a `Fuse` iterator from the default value of `I`.
    ///
    /// ```
    /// # use core::slice;
    /// # use std::iter::Fuse;
    /// let iter: Fuse<slice::Iter<'_, u8>> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    ///
    /// This is equivalent to `I::default().fuse()`[^fuse_note]; e.g. if
    /// `I::default()` is not an empty iterator, then this will not be
    /// an empty iterator.
    ///
    /// ```
    /// # use std::iter::Fuse;
    /// #[derive(Default)]
    /// struct Fourever;
    ///
    /// impl Iterator for Fourever {
    ///     type Item = u32;
    ///     fn next(&mut self) -> Option<u32> {
    ///         Some(4)
    ///     }
    /// }
    ///
    /// let mut iter: Fuse<Fourever> = Default::default();
    /// assert_eq!(iter.next(), Some(4));
    /// ```
    ///
    /// [^fuse_note]: if `I` does not override `Iterator::fuse`'s default implementation
    fn default() -> Self {
        Fuse { iter: Some(I::default()) }
    }
}

#[unstable(feature = "trusted_len", issue = "37572")]
// SAFETY: `TrustedLen` requires that an accurate length is reported via `size_hint()`. As `Fuse`
// is just forwarding this to the wrapped iterator `I` this property is preserved and it is safe to
// implement `TrustedLen` here.
unsafe impl<I> TrustedLen for Fuse<I> where I: TrustedLen {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
// SAFETY: `TrustedRandomAccess` requires that `size_hint()` must be exact and cheap to call, and
// `Iterator::__iterator_get_unchecked()` must be implemented accordingly.
//
// This is safe to implement as `Fuse` is just forwarding these to the wrapped iterator `I`, which
// preserves these properties.
unsafe impl<I> TrustedRandomAccess for Fuse<I> where I: TrustedRandomAccess {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccessNoCoerce for Fuse<I>
where
    I: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = I::MAY_HAVE_SIDE_EFFECT;
}

/// Fuse specialization trait
///
/// We only need to worry about `&mut self` methods, which
/// may exhaust the iterator without consuming it.
#[doc(hidden)]
trait FuseImpl<I> {
    type Item;

    // Functions specific to any normal Iterators
    fn next(&mut self) -> Option<Self::Item>;
    fn nth(&mut self, n: usize) -> Option<Self::Item>;
    fn try_fold<Acc, Fold, R>(&mut self, acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>;
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool;

    // Functions specific to DoubleEndedIterators
    fn next_back(&mut self) -> Option<Self::Item>
    where
        I: DoubleEndedIterator;
    fn nth_back(&mut self, n: usize) -> Option<Self::Item>
    where
        I: DoubleEndedIterator;
    fn try_rfold<Acc, Fold, R>(&mut self, acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
        I: DoubleEndedIterator;
    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
        I: DoubleEndedIterator;
}

/// General `Fuse` impl which sets `iter = None` when exhausted.
#[doc(hidden)]
impl<I> FuseImpl<I> for Fuse<I>
where
    I: Iterator,
{
    type Item = <I as Iterator>::Item;

    #[inline]
    default fn next(&mut self) -> Option<<I as Iterator>::Item> {
        and_then_or_clear(&mut self.iter, Iterator::next)
    }

    #[inline]
    default fn nth(&mut self, n: usize) -> Option<I::Item> {
        and_then_or_clear(&mut self.iter, |iter| iter.nth(n))
    }

    #[inline]
    default fn try_fold<Acc, Fold, R>(&mut self, mut acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        if let Some(ref mut iter) = self.iter {
            acc = iter.try_fold(acc, fold)?;
            self.iter = None;
        }
        try { acc }
    }

    #[inline]
    default fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        and_then_or_clear(&mut self.iter, |iter| iter.find(predicate))
    }

    #[inline]
    default fn next_back(&mut self) -> Option<<I as Iterator>::Item>
    where
        I: DoubleEndedIterator,
    {
        and_then_or_clear(&mut self.iter, |iter| iter.next_back())
    }

    #[inline]
    default fn nth_back(&mut self, n: usize) -> Option<<I as Iterator>::Item>
    where
        I: DoubleEndedIterator,
    {
        and_then_or_clear(&mut self.iter, |iter| iter.nth_back(n))
    }

    #[inline]
    default fn try_rfold<Acc, Fold, R>(&mut self, mut acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
        I: DoubleEndedIterator,
    {
        if let Some(ref mut iter) = self.iter {
            acc = iter.try_rfold(acc, fold)?;
            self.iter = None;
        }
        try { acc }
    }

    #[inline]
    default fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
        I: DoubleEndedIterator,
    {
        and_then_or_clear(&mut self.iter, |iter| iter.rfind(predicate))
    }
}

/// Specialized `Fuse` impl which doesn't bother clearing `iter` when exhausted.
/// However, we must still be prepared for the possibility that it was already cleared!
#[doc(hidden)]
impl<I> FuseImpl<I> for Fuse<I>
where
    I: FusedIterator,
{
    #[inline]
    fn next(&mut self) -> Option<<I as Iterator>::Item> {
        self.iter.as_mut()?.next()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        self.iter.as_mut()?.nth(n)
    }

    #[inline]
    fn try_fold<Acc, Fold, R>(&mut self, mut acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        if let Some(ref mut iter) = self.iter {
            acc = iter.try_fold(acc, fold)?;
        }
        try { acc }
    }

    #[inline]
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        self.iter.as_mut()?.find(predicate)
    }

    #[inline]
    fn next_back(&mut self) -> Option<<I as Iterator>::Item>
    where
        I: DoubleEndedIterator,
    {
        self.iter.as_mut()?.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<<I as Iterator>::Item>
    where
        I: DoubleEndedIterator,
    {
        self.iter.as_mut()?.nth_back(n)
    }

    #[inline]
    fn try_rfold<Acc, Fold, R>(&mut self, mut acc: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
        I: DoubleEndedIterator,
    {
        if let Some(ref mut iter) = self.iter {
            acc = iter.try_rfold(acc, fold)?;
        }
        try { acc }
    }

    #[inline]
    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
        I: DoubleEndedIterator,
    {
        self.iter.as_mut()?.rfind(predicate)
    }
}

// This is used by Flatten's SourceIter impl
#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I> SourceIter for Fuse<I>
where
    I: SourceIter + TrustedFused,
{
    type Source = I::Source;

    #[inline]
    unsafe fn as_inner(&mut self) -> &mut I::Source {
        // SAFETY: unsafe function forwarding to unsafe function with the same requirements.
        // TrustedFused guarantees that we'll never encounter a case where `self.iter` would
        // be set to None.
        unsafe { SourceIter::as_inner(self.iter.as_mut().unwrap_unchecked()) }
    }
}

#[inline]
fn and_then_or_clear<T, U>(opt: &mut Option<T>, f: impl FnOnce(&mut T) -> Option<U>) -> Option<U> {
    let x = f(opt.as_mut()?);
    if x.is_none() {
        *opt = None;
    }
    x
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    // Harnesses for `__iterator_get_unchecked` for Fuse
    // Use a regular proof because `proof_for_contract` cannot resolve this trait method path.
    macro_rules! generate_fuse_get_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Generate a symbolic logical length with no explicit upper bound.
                let len: usize = kani::any();
                // Generate a symbolic access index.
                let idx: usize = kani::any();
                // Generate an arbitrary inner item.
                let value: $ty = kani::any();
                // Record the index actually received by the inner iterator.
                let observed_idx = crate::cell::Cell::new(usize::MAX);

                // Build a lazy iterator of length `len` without allocating `len` elements.
                let source = (0..len).map(|position| {
                    // Record which inner element the target actually requested.
                    observed_idx.set(position);
                    value
                });
                // Construct an active `Fuse<I>` whose inner state is `Some(source)`.
                let mut iter = Fuse::new(source);

                // Express the target's `idx < self.size()` precondition.
                kani::assume(idx < iter.size_hint().0);
                // Save observable iterator state before random access.
                let size_before = iter.size_hint();
                assert!(iter.iter.is_some());

                // Call the target `Fuse<I>` implementation through the trait path.
                let result =
                    unsafe { crate::iter::Iterator::__iterator_get_unchecked(&mut iter, idx) };

                // Check that the target forwarded `idx` exactly.
                assert_eq!(observed_idx.get(), idx);
                // Check that the inner item was forwarded unchanged.
                assert_eq!(result, value);
                // Check that random access kept the inner iterator active.
                assert!(iter.iter.is_some());
                // Check that random access did not consume the iterator.
                assert_eq!(iter.size_hint(), size_before);
            }
        };
    }

    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_i8, i8);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_i16, i16);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_i32, i32);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_i64, i64);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_i128, i128);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_u8, u8);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_u16, u16);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_u32, u32);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_u64, u64);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_u128, u128);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_array, [u8; 4]);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_bool, bool);
    generate_fuse_get_unchecked_harness!(harness_fuse_get_unchecked_unit, ());
}
