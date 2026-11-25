use safety::requires;

use crate::cmp;
use crate::fmt::{self, Debug};
use crate::iter::{FusedIterator, InPlaceIterable, SourceIter, TrustedFused, TrustedLen};
#[cfg(kani)]
use crate::kani;
use crate::num::NonZero;

/// An iterator that iterates two other iterators simultaneously.
///
/// This `struct` is created by [`zip`] or [`Iterator::zip`].
/// See their documentation for more.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Zip<A, B> {
    a: A,
    b: B,
    // index, len and a_len are only used by the specialized version of zip
    index: usize,
    len: usize,
}
impl<A: Iterator, B: Iterator> Zip<A, B> {
    pub(in crate::iter) fn new(a: A, b: B) -> Zip<A, B> {
        ZipImpl::new(a, b)
    }
    fn super_nth(&mut self, mut n: usize) -> Option<(A::Item, B::Item)> {
        #[cfg_attr(
            kani,
            kani::loop_invariant(
                self.index <= self.len
                    && self.len <= self.a.size_hint().0
                    && self.len <= self.b.size_hint().0
            )
        )]
        #[cfg_attr(
            kani,
            kani::loop_modifies(
                &mut self.a,
                &mut self.b,
                &mut self.index,
                &mut n
            )
        )]
        while let Some(x) = Iterator::next(self) {
            if n == 0 {
                return Some(x);
            }
            n -= 1;
        }
        None
    }
}

/// Converts the arguments to iterators and zips them.
///
/// See the documentation of [`Iterator::zip`] for more.
///
/// # Examples
///
/// ```
/// use std::iter::zip;
///
/// let xs = [1, 2, 3];
/// let ys = [4, 5, 6];
///
/// let mut iter = zip(xs, ys);
///
/// assert_eq!(iter.next().unwrap(), (1, 4));
/// assert_eq!(iter.next().unwrap(), (2, 5));
/// assert_eq!(iter.next().unwrap(), (3, 6));
/// assert!(iter.next().is_none());
///
/// // Nested zips are also possible:
/// let zs = [7, 8, 9];
///
/// let mut iter = zip(zip(xs, ys), zs);
///
/// assert_eq!(iter.next().unwrap(), ((1, 4), 7));
/// assert_eq!(iter.next().unwrap(), ((2, 5), 8));
/// assert_eq!(iter.next().unwrap(), ((3, 6), 9));
/// assert!(iter.next().is_none());
/// ```
#[stable(feature = "iter_zip", since = "1.59.0")]
pub fn zip<A, B>(a: A, b: B) -> Zip<A::IntoIter, B::IntoIter>
where
    A: IntoIterator,
    B: IntoIterator,
{
    ZipImpl::new(a.into_iter(), b.into_iter())
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A, B> Iterator for Zip<A, B>
where
    A: Iterator,
    B: Iterator,
{
    type Item = (A::Item, B::Item);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        ZipImpl::next(self)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        ZipImpl::size_hint(self)
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        ZipImpl::nth(self, n)
    }

    #[inline]
    fn fold<Acc, F>(self, init: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        ZipImpl::fold(self, init, f)
    }

    #[inline]
    #[requires(idx < self.size_hint().0)]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: `ZipImpl::__iterator_get_unchecked` has same safety
        // requirements as `Iterator::__iterator_get_unchecked`.
        unsafe { ZipImpl::get_unchecked(self, idx) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A, B> DoubleEndedIterator for Zip<A, B>
where
    A: DoubleEndedIterator + ExactSizeIterator,
    B: DoubleEndedIterator + ExactSizeIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<(A::Item, B::Item)> {
        ZipImpl::next_back(self)
    }
}

// Zip specialization trait
trait ZipImpl<A, B> {
    type Item;
    fn new(a: A, b: B) -> Self;
    fn next(&mut self) -> Option<Self::Item>;
    fn size_hint(&self) -> (usize, Option<usize>);
    fn nth(&mut self, n: usize) -> Option<Self::Item>;
    fn next_back(&mut self) -> Option<Self::Item>
    where
        A: DoubleEndedIterator + ExactSizeIterator,
        B: DoubleEndedIterator + ExactSizeIterator;
    fn fold<Acc, F>(self, init: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc;
    // This has the same safety requirements as `Iterator::__iterator_get_unchecked`
    unsafe fn get_unchecked(&mut self, idx: usize) -> <Self as Iterator>::Item
    where
        Self: Iterator + TrustedRandomAccessNoCoerce;
}

// Work around limitations of specialization, requiring `default` impls to be repeated
// in intermediary impls.
macro_rules! zip_impl_general_defaults {
    () => {
        default fn new(a: A, b: B) -> Self {
            Zip {
                a,
                b,
                index: 0, // unused
                len: 0,   // unused
            }
        }

        #[inline]
        default fn next(&mut self) -> Option<(A::Item, B::Item)> {
            let x = self.a.next()?;
            let y = self.b.next()?;
            Some((x, y))
        }

        #[inline]
        default fn nth(&mut self, n: usize) -> Option<Self::Item> {
            self.super_nth(n)
        }

        #[inline]
        default fn next_back(&mut self) -> Option<(A::Item, B::Item)>
        where
            A: DoubleEndedIterator + ExactSizeIterator,
            B: DoubleEndedIterator + ExactSizeIterator,
        {
            // The function body below only uses `self.a/b.len()` and `self.a/b.next_back()`
            // and doesn’t call `next_back` too often, so this implementation is safe in
            // the `TrustedRandomAccessNoCoerce` specialization

            let a_sz = self.a.len();
            let b_sz = self.b.len();
            if a_sz != b_sz {
                // Adjust a, b to equal length
                if a_sz > b_sz {
                    for _ in 0..a_sz - b_sz {
                        self.a.next_back();
                    }
                } else {
                    for _ in 0..b_sz - a_sz {
                        self.b.next_back();
                    }
                }
            }
            match (self.a.next_back(), self.b.next_back()) {
                (Some(x), Some(y)) => Some((x, y)),
                (None, None) => None,
                _ => unreachable!(),
            }
        }
    };
}

// General Zip impl
impl<A, B> ZipImpl<A, B> for Zip<A, B>
where
    A: Iterator,
    B: Iterator,
{
    type Item = (A::Item, B::Item);

    zip_impl_general_defaults! {}

    #[inline]
    default fn size_hint(&self) -> (usize, Option<usize>) {
        let (a_lower, a_upper) = self.a.size_hint();
        let (b_lower, b_upper) = self.b.size_hint();

        let lower = cmp::min(a_lower, b_lower);

        let upper = match (a_upper, b_upper) {
            (Some(x), Some(y)) => Some(cmp::min(x, y)),
            (Some(x), None) => Some(x),
            (None, Some(y)) => Some(y),
            (None, None) => None,
        };

        (lower, upper)
    }

    default unsafe fn get_unchecked(&mut self, _idx: usize) -> <Self as Iterator>::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        unreachable!("Always specialized");
    }

    #[inline]
    default fn fold<Acc, F>(self, init: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        SpecFold::spec_fold(self, init, f)
    }
}

impl<A, B> ZipImpl<A, B> for Zip<A, B>
where
    A: TrustedRandomAccessNoCoerce + Iterator,
    B: TrustedRandomAccessNoCoerce + Iterator,
{
    zip_impl_general_defaults! {}

    #[inline]
    default fn size_hint(&self) -> (usize, Option<usize>) {
        let size = cmp::min(self.a.size(), self.b.size());
        (size, Some(size))
    }

    #[inline]
    #[requires(idx < TrustedRandomAccessNoCoerce::size(self))]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> <Self as Iterator>::Item {
        let idx = self.index + idx;
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        unsafe { (self.a.__iterator_get_unchecked(idx), self.b.__iterator_get_unchecked(idx)) }
    }

    #[inline]
    fn fold<Acc, F>(mut self, init: Acc, mut f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut accum = init;
        let len = ZipImpl::size_hint(&self).0;
        #[cfg_attr(
            kani,
            kani::loop_invariant(
                kani::index <= len
                    && len <= ZipImpl::size_hint(&self).0
                    && self.index <= self.a.size()
                    && len <= self.a.size() - self.index
                    && self.index <= self.b.size()
                    && len <= self.b.size() - self.index
            )
        )]
        #[cfg_attr(kani, kani::loop_modifies(&self, &accum, &f))]
        for i in 0..len {
            // SAFETY: since Self: TrustedRandomAccessNoCoerce we can trust the size-hint to
            // calculate the length and then use that to do unchecked iteration.
            // fold consumes the iterator so we don't need to fixup any state.
            unsafe {
                accum = f(accum, self.get_unchecked(i));
            }
        }
        accum
    }
}

impl<A, B> ZipImpl<A, B> for Zip<A, B>
where
    A: TrustedRandomAccess + Iterator,
    B: TrustedRandomAccess + Iterator,
{
    fn new(a: A, b: B) -> Self {
        let len = cmp::min(a.size(), b.size());
        Zip { a, b, index: 0, len }
    }

    #[inline]
    fn next(&mut self) -> Option<(A::Item, B::Item)> {
        if self.index < self.len {
            let i = self.index;
            // since get_unchecked executes code which can panic we increment the counters beforehand
            // so that the same index won't be accessed twice, as required by TrustedRandomAccess
            self.index += 1;
            // SAFETY: `i` is smaller than `self.len`, thus smaller than `self.a.len()` and `self.b.len()`
            unsafe {
                Some((self.a.__iterator_get_unchecked(i), self.b.__iterator_get_unchecked(i)))
            }
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len - self.index;
        (len, Some(len))
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let delta = cmp::min(n, self.len - self.index);
        let end = self.index + delta;
        #[cfg_attr(
            kani,
            kani::loop_invariant(
                self.index <= end
                    && end <= self.len
                    && self.len <= self.a.size()
                    && self.len <= self.b.size()
            )
        )]
        #[cfg_attr(
            kani,
            kani::loop_modifies(&mut self.index, &mut self.a, &mut self.b)
        )]
        while self.index < end {
            let i = self.index;
            // since get_unchecked executes code which can panic we increment the counters beforehand
            // so that the same index won't be accessed twice, as required by TrustedRandomAccess
            self.index += 1;
            if A::MAY_HAVE_SIDE_EFFECT {
                // SAFETY: the usage of `cmp::min` to calculate `delta`
                // ensures that `end` is smaller than or equal to `self.len`,
                // so `i` is also smaller than `self.len`.
                unsafe {
                    self.a.__iterator_get_unchecked(i);
                }
            }
            if B::MAY_HAVE_SIDE_EFFECT {
                // SAFETY: same as above.
                unsafe {
                    self.b.__iterator_get_unchecked(i);
                }
            }
        }

        self.super_nth(n - delta)
    }

    #[inline]
    fn next_back(&mut self) -> Option<(A::Item, B::Item)>
    where
        A: DoubleEndedIterator + ExactSizeIterator,
        B: DoubleEndedIterator + ExactSizeIterator,
    {
        // No effects when the iterator is exhausted, to reduce the number of
        // cases the unsafe code has to handle.
        // See #137255 for a case where where too many epicycles lead to unsoundness.
        if self.index < self.len {
            let old_len = self.len;

            // since get_unchecked and the side-effecting code can execute user code
            // which can panic we decrement the counter beforehand
            // so that the same index won't be accessed twice, as required by TrustedRandomAccess.
            // Additionally this will ensure that the side-effects code won't run a second time.
            self.len -= 1;

            // Adjust a, b to equal length if we're iterating backwards.
            if A::MAY_HAVE_SIDE_EFFECT || B::MAY_HAVE_SIDE_EFFECT {
                // note if some forward-iteration already happened then these aren't the real
                // remaining lengths of the inner iterators, so we have to relate them to
                // Zip's internal length-tracking.
                let sz_a = self.a.size();
                let sz_b = self.b.size();
                // This condition can and must only be true on the first `next_back` call,
                // otherwise we will break the restriction on calls to `self.next_back()`
                // after calling `get_unchecked()`.
                if sz_a != sz_b && (old_len == sz_a || old_len == sz_b) {
                    if A::MAY_HAVE_SIDE_EFFECT && sz_a > old_len {
                        for _ in 0..sz_a - old_len {
                            self.a.next_back();
                        }
                    }
                    if B::MAY_HAVE_SIDE_EFFECT && sz_b > old_len {
                        for _ in 0..sz_b - old_len {
                            self.b.next_back();
                        }
                    }
                    debug_assert_eq!(self.a.size(), self.b.size());
                }
            }
            let i = self.len;
            // SAFETY: `i` is smaller than the previous value of `self.len`,
            // which is also smaller than or equal to `self.a.len()` and `self.b.len()`
            unsafe {
                Some((self.a.__iterator_get_unchecked(i), self.b.__iterator_get_unchecked(i)))
            }
        } else {
            None
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A, B> ExactSizeIterator for Zip<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator,
{
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<A, B> TrustedRandomAccess for Zip<A, B>
where
    A: TrustedRandomAccess,
    B: TrustedRandomAccess,
{
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<A, B> TrustedRandomAccessNoCoerce for Zip<A, B>
where
    A: TrustedRandomAccessNoCoerce,
    B: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = A::MAY_HAVE_SIDE_EFFECT || B::MAY_HAVE_SIDE_EFFECT;
}

#[stable(feature = "fused", since = "1.26.0")]
impl<A, B> FusedIterator for Zip<A, B>
where
    A: FusedIterator,
    B: FusedIterator,
{
}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<A, B> TrustedFused for Zip<A, B>
where
    A: TrustedFused,
    B: TrustedFused,
{
}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<A, B> TrustedLen for Zip<A, B>
where
    A: TrustedLen,
    B: TrustedLen,
{
}

// Arbitrarily selects the left side of the zip iteration as extractable "source"
// it would require negative trait bounds to be able to try both
#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<A, B> SourceIter for Zip<A, B>
where
    A: SourceIter,
{
    type Source = A::Source;

    #[inline]
    unsafe fn as_inner(&mut self) -> &mut A::Source {
        // SAFETY: unsafe function forwarding to unsafe function with the same requirements
        unsafe { SourceIter::as_inner(&mut self.a) }
    }
}

// Since SourceIter forwards the left hand side we do the same here
#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<A: InPlaceIterable, B> InPlaceIterable for Zip<A, B> {
    const EXPAND_BY: Option<NonZero<usize>> = A::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = A::MERGE_BY;
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<A: Debug, B: Debug> Debug for Zip<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        ZipFmt::fmt(self, f)
    }
}

trait ZipFmt<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<A: Debug, B: Debug> ZipFmt<A, B> for Zip<A, B> {
    default fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Zip").field("a", &self.a).field("b", &self.b).finish()
    }
}

impl<A: Debug + TrustedRandomAccessNoCoerce, B: Debug + TrustedRandomAccessNoCoerce> ZipFmt<A, B>
    for Zip<A, B>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // It's *not safe* to call fmt on the contained iterators, since once
        // we start iterating they're in strange, potentially unsafe, states.
        f.debug_struct("Zip").finish()
    }
}

/// An iterator whose items are random-accessible efficiently
///
/// # Safety
///
/// The iterator's `size_hint` must be exact and cheap to call.
///
/// `TrustedRandomAccessNoCoerce::size` may not be overridden.
///
/// All subtypes and all supertypes of `Self` must also implement `TrustedRandomAccess`.
/// In particular, this means that types with non-invariant parameters usually can not have
/// an impl for `TrustedRandomAccess` that depends on any trait bounds on such parameters, except
/// for bounds that come from the respective struct/enum definition itself, or bounds involving
/// traits that themselves come with a guarantee similar to this one.
///
/// If `Self: ExactSizeIterator` then `self.len()` must always produce results consistent
/// with `self.size()`.
///
/// If `Self: Iterator`, then `<Self as Iterator>::__iterator_get_unchecked(&mut self, idx)`
/// must be safe to call provided the following conditions are met.
///
/// 1. `0 <= idx` and `idx < self.size()`.
/// 2. If `Self: !Clone`, then `self.__iterator_get_unchecked(idx)` is never called with the same
///    index on `self` more than once.
/// 3. After `self.__iterator_get_unchecked(idx)` has been called, then `self.next_back()` will
///    only be called at most `self.size() - idx - 1` times. If `Self: Clone` and `self` is cloned,
///    then this number is calculated for `self` and its clone individually,
///    but `self.next_back()` calls that happened before the cloning count for both `self` and the clone.
/// 4. After `self.__iterator_get_unchecked(idx)` has been called, then only the following methods
///    will be called on `self` or on any new clones of `self`:
///     * `std::clone::Clone::clone`
///     * `std::iter::Iterator::size_hint`
///     * `std::iter::DoubleEndedIterator::next_back`
///     * `std::iter::ExactSizeIterator::len`
///     * `std::iter::Iterator::__iterator_get_unchecked`
///     * `std::iter::TrustedRandomAccessNoCoerce::size`
/// 5. If `Self` is a subtype of `T`, then `self` is allowed to be coerced
///    to `T`. If `self` is coerced to `T` after `self.__iterator_get_unchecked(idx)` has already
///    been called, then no methods except for the ones listed under 4. are allowed to be called
///    on the resulting value of type `T`, either. Multiple such coercion steps are allowed.
///    Regarding 2. and 3., the number of times `__iterator_get_unchecked(idx)` or `next_back()` is
///    called on `self` and the resulting value of type `T` (and on further coercion results with
///    super-supertypes) are added together and their sums must not exceed the specified bounds.
///
/// Further, given that these conditions are met, it must guarantee that:
///
/// * It does not change the value returned from `size_hint`
/// * It must be safe to call the methods listed above on `self` after calling
///   `self.__iterator_get_unchecked(idx)`, assuming that the required traits are implemented.
/// * It must also be safe to drop `self` after calling `self.__iterator_get_unchecked(idx)`.
/// * If `Self` is a subtype of `T`, then it must be safe to coerce `self` to `T`.
//
// FIXME: Clarify interaction with SourceIter/InPlaceIterable. Calling `SourceIter::as_inner`
// after `__iterator_get_unchecked` is supposed to be allowed.
#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
#[rustc_specialization_trait]
pub unsafe trait TrustedRandomAccess: TrustedRandomAccessNoCoerce {}

/// Like [`TrustedRandomAccess`] but without any of the requirements / guarantees around
/// coercions to supertypes after `__iterator_get_unchecked` (they aren’t allowed here!), and
/// without the requirement that subtypes / supertypes implement `TrustedRandomAccessNoCoerce`.
///
/// This trait was created in PR #85874 to fix soundness issue #85873 without performance regressions.
/// It is subject to change as we might want to build a more generally useful (for performance
/// optimizations) and more sophisticated trait or trait hierarchy that replaces or extends
/// [`TrustedRandomAccess`] and `TrustedRandomAccessNoCoerce`.
#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
#[rustc_specialization_trait]
pub unsafe trait TrustedRandomAccessNoCoerce: Sized {
    // Convenience method.
    fn size(&self) -> usize
    where
        Self: Iterator,
    {
        self.size_hint().0
    }
    /// `true` if getting an iterator element may have side effects.
    /// Remember to take inner iterators into account.
    const MAY_HAVE_SIDE_EFFECT: bool;
}

/// Like `Iterator::__iterator_get_unchecked`, but doesn't require the compiler to
/// know that `U: TrustedRandomAccess`.
///
/// ## Safety
///
/// Same requirements calling `get_unchecked` directly.
#[doc(hidden)]
#[inline]
pub(in crate::iter::adapters) unsafe fn try_get_unchecked<I>(it: &mut I, idx: usize) -> I::Item
where
    I: Iterator,
{
    // SAFETY: the caller must uphold the contract for
    // `Iterator::__iterator_get_unchecked`.
    unsafe { it.try_get_unchecked(idx) }
}

unsafe trait SpecTrustedRandomAccess: Iterator {
    /// If `Self: TrustedRandomAccess`, it must be safe to call
    /// `Iterator::__iterator_get_unchecked(self, index)`.
    unsafe fn try_get_unchecked(&mut self, index: usize) -> Self::Item;
}

unsafe impl<I: Iterator> SpecTrustedRandomAccess for I {
    default unsafe fn try_get_unchecked(&mut self, _: usize) -> Self::Item {
        panic!("Should only be called on TrustedRandomAccess iterators");
    }
}

unsafe impl<I: Iterator + TrustedRandomAccessNoCoerce> SpecTrustedRandomAccess for I {
    #[inline]
    unsafe fn try_get_unchecked(&mut self, index: usize) -> Self::Item {
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        unsafe { self.__iterator_get_unchecked(index) }
    }
}

trait SpecFold: Iterator {
    fn spec_fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B;
}

impl<A: Iterator, B: Iterator> SpecFold for Zip<A, B> {
    // Adapted from default impl from the Iterator trait
    #[inline]
    default fn spec_fold<Acc, F>(mut self, init: Acc, mut f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut accum = init;
        while let Some(x) = ZipImpl::next(&mut self) {
            accum = f(accum, x);
        }
        accum
    }
}

impl<A: TrustedLen, B: TrustedLen> SpecFold for Zip<A, B> {
    #[inline]
    fn spec_fold<Acc, F>(mut self, init: Acc, mut f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut accum = init;
        loop {
            let (upper, more) = if let Some(upper) = ZipImpl::size_hint(&self).1 {
                (upper, false)
            } else {
                // Per TrustedLen contract a None upper bound means more than usize::MAX items
                (usize::MAX, true)
            };

            for _ in 0..upper {
                let pair =
                    // SAFETY: TrustedLen guarantees that at least `upper` many items are available
                    // therefore we know they can't be None
                    unsafe { (self.a.next().unwrap_unchecked(), self.b.next().unwrap_unchecked()) };
                accum = f(accum, pair);
            }

            if !more {
                break;
            }
        }
        accum
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    // Harnesses for `__iterator_get_unchecked` for Zip.
    macro_rules! generate_zip_iterator_get_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(
                            <Zip<
                                crate::iter::Map<crate::ops::Range<usize>, fn(usize) -> $ty>,
                                crate::iter::Map<crate::ops::Range<usize>, fn(usize) -> $ty>,
                            > as crate::iter::Iterator>::__iterator_get_unchecked
                        )]
            pub fn $name() {
                let left_len: usize = kani::any();
                let right_len: usize = kani::any();
                let index: usize = kani::any();
                let idx: usize = kani::any();
                let left_value: $ty = kani::any();
                let right_value: $ty = kani::any();
                let left = (0..left_len).map(move |_| left_value);
                let right = (0..right_len).map(move |_| right_value);
                let mut zip = Zip::new(left, right);
                zip.index = index.min(zip.len);
                let _ = unsafe { Iterator::__iterator_get_unchecked(&mut zip, idx) };
                let remaining = zip.len - zip.index;
                kani::cover(zip.index == 0 && idx == 0, "first element");
                kani::cover(zip.index > 0 && idx == 0, "first element after a prefix");
                kani::cover(idx > 0 && idx < remaining - 1, "interior element");
                kani::cover(idx == remaining - 1, "last element");
                kani::cover(left_len < right_len, "left iterator is shorter");
                kani::cover(left_len > right_len, "right iterator is shorter");
                kani::cover(
                    left_len == usize::MAX && right_len == usize::MAX && idx == usize::MAX - 1,
                    "last element at the maximum logical length",
                );
            }
        };
    }

    #[kani::proof_for_contract(
        <Zip<
            crate::ops::Range<usize>,
            crate::ops::Range<usize>,
        > as crate::iter::Iterator>::__iterator_get_unchecked
    )]
    fn harness_zip_iterator_get_unchecked_unbounded() {
        let left_len: usize = kani::any();
        let right_len: usize = kani::any();
        let index: usize = kani::any();
        let idx: usize = kani::any();
        let mut zip = Zip::new(0..left_len, 0..right_len);
        zip.len = kani::any::<usize>().min(zip.len);
        zip.index = index.min(zip.len);
        let _ = unsafe { Iterator::__iterator_get_unchecked(&mut zip, idx) };
        let remaining = zip.len - zip.index;
        kani::cover(zip.index == 0 && idx == 0, "first element");
        kani::cover(zip.index > 0 && idx == 0, "first element after a prefix");
        kani::cover(idx > 0 && idx < remaining - 1, "interior element");
        kani::cover(idx == remaining - 1, "last element");
        kani::cover(zip.len < left_len.min(right_len), "access after consuming from the back");
        kani::cover(
            left_len == usize::MAX && right_len == usize::MAX && idx == usize::MAX - 1,
            "last element at the maximum logical length",
        );
    }

    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_i8, i8);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_i16, i16);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_i32, i32);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_i64, i64);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_i128, i128);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_u8, u8);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_u16, u16);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_u32, u32);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_u64, u64);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_u128, u128);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_array, [u8; 4]);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_bool, bool);
    generate_zip_iterator_get_unchecked_harness!(harness_zip_iterator_get_unchecked_unit, ());

    // Harnesses for `get_unchecked` for ZipImpl.
    macro_rules! generate_zip_get_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(
                <Zip<
                    crate::iter::Map<crate::ops::Range<usize>, fn(usize) -> (usize, $ty)>,
                    crate::iter::Map<crate::ops::Range<usize>, fn(usize) -> (usize, $ty)>,
                > as ZipImpl<
                    crate::iter::Map<crate::ops::Range<usize>, fn(usize) -> (usize, $ty)>,
                    crate::iter::Map<crate::ops::Range<usize>, fn(usize) -> (usize, $ty)>,
                >>::get_unchecked
            )]
            pub fn $name() {
                let left_len: usize = kani::any();
                let right_len: usize = kani::any();
                let index: usize = kani::any();
                let idx: usize = kani::any();
                let left_value: $ty = kani::any();
                let right_value: $ty = kani::any();
                let left = (0..left_len).map(move |position| (position, left_value));
                let right = (0..right_len).map(move |position| (position, right_value));
                let mut zip = Zip::new(left, right);
                zip.index = index.min(zip.len);
                let _ = unsafe { ZipImpl::get_unchecked(&mut zip, idx) };
                let remaining = zip.len - zip.index;
                kani::cover(zip.index == 0 && idx == 0, "first element");
                kani::cover(zip.index > 0 && idx == 0, "first element after a prefix");
                kani::cover(idx > 0 && idx < remaining - 1, "interior element");
                kani::cover(idx == remaining - 1, "last element");
                kani::cover(left_len < right_len, "left iterator is shorter");
                kani::cover(left_len > right_len, "right iterator is shorter");
                kani::cover(zip.index == usize::MAX - 1 && idx == 0, "maximum valid offset");
                kani::cover(
                    left_len == usize::MAX && right_len == usize::MAX && idx == usize::MAX - 1,
                    "last element at the maximum logical length",
                );
            }
        };
    }

    #[kani::proof_for_contract(
        <Zip<
            crate::ops::Range<usize>,
            crate::ops::Range<usize>,
        > as ZipImpl<
            crate::ops::Range<usize>,
            crate::ops::Range<usize>,
        >>::get_unchecked
    )]
    fn harness_zip_get_unchecked_unbounded() {
        let left_len: usize = kani::any();
        let right_len: usize = kani::any();
        let index: usize = kani::any();
        let idx: usize = kani::any();
        let mut zip = Zip::new(0..left_len, 0..right_len);
        // For ranges, front/back consumption changes only index/len.
        zip.len = kani::any::<usize>().min(zip.len);
        zip.index = index.min(zip.len);
        let _ = unsafe { ZipImpl::get_unchecked(&mut zip, idx) };
        let remaining = zip.len - zip.index;
        kani::cover(zip.index == 0 && idx == 0, "first element");
        kani::cover(zip.index > 0 && idx == 0, "first element after a prefix");
        kani::cover(idx > 0 && idx < remaining - 1, "interior element");
        kani::cover(idx == remaining - 1, "last element");
        kani::cover(zip.len < left_len.min(right_len), "access after consuming from the back");
        kani::cover(zip.index == usize::MAX - 1 && idx == 0, "maximum valid offset");
        kani::cover(
            left_len == usize::MAX && right_len == usize::MAX && idx == usize::MAX - 1,
            "last element at the maximum logical length",
        );
    }

    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_i8, i8);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_i16, i16);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_i32, i32);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_i64, i64);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_i128, i128);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_u8, u8);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_u16, u16);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_u32, u32);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_u64, u64);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_u128, u128);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_array, [u8; 4]);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_bool, bool);
    generate_zip_get_unchecked_harness!(harness_zip_get_unchecked_unit, ());

    // Harnesses for `fold` for ZipImpl.
    macro_rules! generate_zip_fold_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            fn $name() {
                // Generate independent symbolic lengths for both sides.
                let left_len: usize = kani::any();
                let right_len: usize = kani::any();

                // Generate independent symbolic payloads for both sides.
                let left_value: $ty = kani::any();
                let right_value: $ty = kani::any();

                // Map preserves full trusted random access with unbounded lengths.
                let left = (0..left_len).map(move |_| left_value);
                let right = (0..right_len).map(move |_| right_value);
                let mut zip = Zip::new(left, right);

                // Model any reachable offset in the full trusted-random-access Zip.
                let index: usize = kani::any();
                kani::assume(index <= zip.len);
                zip.index = index;

                // Call the specialized safe function directly.
                ZipImpl::fold(zip, (), |(), _pair| ());
            }
        };
    }

    generate_zip_fold_harness!(harness_zip_fold_i8, i8);
    generate_zip_fold_harness!(harness_zip_fold_i16, i16);
    generate_zip_fold_harness!(harness_zip_fold_i32, i32);
    generate_zip_fold_harness!(harness_zip_fold_i64, i64);
    generate_zip_fold_harness!(harness_zip_fold_i128, i128);
    generate_zip_fold_harness!(harness_zip_fold_u8, u8);
    generate_zip_fold_harness!(harness_zip_fold_u16, u16);
    generate_zip_fold_harness!(harness_zip_fold_u32, u32);
    generate_zip_fold_harness!(harness_zip_fold_u64, u64);
    generate_zip_fold_harness!(harness_zip_fold_u128, u128);
    generate_zip_fold_harness!(harness_zip_fold_bool, bool);
    generate_zip_fold_harness!(harness_zip_fold_unit, ());
    generate_zip_fold_harness!(harness_zip_fold_array, [u8; 4]);

    // Harnesses for `next` for ZipImpl.
    macro_rules! generate_zip_next_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            fn $name() {
                // Generate independent symbolic lengths for both sides.
                let left_len: usize = kani::any();
                let right_len: usize = kani::any();

                // Generate independent symbolic payloads for both sides.
                let left_value: $ty = kani::any();
                let right_value: $ty = kani::any();

                // Map over Range preserves TrustedRandomAccess.
                let left = (0..left_len).map(move |_| left_value);
                let right = (0..right_len).map(move |_| right_value);
                let mut zip = Zip::new(left, right);

                // Model any reachable offset in the full trusted-random-access Zip.
                let index: usize = kani::any();
                kani::assume(index <= zip.len);
                zip.index = index;

                // Call the specialized safe function directly.
                ZipImpl::next(&mut zip);
            }
        };
    }

    generate_zip_next_harness!(harness_zip_next_i8, i8);
    generate_zip_next_harness!(harness_zip_next_i16, i16);
    generate_zip_next_harness!(harness_zip_next_i32, i32);
    generate_zip_next_harness!(harness_zip_next_i64, i64);
    generate_zip_next_harness!(harness_zip_next_i128, i128);
    generate_zip_next_harness!(harness_zip_next_u8, u8);
    generate_zip_next_harness!(harness_zip_next_u16, u16);
    generate_zip_next_harness!(harness_zip_next_u32, u32);
    generate_zip_next_harness!(harness_zip_next_u64, u64);
    generate_zip_next_harness!(harness_zip_next_u128, u128);
    generate_zip_next_harness!(harness_zip_next_bool, bool);
    generate_zip_next_harness!(harness_zip_next_unit, ());
    generate_zip_next_harness!(harness_zip_next_array, [u8; 4]);

    // Harnesses for `next` for ZipImpl.
    macro_rules! generate_zip_nth_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            fn $name() {
                // Generate independent symbolic lengths and the requested index.
                let left_len: usize = kani::any();
                let right_len: usize = kani::any();
                let n: usize = kani::any();

                // Generate independent symbolic payloads for both sides.
                let left_value: $ty = kani::any();
                let right_value: $ty = kani::any();

                // Map selects the full trusted-random-access specialization.
                let left = (0..left_len).map(move |_| left_value);
                let right = (0..right_len).map(move |_| right_value);
                let mut zip = Zip::new(left, right);

                // Model any state reachable by prior forward iteration.
                let index: usize = kani::any();
                kani::assume(index <= zip.len);
                zip.index = index;

                // Call the specialized safe function directly.
                ZipImpl::nth(&mut zip, n);
            }
        };
    }

    generate_zip_nth_harness!(harness_zip_nth_i8, i8);
    generate_zip_nth_harness!(harness_zip_nth_i16, i16);
    generate_zip_nth_harness!(harness_zip_nth_i32, i32);
    generate_zip_nth_harness!(harness_zip_nth_i64, i64);
    generate_zip_nth_harness!(harness_zip_nth_i128, i128);
    generate_zip_nth_harness!(harness_zip_nth_u8, u8);
    generate_zip_nth_harness!(harness_zip_nth_u16, u16);
    generate_zip_nth_harness!(harness_zip_nth_u32, u32);
    generate_zip_nth_harness!(harness_zip_nth_u64, u64);
    generate_zip_nth_harness!(harness_zip_nth_u128, u128);
    generate_zip_nth_harness!(harness_zip_nth_bool, bool);
    generate_zip_nth_harness!(harness_zip_nth_unit, ());
    generate_zip_nth_harness!(harness_zip_nth_array, [u8; 4]);

    // Harnesses for `next_back` for ZipImpl.
    #[kani::proof]
    fn harness_zip_next_back() {
        // Generate independent unbounded lengths.
        let left_len: usize = kani::any();
        let right_len: usize = kani::any();

        // Core Range iterators provide trusted random access.
        let left = 0..left_len;
        let right = 0..right_len;
        let mut zip = Zip::new(left, right);

        // Model any state reachable after prior forward iteration.
        let index: usize = kani::any();
        kani::assume(index <= zip.len);
        zip.index = index;

        // Call the specialized safe function directly.
        ZipImpl::next_back(&mut zip);
    }

    // Harnesses for `spec_fold` for ZipImpl.
    macro_rules! generate_zip_spec_fold_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            #[kani::unwind(8)]
            pub fn $name() {
                // Generate independent symbolic lengths, bounded for unwinding.
                let left_len: usize = kani::any();
                let right_len: usize = kani::any();
                kani::assume(left_len <= 4 && right_len <= 4);
                kani::cover(true, "bounded input is satisfiable");
                // Generate independent symbolic payloads.
                let left_value: $ty = kani::any();
                let right_value: $ty = kani::any();
                // Take<Repeat<T>> provides a finite TrustedLen iterator.
                let left = crate::iter::repeat(left_value).take(left_len);
                let right = crate::iter::repeat(right_value).take(right_len);
                let zip = Zip::new(left, right);
                // Exercise the real TrustedLen-specialized implementation.
                let count = SpecFold::spec_fold(zip, 0usize, |count, _pair| count + 1);
                // The fold must process exactly min(left_len, right_len) pairs.
                assert_eq!(count, left_len.min(right_len));
                kani::cover(left_len == 0 || right_len == 0, "empty zip");
                kani::cover(left_len < right_len, "left iterator is shorter");
                kani::cover(left_len > right_len, "right iterator is shorter");
                kani::cover(left_len == right_len && left_len > 0, "equal nonempty lengths");
                kani::cover(left_len == 4 && right_len == 4, "maximum bounded length");
            }
        };
    }

    generate_zip_spec_fold_harness!(harness_zip_spec_fold_i8, i8);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_i16, i16);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_i32, i32);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_i64, i64);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_i128, i128);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_u8, u8);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_u16, u16);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_u32, u32);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_u64, u64);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_u128, u128);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_bool, bool);
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_unit, ());
    generate_zip_spec_fold_harness!(harness_zip_spec_fold_array, [u8; 4]);
}
