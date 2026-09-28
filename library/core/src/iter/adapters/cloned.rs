use core::num::NonZero;

use safety::requires;

use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::adapters::{SourceIter, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
use crate::iter::{FusedIterator, InPlaceIterable, TrustedLen, UncheckedIterator};
#[cfg(kani)]
use crate::kani;
use crate::ops::Try;

/// An iterator that clones the elements of an underlying iterator.
///
/// This `struct` is created by the [`cloned`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`cloned`]: Iterator::cloned
/// [`Iterator`]: trait.Iterator.html
#[stable(feature = "iter_cloned", since = "1.1.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone, Debug)]
pub struct Cloned<I> {
    it: I,
}

impl<I> Cloned<I> {
    pub(in crate::iter) fn new(it: I) -> Cloned<I> {
        Cloned { it }
    }
}

fn clone_try_fold<T: Clone, Acc, R>(mut f: impl FnMut(Acc, T) -> R) -> impl FnMut(Acc, &T) -> R {
    move |acc, elt| f(acc, elt.clone())
}

#[stable(feature = "iter_cloned", since = "1.1.0")]
impl<'a, I, T: 'a> Iterator for Cloned<I>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.it.next().cloned()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }

    fn try_fold<B, F, R>(&mut self, init: B, f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        self.it.try_fold(init, clone_try_fold(f))
    }

    fn fold<Acc, F>(self, init: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        self.it.map(T::clone).fold(init, f)
    }

    #[requires(idx < self.it.size_hint().0)]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> T
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        unsafe { try_get_unchecked(&mut self.it, idx).clone() }
    }
}

#[stable(feature = "iter_cloned", since = "1.1.0")]
impl<'a, I, T: 'a> DoubleEndedIterator for Cloned<I>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: Clone,
{
    fn next_back(&mut self) -> Option<T> {
        self.it.next_back().cloned()
    }

    fn try_rfold<B, F, R>(&mut self, init: B, f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        self.it.try_rfold(init, clone_try_fold(f))
    }

    fn rfold<Acc, F>(self, init: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        self.it.map(T::clone).rfold(init, f)
    }
}

#[stable(feature = "iter_cloned", since = "1.1.0")]
impl<'a, I, T: 'a> ExactSizeIterator for Cloned<I>
where
    I: ExactSizeIterator<Item = &'a T>,
    T: Clone,
{
    fn len(&self) -> usize {
        self.it.len()
    }

    fn is_empty(&self) -> bool {
        self.it.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<'a, I, T: 'a> FusedIterator for Cloned<I>
where
    I: FusedIterator<Item = &'a T>,
    T: Clone,
{
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccess for Cloned<I> where I: TrustedRandomAccess {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccessNoCoerce for Cloned<I>
where
    I: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = true;
}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<'a, I, T: 'a> TrustedLen for Cloned<I>
where
    I: TrustedLen<Item = &'a T>,
    T: Clone,
{
}

impl<'a, I, T: 'a> UncheckedIterator for Cloned<I>
where
    I: UncheckedIterator<Item = &'a T>,
    T: Clone,
{
    #[cfg_attr(kani, kani::requires(self.size_hint().0 != 0))]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn next_unchecked(&mut self) -> T {
        // SAFETY: `Cloned` is 1:1 with the inner iterator, so if the caller promised
        // that there's an element left, the inner iterator has one too.
        let item = unsafe { self.it.next_unchecked() };
        item.clone()
    }
}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<I: Default> Default for Cloned<I> {
    /// Creates a `Cloned` iterator from the default value of `I`
    /// ```
    /// # use core::slice;
    /// # use core::iter::Cloned;
    /// let iter: Cloned<slice::Iter<'_, u8>> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        Self::new(Default::default())
    }
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I> SourceIter for Cloned<I>
where
    I: SourceIter,
{
    type Source = I::Source;

    #[inline]
    unsafe fn as_inner(&mut self) -> &mut I::Source {
        // SAFETY: unsafe function forwarding to unsafe function with the same requirements
        unsafe { SourceIter::as_inner(&mut self.it) }
    }
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I: InPlaceIterable> InPlaceIterable for Cloned<I> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    // Harnesses for `__iterator_get_unchecked` for Cloned.
    // Use a regular proof because `proof_for_contract` cannot resolve this trait method path.
    macro_rules! generate_cloned_get_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Generate a symbolic logical length with no explicit upper bound.
                let len: usize = kani::any();
                // Generate a symbolic access index.
                let idx: usize = kani::any();
                // Generate an arbitrary element to clone.
                let value: $ty = kani::any();
                // Record the index actually received by the inner iterator.
                let observed_idx = crate::cell::Cell::new(usize::MAX);

                // Build a lazy iterator of length `len` without allocating `len` elements.
                let source = (0..len).map(|i| {
                    // Save the index forwarded by the random-access operation.
                    observed_idx.set(i);
                    // Make the inner iterator's item type `&T`.
                    &value
                });
                // Construct the target `Cloned<I>` from the inner iterator.
                let mut iter = Cloned::new(source);
                // Express the target's `idx < self.size()` precondition.
                kani::assume(idx < iter.size_hint().0);
                // Save the iterator size before the call.
                let size_before = iter.size_hint();

                // Call the target `Cloned<I>` implementation through the trait path.
                let result =
                    unsafe { crate::iter::Iterator::__iterator_get_unchecked(&mut iter, idx) };

                // Check that the target forwarded `idx` exactly.
                assert_eq!(observed_idx.get(), idx);
                // Check that the returned value is the correct clone of the inner `&T`.
                assert_eq!(result, value);
                // Check that random access did not consume the iterator.
                assert_eq!(iter.size_hint(), size_before);
            }
        };
    }

    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_i8, i8);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_i16, i16);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_i32, i32);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_i64, i64);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_i128, i128);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_u8, u8);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_u16, u16);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_u32, u32);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_u64, u64);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_u128, u128);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_array, [u8; 4]);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_bool, bool);
    generate_cloned_get_unchecked_harness!(harness_cloned_iterator_get_unchecked_unit, ());

    // Harnesses for `next_unchecked` for Cloned.
    // Use a regular proof because `proof_for_contract` cannot resolve this trait method path.
    macro_rules! generate_cloned_next_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Generate an arbitrary element to clone.
                let value: $ty = kani::any();
                // Generate a symbolic logical length with no explicit upper bound.
                let len: usize = kani::any();
                // Build an exact-length iterator without allocating `len` elements.
                let source = crate::iter::repeat_n(&value, len);
                // Construct the target `Cloned<I>` from the inner iterator.
                let mut iter = Cloned::new(source);

                // Express the target's `self.size_hint().0 != 0` precondition.
                kani::assume(iter.size_hint().0 != 0);

                // Call the target `Cloned<I>` implementation through the trait path.
                let result = unsafe { UncheckedIterator::next_unchecked(&mut iter) };

                // Check that the returned value is the correct clone of the inner `&T`.
                assert_eq!(result, value);
                // Check that the call consumed exactly one element.
                assert_eq!(iter.size_hint(), (len - 1, Some(len - 1)));
            }
        };
    }

    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_i8, i8);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_i16, i16);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_i32, i32);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_i64, i64);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_i128, i128);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_u8, u8);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_u16, u16);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_u32, u32);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_u64, u64);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_u128, u128);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_array, [u8; 4]);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_bool, bool);
    generate_cloned_next_unchecked_harness!(harness_cloned_next_unchecked_unit, ());
}
