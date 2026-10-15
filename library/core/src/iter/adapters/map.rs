use safety::requires;

use crate::fmt;
use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::adapters::{SourceIter, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused, TrustedLen};
#[cfg(kani)]
use crate::kani;
use crate::num::NonZero;
use crate::ops::Try;

/// An iterator that maps the values of `iter` with `f`.
///
/// This `struct` is created by the [`map`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`map`]: Iterator::map
/// [`Iterator`]: trait.Iterator.html
///
/// # Notes about side effects
///
/// The [`map`] iterator implements [`DoubleEndedIterator`], meaning that
/// you can also [`map`] backwards:
///
/// ```rust
/// let v: Vec<i32> = [1, 2, 3].into_iter().map(|x| x + 1).rev().collect();
///
/// assert_eq!(v, [4, 3, 2]);
/// ```
///
/// [`DoubleEndedIterator`]: trait.DoubleEndedIterator.html
///
/// But if your closure has state, iterating backwards may act in a way you do
/// not expect. Let's go through an example. First, in the forward direction:
///
/// ```rust
/// let mut c = 0;
///
/// for pair in ['a', 'b', 'c'].into_iter()
///                                .map(|letter| { c += 1; (letter, c) }) {
///     println!("{pair:?}");
/// }
/// ```
///
/// This will print `('a', 1), ('b', 2), ('c', 3)`.
///
/// Now consider this twist where we add a call to `rev`. This version will
/// print `('c', 1), ('b', 2), ('a', 3)`. Note that the letters are reversed,
/// but the values of the counter still go in order. This is because `map()` is
/// still being called lazily on each item, but we are popping items off the
/// back of the vector now, instead of shifting them from the front.
///
/// ```rust
/// let mut c = 0;
///
/// for pair in ['a', 'b', 'c'].into_iter()
///                                .map(|letter| { c += 1; (letter, c) })
///                                .rev() {
///     println!("{pair:?}");
/// }
/// ```
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Clone)]
pub struct Map<I, F> {
    // Used for `SplitWhitespace` and `SplitAsciiWhitespace` `as_str` methods
    pub(crate) iter: I,
    f: F,
}

impl<I, F> Map<I, F> {
    pub(in crate::iter) const fn new(iter: I, f: F) -> Map<I, F> {
        Map { iter, f }
    }

    pub(crate) fn into_inner(self) -> I {
        self.iter
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<I: fmt::Debug, F> fmt::Debug for Map<I, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Map").field("iter", &self.iter).finish()
    }
}

fn map_fold<T, B, Acc>(
    mut f: impl FnMut(T) -> B,
    mut g: impl FnMut(Acc, B) -> Acc,
) -> impl FnMut(Acc, T) -> Acc {
    move |acc, elt| g(acc, f(elt))
}

fn map_try_fold<'a, T, B, Acc, R>(
    f: &'a mut impl FnMut(T) -> B,
    mut g: impl FnMut(Acc, B) -> R + 'a,
) -> impl FnMut(Acc, T) -> R + 'a {
    move |acc, elt| g(acc, f(elt))
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: Iterator, F> Iterator for Map<I, F>
where
    F: FnMut(I::Item) -> B,
{
    type Item = B;

    #[inline]
    fn next(&mut self) -> Option<B> {
        self.iter.next().map(&mut self.f)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn try_fold<Acc, G, R>(&mut self, init: Acc, g: G) -> R
    where
        Self: Sized,
        G: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_fold(init, map_try_fold(&mut self.f, g))
    }

    fn fold<Acc, G>(self, init: Acc, g: G) -> Acc
    where
        G: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.fold(init, map_fold(self.f, g))
    }

    #[inline]
    #[requires(idx < self.iter.size_hint().0)]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> B
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        unsafe { (self.f)(try_get_unchecked(&mut self.iter, idx)) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: DoubleEndedIterator, F> DoubleEndedIterator for Map<I, F>
where
    F: FnMut(I::Item) -> B,
{
    #[inline]
    fn next_back(&mut self) -> Option<B> {
        self.iter.next_back().map(&mut self.f)
    }

    fn try_rfold<Acc, G, R>(&mut self, init: Acc, g: G) -> R
    where
        Self: Sized,
        G: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_rfold(init, map_try_fold(&mut self.f, g))
    }

    fn rfold<Acc, G>(self, init: Acc, g: G) -> Acc
    where
        G: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.rfold(init, map_fold(self.f, g))
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: ExactSizeIterator, F> ExactSizeIterator for Map<I, F>
where
    F: FnMut(I::Item) -> B,
{
    fn len(&self) -> usize {
        self.iter.len()
    }

    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<B, I: FusedIterator, F> FusedIterator for Map<I, F> where F: FnMut(I::Item) -> B {}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<I: TrustedFused, F> TrustedFused for Map<I, F> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<B, I, F> TrustedLen for Map<I, F>
where
    I: TrustedLen,
    F: FnMut(I::Item) -> B,
{
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I, F> TrustedRandomAccess for Map<I, F> where I: TrustedRandomAccess {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I, F> TrustedRandomAccessNoCoerce for Map<I, F>
where
    I: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = true;
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I, F> SourceIter for Map<I, F>
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
unsafe impl<I: InPlaceIterable, F> InPlaceIterable for Map<I, F> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    // Harnesses for `__iterator_get_unchecked` for Map.
    macro_rules! generate_map_get_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(
                                        <Map<
                                            crate::ops::Range<usize>,
                                            fn(usize) -> ($ty, usize, usize),
                                        > as crate::iter::Iterator>::__iterator_get_unchecked
                                    )]
            pub fn $name() {
                let len: usize = kani::any();
                let idx: usize = kani::any();
                let value: $ty = kani::any();
                let initial_calls: usize = kani::any();
                let mut calls = initial_calls;
                let mut iter = Map::new(0..len, move |position| {
                    calls = calls.wrapping_add(1);
                    (value, position, calls)
                });
                let _ = unsafe { crate::iter::Iterator::__iterator_get_unchecked(&mut iter, idx) };
                kani::cover(idx == 0, "first element");
                kani::cover(idx > 0 && idx < len - 1, "interior element");
                kani::cover(idx == len - 1, "last element");
                kani::cover(initial_calls == usize::MAX, "wrapping closure state");
                kani::cover(
                    len == usize::MAX && idx == len - 1,
                    "last element at the maximum logical length",
                );
            }
        };
    }

    generate_map_get_unchecked_harness!(harness_map_get_unchecked_i8, i8);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_i16, i16);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_i32, i32);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_i64, i64);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_i128, i128);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_u8, u8);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_u16, u16);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_u32, u32);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_u64, u64);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_u128, u128);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_array, [u8; 4]);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_bool, bool);
    generate_map_get_unchecked_harness!(harness_map_get_unchecked_unit, ());
}
