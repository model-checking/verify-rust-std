use safety::requires;

use crate::fmt;
use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::adapters::{SourceIter, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused, TrustedLen, UncheckedIterator};
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
    pub(in crate::iter) fn new(iter: I, f: F) -> Map<I, F> {
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

impl<B, I, F> UncheckedIterator for Map<I, F>
where
    I: UncheckedIterator,
    F: FnMut(I::Item) -> B,
{
    #[requires(self.iter.size_hint().0 > 0)]
    #[cfg_attr(kani, kani::modifies(self))]
    unsafe fn next_unchecked(&mut self) -> B {
        // SAFETY: `Map` is 1:1 with the inner iterator, so if the caller promised
        // that there's an element left, the inner iterator has one too.
        let item = unsafe { self.iter.next_unchecked() };
        (self.f)(item)
    }
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

    // Harnesses for `__iterator_get_unchecked` for Map
    // Use a regular proof because `proof_for_contract` cannot resolve this trait method path.
    macro_rules! generate_map_get_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Generate a symbolic logical length with no explicit upper bound.
                let len: usize = kani::any();
                // Generate a symbolic access index.
                let idx: usize = kani::any();
                // Generate arbitrary data captured by the mapping closure.
                let value: $ty = kani::any();
                // Record the inner item passed to the mapping closure.
                let observed_input = crate::cell::Cell::new(usize::MAX);
                // Count how many times the target invokes the mapping closure.
                let closure_calls = crate::cell::Cell::new(0usize);

                // Use the range item itself as the observable inner position.
                let source = 0..len;
                // Construct the target with a stateful, type-changing closure.
                let mut iter = Map::new(source, |position| {
                    observed_input.set(position);
                    closure_calls.set(closure_calls.get() + 1);
                    (value, position, closure_calls.get())
                });

                // Express the target's `idx < self.size()` precondition.
                kani::assume(idx < iter.size_hint().0);
                // Save the iterator size before random access.
                let size_before = iter.size_hint();

                // Call the target `Map<I, F>` implementation through the trait path.
                let result =
                    unsafe { crate::iter::Iterator::__iterator_get_unchecked(&mut iter, idx) };

                // Check that the target forwarded `idx` to the inner range exactly.
                assert_eq!(observed_input.get(), idx);
                // Check that the target invoked the mapping closure exactly once.
                assert_eq!(closure_calls.get(), 1);
                // Check the closure input, captured value, and stateful output.
                assert_eq!(result, (value, idx, 1));
                // Check that random access did not consume the iterator.
                assert_eq!(iter.size_hint(), size_before);
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

    // Harnesses for `next_unchecked` for Map
    // Use a regular proof because `proof_for_contract` cannot resolve this trait method path.
    macro_rules! generate_map_next_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Generate arbitrary data captured by the mapping closure.
                let value: $ty = kani::any();
                // Generate an arbitrary inner item.
                let inner_value: usize = kani::any();
                // Generate a symbolic logical length with no explicit upper bound.
                let len: usize = kani::any();
                // Record the inner item passed to the mapping closure.
                let observed_input = crate::cell::Cell::new(usize::MAX);
                // Count how many times the target invokes the mapping closure.
                let closure_calls = crate::cell::Cell::new(0usize);

                // Build an exact-length iterator without allocating `len` elements.
                let source = crate::iter::repeat_n(inner_value, len);
                // Construct the target with a stateful, type-changing closure.
                let mut iter = Map::new(source, |item| {
                    observed_input.set(item);
                    closure_calls.set(closure_calls.get() + 1);
                    (value, item, closure_calls.get())
                });

                // Express the target's non-empty precondition.
                kani::assume(iter.size_hint().0 > 0);

                // Call the target `Map<I, F>` implementation through the trait path.
                let result = unsafe { UncheckedIterator::next_unchecked(&mut iter) };

                // Check that the closure received the consumed inner item.
                assert_eq!(observed_input.get(), inner_value);
                // Check that the target invoked the mapping closure exactly once.
                assert_eq!(closure_calls.get(), 1);
                // Check the closure input, captured value, and stateful output.
                assert_eq!(result, (value, inner_value, 1));
                // Check that the target consumed exactly one inner element.
                assert_eq!(iter.size_hint(), (len - 1, Some(len - 1)));
            }
        };
    }

    generate_map_next_unchecked_harness!(harness_map_next_unchecked_i8, i8);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_i16, i16);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_i32, i32);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_i64, i64);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_i128, i128);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_u8, u8);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_u16, u16);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_u32, u32);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_u64, u64);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_u128, u128);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_array, [u8; 4]);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_bool, bool);
    generate_map_next_unchecked_harness!(harness_map_next_unchecked_unit, ());
}
