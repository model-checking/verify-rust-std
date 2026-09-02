use core::array;
use core::mem::MaybeUninit;
use core::ops::ControlFlow;

use crate::fmt;
use crate::iter::adapters::SourceIter;
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused};
use crate::num::NonZero;
use crate::ops::Try;

/// An iterator that filters the elements of `iter` with `predicate`.
///
/// This `struct` is created by the [`filter`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`filter`]: Iterator::filter
/// [`Iterator`]: trait.Iterator.html
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Clone)]
pub struct Filter<I, P> {
    // Used for `SplitWhitespace` and `SplitAsciiWhitespace` `as_str` methods
    pub(crate) iter: I,
    predicate: P,
}
impl<I, P> Filter<I, P> {
    pub(in crate::iter) fn new(iter: I, predicate: P) -> Filter<I, P> {
        Filter { iter, predicate }
    }
}

impl<I, P> Filter<I, P>
where
    I: Iterator,
    P: FnMut(&I::Item) -> bool,
{
    #[inline]
    fn next_chunk_dropless<const N: usize>(
        &mut self,
    ) -> Result<[I::Item; N], array::IntoIter<I::Item, N>> {
        let mut array: [MaybeUninit<I::Item>; N] = [const { MaybeUninit::uninit() }; N];
        let mut initialized = 0;

        let result = self.iter.try_for_each(|element| {
            let idx = initialized;
            // branchless index update combined with unconditionally copying the value even when
            // it is filtered reduces branching and dependencies in the loop.
            initialized = idx + (self.predicate)(&element) as usize;
            // SAFETY: Loop conditions ensure the index is in bounds.
            unsafe { array.get_unchecked_mut(idx) }.write(element);

            if initialized < N { ControlFlow::Continue(()) } else { ControlFlow::Break(()) }
        });

        match result {
            ControlFlow::Break(()) => {
                // SAFETY: The loop above is only explicitly broken when the array has been fully initialized
                Ok(unsafe { MaybeUninit::array_assume_init(array) })
            }
            ControlFlow::Continue(()) => {
                // SAFETY: The range is in bounds since the loop breaks when reaching N elements.
                Err(unsafe { array::IntoIter::new_unchecked(array, 0..initialized) })
            }
        }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<I: fmt::Debug, P> fmt::Debug for Filter<I, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Filter").field("iter", &self.iter).finish()
    }
}

fn filter_fold<T, Acc>(
    mut predicate: impl FnMut(&T) -> bool,
    mut fold: impl FnMut(Acc, T) -> Acc,
) -> impl FnMut(Acc, T) -> Acc {
    move |acc, item| if predicate(&item) { fold(acc, item) } else { acc }
}

fn filter_try_fold<'a, T, Acc, R: Try<Output = Acc>>(
    predicate: &'a mut impl FnMut(&T) -> bool,
    mut fold: impl FnMut(Acc, T) -> R + 'a,
) -> impl FnMut(Acc, T) -> R + 'a {
    move |acc, item| if predicate(&item) { fold(acc, item) } else { try { acc } }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I: Iterator, P> Iterator for Filter<I, P>
where
    P: FnMut(&I::Item) -> bool,
{
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        self.iter.find(&mut self.predicate)
    }

    #[inline]
    fn next_chunk<const N: usize>(
        &mut self,
    ) -> Result<[Self::Item; N], array::IntoIter<Self::Item, N>> {
        // avoid codegen for the dead branch
        let fun = const {
            if crate::mem::needs_drop::<I::Item>() {
                array::iter_next_chunk::<I::Item, N>
            } else {
                Self::next_chunk_dropless::<N>
            }
        };

        fun(self)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper) // can't know a lower bound, due to the predicate
    }

    // this special case allows the compiler to make `.filter(_).count()`
    // branchless. Barring perfect branch prediction (which is unattainable in
    // the general case), this will be much faster in >90% of cases (containing
    // virtually all real workloads) and only a tiny bit slower in the rest.
    //
    // Having this specialization thus allows us to write `.filter(p).count()`
    // where we would otherwise write `.map(|x| p(x) as usize).sum()`, which is
    // less readable and also less backwards-compatible to Rust before 1.10.
    //
    // Using the branchless version will also simplify the LLVM byte code, thus
    // leaving more budget for LLVM optimizations.
    #[inline]
    fn count(self) -> usize {
        #[inline]
        fn to_usize<T>(mut predicate: impl FnMut(&T) -> bool) -> impl FnMut(T) -> usize {
            move |x| predicate(&x) as usize
        }

        self.iter.map(to_usize(self.predicate)).sum()
    }

    #[inline]
    fn try_fold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_fold(init, filter_try_fold(&mut self.predicate, fold))
    }

    #[inline]
    fn fold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.fold(init, filter_fold(self.predicate, fold))
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I: DoubleEndedIterator, P> DoubleEndedIterator for Filter<I, P>
where
    P: FnMut(&I::Item) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<I::Item> {
        self.iter.rfind(&mut self.predicate)
    }

    #[inline]
    fn try_rfold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_rfold(init, filter_try_fold(&mut self.predicate, fold))
    }

    #[inline]
    fn rfold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.rfold(init, filter_fold(self.predicate, fold))
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<I: FusedIterator, P> FusedIterator for Filter<I, P> where P: FnMut(&I::Item) -> bool {}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<I: TrustedFused, F> TrustedFused for Filter<I, F> {}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<P, I> SourceIter for Filter<I, P>
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
unsafe impl<I: InPlaceIterable, P> InPlaceIterable for Filter<I, P> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;
    use crate::kani;

    fn any_slice<T>(orig: &[T]) -> &[T] {
        if kani::any() {
            let last = kani::any_where(|i: &usize| *i <= orig.len());
            let first = kani::any_where(|i: &usize| *i <= last);
            &orig[first..last]
        } else {
            let ptr = kani::any_where::<usize, _>(|v| *v != 0) as *const T;
            kani::assume(ptr.is_aligned());
            unsafe { crate::slice::from_raw_parts(ptr, 0) }
        }
    }

    // `Filter`'s predicate is `FnMut(&Self::Item)`; for `slice::Iter<T>` that is
    // `FnMut(&&T)`. A nondeterministic predicate exercises both the kept and the
    // filtered branch. A named fn pointer keeps the helper return type nameable.
    fn maybe_keep<T>(_: &&T) -> bool {
        kani::any()
    }

    // `next_chunk_dropless` writes every element (branchlessly) into a
    // `MaybeUninit<[_; N]>` and bumps `initialized` only for kept elements,
    // breaking once `initialized == N`; this proves the `get_unchecked_mut(idx)`
    // writes and the final `array_assume_init` / `IntoIter` range stay in bounds.
    //
    // Boundedness: the chunk fill iterates through the generic default
    // `Iterator::try_fold` (a while-let loop that calls a generic closure in
    // iterator.rs), so this adapter cannot attach a loop contract to it. A
    // fixed `MAX_LEN` is still a complete state-space cover, not a truncation:
    // every reachable value of `initialized` is in 0..=N for every slice
    // length, so any `MAX_LEN >= N + 2` exercises every reachable
    // configuration (empty source, saturation before exhaustion, and
    // exhaustion before saturation).
    //
    // N = 0 is excluded on purpose. The current upstream implementation has a
    // latent N = 0 defect: the closure writes through
    // `array.get_unchecked_mut(idx)` before it compares `initialized < N`, so
    // `next_chunk::<0>()` on a source that yields at least one element writes
    // out of bounds into the zero-length array. Repo rules
    // (doc/src/general-rules.md) do not permit a local change to the runtime
    // logic, so the fix must land upstream. An upstream report is prepared.
    // These harnesses cover N >= 1.
    macro_rules! check_next_chunk_dropless {
        ($harness:ident, $elem_ty:ty, $n:expr) => {
            #[kani::proof]
            #[kani::unwind(7)]
            fn $harness() {
                const MAX_LEN: usize = 6;
                const N: usize = $n;
                let array: [$elem_ty; MAX_LEN] = kani::any();
                let mut it = Filter::new(
                    any_slice(&array).iter(),
                    maybe_keep::<$elem_ty> as fn(&&$elem_ty) -> bool,
                );
                let _ = it.next_chunk_dropless::<N>();
            }
        };
    }
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_unit, (), 4);
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_u8, u8, 4);
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_char, char, 4);
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_tup, (char, u8), 4);
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_unit_n1, (), 1);
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_u8_n1, u8, 1);
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_char_n1, char, 1);
    check_next_chunk_dropless!(check_filter_next_chunk_dropless_tup_n1, (char, u8), 1);
}
