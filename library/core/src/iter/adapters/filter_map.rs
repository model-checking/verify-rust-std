use crate::iter::adapters::SourceIter;
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused};
use crate::mem::{ManuallyDrop, MaybeUninit};
use crate::num::NonZero;
use crate::ops::{ControlFlow, Try};
use crate::{array, fmt};

/// An iterator that uses `f` to both filter and map elements from `iter`.
///
/// This `struct` is created by the [`filter_map`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`filter_map`]: Iterator::filter_map
/// [`Iterator`]: trait.Iterator.html
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Clone)]
pub struct FilterMap<I, F> {
    iter: I,
    f: F,
}
impl<I, F> FilterMap<I, F> {
    pub(in crate::iter) fn new(iter: I, f: F) -> FilterMap<I, F> {
        FilterMap { iter, f }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<I: fmt::Debug, F> fmt::Debug for FilterMap<I, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FilterMap").field("iter", &self.iter).finish()
    }
}

fn filter_map_fold<T, B, Acc>(
    mut f: impl FnMut(T) -> Option<B>,
    mut fold: impl FnMut(Acc, B) -> Acc,
) -> impl FnMut(Acc, T) -> Acc {
    move |acc, item| match f(item) {
        Some(x) => fold(acc, x),
        None => acc,
    }
}

fn filter_map_try_fold<'a, T, B, Acc, R: Try<Output = Acc>>(
    f: &'a mut impl FnMut(T) -> Option<B>,
    mut fold: impl FnMut(Acc, B) -> R + 'a,
) -> impl FnMut(Acc, T) -> R + 'a {
    move |acc, item| match f(item) {
        Some(x) => fold(acc, x),
        None => try { acc },
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: Iterator, F> Iterator for FilterMap<I, F>
where
    F: FnMut(I::Item) -> Option<B>,
{
    type Item = B;

    #[inline]
    fn next(&mut self) -> Option<B> {
        self.iter.find_map(&mut self.f)
    }

    #[inline]
    fn next_chunk<const N: usize>(
        &mut self,
    ) -> Result<[Self::Item; N], array::IntoIter<Self::Item, N>> {
        let mut array: [MaybeUninit<Self::Item>; N] = [const { MaybeUninit::uninit() }; N];

        struct Guard<'a, T> {
            array: &'a mut [MaybeUninit<T>],
            initialized: usize,
        }

        impl<T> Drop for Guard<'_, T> {
            #[inline]
            fn drop(&mut self) {
                if const { crate::mem::needs_drop::<T>() } {
                    // SAFETY: self.initialized is always <= N, which also is the length of the array.
                    unsafe {
                        self.array.get_unchecked_mut(..self.initialized).assume_init_drop();
                    }
                }
            }
        }

        let mut guard = Guard { array: &mut array, initialized: 0 };

        let result = self.iter.try_for_each(|element| {
            let idx = guard.initialized;
            let val = (self.f)(element);
            guard.initialized = idx + val.is_some() as usize;

            // SAFETY: Loop conditions ensure the index is in bounds.

            unsafe {
                let opt_payload_at: *const MaybeUninit<B> =
                    (&raw const val).byte_add(core::mem::offset_of!(Option<B>, Some.0)).cast();
                let dst = guard.array.as_mut_ptr().add(idx);
                crate::ptr::copy_nonoverlapping(opt_payload_at, dst, 1);
                crate::mem::forget(val);
            };

            if guard.initialized < N { ControlFlow::Continue(()) } else { ControlFlow::Break(()) }
        });

        let guard = ManuallyDrop::new(guard);

        match result {
            ControlFlow::Break(()) => {
                // SAFETY: The loop above is only explicitly broken when the array has been fully initialized
                Ok(unsafe { MaybeUninit::array_assume_init(array) })
            }
            ControlFlow::Continue(()) => {
                let initialized = guard.initialized;
                // SAFETY: The range is in bounds since the loop breaks when reaching N elements.
                Err(unsafe { array::IntoIter::new_unchecked(array, 0..initialized) })
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper) // can't know a lower bound, due to the predicate
    }

    #[inline]
    fn try_fold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_fold(init, filter_map_try_fold(&mut self.f, fold))
    }

    #[inline]
    fn fold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.fold(init, filter_map_fold(self.f, fold))
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<B, I: DoubleEndedIterator, F> DoubleEndedIterator for FilterMap<I, F>
where
    F: FnMut(I::Item) -> Option<B>,
{
    #[inline]
    fn next_back(&mut self) -> Option<B> {
        #[inline]
        fn find<T, B>(
            f: &mut impl FnMut(T) -> Option<B>,
        ) -> impl FnMut((), T) -> ControlFlow<B> + '_ {
            move |(), x| match f(x) {
                Some(x) => ControlFlow::Break(x),
                None => ControlFlow::Continue(()),
            }
        }

        self.iter.try_rfold((), find(&mut self.f)).break_value()
    }

    #[inline]
    fn try_rfold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> R,
        R: Try<Output = Acc>,
    {
        self.iter.try_rfold(init, filter_map_try_fold(&mut self.f, fold))
    }

    #[inline]
    fn rfold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        self.iter.rfold(init, filter_map_fold(self.f, fold))
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<B, I: FusedIterator, F> FusedIterator for FilterMap<I, F> where F: FnMut(I::Item) -> Option<B> {}

#[unstable(issue = "none", feature = "trusted_fused")]
unsafe impl<I: TrustedFused, F> TrustedFused for FilterMap<I, F> {}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I, F> SourceIter for FilterMap<I, F>
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
unsafe impl<I: InPlaceIterable, F> InPlaceIterable for FilterMap<I, F> {
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

    // Maps `&T -> Option<B>` nondeterministically to exercise both the
    // "element kept" and "element filtered" paths of the chunk-fill loop, with
    // a nondeterministic payload of the parameterized output type `B`.
    fn maybe_map_to<T, B: kani::Arbitrary>(_: &T) -> Option<B> {
        kani::any::<bool>().then(|| kani::any())
    }

    // A drop-requiring output type: `needs_drop::<DropToken>()` is true, so
    // the chunk loop's `Guard` compiles real drop glue instead of a no-op and
    // the payload byte-copy plus `mem::forget` handling must keep every
    // initialized slot live and in bounds. Kani models a panic as a
    // verification failure and has no unwinding, so the panic-during-drop
    // path itself is not expressible in a passing harness; the coverage this
    // type adds is the non-trivial drop-glue code path.
    struct DropToken(u8);

    impl Drop for DropToken {
        fn drop(&mut self) {
            let _ = crate::hint::black_box(self.0);
        }
    }

    impl kani::Arbitrary for DropToken {
        fn any() -> Self {
            DropToken(kani::any())
        }
    }

    // `next_chunk` fills a `MaybeUninit<[B; N]>` via a `Guard`-protected loop
    // that byte-copies each mapped value's payload and bumps `initialized` only
    // when the map yields `Some`; this proves the copies, the `array_assume_init`,
    // and the partial-fill `IntoIter` range all stay in bounds. The output menu
    // covers `usize`, a validity niche (`char`), a ZST (`()`), a padded pair
    // (`(char, u8)`), and a drop-requiring type (`DropToken`).
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
    // latent N = 0 defect: the closure does a one-element
    // `copy_nonoverlapping` of the mapped payload into `guard.array` at
    // `idx` before it compares `guard.initialized < N`, so `next_chunk::<0>()`
    // on a source that yields at least one element writes out of bounds into
    // the zero-capacity array. Repo rules (doc/src/general-rules.md) do not
    // permit a local change to the runtime logic, so the fix must land
    // upstream. An upstream report is prepared. These harnesses cover N >= 1.
    macro_rules! check_next_chunk {
        ($harness:ident, $elem_ty:ty, $out_ty:ty, $n:expr) => {
            #[kani::proof]
            #[kani::unwind(6)]
            fn $harness() {
                const MAX_LEN: usize = 5;
                const N: usize = $n;
                let array: [$elem_ty; MAX_LEN] = kani::any();
                let mut it = FilterMap::new(
                    any_slice(&array).iter(),
                    maybe_map_to::<$elem_ty, $out_ty> as fn(&$elem_ty) -> Option<$out_ty>,
                );
                let _ = it.next_chunk::<N>();
            }
        };
    }
    check_next_chunk!(check_filter_map_next_chunk_unit, (), usize, 3);
    check_next_chunk!(check_filter_map_next_chunk_u8, u8, usize, 3);
    check_next_chunk!(check_filter_map_next_chunk_char, char, usize, 3);
    check_next_chunk!(check_filter_map_next_chunk_tup, (char, u8), usize, 3);
    check_next_chunk!(check_filter_map_next_chunk_unit_n1, (), usize, 1);
    check_next_chunk!(check_filter_map_next_chunk_u8_n1, u8, usize, 1);
    check_next_chunk!(check_filter_map_next_chunk_char_n1, char, usize, 1);
    check_next_chunk!(check_filter_map_next_chunk_tup_n1, (char, u8), usize, 1);
    check_next_chunk!(check_filter_map_next_chunk_out_char, u8, char, 3);
    check_next_chunk!(check_filter_map_next_chunk_out_unit, u8, (), 3);
    check_next_chunk!(check_filter_map_next_chunk_out_tup, u8, (char, u8), 3);
    check_next_chunk!(check_filter_map_next_chunk_out_drop, u8, DropToken, 3);
}
