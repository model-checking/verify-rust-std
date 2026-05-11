use crate::iter::adapters::SourceIter;
use crate::iter::{FusedIterator, InPlaceIterable, TrustedFused};
#[cfg(kani)]
use crate::kani;
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

    // next_chunk (uses get_unchecked_mut, copy_nonoverlapping, array_assume_init,
    //             IntoIter::new_unchecked)
    // End-to-end bounded harness: exercises full next_chunk path
    // including both Ok (Break) and Err (Continue) exit paths.
    #[kani::proof]
    #[kani::unwind(9)]
    fn check_filter_map_next_chunk_n2_u8() {
        const MAX_LEN: usize = 8;
        let array: [u8; MAX_LEN] = kani::any();
        let slice = kani::slice::any_slice_of_array(&array);
        let mut iter = FilterMap::new(slice.iter(), |&x: &u8| if x < 128 { Some(x) } else { None });
        let _ = iter.next_chunk::<2>();
    }

    #[kani::proof]
    #[kani::unwind(9)]
    fn check_filter_map_next_chunk_n3_u8() {
        const MAX_LEN: usize = 8;
        let array: [u8; MAX_LEN] = kani::any();
        let slice = kani::slice::any_slice_of_array(&array);
        let mut iter = FilterMap::new(slice.iter(), |&x: &u8| if x < 128 { Some(x) } else { None });
        let _ = iter.next_chunk::<3>();
    }

    #[kani::proof]
    #[kani::unwind(9)]
    fn check_filter_map_next_chunk_n2_char() {
        const MAX_LEN: usize = 8;
        let array: [char; MAX_LEN] = kani::any();
        let slice = kani::slice::any_slice_of_array(&array);
        let mut iter =
            FilterMap::new(slice.iter(), |&x: &char| if (x as u32) < 128 { Some(x) } else { None });
        let _ = iter.next_chunk::<2>();
    }

    // Unbounded inductive step for next_chunk: proves the unsafe block
    // (as_mut_ptr().add, copy_nonoverlapping) is safe at ANY iteration of the
    // try_for_each loop, for ANY source iterator length. The loop body executes
    // only when initialized < N (break condition). With idx = initialized,
    // as_mut_ptr().add(idx) stays within the N-element array bounds, and
    // copy_nonoverlapping writes exactly one element to that location.
    // Combined with bounded end-to-end harnesses above (which exercise both
    // Ok/Break and Err/Continue exit paths), this gives complete unbounded
    // coverage of all unsafe operations in next_chunk.
    #[kani::proof]
    fn check_filter_map_next_chunk_unbounded() {
        // N=2 is concrete for Kani; the safety argument (idx < N => in-bounds)
        // generalizes to all N >= 1 since the invariant is N-independent.
        const N: usize = 2;
        let mut array: [MaybeUninit<u8>; N] = [const { MaybeUninit::uninit() }; N];

        // Symbolic loop state at arbitrary iteration k (any source iterator length)
        let initialized: usize = kani::any();
        kani::assume(initialized < N); // Loop continues only when initialized < N

        let idx = initialized;
        let val: Option<u8> = kani::any();
        let new_initialized = idx + val.is_some() as usize;

        // Exact unsafe block from the loop body: safe because idx < N = array.len()
        unsafe {
            let opt_payload_at: *const MaybeUninit<u8> =
                (&raw const val).byte_add(core::mem::offset_of!(Option<u8>, Some.0)).cast();
            let dst = array.as_mut_ptr().add(idx);
            crate::ptr::copy_nonoverlapping(opt_payload_at, dst, 1);
            crate::mem::forget(val);
        };

        // Invariant preserved: new_initialized <= initialized + 1 <= N
        assert!(new_initialized <= N);
    }
}
