use safety::requires;

use crate::iter::adapters::zip::try_get_unchecked;
use crate::iter::adapters::{SourceIter, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
use crate::iter::{FusedIterator, InPlaceIterable, TrustedLen};
#[cfg(kani)]
use crate::kani;
use crate::mem::{MaybeUninit, SizedTypeProperties};
use crate::num::NonZero;
use crate::ops::Try;
use crate::{array, ptr};

/// An iterator that copies the elements of an underlying iterator.
///
/// This `struct` is created by the [`copied`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`copied`]: Iterator::copied
/// [`Iterator`]: trait.Iterator.html
#[stable(feature = "iter_copied", since = "1.36.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone, Debug)]
pub struct Copied<I> {
    it: I,
}

impl<I> Copied<I> {
    pub(in crate::iter) fn new(it: I) -> Copied<I> {
        Copied { it }
    }

    #[doc(hidden)]
    #[unstable(feature = "copied_into_inner", issue = "none")]
    pub fn into_inner(self) -> I {
        self.it
    }
}

fn copy_fold<T: Copy, Acc>(mut f: impl FnMut(Acc, T) -> Acc) -> impl FnMut(Acc, &T) -> Acc {
    move |acc, &elt| f(acc, elt)
}

fn copy_try_fold<T: Copy, Acc, R>(mut f: impl FnMut(Acc, T) -> R) -> impl FnMut(Acc, &T) -> R {
    move |acc, &elt| f(acc, elt)
}

#[stable(feature = "iter_copied", since = "1.36.0")]
impl<'a, I, T: 'a> Iterator for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.it.next().copied()
    }

    fn next_chunk<const N: usize>(
        &mut self,
    ) -> Result<[Self::Item; N], array::IntoIter<Self::Item, N>>
    where
        Self: Sized,
    {
        <I as SpecNextChunk<'_, N, T>>::spec_next_chunk(&mut self.it)
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
        self.it.try_fold(init, copy_try_fold(f))
    }

    fn fold<Acc, F>(self, init: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        self.it.fold(init, copy_fold(f))
    }

    fn nth(&mut self, n: usize) -> Option<T> {
        self.it.nth(n).copied()
    }

    fn last(self) -> Option<T> {
        self.it.last().copied()
    }

    fn count(self) -> usize {
        self.it.count()
    }

    #[inline]
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        self.it.advance_by(n)
    }

    #[requires(idx < self.it.size_hint().0)]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> T
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: the caller must uphold the contract for
        // `Iterator::__iterator_get_unchecked`.
        *unsafe { try_get_unchecked(&mut self.it, idx) }
    }
}

#[stable(feature = "iter_copied", since = "1.36.0")]
impl<'a, I, T: 'a> DoubleEndedIterator for Copied<I>
where
    I: DoubleEndedIterator<Item = &'a T>,
    T: Copy,
{
    fn next_back(&mut self) -> Option<T> {
        self.it.next_back().copied()
    }

    fn try_rfold<B, F, R>(&mut self, init: B, f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        self.it.try_rfold(init, copy_try_fold(f))
    }

    fn rfold<Acc, F>(self, init: Acc, f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        self.it.rfold(init, copy_fold(f))
    }

    #[inline]
    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        self.it.advance_back_by(n)
    }
}

#[stable(feature = "iter_copied", since = "1.36.0")]
impl<'a, I, T: 'a> ExactSizeIterator for Copied<I>
where
    I: ExactSizeIterator<Item = &'a T>,
    T: Copy,
{
    fn len(&self) -> usize {
        self.it.len()
    }

    fn is_empty(&self) -> bool {
        self.it.is_empty()
    }
}

#[stable(feature = "iter_copied", since = "1.36.0")]
impl<'a, I, T: 'a> FusedIterator for Copied<I>
where
    I: FusedIterator<Item = &'a T>,
    T: Copy,
{
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccess for Copied<I> where I: TrustedRandomAccess {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<I> TrustedRandomAccessNoCoerce for Copied<I>
where
    I: TrustedRandomAccessNoCoerce,
{
    const MAY_HAVE_SIDE_EFFECT: bool = I::MAY_HAVE_SIDE_EFFECT;
}

#[stable(feature = "iter_copied", since = "1.36.0")]
unsafe impl<'a, I, T: 'a> TrustedLen for Copied<I>
where
    I: TrustedLen<Item = &'a T>,
    T: Copy,
{
}

trait SpecNextChunk<'a, const N: usize, T: 'a>: Iterator<Item = &'a T>
where
    T: Copy,
{
    fn spec_next_chunk(&mut self) -> Result<[T; N], array::IntoIter<T, N>>;
}

impl<'a, const N: usize, I, T: 'a> SpecNextChunk<'a, N, T> for I
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    default fn spec_next_chunk(&mut self) -> Result<[T; N], array::IntoIter<T, N>> {
        array::iter_next_chunk(&mut self.copied())
    }
}

impl<'a, const N: usize, T: 'a> SpecNextChunk<'a, N, T> for crate::slice::Iter<'a, T>
where
    T: Copy,
{
    fn spec_next_chunk(&mut self) -> Result<[T; N], array::IntoIter<T, N>> {
        let mut raw_array = [const { MaybeUninit::uninit() }; N];

        let len = self.len();

        if T::IS_ZST {
            if len < N {
                let _ = self.advance_by(len);
                // SAFETY: ZSTs can be conjured ex nihilo; only the amount has to be correct
                return Err(unsafe { array::IntoIter::new_unchecked(raw_array, 0..len) });
            }

            let _ = self.advance_by(N);
            // SAFETY: ditto
            return Ok(unsafe { MaybeUninit::array_assume_init(raw_array) });
        }

        if len < N {
            // SAFETY: `len` indicates that this many elements are available and we just checked that
            // it fits into the array.
            unsafe {
                ptr::copy_nonoverlapping(
                    self.as_ref().as_ptr(),
                    raw_array.as_mut_ptr() as *mut T,
                    len,
                );
                let _ = self.advance_by(len);
                return Err(array::IntoIter::new_unchecked(raw_array, 0..len));
            }
        }

        // SAFETY: `len` is larger than the array size. Copy a fixed amount here to fully initialize
        // the array.
        unsafe {
            ptr::copy_nonoverlapping(self.as_ref().as_ptr(), raw_array.as_mut_ptr() as *mut T, N);
            let _ = self.advance_by(N);
            Ok(MaybeUninit::array_assume_init(raw_array))
        }
    }
}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<I: Default> Default for Copied<I> {
    /// Creates a `Copied` iterator from the default value of `I`
    /// ```
    /// # use core::slice;
    /// # use core::iter::Copied;
    /// let iter: Copied<slice::Iter<'_, u8>> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        Self::new(Default::default())
    }
}

#[unstable(issue = "none", feature = "inplace_iteration")]
unsafe impl<I> SourceIter for Copied<I>
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
unsafe impl<I: InPlaceIterable> InPlaceIterable for Copied<I> {
    const EXPAND_BY: Option<NonZero<usize>> = I::EXPAND_BY;
    const MERGE_BY: Option<NonZero<usize>> = I::MERGE_BY;
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;
    use crate::kani;

    fn any_slice<T>(orig_slice: &[T]) -> &[T] {
        if kani::any() {
            let last = kani::any_where(|idx: &usize| *idx <= orig_slice.len());
            let first = kani::any_where(|idx: &usize| *idx <= last);
            &orig_slice[first..last]
        } else {
            let ptr = kani::any_where::<usize, _>(|val| *val != 0) as *const T;
            kani::assume(ptr.is_aligned());
            unsafe { crate::slice::from_raw_parts(ptr, 0) }
        }
    }

    fn any_adapter_iter<'a, T>(orig_slice: &'a [T]) -> Copied<crate::slice::Iter<'a, T>> {
        Copied::new(any_slice(orig_slice).iter())
    }

    macro_rules! check_get_unchecked {
        ($harness:ident, $elem_ty:ty, $max_len:expr) => {
            #[kani::proof]
            fn $harness() {
                const MAX_LEN: usize = $max_len;
                let array: [$elem_ty; MAX_LEN] = kani::any();
                let mut it = any_adapter_iter::<$elem_ty>(&array);
                let idx = kani::any_where(|i: &usize| *i < it.it.size_hint().0);
                let _ = unsafe { it.__iterator_get_unchecked(idx) };
            }
        };
    }
    check_get_unchecked!(check_copied_get_unchecked_unit, (), isize::MAX as usize);
    check_get_unchecked!(check_copied_get_unchecked_u8, u8, u32::MAX as usize);
    check_get_unchecked!(check_copied_get_unchecked_char, char, 50);
    check_get_unchecked!(check_copied_get_unchecked_tup, (char, u8), 50);

    // `spec_next_chunk` on the `slice::Iter` specialization bulk-copies `N` (or
    // `len`) elements into a `MaybeUninit<[T; N]>` and then either
    // `array_assume_init`s the full array or returns a `0..len` `IntoIter`; this
    // proves the `copy_nonoverlapping` lengths and the init range stay in bounds.
    // `N` is a trait generic, so it is pinned via the result type annotation.
    // The `MAX_LEN` menu mirrors `check_get_unchecked` above: the `u8`/ZST
    // harnesses raise the bound very high (there is no per-iteration loop, only
    // a bulk copy, so the cost stays flat), the wider types use a moderate one.
    macro_rules! check_spec_next_chunk {
        ($harness:ident, $elem_ty:ty, $n:expr, $max_len:expr) => {
            #[kani::proof]
            fn $harness() {
                const N: usize = $n;
                const MAX_LEN: usize = $max_len;
                let array: [$elem_ty; MAX_LEN] = kani::any();
                let mut it = any_slice(&array).iter();
                let _result: Result<[$elem_ty; N], crate::array::IntoIter<$elem_ty, N>> =
                    it.spec_next_chunk();
            }
        };
    }
    check_spec_next_chunk!(check_copied_spec_next_chunk_unit, (), 2, isize::MAX as usize);
    check_spec_next_chunk!(check_copied_spec_next_chunk_u8, u8, 3, u32::MAX as usize);
    check_spec_next_chunk!(check_copied_spec_next_chunk_char, char, 2, 50);
    check_spec_next_chunk!(check_copied_spec_next_chunk_tup, (char, u8), 2, 50);
}
