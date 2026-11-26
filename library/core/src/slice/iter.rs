//! Definitions of a bunch of iterators for `[T]`.

#[macro_use] // import iterator! and forward_iterator!
mod macros;

use safety::{ensures, requires};

use super::{from_raw_parts, from_raw_parts_mut};
use crate::hint::assert_unchecked;
use crate::iter::{FusedIterator, TrustedLen, TrustedRandomAccess, TrustedRandomAccessNoCoerce};
#[cfg(kani)]
use crate::kani;
use crate::marker::PhantomData;
use crate::mem::{self, SizedTypeProperties};
use crate::num::NonZero;
use crate::ptr::{NonNull, without_provenance, without_provenance_mut};
use crate::ub_checks::Invariant;
use crate::{cmp, fmt};

#[stable(feature = "boxed_slice_into_iter", since = "1.80.0")]
impl<T> !Iterator for [T] {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> IntoIterator for &'a [T] {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> IntoIterator for &'a mut [T] {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

/// Immutable slice iterator
///
/// This struct is created by the [`iter`] method on [slices].
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// // First, we need a slice to call the `iter` method on:
/// let slice = &[1, 2, 3];
///
/// // Then we call `iter` on the slice to get the `Iter` iterator,
/// // and iterate over it:
/// for element in slice.iter() {
///     println!("{element}");
/// }
///
/// // This for loop actually already works without calling `iter`:
/// for element in slice {
///     println!("{element}");
/// }
/// ```
///
/// [`iter`]: slice::iter
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[rustc_diagnostic_item = "SliceIter"]
pub struct Iter<'a, T: 'a> {
    /// The pointer to the next element to return, or the past-the-end location
    /// if the iterator is empty.
    ///
    /// This address will be used for all ZST elements, never changed.
    ptr: NonNull<T>,
    /// For non-ZSTs, the non-null pointer to the past-the-end element.
    ///
    /// For ZSTs, this is `ptr::without_provenance_mut(len)`.
    end_or_len: *const T,
    _marker: PhantomData<&'a T>,
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter").field(&self.as_slice()).finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync> Sync for Iter<'_, T> {}
#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync> Send for Iter<'_, T> {}

impl<'a, T> Iter<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a [T]) -> Self {
        let len = slice.len();
        let ptr: NonNull<T> = NonNull::from_ref(slice).cast();
        // SAFETY: Similar to `IterMut::new`.
        unsafe {
            let end_or_len =
                if T::IS_ZST { without_provenance(len) } else { ptr.as_ptr().add(len) };

            Self { ptr, end_or_len, _marker: PhantomData }
        }
    }

    /// Views the underlying data as a subslice of the original data.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // First, we need a slice to call the `iter` method on:
    /// let slice = &[1, 2, 3];
    ///
    /// // Then we call `iter` on the slice to get the `Iter` iterator:
    /// let mut iter = slice.iter();
    /// // Here `as_slice` still returns the whole slice, so this prints "[1, 2, 3]":
    /// println!("{:?}", iter.as_slice());
    ///
    /// // Now, we call the `next` method to remove the first element from the iterator:
    /// iter.next();
    /// // Here the iterator does not contain the first element of the slice any more,
    /// // so `as_slice` only returns the last two elements of the slice,
    /// // and so this prints "[2, 3]":
    /// println!("{:?}", iter.as_slice());
    ///
    /// // The underlying slice has not been modified and still contains three elements,
    /// // so this prints "[1, 2, 3]":
    /// println!("{:?}", slice);
    /// ```
    #[must_use]
    #[stable(feature = "iter_to_slice", since = "1.4.0")]
    #[inline]
    pub fn as_slice(&self) -> &'a [T] {
        self.make_slice()
    }
}

iterator! {struct Iter -> *const T, &'a T, const, {/* no mut */}, as_ref, each_ref, {
    fn is_sorted_by<F>(self, mut compare: F) -> bool
    where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> bool,
    {
        self.as_slice().is_sorted_by(|a, b| compare(&a, &b))
    }
}}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Clone for Iter<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        Iter { ptr: self.ptr, end_or_len: self.end_or_len, _marker: self._marker }
    }
}

#[stable(feature = "slice_iter_as_ref", since = "1.13.0")]
impl<T> AsRef<[T]> for Iter<'_, T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

#[unstable(feature = "ub_checks", issue = "none")]
impl<T> Invariant for Iter<'_, T> {
    /// An iterator can be safely used if its pointer can be read for its current length.
    ///
    /// If the type is a ZST or the encoded length is `0`, the only safety requirement is that
    /// its pointer is aligned (since zero-size access is always safe for aligned pointers).
    ///
    /// For other cases, we need to ensure that it is safe to read the memory between
    /// `self.ptr` and `self.end_or_len`.
    fn is_safe(&self) -> bool {
        let ty_size = crate::mem::size_of::<T>();
        // Use `abs_diff` since `end_or_len` may be smaller than `ptr` if `T` is a ZST.
        let distance = self.ptr.addr().get().abs_diff(self.end_or_len.addr());
        if ty_size == 0 || distance == 0 {
            self.ptr.is_aligned()
        } else {
            let slice_ptr: *const [T] =
                crate::ptr::from_raw_parts(self.ptr.as_ptr(), distance / ty_size);
            crate::ub_checks::same_allocation(self.ptr.as_ptr(), self.end_or_len)
                && self.ptr.addr().get() <= self.end_or_len.addr()
                && distance % ty_size == 0
                && crate::ub_checks::can_dereference(slice_ptr)
        }
    }
}

/// Mutable slice iterator.
///
/// This struct is created by the [`iter_mut`] method on [slices].
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// // First, we need a slice to call the `iter_mut` method on:
/// let slice = &mut [1, 2, 3];
///
/// // Then we call `iter_mut` on the slice to get the `IterMut` iterator,
/// // iterate over it and increment each element value:
/// for element in slice.iter_mut() {
///     *element += 1;
/// }
///
/// // We now have "[2, 3, 4]":
/// println!("{slice:?}");
/// ```
///
/// [`iter_mut`]: slice::iter_mut
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IterMut<'a, T: 'a> {
    /// The pointer to the next element to return, or the past-the-end location
    /// if the iterator is empty.
    ///
    /// This address will be used for all ZST elements, never changed.
    ptr: NonNull<T>,
    /// For non-ZSTs, the non-null pointer to the past-the-end element.
    ///
    /// For ZSTs, this is `ptr::without_provenance_mut(len)`.
    end_or_len: *mut T,
    _marker: PhantomData<&'a mut T>,
}

#[unstable(feature = "ub_checks", issue = "none")]
impl<T> Invariant for IterMut<'_, T> {
    /// This is similar to [Iter] with an extra write requirement.
    ///
    /// It must be safe to write in the memory interval between `self.ptr`
    /// and `self.end_or_len`.
    fn is_safe(&self) -> bool {
        let ty_size = crate::mem::size_of::<T>();
        let distance = self.ptr.addr().get().abs_diff(self.end_or_len.addr());
        if ty_size == 0 || distance == 0 {
            self.ptr.is_aligned()
        } else {
            let slice_ptr: *mut [T] =
                crate::ptr::from_raw_parts_mut(self.ptr.as_ptr(), distance / ty_size);
            crate::ub_checks::same_allocation(self.ptr.as_ptr(), self.end_or_len)
                && self.ptr.addr().get() <= self.end_or_len.addr()
                && distance % ty_size == 0
                && crate::ub_checks::can_dereference(slice_ptr)
                && crate::ub_checks::can_write(slice_ptr)
        }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug> fmt::Debug for IterMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IterMut").field(&self.make_slice()).finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync> Sync for IterMut<'_, T> {}
#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Send> Send for IterMut<'_, T> {}

impl<'a, T> IterMut<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a mut [T]) -> Self {
        let len = slice.len();
        let ptr: NonNull<T> = NonNull::from_mut(slice).cast();
        // SAFETY: There are several things here:
        //
        // `ptr` has been obtained by `slice.as_ptr()` where `slice` is a valid
        // reference thus it is non-NUL and safe to use and pass to
        // `NonNull::new_unchecked` .
        //
        // Adding `slice.len()` to the starting pointer gives a pointer
        // at the end of `slice`. `end` will never be dereferenced, only checked
        // for direct pointer equality with `ptr` to check if the iterator is
        // done.
        //
        // In the case of a ZST, the end pointer is just the length.  It's never
        // used as a pointer at all, and thus it's fine to have no provenance.
        //
        // See the `next_unchecked!` and `is_empty!` macros as well as the
        // `post_inc_start` method for more information.
        unsafe {
            let end_or_len =
                if T::IS_ZST { without_provenance_mut(len) } else { ptr.as_ptr().add(len) };

            Self { ptr, end_or_len, _marker: PhantomData }
        }
    }

    /// Views the underlying data as a subslice of the original data.
    ///
    /// To avoid creating `&mut` references that alias, this is forced
    /// to consume the iterator.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // First, we need a slice to call the `iter_mut` method on:
    /// let mut slice = &mut [1, 2, 3];
    ///
    /// // Then we call `iter_mut` on the slice to get the `IterMut` struct:
    /// let mut iter = slice.iter_mut();
    /// // Now, we call the `next` method to remove the first element of the iterator,
    /// // unwrap and dereference what we get from `next` and increase its value by 1:
    /// *iter.next().unwrap() += 1;
    /// // Here the iterator does not contain the first element of the slice any more,
    /// // so `into_slice` only returns the last two elements of the slice,
    /// // and so this prints "[2, 3]":
    /// println!("{:?}", iter.into_slice());
    /// // The underlying slice still contains three elements, but its first element
    /// // was increased by 1, so this prints "[2, 2, 3]":
    /// println!("{:?}", slice);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "iter_to_slice", since = "1.4.0")]
    pub fn into_slice(self) -> &'a mut [T] {
        // SAFETY: the iterator was created from a mutable slice with pointer
        // `self.ptr` and length `len!(self)`. This guarantees that all the prerequisites
        // for `from_raw_parts_mut` are fulfilled.
        unsafe { from_raw_parts_mut(self.ptr.as_ptr(), len!(self)) }
    }

    /// Views the underlying data as a subslice of the original data.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // First, we need a slice to call the `iter_mut` method on:
    /// let slice = &mut [1, 2, 3];
    ///
    /// // Then we call `iter_mut` on the slice to get the `IterMut` iterator:
    /// let mut iter = slice.iter_mut();
    /// // Here `as_slice` still returns the whole slice, so this prints "[1, 2, 3]":
    /// println!("{:?}", iter.as_slice());
    ///
    /// // Now, we call the `next` method to remove the first element from the iterator
    /// // and increment its value:
    /// *iter.next().unwrap() += 1;
    /// // Here the iterator does not contain the first element of the slice any more,
    /// // so `as_slice` only returns the last two elements of the slice,
    /// // and so this prints "[2, 3]":
    /// println!("{:?}", iter.as_slice());
    ///
    /// // The underlying slice still contains three elements, but its first element
    /// // was increased by 1, so this prints "[2, 2, 3]":
    /// println!("{:?}", slice);
    /// ```
    #[must_use]
    #[stable(feature = "slice_iter_mut_as_slice", since = "1.53.0")]
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.make_slice()
    }

    /// Views the underlying data as a mutable subslice of the original data.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(slice_iter_mut_as_mut_slice)]
    ///
    /// let mut slice: &mut [usize] = &mut [1, 2, 3];
    ///
    /// // First, we get the iterator:
    /// let mut iter = slice.iter_mut();
    /// // Then, we get a mutable slice from it:
    /// let mut_slice = iter.as_mut_slice();
    /// // So if we check what the `as_mut_slice` method returned, we have "[1, 2, 3]":
    /// assert_eq!(mut_slice, &mut [1, 2, 3]);
    ///
    /// // We can use it to mutate the slice:
    /// mut_slice[0] = 4;
    /// mut_slice[2] = 5;
    ///
    /// // Next, we can move to the second element of the slice, checking that
    /// // it yields the value we just wrote:
    /// assert_eq!(iter.next(), Some(&mut 4));
    /// // Now `as_mut_slice` returns "[2, 5]":
    /// assert_eq!(iter.as_mut_slice(), &mut [2, 5]);
    /// ```
    #[must_use]
    // FIXME: Uncomment the `AsMut<[T]>` impl when this gets stabilized.
    #[unstable(feature = "slice_iter_mut_as_mut_slice", issue = "93079")]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: the iterator was created from a mutable slice with pointer
        // `self.ptr` and length `len!(self)`. This guarantees that all the prerequisites
        // for `from_raw_parts_mut` are fulfilled.
        unsafe { from_raw_parts_mut(self.ptr.as_ptr(), len!(self)) }
    }
}

#[stable(feature = "slice_iter_mut_as_slice", since = "1.53.0")]
impl<T> AsRef<[T]> for IterMut<'_, T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

// #[stable(feature = "slice_iter_mut_as_mut_slice", since = "FIXME")]
// impl<T> AsMut<[T]> for IterMut<'_, T> {
//     fn as_mut(&mut self) -> &mut [T] {
//         self.as_mut_slice()
//     }
// }

iterator! {struct IterMut -> *mut T, &'a mut T, mut, {mut}, as_mut, each_mut, {}}

/// An internal abstraction over the splitting iterators, so that
/// splitn, splitn_mut etc can be implemented once.
#[doc(hidden)]
pub(super) trait SplitIter: DoubleEndedIterator {
    /// Marks the underlying iterator as complete, extracting the remaining
    /// portion of the slice.
    fn finish(&mut self) -> Option<Self::Item>;
}

/// An iterator over subslices separated by elements that match a predicate
/// function.
///
/// This struct is created by the [`split`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = [10, 40, 33, 20];
/// let mut iter = slice.split(|num| num % 3 == 0);
/// assert_eq!(iter.next(), Some(&[10, 40][..]));
/// assert_eq!(iter.next(), Some(&[20][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`split`]: slice::split
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Split<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    // Used for `SplitWhitespace` and `SplitAsciiWhitespace` `as_str` methods
    pub(crate) v: &'a [T],
    pred: P,
    // Used for `SplitAsciiWhitespace` `as_str` method
    pub(crate) finished: bool,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> Split<'a, T, P> {
    #[inline]
    pub(super) fn new(slice: &'a [T], pred: P) -> Self {
        Self { v: slice, pred, finished: false }
    }
    /// Returns a slice which contains items not yet handled by split.
    /// # Example
    ///
    /// ```
    /// #![feature(split_as_slice)]
    /// let slice = [1,2,3,4,5];
    /// let mut split = slice.split(|v| v % 2 == 0);
    /// assert!(split.next().is_some());
    /// assert_eq!(split.as_slice(), &[3,4,5]);
    /// ```
    #[unstable(feature = "split_as_slice", issue = "96137")]
    pub fn as_slice(&self) -> &'a [T] {
        if self.finished { &[] } else { self.v }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug, P> fmt::Debug for Split<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Split").field("v", &self.v).field("finished", &self.finished).finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "rust1", since = "1.0.0")]
impl<T, P> Clone for Split<'_, T, P>
where
    P: Clone + FnMut(&T) -> bool,
{
    fn clone(&self) -> Self {
        Split { v: self.v, pred: self.pred.clone(), finished: self.finished }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, P> Iterator for Split<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.finished {
            return None;
        }

        match self.v.iter().position(|x| (self.pred)(x)) {
            None => self.finish(),
            Some(idx) => {
                let (left, right) =
                    // SAFETY: if v.iter().position returns Some(idx), that
                    // idx is definitely a valid index for v
                    unsafe { (self.v.get_unchecked(..idx), self.v.get_unchecked(idx + 1..)) };
                let ret = Some(left);
                self.v = right;
                ret
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            // If the predicate doesn't match anything, we yield one slice.
            // If it matches every element, we yield `len() + 1` empty slices.
            (1, Some(self.v.len() + 1))
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, P> DoubleEndedIterator for Split<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.finished {
            return None;
        }

        match self.v.iter().rposition(|x| (self.pred)(x)) {
            None => self.finish(),
            Some(idx) => {
                let (left, right) =
                    // SAFETY: if v.iter().rposition returns Some(idx), then
                    // idx is definitely a valid index for v
                    unsafe { (self.v.get_unchecked(..idx), self.v.get_unchecked(idx + 1..)) };
                let ret = Some(right);
                self.v = left;
                ret
            }
        }
    }
}

impl<'a, T, P> SplitIter for Split<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn finish(&mut self) -> Option<&'a [T]> {
        if self.finished {
            None
        } else {
            self.finished = true;
            Some(self.v)
        }
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T, P> FusedIterator for Split<'_, T, P> where P: FnMut(&T) -> bool {}

/// An iterator over subslices separated by elements that match a predicate
/// function. Unlike `Split`, it contains the matched part as a terminator
/// of the subslice.
///
/// This struct is created by the [`split_inclusive`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = [10, 40, 33, 20];
/// let mut iter = slice.split_inclusive(|num| num % 3 == 0);
/// assert_eq!(iter.next(), Some(&[10, 40, 33][..]));
/// assert_eq!(iter.next(), Some(&[20][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`split_inclusive`]: slice::split_inclusive
/// [slices]: slice
#[stable(feature = "split_inclusive", since = "1.51.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct SplitInclusive<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    v: &'a [T],
    pred: P,
    finished: bool,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> SplitInclusive<'a, T, P> {
    #[inline]
    pub(super) fn new(slice: &'a [T], pred: P) -> Self {
        let finished = slice.is_empty();
        Self { v: slice, pred, finished }
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<T: fmt::Debug, P> fmt::Debug for SplitInclusive<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitInclusive")
            .field("v", &self.v)
            .field("finished", &self.finished)
            .finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<T, P> Clone for SplitInclusive<'_, T, P>
where
    P: Clone + FnMut(&T) -> bool,
{
    fn clone(&self) -> Self {
        SplitInclusive { v: self.v, pred: self.pred.clone(), finished: self.finished }
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, T, P> Iterator for SplitInclusive<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.finished {
            return None;
        }

        let idx =
            self.v.iter().position(|x| (self.pred)(x)).map(|idx| idx + 1).unwrap_or(self.v.len());
        if idx == self.v.len() {
            self.finished = true;
        }
        let ret = Some(&self.v[..idx]);
        self.v = &self.v[idx..];
        ret
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            // If the predicate doesn't match anything, we yield one slice.
            // If it matches every element, we yield `len()` one-element slices,
            // or a single empty slice.
            (1, Some(cmp::max(1, self.v.len())))
        }
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, T, P> DoubleEndedIterator for SplitInclusive<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.finished {
            return None;
        }

        // The last index of self.v is already checked and found to match
        // by the last iteration, so we start searching a new match
        // one index to the left.
        let remainder = if self.v.is_empty() { &[] } else { &self.v[..(self.v.len() - 1)] };
        let idx = remainder.iter().rposition(|x| (self.pred)(x)).map(|idx| idx + 1).unwrap_or(0);
        if idx == 0 {
            self.finished = true;
        }
        let ret = Some(&self.v[idx..]);
        self.v = &self.v[..idx];
        ret
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<T, P> FusedIterator for SplitInclusive<'_, T, P> where P: FnMut(&T) -> bool {}

/// An iterator over the mutable subslices of the vector which are separated
/// by elements that match `pred`.
///
/// This struct is created by the [`split_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut v = [10, 40, 30, 20, 60, 50];
/// let iter = v.split_mut(|num| *num % 3 == 0);
/// ```
///
/// [`split_mut`]: slice::split_mut
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct SplitMut<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    v: &'a mut [T],
    pred: P,
    finished: bool,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> SplitMut<'a, T, P> {
    #[inline]
    pub(super) fn new(slice: &'a mut [T], pred: P) -> Self {
        Self { v: slice, pred, finished: false }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug, P> fmt::Debug for SplitMut<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitMut").field("v", &self.v).field("finished", &self.finished).finish()
    }
}

impl<'a, T, P> SplitIter for SplitMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn finish(&mut self) -> Option<&'a mut [T]> {
        if self.finished {
            None
        } else {
            self.finished = true;
            Some(mem::take(&mut self.v))
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, P> Iterator for SplitMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.finished {
            return None;
        }

        match self.v.iter().position(|x| (self.pred)(x)) {
            None => self.finish(),
            Some(idx) => {
                let tmp = mem::take(&mut self.v);
                // idx is the index of the element we are splitting on. We want to set self to the
                // region after idx, and return the subslice before and not including idx.
                // So first we split after idx
                let (head, tail) = tmp.split_at_mut(idx + 1);
                self.v = tail;
                // Then return the subslice up to but not including the found element
                Some(&mut head[..idx])
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            // If the predicate doesn't match anything, we yield one slice.
            // If it matches every element, we yield `len() + 1` empty slices.
            (1, Some(self.v.len() + 1))
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, P> DoubleEndedIterator for SplitMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.finished {
            return None;
        }

        let idx_opt = {
            // work around borrowck limitations
            let pred = &mut self.pred;
            self.v.iter().rposition(|x| (*pred)(x))
        };
        match idx_opt {
            None => self.finish(),
            Some(idx) => {
                let tmp = mem::take(&mut self.v);
                let (head, tail) = tmp.split_at_mut(idx);
                self.v = head;
                Some(&mut tail[1..])
            }
        }
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<T, P> FusedIterator for SplitMut<'_, T, P> where P: FnMut(&T) -> bool {}

/// An iterator over the mutable subslices of the vector which are separated
/// by elements that match `pred`. Unlike `SplitMut`, it contains the matched
/// parts in the ends of the subslices.
///
/// This struct is created by the [`split_inclusive_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut v = [10, 40, 30, 20, 60, 50];
/// let iter = v.split_inclusive_mut(|num| *num % 3 == 0);
/// ```
///
/// [`split_inclusive_mut`]: slice::split_inclusive_mut
/// [slices]: slice
#[stable(feature = "split_inclusive", since = "1.51.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct SplitInclusiveMut<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    v: &'a mut [T],
    pred: P,
    finished: bool,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> SplitInclusiveMut<'a, T, P> {
    #[inline]
    pub(super) fn new(slice: &'a mut [T], pred: P) -> Self {
        let finished = slice.is_empty();
        Self { v: slice, pred, finished }
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<T: fmt::Debug, P> fmt::Debug for SplitInclusiveMut<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitInclusiveMut")
            .field("v", &self.v)
            .field("finished", &self.finished)
            .finish()
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, T, P> Iterator for SplitInclusiveMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.finished {
            return None;
        }

        let idx_opt = {
            // work around borrowck limitations
            let pred = &mut self.pred;
            self.v.iter().position(|x| (*pred)(x))
        };
        let idx = idx_opt.map(|idx| idx + 1).unwrap_or(self.v.len());
        if idx == self.v.len() {
            self.finished = true;
        }
        let tmp = mem::take(&mut self.v);
        let (head, tail) = tmp.split_at_mut(idx);
        self.v = tail;
        Some(head)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.finished {
            (0, Some(0))
        } else {
            // If the predicate doesn't match anything, we yield one slice.
            // If it matches every element, we yield `len()` one-element slices,
            // or a single empty slice.
            (1, Some(cmp::max(1, self.v.len())))
        }
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, T, P> DoubleEndedIterator for SplitInclusiveMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.finished {
            return None;
        }

        let idx_opt = if self.v.is_empty() {
            None
        } else {
            // work around borrowck limitations
            let pred = &mut self.pred;

            // The last index of self.v is already checked and found to match
            // by the last iteration, so we start searching a new match
            // one index to the left.
            let remainder = &self.v[..(self.v.len() - 1)];
            remainder.iter().rposition(|x| (*pred)(x))
        };
        let idx = idx_opt.map(|idx| idx + 1).unwrap_or(0);
        if idx == 0 {
            self.finished = true;
        }
        let tmp = mem::take(&mut self.v);
        let (head, tail) = tmp.split_at_mut(idx);
        self.v = head;
        Some(tail)
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<T, P> FusedIterator for SplitInclusiveMut<'_, T, P> where P: FnMut(&T) -> bool {}

/// An iterator over subslices separated by elements that match a predicate
/// function, starting from the end of the slice.
///
/// This struct is created by the [`rsplit`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = [11, 22, 33, 0, 44, 55];
/// let mut iter = slice.rsplit(|num| *num == 0);
/// assert_eq!(iter.next(), Some(&[44, 55][..]));
/// assert_eq!(iter.next(), Some(&[11, 22, 33][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`rsplit`]: slice::rsplit
/// [slices]: slice
#[stable(feature = "slice_rsplit", since = "1.27.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RSplit<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    inner: Split<'a, T, P>,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> RSplit<'a, T, P> {
    #[inline]
    pub(super) fn new(slice: &'a [T], pred: P) -> Self {
        Self { inner: Split::new(slice, pred) }
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<T: fmt::Debug, P> fmt::Debug for RSplit<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RSplit")
            .field("v", &self.inner.v)
            .field("finished", &self.inner.finished)
            .finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<T, P> Clone for RSplit<'_, T, P>
where
    P: Clone + FnMut(&T) -> bool,
{
    fn clone(&self) -> Self {
        RSplit { inner: self.inner.clone() }
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<'a, T, P> Iterator for RSplit<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        self.inner.next_back()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<'a, T, P> DoubleEndedIterator for RSplit<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T]> {
        self.inner.next()
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<'a, T, P> SplitIter for RSplit<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn finish(&mut self) -> Option<&'a [T]> {
        self.inner.finish()
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<T, P> FusedIterator for RSplit<'_, T, P> where P: FnMut(&T) -> bool {}

/// An iterator over the subslices of the vector which are separated
/// by elements that match `pred`, starting from the end of the slice.
///
/// This struct is created by the [`rsplit_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = [11, 22, 33, 0, 44, 55];
/// let iter = slice.rsplit_mut(|num| *num == 0);
/// ```
///
/// [`rsplit_mut`]: slice::rsplit_mut
/// [slices]: slice
#[stable(feature = "slice_rsplit", since = "1.27.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RSplitMut<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    inner: SplitMut<'a, T, P>,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> RSplitMut<'a, T, P> {
    #[inline]
    pub(super) fn new(slice: &'a mut [T], pred: P) -> Self {
        Self { inner: SplitMut::new(slice, pred) }
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<T: fmt::Debug, P> fmt::Debug for RSplitMut<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RSplitMut")
            .field("v", &self.inner.v)
            .field("finished", &self.inner.finished)
            .finish()
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<'a, T, P> SplitIter for RSplitMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn finish(&mut self) -> Option<&'a mut [T]> {
        self.inner.finish()
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<'a, T, P> Iterator for RSplitMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        self.inner.next_back()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<'a, T, P> DoubleEndedIterator for RSplitMut<'a, T, P>
where
    P: FnMut(&T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        self.inner.next()
    }
}

#[stable(feature = "slice_rsplit", since = "1.27.0")]
impl<T, P> FusedIterator for RSplitMut<'_, T, P> where P: FnMut(&T) -> bool {}

/// An private iterator over subslices separated by elements that
/// match a predicate function, splitting at most a fixed number of
/// times.
#[derive(Debug)]
struct GenericSplitN<I> {
    iter: I,
    count: usize,
}

impl<T, I: SplitIter<Item = T>> Iterator for GenericSplitN<I> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        match self.count {
            0 => None,
            1 => {
                self.count -= 1;
                self.iter.finish()
            }
            _ => {
                self.count -= 1;
                self.iter.next()
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lower, upper_opt) = self.iter.size_hint();
        (
            cmp::min(self.count, lower),
            Some(upper_opt.map_or(self.count, |upper| cmp::min(self.count, upper))),
        )
    }
}

/// An iterator over subslices separated by elements that match a predicate
/// function, limited to a given number of splits.
///
/// This struct is created by the [`splitn`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = [10, 40, 30, 20, 60, 50];
/// let mut iter = slice.splitn(2, |num| *num % 3 == 0);
/// assert_eq!(iter.next(), Some(&[10, 40][..]));
/// assert_eq!(iter.next(), Some(&[20, 60, 50][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`splitn`]: slice::splitn
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct SplitN<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    inner: GenericSplitN<Split<'a, T, P>>,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> SplitN<'a, T, P> {
    #[inline]
    pub(super) fn new(s: Split<'a, T, P>, n: usize) -> Self {
        Self { inner: GenericSplitN { iter: s, count: n } }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug, P> fmt::Debug for SplitN<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitN").field("inner", &self.inner).finish()
    }
}

/// An iterator over subslices separated by elements that match a
/// predicate function, limited to a given number of splits, starting
/// from the end of the slice.
///
/// This struct is created by the [`rsplitn`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = [10, 40, 30, 20, 60, 50];
/// let mut iter = slice.rsplitn(2, |num| *num % 3 == 0);
/// assert_eq!(iter.next(), Some(&[50][..]));
/// assert_eq!(iter.next(), Some(&[10, 40, 30, 20][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`rsplitn`]: slice::rsplitn
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RSplitN<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    inner: GenericSplitN<RSplit<'a, T, P>>,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> RSplitN<'a, T, P> {
    #[inline]
    pub(super) fn new(s: RSplit<'a, T, P>, n: usize) -> Self {
        Self { inner: GenericSplitN { iter: s, count: n } }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug, P> fmt::Debug for RSplitN<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RSplitN").field("inner", &self.inner).finish()
    }
}

/// An iterator over subslices separated by elements that match a predicate
/// function, limited to a given number of splits.
///
/// This struct is created by the [`splitn_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = [10, 40, 30, 20, 60, 50];
/// let iter = slice.splitn_mut(2, |num| *num % 3 == 0);
/// ```
///
/// [`splitn_mut`]: slice::splitn_mut
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct SplitNMut<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    inner: GenericSplitN<SplitMut<'a, T, P>>,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> SplitNMut<'a, T, P> {
    #[inline]
    pub(super) fn new(s: SplitMut<'a, T, P>, n: usize) -> Self {
        Self { inner: GenericSplitN { iter: s, count: n } }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug, P> fmt::Debug for SplitNMut<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitNMut").field("inner", &self.inner).finish()
    }
}

/// An iterator over subslices separated by elements that match a
/// predicate function, limited to a given number of splits, starting
/// from the end of the slice.
///
/// This struct is created by the [`rsplitn_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = [10, 40, 30, 20, 60, 50];
/// let iter = slice.rsplitn_mut(2, |num| *num % 3 == 0);
/// ```
///
/// [`rsplitn_mut`]: slice::rsplitn_mut
/// [slices]: slice
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RSplitNMut<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    inner: GenericSplitN<RSplitMut<'a, T, P>>,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> RSplitNMut<'a, T, P> {
    #[inline]
    pub(super) fn new(s: RSplitMut<'a, T, P>, n: usize) -> Self {
        Self { inner: GenericSplitN { iter: s, count: n } }
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: fmt::Debug, P> fmt::Debug for RSplitNMut<'_, T, P>
where
    P: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RSplitNMut").field("inner", &self.inner).finish()
    }
}

forward_iterator! { SplitN: T, &'a [T] }
forward_iterator! { RSplitN: T, &'a [T] }
forward_iterator! { SplitNMut: T, &'a mut [T] }
forward_iterator! { RSplitNMut: T, &'a mut [T] }

/// An iterator over overlapping subslices of length `size`.
///
/// This struct is created by the [`windows`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = ['r', 'u', 's', 't'];
/// let mut iter = slice.windows(2);
/// assert_eq!(iter.next(), Some(&['r', 'u'][..]));
/// assert_eq!(iter.next(), Some(&['u', 's'][..]));
/// assert_eq!(iter.next(), Some(&['s', 't'][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`windows`]: slice::windows
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Windows<'a, T: 'a> {
    v: &'a [T],
    size: NonZero<usize>,
}

impl<'a, T: 'a> Windows<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a [T], size: NonZero<usize>) -> Self {
        Self { v: slice, size }
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Clone for Windows<'_, T> {
    fn clone(&self) -> Self {
        Windows { v: self.v, size: self.size }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for Windows<'a, T> {
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.size.get() > self.v.len() {
            None
        } else {
            let ret = Some(&self.v[..self.size.get()]);
            self.v = &self.v[1..];
            ret
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.size.get() > self.v.len() {
            (0, Some(0))
        } else {
            let size = self.v.len() - self.size.get() + 1;
            (size, Some(size))
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let size = self.size.get();
        if let Some(rest) = self.v.get(n..)
            && let Some(nth) = rest.get(..size)
        {
            self.v = &rest[1..];
            Some(nth)
        } else {
            // setting length to 0 is cheaper than overwriting the pointer when assigning &[]
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        if self.size.get() > self.v.len() {
            None
        } else {
            let start = self.v.len() - self.size.get();
            Some(&self.v[start..])
        }
    }

    #[requires(idx < self.len())]
    #[ensures(|result: &&'a [T]| {
        (result.len() == old(self.size.get()))
        && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.size.get() == old(self.size.get()))
        && (crate::ub_checks::can_dereference(*result as *const [T]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        // SAFETY: since the caller guarantees that `i` is in bounds,
        // which means that `i` cannot overflow an `isize`, and the
        // slice created by `from_raw_parts` is a subslice of `self.v`
        // thus is guaranteed to be valid for the lifetime `'a` of `self.v`.
        unsafe { from_raw_parts(self.v.as_ptr().add(idx), self.size.get()) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for Windows<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.nth_back(0)
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if let Some(end) = self.v.len().checked_sub(n)
            && let Some(start) = end.checked_sub(self.size.get())
        {
            let res = &self.v[start..end];
            self.v = &self.v[..end - 1];
            Some(res)
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for Windows<'_, T> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for Windows<'_, T> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for Windows<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for Windows<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for Windows<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// An iterator over a slice in (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last slice
/// of the iteration will be the remainder.
///
/// This struct is created by the [`chunks`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let mut iter = slice.chunks(2);
/// assert_eq!(iter.next(), Some(&['l', 'o'][..]));
/// assert_eq!(iter.next(), Some(&['r', 'e'][..]));
/// assert_eq!(iter.next(), Some(&['m'][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`chunks`]: slice::chunks
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Chunks<'a, T: 'a> {
    v: &'a [T],
    chunk_size: usize,
}

impl<'a, T: 'a> Chunks<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a [T], size: usize) -> Self {
        Self { v: slice, chunk_size: size }
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Clone for Chunks<'_, T> {
    fn clone(&self) -> Self {
        Chunks { v: self.v, chunk_size: self.chunk_size }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for Chunks<'a, T> {
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() {
            None
        } else {
            let chunksz = cmp::min(self.v.len(), self.chunk_size);
            let (fst, snd) = self.v.split_at(chunksz);
            self.v = snd;
            Some(fst)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.v.is_empty() {
            (0, Some(0))
        } else {
            let n = self.v.len().div_ceil(self.chunk_size);
            (n, Some(n))
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if let Some(start) = n.checked_mul(self.chunk_size)
            && start < self.v.len()
        {
            let rest = &self.v[start..];
            let (chunk, rest) = rest.split_at(self.chunk_size.min(rest.len()));
            self.v = rest;
            Some(chunk)
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        if self.v.is_empty() {
            None
        } else {
            let start = (self.v.len() - 1) / self.chunk_size * self.chunk_size;
            Some(&self.v[start..])
        }
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size) < self.v.len()
    )]
    #[ensures(|result: &&'a [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.chunk_size == old(self.chunk_size))
        && (crate::ub_checks::can_dereference(*result as *const [T]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let start = idx * self.chunk_size;
        // SAFETY: the caller guarantees that `i` is in bounds,
        // which means that `start` must be in bounds of the
        // underlying `self.v` slice, and we made sure that `len`
        // is also in bounds of `self.v`. Thus, `start` cannot overflow
        // an `isize`, and the slice constructed by `from_raw_parts`
        // is a subslice of `self.v` which is guaranteed to be valid
        // for the lifetime `'a` of `self.v`.
        unsafe {
            let len = cmp::min(self.v.len().unchecked_sub(start), self.chunk_size);
            from_raw_parts(self.v.as_ptr().add(start), len)
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for Chunks<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() {
            None
        } else {
            let remainder = self.v.len() % self.chunk_size;
            let chunksz = if remainder != 0 { remainder } else { self.chunk_size };
            // SAFETY: split_at_unchecked requires the argument be less than or
            // equal to the length. This is guaranteed, but subtle: `chunksz`
            // will always either be `self.v.len() % self.chunk_size`, which
            // will always evaluate to strictly less than `self.v.len()` (or
            // panic, in the case that `self.chunk_size` is zero), or it can be
            // `self.chunk_size`, in the case that the length is exactly
            // divisible by the chunk size.
            //
            // While it seems like using `self.chunk_size` in this case could
            // lead to a value greater than `self.v.len()`, it cannot: if
            // `self.chunk_size` were greater than `self.v.len()`, then
            // `self.v.len() % self.chunk_size` would return nonzero (note that
            // in this branch of the `if`, we already know that `self.v` is
            // non-empty).
            let (fst, snd) = unsafe { self.v.split_at_unchecked(self.v.len() - chunksz) };
            self.v = fst;
            Some(snd)
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            let start = (len - 1 - n) * self.chunk_size;
            let end = start + (self.v.len() - start).min(self.chunk_size);
            let nth_back = &self.v[start..end];
            self.v = &self.v[..start];
            Some(nth_back)
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for Chunks<'_, T> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for Chunks<'_, T> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for Chunks<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for Chunks<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for Chunks<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// An iterator over a slice in (non-overlapping) mutable chunks (`chunk_size`
/// elements at a time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last slice
/// of the iteration will be the remainder.
///
/// This struct is created by the [`chunks_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = ['l', 'o', 'r', 'e', 'm'];
/// let iter = slice.chunks_mut(2);
/// ```
///
/// [`chunks_mut`]: slice::chunks_mut
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ChunksMut<'a, T: 'a> {
    /// # Safety
    /// This slice pointer must point at a valid region of `T` with at least length `v.len()`. Normally,
    /// those requirements would mean that we could instead use a `&mut [T]` here, but we cannot
    /// because `__iterator_get_unchecked` needs to return `&mut [T]`, which guarantees certain aliasing
    /// properties that we cannot uphold if we hold on to the full original `&mut [T]`. Wrapping a raw
    /// slice instead lets us hand out non-overlapping `&mut [T]` subslices of the slice we wrap.
    v: *mut [T],
    chunk_size: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T: 'a> ChunksMut<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a mut [T], size: usize) -> Self {
        Self { v: slice, chunk_size: size, _marker: PhantomData }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for ChunksMut<'a, T> {
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() {
            None
        } else {
            let sz = cmp::min(self.v.len(), self.chunk_size);
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (head, tail) = unsafe { self.v.split_at_mut(sz) };
            self.v = tail;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *head })
        }
    }

    #[inline]
    #[requires(self.chunk_size > 0)]
    #[ensures(|hint: &(usize, Option<usize>)| hint.1 == Some(hint.0))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.v.is_empty() {
            (0, Some(0))
        } else {
            let n = self.v.len().div_ceil(self.chunk_size);
            (n, Some(n))
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        if let Some(start) = n.checked_mul(self.chunk_size)
            && start < self.v.len()
        {
            // SAFETY: `start < self.v.len()` ensures this is in bounds
            let (_, rest) = unsafe { self.v.split_at_mut(start) };
            // SAFETY: `.min(rest.len()` ensures this is in bounds
            let (chunk, rest) = unsafe { rest.split_at_mut(self.chunk_size.min(rest.len())) };
            self.v = rest;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *chunk })
        } else {
            self.v = &mut [];
            None
        }
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        if self.v.is_empty() {
            None
        } else {
            let start = (self.v.len() - 1) / self.chunk_size * self.chunk_size;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *self.v.get_unchecked_mut(start..) })
        }
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size) < self.v.len()
    )]
    #[ensures(|result: &&'a mut [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.chunk_size == old(self.chunk_size))
        && (crate::ub_checks::can_dereference(&**result as *const [T]))
        && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let start = idx * self.chunk_size;
        // SAFETY: see comments for `Chunks::__iterator_get_unchecked` and `self.v`.
        //
        // Also note that the caller also guarantees that we're never called
        // with the same index again, and that no other methods that will
        // access this subslice are called, so it is valid for the returned
        // slice to be mutable.
        unsafe {
            let len = cmp::min(self.v.len().unchecked_sub(start), self.chunk_size);
            from_raw_parts_mut(self.v.as_mut_ptr().add(start), len)
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for ChunksMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() {
            None
        } else {
            let remainder = self.v.len() % self.chunk_size;
            let sz = if remainder != 0 { remainder } else { self.chunk_size };
            let len = self.v.len();
            // SAFETY: Similar to `Chunks::next_back`
            let (head, tail) = unsafe { self.v.split_at_mut_unchecked(len - sz) };
            self.v = head;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *tail })
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            let start = (len - 1 - n) * self.chunk_size;
            let end = match start.checked_add(self.chunk_size) {
                Some(res) => cmp::min(self.v.len(), res),
                None => self.v.len(),
            };
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (temp, _tail) = unsafe { self.v.split_at_mut(end) };
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (head, nth_back) = unsafe { temp.split_at_mut(start) };
            self.v = head;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *nth_back })
        } else {
            self.v = &mut [];
            None
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for ChunksMut<'_, T> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for ChunksMut<'_, T> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for ChunksMut<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for ChunksMut<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for ChunksMut<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T> Send for ChunksMut<'_, T> where T: Send {}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T> Sync for ChunksMut<'_, T> where T: Sync {}

/// An iterator over a slice in (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last
/// up to `chunk_size-1` elements will be omitted but can be retrieved from
/// the [`remainder`] function from the iterator.
///
/// This struct is created by the [`chunks_exact`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let mut iter = slice.chunks_exact(2);
/// assert_eq!(iter.next(), Some(&['l', 'o'][..]));
/// assert_eq!(iter.next(), Some(&['r', 'e'][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`chunks_exact`]: slice::chunks_exact
/// [`remainder`]: ChunksExact::remainder
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "chunks_exact", since = "1.31.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}

impl<'a, T> ChunksExact<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a [T], chunk_size: usize) -> Self {
        let rem = slice.len() % chunk_size;
        let fst_len = slice.len() - rem;
        // SAFETY: 0 <= fst_len <= slice.len() by construction above
        let (fst, snd) = unsafe { slice.split_at_unchecked(fst_len) };
        Self { v: fst, rem: snd, chunk_size }
    }

    /// Returns the remainder of the original slice that is not going to be
    /// returned by the iterator. The returned slice has at most `chunk_size-1`
    /// elements.
    ///
    /// # Example
    ///
    /// ```
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = slice.chunks_exact(2);
    /// assert_eq!(iter.remainder(), &['m'][..]);
    /// assert_eq!(iter.next(), Some(&['l', 'o'][..]));
    /// assert_eq!(iter.remainder(), &['m'][..]);
    /// assert_eq!(iter.next(), Some(&['r', 'e'][..]));
    /// assert_eq!(iter.remainder(), &['m'][..]);
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.remainder(), &['m'][..]);
    /// ```
    #[must_use]
    #[stable(feature = "chunks_exact", since = "1.31.0")]
    pub fn remainder(&self) -> &'a [T] {
        self.rem
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<T> Clone for ChunksExact<'_, T> {
    fn clone(&self) -> Self {
        ChunksExact { v: self.v, rem: self.rem, chunk_size: self.chunk_size }
    }
}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<'a, T> Iterator for ChunksExact<'a, T> {
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        self.v.split_at_checked(self.chunk_size).map(|(chunk, rest)| {
            self.v = rest;
            chunk
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.v.len() / self.chunk_size;
        (n, Some(n))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if let Some(start) = n.checked_mul(self.chunk_size)
            && start < self.v.len()
        {
            self.v = &self.v[start..];
            self.next()
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size).checked_add(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size).wrapping_add(self.chunk_size) <= self.v.len()
    )]
    #[ensures(|result: &&'a [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.chunk_size == old(self.chunk_size))
        && (self.rem.len() == old(self.rem.len()))
        && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        && (crate::ub_checks::can_dereference(*result as *const [T]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let start = idx * self.chunk_size;
        // SAFETY: mostly identical to `Chunks::__iterator_get_unchecked`.
        unsafe { from_raw_parts(self.v.as_ptr().add(start), self.chunk_size) }
    }
}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<'a, T> DoubleEndedIterator for ChunksExact<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.len() < self.chunk_size {
            None
        } else {
            let (fst, snd) = self.v.split_at(self.v.len() - self.chunk_size);
            self.v = fst;
            Some(snd)
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            let start = (len - 1 - n) * self.chunk_size;
            let end = start + self.chunk_size;
            let nth_back = &self.v[start..end];
            self.v = &self.v[..start];
            Some(nth_back)
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }
}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<T> ExactSizeIterator for ChunksExact<'_, T> {
    fn is_empty(&self) -> bool {
        self.v.is_empty()
    }
}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for ChunksExact<'_, T> {}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<T> FusedIterator for ChunksExact<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for ChunksExact<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for ChunksExact<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// An iterator over a slice in (non-overlapping) mutable chunks (`chunk_size`
/// elements at a time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last up to
/// `chunk_size-1` elements will be omitted but can be retrieved from the
/// [`into_remainder`] function from the iterator.
///
/// This struct is created by the [`chunks_exact_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = ['l', 'o', 'r', 'e', 'm'];
/// let iter = slice.chunks_exact_mut(2);
/// ```
///
/// [`chunks_exact_mut`]: slice::chunks_exact_mut
/// [`into_remainder`]: ChunksExactMut::into_remainder
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "chunks_exact", since = "1.31.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ChunksExactMut<'a, T: 'a> {
    /// # Safety
    /// This slice pointer must point at a valid region of `T` with at least length `v.len()`. Normally,
    /// those requirements would mean that we could instead use a `&mut [T]` here, but we cannot
    /// because `__iterator_get_unchecked` needs to return `&mut [T]`, which guarantees certain aliasing
    /// properties that we cannot uphold if we hold on to the full original `&mut [T]`. Wrapping a raw
    /// slice instead lets us hand out non-overlapping `&mut [T]` subslices of the slice we wrap.
    v: *mut [T],
    rem: &'a mut [T], // The iterator never yields from here, so this can be unique
    chunk_size: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> ChunksExactMut<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a mut [T], chunk_size: usize) -> Self {
        let rem = slice.len() % chunk_size;
        let fst_len = slice.len() - rem;
        // SAFETY: 0 <= fst_len <= slice.len() by construction above
        let (fst, snd) = unsafe { slice.split_at_mut_unchecked(fst_len) };
        Self { v: fst, rem: snd, chunk_size, _marker: PhantomData }
    }

    /// Returns the remainder of the original slice that is not going to be
    /// returned by the iterator. The returned slice has at most `chunk_size-1`
    /// elements.
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "chunks_exact", since = "1.31.0")]
    pub fn into_remainder(self) -> &'a mut [T] {
        self.rem
    }
}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<'a, T> Iterator for ChunksExactMut<'a, T> {
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        // SAFETY: we have `&mut self`, so are allowed to temporarily materialize a mut slice
        unsafe { &mut *self.v }.split_at_mut_checked(self.chunk_size).map(|(chunk, rest)| {
            self.v = rest;
            chunk
        })
    }

    #[inline]
    #[requires(self.chunk_size > 0)]
    #[ensures(|hint: &(usize, Option<usize>)| hint.1 == Some(hint.0) && hint.0 <= self.v.len())]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.v.len() / self.chunk_size;
        (n, Some(n))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        if let Some(start) = n.checked_mul(self.chunk_size)
            && start < self.v.len()
        {
            // SAFETY: `start < self.v.len()`
            self.v = unsafe { self.v.split_at_mut(start).1 };
            self.next()
        } else {
            self.v = &mut [];
            None
        }
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size).checked_add(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size).wrapping_add(self.chunk_size) <= self.v.len()
    )]
    #[ensures(|result: &&'a mut [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.chunk_size == old(self.chunk_size))
        && (self.rem.len() == old(self.rem.len()))
        && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        && (crate::ub_checks::can_dereference(&**result as *const [T]))
        && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let start = idx * self.chunk_size;
        // SAFETY: see comments for `Chunks::__iterator_get_unchecked` and `self.v`.
        unsafe { from_raw_parts_mut(self.v.as_mut_ptr().add(start), self.chunk_size) }
    }
}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<'a, T> DoubleEndedIterator for ChunksExactMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.len() < self.chunk_size {
            None
        } else {
            // SAFETY: This subtraction is inbounds because of the check above
            let (head, tail) = unsafe { self.v.split_at_mut(self.v.len() - self.chunk_size) };
            self.v = head;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *tail })
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            let start = (len - 1 - n) * self.chunk_size;
            let end = start + self.chunk_size;
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (temp, _tail) = unsafe { mem::replace(&mut self.v, &mut []).split_at_mut(end) };
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (head, nth_back) = unsafe { temp.split_at_mut(start) };
            self.v = head;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *nth_back })
        } else {
            self.v = &mut [];
            None
        }
    }
}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<T> ExactSizeIterator for ChunksExactMut<'_, T> {
    fn is_empty(&self) -> bool {
        self.v.is_empty()
    }
}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for ChunksExactMut<'_, T> {}

#[stable(feature = "chunks_exact", since = "1.31.0")]
impl<T> FusedIterator for ChunksExactMut<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for ChunksExactMut<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for ChunksExactMut<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

#[stable(feature = "chunks_exact", since = "1.31.0")]
unsafe impl<T> Send for ChunksExactMut<'_, T> where T: Send {}

#[stable(feature = "chunks_exact", since = "1.31.0")]
unsafe impl<T> Sync for ChunksExactMut<'_, T> where T: Sync {}

/// A windowed iterator over a slice in overlapping chunks (`N` elements at a
/// time), starting at the beginning of the slice
///
/// This struct is created by the [`array_windows`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = [0, 1, 2, 3];
/// let mut iter = slice.array_windows::<2>();
/// assert_eq!(iter.next(), Some(&[0, 1]));
/// assert_eq!(iter.next(), Some(&[1, 2]));
/// assert_eq!(iter.next(), Some(&[2, 3]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`array_windows`]: slice::array_windows
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "array_windows", since = "1.94.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ArrayWindows<'a, T: 'a, const N: usize> {
    v: &'a [T],
}

impl<'a, T: 'a, const N: usize> ArrayWindows<'a, T, N> {
    #[inline]
    pub(super) const fn new(slice: &'a [T]) -> Self {
        Self { v: slice }
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "array_windows", since = "1.94.0")]
impl<T, const N: usize> Clone for ArrayWindows<'_, T, N> {
    fn clone(&self) -> Self {
        Self { v: self.v }
    }
}

#[stable(feature = "array_windows", since = "1.94.0")]
impl<'a, T, const N: usize> Iterator for ArrayWindows<'a, T, N> {
    type Item = &'a [T; N];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.v.first_chunk();
        if ret.is_some() {
            self.v = &self.v[1..];
        }
        ret
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.v.len().saturating_sub(N - 1);
        (size, Some(size))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let idx = n.min(self.v.len());
        self.v = &self.v[idx..];
        self.next()
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        self.v.last_chunk()
    }

    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        // SAFETY: since the caller guarantees that `idx` is in bounds,
        // which means that `idx` cannot overflow an `isize`, and the
        // "slice" created by `cast_array` is a subslice of `self.v`
        // thus is guaranteed to be valid for the lifetime `'a` of `self.v`.
        unsafe { &*self.v.as_ptr().add(idx).cast_array() }
    }
}

#[stable(feature = "array_windows", since = "1.94.0")]
impl<'a, T, const N: usize> DoubleEndedIterator for ArrayWindows<'a, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T; N]> {
        let ret = self.v.last_chunk();
        if ret.is_some() {
            self.v = &self.v[..self.v.len() - 1];
        }
        ret
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<&'a [T; N]> {
        let idx = self.v.len().saturating_sub(n);
        self.v = &self.v[..idx];
        self.next_back()
    }
}

#[stable(feature = "array_windows", since = "1.94.0")]
impl<T, const N: usize> ExactSizeIterator for ArrayWindows<'_, T, N> {
    fn is_empty(&self) -> bool {
        self.v.len() < N
    }
}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T, const N: usize> TrustedLen for ArrayWindows<'_, T, N> {}

#[stable(feature = "array_windows", since = "1.94.0")]
impl<T, const N: usize> FusedIterator for ArrayWindows<'_, T, N> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<T, const N: usize> TrustedRandomAccess for ArrayWindows<'_, T, N> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<T, const N: usize> TrustedRandomAccessNoCoerce for ArrayWindows<'_, T, N> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// An iterator over a slice in (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the end of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last slice
/// of the iteration will be the remainder.
///
/// This struct is created by the [`rchunks`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let mut iter = slice.rchunks(2);
/// assert_eq!(iter.next(), Some(&['e', 'm'][..]));
/// assert_eq!(iter.next(), Some(&['o', 'r'][..]));
/// assert_eq!(iter.next(), Some(&['l'][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`rchunks`]: slice::rchunks
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "rchunks", since = "1.31.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RChunks<'a, T: 'a> {
    v: &'a [T],
    chunk_size: usize,
}

impl<'a, T: 'a> RChunks<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a [T], size: usize) -> Self {
        Self { v: slice, chunk_size: size }
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> Clone for RChunks<'_, T> {
    fn clone(&self) -> Self {
        RChunks { v: self.v, chunk_size: self.chunk_size }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> Iterator for RChunks<'a, T> {
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() {
            None
        } else {
            let idx = self.v.len().saturating_sub(self.chunk_size);
            // SAFETY: self.chunk_size() > 0, so 0 <= idx < self.v.len().
            // Thus `idx` is in-bounds for `self.v` and can be used as a valid argument for `split_at_mut_unchecked`.
            let (rest, chunk) = unsafe { self.v.split_at_unchecked(idx) };
            self.v = rest;
            Some(chunk)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.v.is_empty() {
            (0, Some(0))
        } else {
            let n = self.v.len().div_ceil(self.chunk_size);
            (n, Some(n))
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if let Some(end) = n.checked_mul(self.chunk_size)
            && end < self.v.len()
        {
            let end = self.v.len() - end;
            let rest = &self.v[..end];
            let (rest, chunk) = rest.split_at(end.saturating_sub(self.chunk_size));
            self.v = rest;
            Some(chunk)
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        if self.v.is_empty() {
            None
        } else {
            let rem = self.v.len() % self.chunk_size;
            let end = if rem == 0 { self.chunk_size } else { rem };
            Some(&self.v[0..end])
        }
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size) < self.v.len()
    )]
    #[ensures(|result: &&'a [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.chunk_size == old(self.chunk_size))
        && (crate::ub_checks::can_dereference(*result as *const [T]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end.saturating_sub(self.chunk_size);
        // SAFETY: mostly identical to `Chunks::__iterator_get_unchecked`.
        unsafe { from_raw_parts(self.v.as_ptr().add(start), end - start) }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> DoubleEndedIterator for RChunks<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() {
            None
        } else {
            let remainder = self.v.len() % self.chunk_size;
            let chunksz = if remainder != 0 { remainder } else { self.chunk_size };
            // SAFETY: similar to Chunks::next_back
            let (fst, snd) = unsafe { self.v.split_at_unchecked(chunksz) };
            self.v = snd;
            Some(fst)
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            let offset_from_end = (len - 1 - n) * self.chunk_size;
            let end = self.v.len() - offset_from_end;
            let start = end.saturating_sub(self.chunk_size);
            let nth_back = &self.v[start..end];
            self.v = &self.v[end..];
            Some(nth_back)
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> ExactSizeIterator for RChunks<'_, T> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for RChunks<'_, T> {}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> FusedIterator for RChunks<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for RChunks<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for RChunks<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// An iterator over a slice in (non-overlapping) mutable chunks (`chunk_size`
/// elements at a time), starting at the end of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last slice
/// of the iteration will be the remainder.
///
/// This struct is created by the [`rchunks_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = ['l', 'o', 'r', 'e', 'm'];
/// let iter = slice.rchunks_mut(2);
/// ```
///
/// [`rchunks_mut`]: slice::rchunks_mut
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "rchunks", since = "1.31.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RChunksMut<'a, T: 'a> {
    /// # Safety
    /// This slice pointer must point at a valid region of `T` with at least length `v.len()`. Normally,
    /// those requirements would mean that we could instead use a `&mut [T]` here, but we cannot
    /// because `__iterator_get_unchecked` needs to return `&mut [T]`, which guarantees certain aliasing
    /// properties that we cannot uphold if we hold on to the full original `&mut [T]`. Wrapping a raw
    /// slice instead lets us hand out non-overlapping `&mut [T]` subslices of the slice we wrap.
    v: *mut [T],
    chunk_size: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T: 'a> RChunksMut<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a mut [T], size: usize) -> Self {
        Self { v: slice, chunk_size: size, _marker: PhantomData }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> Iterator for RChunksMut<'a, T> {
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() {
            None
        } else {
            let idx = self.v.len().saturating_sub(self.chunk_size);
            // SAFETY: self.chunk_size() > 0, so 0 <= idx < self.v.len().
            // Thus `idx` is in-bounds for `self.v` and can be used as a valid argument for `split_at_mut_unchecked`.
            let (rest, chunk) = unsafe { self.v.split_at_mut_unchecked(idx) };
            self.v = rest;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *chunk })
        }
    }

    #[inline]
    #[requires(self.chunk_size > 0)]
    #[ensures(|hint: &(usize, Option<usize>)| hint.1 == Some(hint.0))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.v.is_empty() {
            (0, Some(0))
        } else {
            let n = self.v.len().div_ceil(self.chunk_size);
            (n, Some(n))
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        if let Some(end) = n.checked_mul(self.chunk_size)
            && end < self.v.len()
        {
            let end = self.v.len() - end;
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (rest, _) = unsafe { self.v.split_at_mut(end) };
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (rest, chunk) = unsafe { rest.split_at_mut(end.saturating_sub(self.chunk_size)) };
            self.v = rest;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *chunk })
        } else {
            self.v = &mut [];
            None
        }
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        if self.v.is_empty() {
            None
        } else {
            let rem = self.v.len() % self.chunk_size;
            let end = if rem == 0 { self.chunk_size } else { rem };
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *self.v.get_unchecked_mut(0..end) })
        }
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size) < self.v.len()
    )]
    #[ensures(|result: &&'a mut [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.chunk_size == old(self.chunk_size))
        && (crate::ub_checks::can_dereference(&**result as *const [T]))
        && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end.saturating_sub(self.chunk_size);
        // SAFETY: see comments for `RChunks::__iterator_get_unchecked` and
        // `ChunksMut::__iterator_get_unchecked`, `self.v`.
        unsafe { from_raw_parts_mut(self.v.as_mut_ptr().add(start), end - start) }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> DoubleEndedIterator for RChunksMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() {
            None
        } else {
            let remainder = self.v.len() % self.chunk_size;
            let sz = if remainder != 0 { remainder } else { self.chunk_size };
            // SAFETY: Similar to `Chunks::next_back`
            let (head, tail) = unsafe { self.v.split_at_mut_unchecked(sz) };
            self.v = tail;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *head })
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            // can't underflow because `n < len`
            let offset_from_end = (len - 1 - n) * self.chunk_size;
            let end = self.v.len() - offset_from_end;
            let start = end.saturating_sub(self.chunk_size);
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (tmp, tail) = unsafe { self.v.split_at_mut(end) };
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (_, nth_back) = unsafe { tmp.split_at_mut(start) };
            self.v = tail;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *nth_back })
        } else {
            self.v = &mut [];
            None
        }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> ExactSizeIterator for RChunksMut<'_, T> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for RChunksMut<'_, T> {}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> FusedIterator for RChunksMut<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for RChunksMut<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for RChunksMut<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

#[stable(feature = "rchunks", since = "1.31.0")]
unsafe impl<T> Send for RChunksMut<'_, T> where T: Send {}

#[stable(feature = "rchunks", since = "1.31.0")]
unsafe impl<T> Sync for RChunksMut<'_, T> where T: Sync {}

/// An iterator over a slice in (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the end of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last
/// up to `chunk_size-1` elements will be omitted but can be retrieved from
/// the [`remainder`] function from the iterator.
///
/// This struct is created by the [`rchunks_exact`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let mut iter = slice.rchunks_exact(2);
/// assert_eq!(iter.next(), Some(&['e', 'm'][..]));
/// assert_eq!(iter.next(), Some(&['o', 'r'][..]));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`rchunks_exact`]: slice::rchunks_exact
/// [`remainder`]: RChunksExact::remainder
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "rchunks", since = "1.31.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}

impl<'a, T> RChunksExact<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a [T], chunk_size: usize) -> Self {
        let rem = slice.len() % chunk_size;
        // SAFETY: 0 <= rem <= slice.len() by construction above
        let (fst, snd) = unsafe { slice.split_at_unchecked(rem) };
        Self { v: snd, rem: fst, chunk_size }
    }

    /// Returns the remainder of the original slice that is not going to be
    /// returned by the iterator. The returned slice has at most `chunk_size-1`
    /// elements.
    ///
    /// # Example
    ///
    /// ```
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = slice.rchunks_exact(2);
    /// assert_eq!(iter.remainder(), &['l'][..]);
    /// assert_eq!(iter.next(), Some(&['e', 'm'][..]));
    /// assert_eq!(iter.remainder(), &['l'][..]);
    /// assert_eq!(iter.next(), Some(&['o', 'r'][..]));
    /// assert_eq!(iter.remainder(), &['l'][..]);
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.remainder(), &['l'][..]);
    /// ```
    #[must_use]
    #[stable(feature = "rchunks", since = "1.31.0")]
    #[rustc_const_unstable(feature = "const_slice_make_iter", issue = "137737")]
    pub const fn remainder(&self) -> &'a [T] {
        self.rem
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> Clone for RChunksExact<'a, T> {
    fn clone(&self) -> RChunksExact<'a, T> {
        RChunksExact { v: self.v, rem: self.rem, chunk_size: self.chunk_size }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> Iterator for RChunksExact<'a, T> {
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.len() < self.chunk_size {
            None
        } else {
            let (fst, snd) = self.v.split_at(self.v.len() - self.chunk_size);
            self.v = fst;
            Some(snd)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.v.len() / self.chunk_size;
        (n, Some(n))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if let Some(end) = n.checked_mul(self.chunk_size)
            && end < self.v.len()
        {
            self.v = &self.v[..self.v.len() - end];
            self.next()
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && self.chunk_size <= self.v.len()
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size) <= self.v.len().wrapping_sub(self.chunk_size)
    )]
    #[ensures(|result: &&'a [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.chunk_size == old(self.chunk_size))
        && (self.rem.len() == old(self.rem.len()))
        && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        && (crate::ub_checks::can_dereference(*result as *const [T]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end - self.chunk_size;
        // SAFETY: mostly identical to `Chunks::__iterator_get_unchecked`.
        unsafe { from_raw_parts(self.v.as_ptr().add(start), self.chunk_size) }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> DoubleEndedIterator for RChunksExact<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.len() < self.chunk_size {
            None
        } else {
            let (fst, snd) = self.v.split_at(self.chunk_size);
            self.v = snd;
            Some(fst)
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            // now that we know that `n` corresponds to a chunk,
            // none of these operations can underflow/overflow
            let offset = (len - n) * self.chunk_size;
            let start = self.v.len() - offset;
            let end = start + self.chunk_size;
            let nth_back = &self.v[start..end];
            self.v = &self.v[end..];
            Some(nth_back)
        } else {
            self.v = &self.v[..0]; // cheaper than &[]
            None
        }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> ExactSizeIterator for RChunksExact<'a, T> {
    fn is_empty(&self) -> bool {
        self.v.is_empty()
    }
}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for RChunksExact<'_, T> {}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> FusedIterator for RChunksExact<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for RChunksExact<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for RChunksExact<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// An iterator over a slice in (non-overlapping) mutable chunks (`chunk_size`
/// elements at a time), starting at the end of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last up to
/// `chunk_size-1` elements will be omitted but can be retrieved from the
/// [`into_remainder`] function from the iterator.
///
/// This struct is created by the [`rchunks_exact_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = ['l', 'o', 'r', 'e', 'm'];
/// let iter = slice.rchunks_exact_mut(2);
/// ```
///
/// [`rchunks_exact_mut`]: slice::rchunks_exact_mut
/// [`into_remainder`]: RChunksExactMut::into_remainder
/// [slices]: slice
#[derive(Debug)]
#[stable(feature = "rchunks", since = "1.31.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RChunksExactMut<'a, T: 'a> {
    /// # Safety
    /// This slice pointer must point at a valid region of `T` with at least length `v.len()`. Normally,
    /// those requirements would mean that we could instead use a `&mut [T]` here, but we cannot
    /// because `__iterator_get_unchecked` needs to return `&mut [T]`, which guarantees certain aliasing
    /// properties that we cannot uphold if we hold on to the full original `&mut [T]`. Wrapping a raw
    /// slice instead lets us hand out non-overlapping `&mut [T]` subslices of the slice we wrap.
    v: *mut [T],
    rem: &'a mut [T],
    chunk_size: usize,
}

impl<'a, T> RChunksExactMut<'a, T> {
    #[inline]
    pub(super) const fn new(slice: &'a mut [T], chunk_size: usize) -> Self {
        let rem = slice.len() % chunk_size;
        // SAFETY: 0 <= rem <= slice.len() by construction above
        let (fst, snd) = unsafe { slice.split_at_mut_unchecked(rem) };
        Self { v: snd, rem: fst, chunk_size }
    }

    /// Returns the remainder of the original slice that is not going to be
    /// returned by the iterator. The returned slice has at most `chunk_size-1`
    /// elements.
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "rchunks", since = "1.31.0")]
    #[rustc_const_unstable(feature = "const_slice_make_iter", issue = "137737")]
    pub const fn into_remainder(self) -> &'a mut [T] {
        self.rem
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> Iterator for RChunksExactMut<'a, T> {
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.len() < self.chunk_size {
            None
        } else {
            let len = self.v.len();
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (head, tail) = unsafe { self.v.split_at_mut(len - self.chunk_size) };
            self.v = head;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *tail })
        }
    }

    #[inline]
    #[requires(self.chunk_size > 0)]
    #[ensures(|hint: &(usize, Option<usize>)| hint.1 == Some(hint.0))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.v.len() / self.chunk_size;
        (n, Some(n))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        if let Some(end) = n.checked_mul(self.chunk_size)
            && end < self.v.len()
        {
            let idx = self.v.len() - end;
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (fst, _) = unsafe { self.v.split_at_mut(idx) };
            self.v = fst;
            self.next()
        } else {
            self.v = &mut [];
            None
        }
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        self.chunk_size > 0
            && self.chunk_size <= self.v.len()
            && idx.checked_mul(self.chunk_size).is_some()
            && idx.wrapping_mul(self.chunk_size) <= self.v.len().wrapping_sub(self.chunk_size)
    )]
    #[ensures(|result: &&'a mut [T]| {
        (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.chunk_size == old(self.chunk_size))
        && (self.rem.len() == old(self.rem.len()))
        && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        && (crate::ub_checks::can_dereference(&**result as *const [T]))
        && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end - self.chunk_size;
        // SAFETY: see comments for `RChunksMut::__iterator_get_unchecked` and `self.v`.
        unsafe { from_raw_parts_mut(self.v.as_mut_ptr().add(start), self.chunk_size) }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<'a, T> DoubleEndedIterator for RChunksExactMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.len() < self.chunk_size {
            None
        } else {
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (head, tail) = unsafe { self.v.split_at_mut(self.chunk_size) };
            self.v = tail;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *head })
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let len = self.len();
        if n < len {
            // now that we know that `n` corresponds to a chunk,
            // none of these operations can underflow/overflow
            let offset = (len - n) * self.chunk_size;
            let start = self.v.len() - offset;
            let end = start + self.chunk_size;
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (tmp, tail) = unsafe { self.v.split_at_mut(end) };
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (_, nth_back) = unsafe { tmp.split_at_mut(start) };
            self.v = tail;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *nth_back })
        } else {
            self.v = &mut [];
            None
        }
    }
}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> ExactSizeIterator for RChunksExactMut<'_, T> {
    fn is_empty(&self) -> bool {
        self.v.is_empty()
    }
}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<T> TrustedLen for RChunksExactMut<'_, T> {}

#[stable(feature = "rchunks", since = "1.31.0")]
impl<T> FusedIterator for RChunksExactMut<'_, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for RChunksExactMut<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for RChunksExactMut<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

#[stable(feature = "rchunks", since = "1.31.0")]
unsafe impl<T> Send for RChunksExactMut<'_, T> where T: Send {}

#[stable(feature = "rchunks", since = "1.31.0")]
unsafe impl<T> Sync for RChunksExactMut<'_, T> where T: Sync {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for Iter<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for Iter<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccess for IterMut<'a, T> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl<'a, T> TrustedRandomAccessNoCoerce for IterMut<'a, T> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// An iterator over slice in (non-overlapping) chunks separated by a predicate.
///
/// This struct is created by the [`chunk_by`] method on [slices].
///
/// [`chunk_by`]: slice::chunk_by
/// [slices]: slice
#[stable(feature = "slice_group_by", since = "1.77.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ChunkBy<'a, T: 'a, P> {
    slice: &'a [T],
    predicate: P,
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> ChunkBy<'a, T, P> {
    pub(super) const fn new(slice: &'a [T], predicate: P) -> Self {
        ChunkBy { slice, predicate }
    }
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> Iterator for ChunkBy<'a, T, P>
where
    P: FnMut(&T, &T) -> bool,
{
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.slice.is_empty() {
            None
        } else {
            let mut len = 1;
            let mut iter = self.slice.windows(2);
            while let Some([l, r]) = iter.next() {
                if (self.predicate)(l, r) { len += 1 } else { break }
            }
            let (head, tail) = self.slice.split_at(len);
            self.slice = tail;
            Some(head)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.slice.is_empty() { (0, Some(0)) } else { (1, Some(self.slice.len())) }
    }

    #[inline]
    fn count(mut self) -> usize {
        let Some((mut previous, rest)) = self.slice.split_first() else {
            return 0;
        };

        let mut count = 1;
        for current in rest {
            count += usize::from(!(self.predicate)(previous, current));
            previous = current;
        }
        count
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> DoubleEndedIterator for ChunkBy<'a, T, P>
where
    P: FnMut(&T, &T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.slice.is_empty() {
            None
        } else {
            let mut len = 1;
            let mut iter = self.slice.windows(2);
            while let Some([l, r]) = iter.next_back() {
                if (self.predicate)(l, r) { len += 1 } else { break }
            }
            let (head, tail) = self.slice.split_at(self.slice.len() - len);
            self.slice = head;
            Some(tail)
        }
    }
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> FusedIterator for ChunkBy<'a, T, P> where P: FnMut(&T, &T) -> bool {}

#[stable(feature = "slice_group_by_clone", since = "1.89.0")]
impl<'a, T: 'a, P: Clone> Clone for ChunkBy<'a, T, P> {
    fn clone(&self) -> Self {
        Self { slice: self.slice, predicate: self.predicate.clone() }
    }
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a + fmt::Debug, P> fmt::Debug for ChunkBy<'a, T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChunkBy").field("slice", &self.slice).finish()
    }
}

/// An iterator over slice in (non-overlapping) mutable chunks separated
/// by a predicate.
///
/// This struct is created by the [`chunk_by_mut`] method on [slices].
///
/// [`chunk_by_mut`]: slice::chunk_by_mut
/// [slices]: slice
#[stable(feature = "slice_group_by", since = "1.77.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ChunkByMut<'a, T: 'a, P> {
    slice: &'a mut [T],
    predicate: P,
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> ChunkByMut<'a, T, P> {
    pub(super) const fn new(slice: &'a mut [T], predicate: P) -> Self {
        ChunkByMut { slice, predicate }
    }
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> Iterator for ChunkByMut<'a, T, P>
where
    P: FnMut(&T, &T) -> bool,
{
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.slice.is_empty() {
            None
        } else {
            let mut len = 1;
            let mut iter = self.slice.windows(2);
            while let Some([l, r]) = iter.next() {
                if (self.predicate)(l, r) { len += 1 } else { break }
            }
            let slice = mem::take(&mut self.slice);
            let (head, tail) = slice.split_at_mut(len);
            self.slice = tail;
            Some(head)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.slice.is_empty() { (0, Some(0)) } else { (1, Some(self.slice.len())) }
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> DoubleEndedIterator for ChunkByMut<'a, T, P>
where
    P: FnMut(&T, &T) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.slice.is_empty() {
            None
        } else {
            let mut len = 1;
            let mut iter = self.slice.windows(2);
            while let Some([l, r]) = iter.next_back() {
                if (self.predicate)(l, r) { len += 1 } else { break }
            }
            let slice = mem::take(&mut self.slice);
            let (head, tail) = slice.split_at_mut(slice.len() - len);
            self.slice = head;
            Some(tail)
        }
    }
}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a, P> FusedIterator for ChunkByMut<'a, T, P> where P: FnMut(&T, &T) -> bool {}

#[stable(feature = "slice_group_by", since = "1.77.0")]
impl<'a, T: 'a + fmt::Debug, P> fmt::Debug for ChunkByMut<'a, T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChunkByMut").field("slice", &self.slice).finish()
    }
}

/// Verify the safety of the code implemented in this module (including generated code from macros).
#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Unbounded input models and Kani safety harnesses for Challenge 18.
    //!
    //! Slice lengths and skip counts are symbolic. Element types and
    //! array-window widths use concrete instantiations.

    use super::*;
    use crate::ffi::c_int;
    use crate::{kani, ptr};

    // Keep proof diagnostics out of Rust's formatting machinery, avoiding
    // unnecessary recursive formatter types in SMT input. These macros retain
    // the assertions and evaluate each operand once.
    macro_rules! assert {
        ($condition:expr $(,)?) => {
            kani::safety_check_no_assume($condition, stringify!($condition))
        };
        ($condition:expr, $message:literal $(,)?) => {
            kani::safety_check_no_assume($condition, $message)
        };
    }

    macro_rules! assert_eq {
        ($left:expr, $right:expr $(,)?) => {
            kani::safety_check_no_assume(
                ($left) == ($right),
                concat!(stringify!($left), " == ", stringify!($right)),
            )
        };
    }

    // Select CVC5 for bit-vector queries that are expensive with CaDiCaL.
    // CVC5 is installed by the pinned Kani's Ubuntu and macOS setup scripts.
    macro_rules! chunk_getter_solver {
        (unit, $iterator:ident, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        (aligned_zst, $iterator:ident, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        (byte, RChunks, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        (byte, RChunksMut, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        (boolean, RChunks, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        (boolean, RChunksMut, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        (aligned_word, ChunksMut, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        (aligned_word, RChunks, $default:ident, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
        ($module:ident, $iterator:ident, $default:ident, $harness:item) => {
            #[kani::solver($default)]
            $harness
        };
    }

    /// State a callback may change, and its safety invariant at a loop head.
    ///
    /// A closure's bytes are not its captured referents. Consuming callbacks
    /// default to their own state; borrowed state needs a specialization.
    /// Predicate frames are supplied per model so call-through closures keep
    /// their capture pointers. An omitted target fails its assigns check.
    pub(super) trait CallbackState {
        fn frame(&self) -> *const [u8];
        fn predicate_frame(&self) -> *const [u8];
        fn invariant(&self, base: *const (), visited: usize) -> bool;
    }

    impl<F> CallbackState for F {
        default fn frame(&self) -> *const [u8] {
            ptr::slice_from_raw_parts(self as *const F as *const u8, mem::size_of::<F>())
        }

        default fn predicate_frame(&self) -> *const [u8] {
            ptr::slice_from_raw_parts(self as *const F as *const u8, 0)
        }

        default fn invariant(&self, _base: *const (), _visited: usize) -> bool {
            true
        }
    }

    impl<F> CallbackState for &mut F {
        fn frame(&self) -> *const [u8] {
            CallbackState::frame(&**self)
        }

        fn predicate_frame(&self) -> *const [u8] {
            CallbackState::predicate_frame(&**self)
        }

        fn invariant(&self, base: *const (), visited: usize) -> bool {
            CallbackState::invariant(&**self, base, visited)
        }
    }

    /// A callback with state behind a reference, like a borrowing closure.
    /// Its capture pointer stays fixed; only the pointed-to Option is writable.
    struct RetainFirst<'state, 'a, T> {
        retained: &'state mut Option<&'a mut T>,
    }

    impl<T> CallbackState for RetainFirst<'_, '_, T> {
        fn frame(&self) -> *const [u8] {
            ptr::slice_from_raw_parts(
                self.retained as *const Option<&mut T> as *const u8,
                mem::size_of::<Option<&mut T>>(),
            )
        }

        fn invariant(&self, base: *const (), visited: usize) -> bool {
            // Option<&mut T> has the reference's representation, with null for
            // None. Read that representation before interpreting havocked bytes
            // as a reference. A retained reference belongs to the visited prefix.
            let retained = unsafe { *(self.retained as *const Option<&mut T> as *const *mut T) };
            if visited == 0 {
                retained as usize == 0
            } else {
                retained as *mut () == base as *mut ()
                    // The loop frame also havocs visited elements. Keep the
                    // retained referent valid, not just the pointer's bits.
                    && unsafe { loop_elements_valid(base as *const T, 1) }
            }
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnOnce<(&'a mut T,)> for RetainFirst<'_, 'a, T> {
        type Output = ();

        extern "rust-call" fn call_once(mut self, args: (&'a mut T,)) {
            self.call_mut(args);
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnMut<(&'a mut T,)> for RetainFirst<'_, 'a, T> {
        extern "rust-call" fn call_mut(&mut self, (item,): (&'a mut T,)) {
            assert!(element_is_readable(item as *const T));
            if self.retained.is_none() {
                *self.retained = Some(item);
            } else {
                *item = kani::any();
            }
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnOnce<((), &'a mut T)> for RetainFirst<'_, 'a, T> {
        type Output = ();

        extern "rust-call" fn call_once(mut self, args: ((), &'a mut T)) {
            self.call_mut(args);
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnMut<((), &'a mut T)> for RetainFirst<'_, 'a, T> {
        extern "rust-call" fn call_mut(&mut self, ((), item): ((), &'a mut T)) {
            self.call_mut((item,));
        }
    }

    /// Like a move closure updating one of its own captures. Together with
    /// RetainFirst this exercises owned and borrowed callback state. The
    /// iterator observes only callback results and valid writes through items;
    /// other safe captured state does not affect its pointer arithmetic.
    struct Toggle(u8);

    impl CallbackState for Toggle {
        fn frame(&self) -> *const [u8] {
            ptr::slice_from_raw_parts(&self.0, 1)
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnOnce<(&'a mut T,)> for Toggle {
        type Output = ();

        extern "rust-call" fn call_once(mut self, args: (&'a mut T,)) {
            self.call_mut(args);
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnMut<(&'a mut T,)> for Toggle {
        extern "rust-call" fn call_mut(&mut self, (item,): (&'a mut T,)) {
            assert!(element_is_readable(item as *const T));
            self.0 ^= 1;
            *item = kani::any();
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnOnce<((), &'a mut T)> for Toggle {
        type Output = ();

        extern "rust-call" fn call_once(mut self, args: ((), &'a mut T)) {
            self.call_mut(args);
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnMut<((), &'a mut T)> for Toggle {
        extern "rust-call" fn call_mut(&mut self, ((), item): ((), &'a mut T)) {
            self.call_mut((item,));
        }
    }

    struct Predicate(u8);

    impl CallbackState for Predicate {
        fn predicate_frame(&self) -> *const [u8] {
            ptr::slice_from_raw_parts(&self.0, 1)
        }
    }

    impl<'a, T: Copy> FnOnce<(&'a T,)> for Predicate {
        type Output = bool;

        extern "rust-call" fn call_once(mut self, args: (&'a T,)) -> bool {
            self.call_mut(args)
        }
    }

    impl<'a, T: Copy> FnMut<(&'a T,)> for Predicate {
        extern "rust-call" fn call_mut(&mut self, (item,): (&'a T,)) -> bool {
            assert!(element_is_readable(item as *const T));
            let _value = *item;
            self.0 ^= 1;
            kani::any()
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnOnce<(&'a mut T,)> for Predicate {
        type Output = bool;

        extern "rust-call" fn call_once(mut self, args: (&'a mut T,)) -> bool {
            self.call_mut(args)
        }
    }

    impl<'a, T: Copy + kani::Arbitrary> FnMut<(&'a mut T,)> for Predicate {
        extern "rust-call" fn call_mut(&mut self, (item,): (&'a mut T,)) -> bool {
            assert!(element_is_readable(item as *const T));
            *item = kani::any();
            self.0 ^= 1;
            kani::any()
        }
    }

    // Specification-only encodings must admit exactly the same index domain.
    // Keeping these checks independent avoids assuming the equivalence in a getter.
    #[kani::proof]
    fn check_chunk_precondition_encodings() {
        let index: usize = kani::any();
        let size: usize = kani::any();
        let len: usize = kani::any();
        let product = index.checked_mul(size);
        let wrapped = index.wrapping_mul(size);
        let partial = product.is_some_and(|start| start < len);
        assert_eq!(partial, product.is_some() && wrapped < len);
        let exact = product.and_then(|start| start.checked_add(size)).is_some_and(|end| end <= len);
        assert_eq!(
            exact,
            product.is_some()
                && wrapped.checked_add(size).is_some()
                && wrapped.wrapping_add(size) <= len,
        );
        // The early getter filter below repeats the native exact-getter
        // precondition. Prove its checked-value spelling for every usize.
        let exact_filter =
            size > 0 && size <= len && product.is_some_and(|start| start <= len.wrapping_sub(size));
        let exact_native =
            size > 0 && size <= len && product.is_some() && wrapped <= len.wrapping_sub(size);
        assert_eq!(exact_filter, exact_native);
        kani::cover(partial, "admissible partial-chunk index");
        kani::cover(exact && size > 0, "admissible exact-chunk index");
        kani::cover(product.is_none(), "overflowing product excluded");
        kani::cover(size == 0, "zero-size encoding still agrees");
        kani::cover(wrapped == usize::MAX && product.is_some(), "maximal product");
    }

    // The auxiliary bounds used to select getter arguments are consequences
    // of the original range preconditions, not smaller verification limits.
    #[kani::proof]
    fn check_getter_argument_bounds() {
        let index: usize = kani::any();
        let size: usize = kani::any();
        let len: usize = kani::any();
        if size > 0 {
            if let Some(start) = index.checked_mul(size) {
                if start < len {
                    assert!(index < len);
                    kani::cover(index == 0, "first partial chunk index");
                    kani::cover(index > isize::MAX as usize, "large ZST-compatible index");
                }
                if let Some(end) = start.checked_add(size) {
                    if end <= len {
                        assert!(index < len);
                        assert!(size <= len);
                        kani::cover(size == len, "one exact chunk");
                        kani::cover(index > 0, "nonzero exact chunk index");
                        kani::cover(len == usize::MAX, "maximal exact input length");
                    }
                }
            }
        }
    }

    // The subtraction form used by exact getters avoids addition overflow in
    // the specification while admitting precisely the same complete ranges.
    #[kani::proof]
    fn check_exact_chunk_range() {
        let start: usize = kani::any();
        let size: usize = kani::any();
        let len: usize = kani::any();
        let checked = start.checked_add(size).is_some_and(|end| end <= len);
        let subtraction = size <= len && start <= len.wrapping_sub(size);
        assert_eq!(checked, subtraction);
        kani::cover(checked && size > 0, "nonempty complete range");
        kani::cover(checked && start > 0, "interior complete range");
        kani::cover(checked && len == usize::MAX, "maximal complete range");
        kani::cover(start.checked_add(size).is_none(), "overflowing range excluded");
        kani::cover(size > len && !subtraction, "oversized chunk excluded");
    }

    // ArrayWindows' four step methods branch on the remaining length, not on
    // particular positive values of N. Check their index bounds for arbitrary N;
    // the typed-pointer paths still run in the N = 1, 2, 4 harnesses below.
    #[kani::proof]
    fn check_array_window_bounds() {
        let len: usize = kani::any();
        let width: usize = kani::any();
        let n: usize = kani::any();
        if width == 0 {
            // slice::array_windows rejects zero before constructing the iterator.
            return;
        }

        let skipped = n.min(len);
        let forward = len - skipped;
        let backward = len.saturating_sub(n);
        assert_eq!(forward, backward);
        if forward >= width {
            assert!(skipped < len);
            assert!(skipped + width <= len);
            assert!(skipped + 1 <= len);
            kani::cover(true, "forward window and iterator advance fit");
        }
        if backward >= width {
            let start = backward - width;
            assert!(start + width == backward);
            assert!(backward <= len);
            assert!(backward - 1 < len);
            kani::cover(true, "backward window and iterator retreat fit");
        }
        if len >= width {
            assert!(len - width + 1 <= len);
        }
        kani::cover(width == 1 && len == 0, "single-element window absent");
        kani::cover(width == 2 && len == 3 && n == 1, "nonzero skip to a full window");
        kani::cover(width == 4 && len == 6 && n == 1, "overlapping windows remain");
        kani::cover(width > 4 && len == usize::MAX && n == 0, "other and maximal widths");
        kani::cover(n > len, "saturating skip past the input");
    }

    // Getter harnesses target the original Iterator implementation directly.
    // For positive chunk size, a checked start strictly below len is equivalent
    // to idx < ceil(len / size); a full remaining chunk is equivalent to
    // idx < floor(len / size). These spatial forms admit every documented index
    // without a division oracle or a replacement getter.
    // TrustedRandomAccess's history-dependent caller obligations still apply.

    fn any_slice<T>(orig_slice: &[T]) -> &[T] {
        if kani::any() {
            let len = kani::any_where(|len: &usize| *len <= orig_slice.len());
            kani::cover(true, "admissible symbolic view length");
            let start = kani::any_where(|start: &usize| *start <= orig_slice.len() - len);
            kani::cover(true, "admissible symbolic view start");
            // SAFETY: start + len <= orig_slice.len(); the original borrow
            // keeps this initialized subregion alive for the returned lifetime.
            unsafe { from_raw_parts(orig_slice.as_ptr().wrapping_add(start), len) }
        } else {
            let ptr = kani::any_where::<usize, _>(|val| *val != 0) as *const T;
            kani::cover(true, "admissible symbolic ptr");
            kani::assume(ptr.is_aligned());
            kani::cover(true, "aligned dangling shared slice");
            // SAFETY: an empty slice only needs a non-null, aligned pointer.
            unsafe { crate::slice::from_raw_parts(ptr, 0) }
        }
    }

    // Preserve the upstream checks for iterator APIs and types outside the
    // symbolic suites. The fixed-size arrays belong to these regression proofs.
    fn any_iter<T>(orig_slice: &[T]) -> Iter<'_, T> {
        Iter::new(any_slice(orig_slice))
    }

    /// Macro that generates a harness for a given `Iter` method.
    ///
    /// Takes the name of the harness, the element type, and an expression to check.
    macro_rules! check_safe_abstraction {
        ($harness:ident, $ty:ty, $call:expr) => {
            #[kani::proof]
            fn $harness() {
                let array: [$ty; MAX_LEN] = kani::any();
                let mut iter = any_iter(&array);
                let target = $call;
                target(&mut iter);
                assert!(iter.is_safe());
                kani::cover(true, "iterator remains safe after the call");
            }
        };
    }

    macro_rules! check_iter_wrappers {
        ($ty:ty) => {
            #[kani::proof]
            fn check_default() {
                let iter: Iter<'_, $ty> = Iter::default();
                assert!(iter.is_safe());
                kani::cover(iter.is_empty(), "default iterator is empty");
            }

            // Public functions that call safe abstraction `make_slice`.
            check_safe_abstraction!(check_as_slice, $ty, |iter: &mut Iter<'_, $ty>| {
                iter.as_slice();
            });
            check_safe_abstraction!(check_as_ref, $ty, |iter: &mut Iter<'_, $ty>| {
                iter.as_ref();
            });
            // Ensure that clone always generates a safe object.
            check_safe_abstraction!(check_clone, $ty, |iter: &mut Iter<'_, $ty>| {
                assert!(iter.clone().is_safe());
            });
        };
    }

    /// Macro that generates a harness for a given unsafe `Iter` method.
    ///
    /// Takes:
    /// 1. The name of the harness
    /// 2. the element type
    /// 3. the target function
    /// 4. the optional arguments.
    macro_rules! check_unsafe_contracts {
        ($harness:ident, $ty:ty, $func:ident($($arg:expr),*)) => {
            #[kani::proof_for_contract(Iter::$func)]
            fn $harness() {
                let array: [$ty; MAX_LEN] = kani::any();
                let mut iter = any_iter(&array);
                let _ = unsafe { iter.$func($($arg),*) };
                kani::cover(true, "iterator contract exercised");
            }
        };
    }

    macro_rules! check_iter_with_ty {
        ($module:ident, $ty:ty) => {
            mod $module {
                use super::*;
                const MAX_LEN: usize = 50;

                check_iter_wrappers!($ty);

                #[kani::proof]
                fn check_new_iter() {
                    let array: [$ty; MAX_LEN] = kani::any();
                    let iter = any_iter(&array);
                    assert!(iter.is_safe());
                    kani::cover(true, "iterator construction reached");
                }

                /// Count consumes the value, thus, invoke it directly.
                #[kani::proof]
                fn check_count() {
                    let array: [$ty; MAX_LEN] = kani::any();
                    let iter = any_iter(&array);
                    iter.count();
                    kani::cover(true, "iterator count reached");
                }

                check_unsafe_contracts!(check_next_back_unchecked, $ty, next_back_unchecked());
                check_unsafe_contracts!(check_post_inc_start, $ty, post_inc_start(kani::any()));
                check_unsafe_contracts!(check_pre_dec_end, $ty, pre_dec_end(kani::any()));

                check_safe_abstraction!(check_advance_back_by, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.advance_back_by(kani::any());
                });
                check_safe_abstraction!(check_is_empty, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.is_empty();
                });
                check_safe_abstraction!(check_len, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.len();
                });
                check_safe_abstraction!(check_size_hint, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.size_hint();
                });
                check_safe_abstraction!(check_nth, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.nth(kani::any());
                });
                check_safe_abstraction!(check_advance_by, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.advance_by(kani::any());
                });
                check_safe_abstraction!(check_next_back, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.next_back();
                });
                check_safe_abstraction!(check_nth_back, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.nth_back(kani::any());
                });
                check_safe_abstraction!(check_next, $ty, |iter: &mut Iter<'_, $ty>| {
                    let _ = iter.next();
                });
            }
        };
    }

    mod verify_unit {
        use super::*;
        const MAX_LEN: usize = isize::MAX as usize;
        check_iter_wrappers!(());
    }

    mod verify_u8 {
        use super::*;
        const MAX_LEN: usize = u32::MAX as usize;
        check_iter_wrappers!(u8);
    }

    check_iter_with_ty!(verify_char, char);
    check_iter_with_ty!(verify_tup, (char, u8));

    // Challenge 18 asks for access safety, not full iterator semantics. All
    // lengths and positive chunk sizes are symbolic; no loop over a slice is
    // unwound. Exact-step inputs overapproximate valid constructor states by
    // admitting any disjoint main/remainder partition. Constructors are checked
    // separately on their real inputs. Only nth_back abstracts a separately
    // verified size_hint contract; its body and unsafe accesses still execute.
    //
    // Non-ZST storage covers the backend-representable allocation domain;
    // ZST lengths cover every usize. Concrete type instantiations and N = 1,
    // 2, 4 do not establish the challenge's no-monomorphization requirement.
    // Memory predicates establish spatial validity, not lifetime ownership or
    // the complete history-dependent TrustedRandomAccess caller protocol.

    // Sized byte pointers have the same C ABI as void pointers. The allocation contains
    // untyped storage, not a Rust c_void enum value; byte-pointer declarations also avoid
    // Kani's unsupported c_void mutable-cast validity check. No target checks are disabled.
    unsafe extern "C" {
        fn posix_memalign(out: *mut *mut u8, alignment: usize, size: usize) -> c_int;
        fn free(ptr: *const u8);
        // CBMC's input-model primitive: initializes every byte of a fresh allocation
        // nondeterministically. It changes object contents, not allocation metadata.
        fn __CPROVER_havoc_object(ptr: *mut u8);
        // Set by CBMC from --object-bits, not a host allocation or a guessed size constant.
        static __CPROVER_max_malloc_size: usize;
    }

    const fn same_type_name(left: &str, right: &str) -> bool {
        let left = left.as_bytes();
        let right = right.as_bytes();
        if left.len() != right.len() {
            return false;
        }
        let mut index = 0;
        while index < left.len() {
            if left[index] != right[index] {
                return false;
            }
            index += 1;
        }
        true
    }

    #[rustc_const_unstable(feature = "kani", issue = "none")]
    pub(super) const fn element_validity_kind<T>() -> u8 {
        let name = crate::any::type_name::<T>();
        if same_type_name(name, "bool") {
            1
        } else if same_type_name(name, "u8")
            || same_type_name(name, "()")
            || same_type_name(name, "[u8; 3]")
            || same_type_name(name, "core::slice::iter::verify::Padded")
            || same_type_name(name, "core::slice::iter::verify::AlignedZst")
            || same_type_name(name, "core::slice::iter::verify::AlignedWord")
        {
            0
        } else {
            255
        }
    }

    // One arbitrary observed element replaces an unbounded validity quantifier.
    // Initial bytes outside this element are unconstrained, so every valid
    // slice is included. Checking preservation at an arbitrary element proves
    // preservation at every element of a valid slice. Iterator control sees
    // arbitrary predicate results; no model branches on unobserved T values.
    // This is an abstraction for the concrete Copy types, not a generic-T proof.
    static mut OBSERVED_ELEMENT: *const u8 = ptr::null();
    static mut SYMBOLIC_SLICE_ACTIVE: bool = false;

    // Contract proofs havoc mutable statics. Initialize only this model's
    // verification state at harness entry, before constructing any input.
    fn reset_observation() {
        unsafe {
            OBSERVED_ELEMENT = ptr::null();
            SYMBOLIC_SLICE_ACTIVE = false;
        }
    }

    // Kani #4796: a helper called from both a loop clause and ordinary code can
    // lose DFCC's internal write-set argument. Clause-only helpers below use
    // these same expressions without calling shared methods or functions.
    macro_rules! element_representation_valid {
        ($ty:ty, $data:expr) => {{
            let data: *const $ty = $data;
            match const { element_validity_kind::<$ty>() } {
                0 => true,
                1 => unsafe { *(data as *const u8) <= 1 },
                _ => false,
            }
        }};
    }

    macro_rules! observation_in_region {
        ($ty:ty, $data:expr, $len:expr) => {{
            let data: *const $ty = $data;
            let len: usize = $len;
            let size = const { mem::size_of::<$ty>() };
            // SAFETY: this ghost pointer is initialized before creating an input.
            let observed = unsafe { OBSERVED_ELEMENT };
            if size == 0 || len == 0 || observed as usize == 0 {
                false
            } else if len > usize::MAX / size {
                false
            } else {
                let bytes = len * size;
                let offset = crate::intrinsics::wrapping_sub(observed as usize, data as usize);
                offset < bytes && offset % size == 0
            }
        }};
    }

    /// Test one representation through initialized raw storage, not an invalid T.
    unsafe fn element_bits_valid<T>(data: *const T) -> bool {
        element_representation_valid!(T, data)
    }

    /// Whether the arbitrary observation lies on an element of this interval.
    fn observes_region<T>(data: *const T, len: usize) -> bool {
        observation_in_region!(T, data, len)
    }

    /// Validity at the arbitrary observed element, if it belongs to this region.
    ///
    /// # Safety
    /// This region must have live initialized storage, aligned for T. No value
    /// validity is required: this predicate checks it at the observed element.
    pub(super) unsafe fn observed_elements_valid<T>(data: *const T, len: usize) -> bool {
        !observes_region(data, len) || unsafe { element_bits_valid((OBSERVED_ELEMENT).cast::<T>()) }
    }

    /// The same predicate for loop clauses, avoiding shared DFCC callees (#4796).
    ///
    /// # Safety
    /// The storage requirements are the same as for `observed_elements_valid`.
    pub(super) unsafe fn loop_elements_valid<T>(data: *const T, len: usize) -> bool {
        !observation_in_region!(T, data, len)
            || element_representation_valid!(T, unsafe { OBSERVED_ELEMENT as *const T })
    }

    // Separate spatial readability from scalar validity explicitly. MaybeUninit
    // imposes no value/padding requirements on unobserved elements; the second
    // conjunct checks the arbitrary observed element's actual representation.
    fn region_is_readable<T>(data: *const T, len: usize) -> bool {
        crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(
            data.cast::<mem::MaybeUninit<T>>(),
            len,
        )) && unsafe { observed_elements_valid(data, len) }
    }

    fn element_is_readable<T>(data: *const T) -> bool {
        region_is_readable(data, 1)
    }

    /// Describes a remaining interval without first loading a potentially havocked NonNull.
    /// The exact pointer identities recover the original allocation and alignment; actual
    /// accesses in the iterator body are still checked by Kani.
    ///
    /// # Safety
    /// ptr_field must point to an initialized NonNull field (its bytes may encode an invalid
    /// NonNull while checking a loop hypothesis). initial_ptr must describe live initialized
    /// storage for initial_len elements, or be aligned/non-null for an empty or ZST region.
    pub(super) unsafe fn iter_state_matches<T>(
        ptr_field: *const NonNull<T>,
        end_or_len: *const T,
        initial_ptr: *mut T,
        initial_len: usize,
        front: usize,
        back: usize,
    ) -> bool {
        if front > initial_len || back > initial_len - front {
            return false;
        }
        // NonNull is transparent over a pointer. Read its representation as a raw pointer
        // so an invalid hypothesis is rejected by comparison before any NonNull method call.
        let current = unsafe { *(ptr_field as *const *mut T) };
        // SAFETY: arith_offset implements wrapping pointer arithmetic with no
        // preconditions, including ZST indices above isize::MAX.
        let expected = unsafe { crate::intrinsics::arith_offset(initial_ptr, front as isize) };
        if current != expected as *mut T {
            return false;
        }
        let remaining = initial_len - front - back;
        let end_matches = if T::IS_ZST {
            end_or_len as usize == remaining
        } else {
            // SAFETY: as above; this computes a pointer without dereferencing it.
            end_or_len
                == unsafe {
                    crate::intrinsics::arith_offset(initial_ptr, (initial_len - back) as isize)
                }
        };
        end_matches
            && ((const { element_validity_kind::<T>() == 0 })
                || unsafe { loop_elements_valid(current, remaining) })
    }

    /// Initialized storage with one arbitrary element's validity constrained.
    /// Other bytes overapproximate valid slice inputs; all reads/returned regions
    /// check validity at the observation. Copy excludes unrelated destructor loops.
    struct SymbolicSlice<T: Copy> {
        data: *mut T,
        len: usize,
        allocation: *mut u8,
    }

    impl<T: Copy + kani::Arbitrary> SymbolicSlice<T> {
        fn any() -> Self {
            Self::with_optional_suffix::<false>()
        }

        fn with_optional_suffix<const WITH_SUFFIX: bool>() -> Self {
            assert!(
                const { element_validity_kind::<T>() != 255 },
                "SymbolicSlice needs a complete element-validity predicate for T",
            );
            assert!(!unsafe { SYMBOLIC_SLICE_ACTIVE }, "one active symbolic slice per harness");
            unsafe {
                SYMBOLIC_SLICE_ACTIVE = true;
                OBSERVED_ELEMENT = ptr::null();
            }
            let len: usize = kani::any();
            let element_size = mem::size_of::<T>();
            // size_of::<T>() is a multiple of align_of::<T>(). Thus this
            // division is exactly the Layout::array bound, without bringing
            // Result::unwrap's formatting types into SMT's datatype graph.
            if element_size != 0 {
                kani::assume(len <= isize::MAX as usize / element_size);
                kani::cover(true, "slice byte length fits isize");
            }
            let bytes = len * element_size;
            if bytes == 0 && (!WITH_SUFFIX || element_size == 0 || kani::any()) {
                // For a nonempty ZST slice, establish that T has an inhabitant as well.
                if len != 0 {
                    let _: T = kani::any();
                }
                let address: usize = kani::any();
                let data = address as *mut T;
                kani::assume(!data.is_null() && data.is_aligned());
                kani::cover(true, "non-null aligned empty or ZST slice");
                return Self { data, len, allocation: ptr::null_mut() };
            }

            // The pointer encoding reserves object-id bits. Requests outside its offset
            // domain are not representable allocations (and also violate loop-frame CAR
            // bounds). Read the backend's own limit so changing --object-bits stays coherent.
            // SAFETY: CBMC provides this immutable, initialized runtime constant.
            let model_limit = unsafe { __CPROVER_max_malloc_size };
            kani::assume(bytes < model_limit);
            kani::cover(true, "allocation fits the backend object model");
            // Model an arbitrary aligned interior start, not just the stronger
            // alignment of a POSIX allocation. In particular, u8 slices may
            // start at odd addresses, and a prefix need not be a multiple of
            // size_of::<T>(). Only align_of::<T>() is required.
            let prefix: usize = kani::any();
            kani::assume(prefix % mem::align_of::<T>() == 0);
            kani::cover(true, "slice prefix respects element alignment");
            kani::assume(prefix < model_limit - bytes);
            kani::cover(true, "prefix and slice fit in one allocation");
            let used = prefix + bytes;
            let allocation_bytes = if WITH_SUFFIX {
                let suffix = kani::any_where(|suffix: &usize| {
                    *suffix < model_limit - used && (used > 0 || *suffix > 0)
                });
                kani::cover(true, "nonempty allocation including arbitrary suffix bytes");
                kani::cover(suffix > 0 && bytes == 0, "allocated empty slice with trailing bytes");
                kani::cover(suffix > 0 && bytes > 0, "nonempty slice with trailing bytes");
                used + suffix
            } else {
                used
            };
            let mut memory = ptr::null_mut();
            let alignment = mem::align_of::<T>().max(mem::size_of::<*mut u8>());
            // SAFETY: alignment is a power of two and a multiple of sizeof(void*), and out
            // points to a live local. The prefix and slice both fit in this allocation.
            let status = unsafe { posix_memalign(&mut memory, alignment, allocation_bytes) };
            // We need valid existing slices, so allocation failure is not an input case.
            kani::assume(status == 0);
            kani::cover(true, "existing slice allocation succeeds");
            let data = memory.wrapping_add(prefix).cast::<T>();
            assert!(!data.is_null() && data.is_aligned());
            assert!(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(data, len)));
            // SAFETY: this is fresh, exclusively owned, live storage; no references have
            // been created yet. The CBMC primitive writes independent initialized bytes
            // throughout this allocation. Constrain the arbitrary observation
            // before testing any iterator operation. Other initialized bytes
            // overapproximate the valid-input domain; they are never assumed
            // valid after the operation to make a read check pass.
            unsafe { __CPROVER_havoc_object(memory) };
            if const { element_validity_kind::<T>() != 0 } {
                let index = kani::any_where(|index: &usize| *index < len);
                kani::cover(true, "admissible symbolic index");
                let observed = data.wrapping_add(index);
                unsafe { OBSERVED_ELEMENT = observed.cast::<u8>() };
                // This is the only scalar-validity assumption. It precedes the
                // tested operation; later reads and loop invariants must prove it.
                kani::assume(unsafe { element_bits_valid(observed) });
                kani::cover(true, "initial observed element is valid");
            }
            Self { data, len, allocation: memory }
        }
    }

    impl<T: Copy> SymbolicSlice<T> {
        // Typed views belong to the abstract Kani input model: unobserved
        // representations remain unconstrained. This is not a Rust allocator
        // establishing every value, initialization or aliasing obligation.
        fn as_slice(&self) -> &[T] {
            // SAFETY (Kani model): storage is live, initialized and aligned;
            // scalar validity uses the arbitrary observation documented above.
            unsafe { from_raw_parts(self.data, self.len) }
        }

        fn as_mut_slice(&mut self) -> &mut [T] {
            // SAFETY (Kani model): the same storage abstraction applies, and
            // the mutable borrow prevents another view while this one is live.
            unsafe { from_raw_parts_mut(self.data, self.len) }
        }
    }

    impl<T: Copy> Drop for SymbolicSlice<T> {
        fn drop(&mut self) {
            // Include early returns/breaks from consuming iterator methods.
            // No operation may leave the arbitrary original element invalid.
            assert!(unsafe { observed_elements_valid(self.data, self.len) });
            kani::cover(true, "original input validity checked at cleanup");
            unsafe {
                OBSERVED_ELEMENT = ptr::null();
                SYMBOLIC_SLICE_ACTIVE = false;
            }
            if !self.allocation.is_null() {
                // SAFETY: free the allocation base, not its interior slice pointer.
                // T is Copy, so no element destructor is skipped.
                unsafe { free(self.allocation.cast_const()) };
            }
        }
    }

    #[kani::proof]
    fn check_symbolic_byte_slice_domain() {
        reset_observation();
        let mut storage = SymbolicSlice::<u8>::any();
        let len = storage.len;
        let data = storage.data;
        let prefix = data.addr().wrapping_sub(storage.allocation.addr());
        let mut slice = storage.as_mut_slice();
        check_slice(&slice, data, 0, len);
        touch_mut(&mut slice);
        kani::cover(len == 0, "empty symbolic slice");
        kani::cover(len > 1 && data.addr() % 8 == 1, "odd byte-slice address");
        kani::cover(len > 1 && prefix > 8, "arbitrary interior allocation offset");
        kani::cover(
            len == unsafe { __CPROVER_max_malloc_size } - 1,
            "full backend allocation length remains possible",
        );
    }

    #[kani::proof]
    fn check_bool_validity_predicate() {
        reset_observation();
        let bytes: [u8; 2] = kani::any();
        let index = kani::any_where(|index: &usize| *index < bytes.len());
        kani::cover(true, "admissible symbolic index");
        let point = bytes.as_ptr().wrapping_add(index).cast::<bool>();
        unsafe { OBSERVED_ELEMENT = point.cast::<u8>() };
        let valid = unsafe { observed_elements_valid(point, 1) };
        assert_eq!(valid, bytes[index] <= 1);
        let other = bytes.as_ptr().wrapping_add(1 - index).cast::<bool>();
        assert!(unsafe { observed_elements_valid(other, 1) });
        kani::cover(valid, "valid observed boolean");
        kani::cover(!valid, "invalid observed boolean");
    }

    #[kani::proof]
    fn check_observed_invalid_write_is_detected() {
        reset_observation();
        let initial: [bool; 2] = kani::any();
        let mut bytes = [initial[0] as u8, initial[1] as u8];
        let observed = kani::any_where(|index: &usize| *index < bytes.len());
        kani::cover(true, "admissible symbolic observed");
        let changed = kani::any_where(|index: &usize| *index < bytes.len());
        kani::cover(true, "admissible symbolic changed");
        let data = bytes.as_ptr().cast::<bool>();
        unsafe { OBSERVED_ELEMENT = data.wrapping_add(observed).cast::<u8>() };
        let invalid = kani::any_where(|byte: &u8| *byte > 1);
        kani::cover(true, "admissible invalid boolean representation");
        bytes[changed] = invalid;
        let valid = unsafe { observed_elements_valid(data, bytes.len()) };
        assert_eq!(valid, observed != changed);
        kani::cover(valid, "mutation outside observation preserves observed validity");
        kani::cover(observed == changed && !valid, "invalid mutation detected at observation");
    }

    #[kani::proof]
    fn check_bool_input_domain() {
        reset_observation();
        let storage = SymbolicSlice::<bool>::any();
        kani::cover(storage.len == 0, "empty iterator");
        kani::cover(storage.len > 1, "multiple elements");
        let index: usize = kani::any();
        if index < storage.len && observes_region(storage.data.wrapping_add(index), 1) {
            // SAFETY: the fresh allocation contains initialized bytes for every element;
            // the symbolic index is in bounds. Inspect raw bytes without
            // loading a potentially invalid bool from unobserved storage.
            let bits = unsafe { *storage.data.wrapping_add(index).cast::<u8>() };
            assert!(bits <= 1);
            kani::cover(true, "nonempty symbolic boolean read");
        }
    }

    fn any_slice_mut<T>(original: &mut [T]) -> &mut [T] {
        if kani::any() {
            let len = kani::any_where(|len: &usize| *len <= original.len());
            kani::cover(true, "admissible symbolic view length");
            let start = kani::any_where(|start: &usize| *start <= original.len() - len);
            kani::cover(true, "admissible symbolic view start");
            // SAFETY: start + len <= original.len(). This constructs an input
            // view without introducing slice-index panic formatting into SMT.
            unsafe { from_raw_parts_mut(original.as_mut_ptr().wrapping_add(start), len) }
        } else {
            let data = kani::any::<usize>() as *mut T;
            kani::assume(!data.is_null() && data.is_aligned());
            kani::cover(true, "non-null aligned empty or ZST slice");
            // SAFETY: empty slices require non-null, aligned pointers, not an allocation.
            unsafe { from_raw_parts_mut(data, 0) }
        }
    }

    // Both parameterizations describe exactly every interval in a slice.
    // This check has no assumptions and includes the full usize domain.
    #[kani::proof]
    fn check_view_domain_equivalence() {
        let total: usize = kani::any();
        let first: usize = kani::any();
        let last: usize = kani::any();
        if first <= last && last <= total {
            let len = last - first;
            assert!(len <= total);
            assert!(first <= total - len);
            assert_eq!(first + len, last);
            // The same interval after advancing from both ends.
            let back = total - last;
            assert!(back <= total - first);
            assert_eq!(total - first - back, len);
            kani::cover(len == 0, "empty interval in endpoint form");
            kani::cover(first > 0 && len > 0, "interior interval in endpoint form");
            kani::cover(len == usize::MAX, "maximal interval in endpoint form");
            kani::cover(
                first > 0 && last < total && len > 0,
                "nonempty interval after advancing both ends",
            );
        }
        let len: usize = kani::any();
        let start: usize = kani::any();
        if len <= total && start <= total - len {
            let end = start + len;
            assert!(start <= end && end <= total);
            assert_eq!(end - start, len);
            let back = total - end;
            assert!(back <= total - start);
            assert_eq!(total - start - back, len);
            kani::cover(len == 0 && start == total, "empty interval at the end");
            kani::cover(start > 0 && len > 0, "interior interval in length form");
            kani::cover(len == usize::MAX, "maximal interval in length form");
        }
    }

    macro_rules! check_writable_region {
        (as_slice, $data:expr, $len:expr) => {};
        (as_mut_slice, $data:expr, $len:expr) => {
            assert!(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(
                ($data).cast_mut(),
                $len,
            )));
        };
    }

    fn check_slice<T>(slice: &[T], base: *const T, start: usize, len: usize) {
        kani::safety_check_no_assume(
            slice.len() == len,
            "slice length matches the expected length",
        );
        kani::safety_check_no_assume(
            slice.as_ptr() == base.wrapping_add(start),
            "slice pointer matches the expected start",
        );
        assert!(region_is_readable(slice.as_ptr(), slice.len()));
        if const { element_validity_kind::<T>() != 0 } {
            kani::cover(
                observes_region(slice.as_ptr(), slice.len()),
                "observation in returned region",
            );
        }
        // Check the first and last element accesses; scalar loads and writes
        // belong to the callers. Padding bytes are not compared.
        if let Some(first) = slice.first() {
            kani::safety_check_no_assume(
                element_is_readable(first),
                "first slice element is readable",
            );
        }
        if let Some(last) = slice.last() {
            kani::safety_check_no_assume(
                element_is_readable(last),
                "last slice element is readable",
            );
        }
    }

    fn touch_shared<T: Copy>(slice: &mut &[T]) {
        assert!(region_is_readable(slice.as_ptr(), slice.len()));
        if let Some(first) = slice.first() {
            let _value = *first;
        }
    }

    fn touch_mut<T: Copy + kani::Arbitrary>(slice: &mut &mut [T]) {
        assert!(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(
            slice.as_mut_ptr(),
            slice.len()
        )));
        assert!(unsafe { observed_elements_valid(slice.as_ptr(), slice.len()) });
        if let Some(first) = slice.first_mut() {
            *first = kani::any();
        }
        if let Some(last) = slice.last_mut() {
            *last = kani::any();
        }
    }

    fn check_exact_hint<I>(iter: &I, count: usize)
    where
        I: ExactSizeIterator + TrustedRandomAccessNoCoerce,
    {
        kani::safety_check_no_assume(
            iter.size_hint() == (count, Some(count)),
            "size_hint matches exact remaining count",
        );
        kani::safety_check_no_assume(iter.len() == count, "len matches exact remaining count");
        kani::safety_check_no_assume(
            TrustedRandomAccessNoCoerce::size(iter) == count,
            "trusted size matches exact remaining count",
        );
    }

    // All field bit patterns are valid; padding is deliberately unconstrained.
    // The byte model must not treat padding as an initialized-value obligation.
    #[repr(C)]
    #[derive(Clone, Copy, kani::Arbitrary)]
    struct Padded {
        byte: u8,
        word: u32,
    }

    #[repr(align(16))]
    #[derive(Clone, Copy, kani::Arbitrary)]
    struct AlignedZst;

    #[repr(align(32))]
    #[derive(Clone, Copy, kani::Arbitrary)]
    struct AlignedWord(u8);

    // Getter inputs deliberately overapproximate constructor states: every safe split
    // is admitted, including partitions whose main length is not a multiple of size.
    // Every original constructor partition is included (the constructor proofs below
    // establish its bounds). The getter's complete selected-range precondition suffices
    // even on these additional states. No constructor invariant is assumed away.
    //
    // Safe splitting preserves the allocation and mutable-region disjointness. Actual
    // constructors remain checked by gen_exact_constructor, and getter bodies execute
    // without stubs. This is a local getter proof, not a proof that the extra states
    // satisfy every other iterator method's invariants.
    fn any_exact_partition(len: usize) -> usize {
        let split = kani::any_where(|split: &usize| *split <= len);
        kani::cover(true, "admissible exact-iterator partition");
        split
    }

    macro_rules! contract_iterator {
        (ChunksExact, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let main_len = any_exact_partition(slice.len());
            let (main, rem) = slice.split_at(main_len);
            let v = any_slice(main);
            ChunksExact { v, rem, chunk_size: size }
        }};
        (ChunksExactMut, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let main_len = any_exact_partition(slice.len());
            let (main, rem) = slice.split_at_mut(main_len);
            let v = any_slice_mut(main);
            ChunksExactMut { v, rem, chunk_size: size, _marker: PhantomData }
        }};
        (RChunksExact, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let rem_len = any_exact_partition(slice.len());
            let (rem, main) = slice.split_at(rem_len);
            let v = any_slice(main);
            RChunksExact { v, rem, chunk_size: size }
        }};
        (RChunksExactMut, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let rem_len = any_exact_partition(slice.len());
            let (rem, main) = slice.split_at_mut(rem_len);
            let v = any_slice_mut(main);
            RChunksExactMut { v, rem, chunk_size: size }
        }};
        ($iterator:ident, $slice:expr, $size:expr) => {
            $iterator::new($slice, $size)
        };
    }

    // nth_back never reads rem. Selecting v directly from the original storage
    // has the same projected domain as selecting a main partition and then v:
    // view_len + start <= main_len <= original_len. Keep the allocation and
    // its arbitrary observation, including observations outside v.
    macro_rules! step_storage {
        (ChunksExactMut, next, $ty:ty) => {
            SymbolicSlice::<$ty>::with_optional_suffix::<{ mem::size_of::<$ty>() == 3 }>()
        };
        ($iterator:ident, $method:ident, $ty:ty) => {
            SymbolicSlice::<$ty>::any()
        };
    }

    macro_rules! step_iterator {
        (ChunksExactMut, nth_back, $ty:ty, $slice:expr, $size:expr) => {
            step_iterator!(@exact_mut $slice, $size)
        };
        (ChunksExactMut, next_back, $ty:ty, $slice:expr, $size:expr) => {
            if const { mem::size_of::<$ty>() == 3 } {
                step_iterator!(@exact_mut $slice, $size)
            } else {
                contract_iterator!(ChunksExactMut, $slice, $size)
            }
        };
        (@exact_mut $slice:expr, $size:expr) => {{
            let v = any_slice_mut($slice);
            ChunksExactMut {
                v,
                rem: &mut [],
                chunk_size: $size,
                _marker: PhantomData,
            }
        }};
        (ChunksExactMut, nth, $ty:ty, $slice:expr, $size:expr) => {{
            if const { mem::size_of::<$ty>() == 3 } {
                ChunksExactMut {
                    v: any_slice_mut($slice),
                    rem: &mut [],
                    chunk_size: $size,
                    _marker: PhantomData,
                }
            } else {
                contract_iterator!(ChunksExactMut, $slice, $size)
            }
        }};
        (RChunksExactMut, nth, $ty:ty, $slice:expr, $size:expr) => {{
            if const { mem::size_of::<$ty>() == 3 } {
                RChunksExactMut {
                    v: any_slice_mut($slice),
                    rem: &mut [],
                    chunk_size: $size,
                }
            } else {
                contract_iterator!(RChunksExactMut, $slice, $size)
            }
        }};
        (ChunksExactMut, next, $ty:ty, $slice:expr, $size:expr) => {
            if const { mem::size_of::<$ty>() == 3 } {
                ChunksExactMut {
                    v: $slice,
                    rem: &mut [],
                    chunk_size: $size,
                    _marker: PhantomData,
                }
            } else {
                contract_iterator!(ChunksExactMut, $slice, $size)
            }
        };
        ($iterator:ident, $method:ident, $ty:ty, $slice:expr, $size:expr) => {
            contract_iterator!($iterator, $slice, $size)
        };
    }

    #[kani::proof]
    fn check_exact_step_input_domain() {
        let original_len: usize = kani::any();
        let main_len: usize = kani::any();
        let view_len: usize = kani::any();
        let start: usize = kani::any();
        if main_len <= original_len && view_len <= main_len && start <= main_len - view_len {
            assert!(view_len <= original_len);
            assert!(start <= original_len - view_len);
            kani::cover(main_len < original_len && view_len > 0, "nonempty ignored remainder");
            kani::cover(start > 0, "interior remaining slice");
            kani::cover(original_len == usize::MAX, "maximal length domain");
        }
        if view_len <= original_len && start <= original_len - view_len {
            let witness = original_len;
            assert!(witness <= original_len && view_len <= witness && start <= witness - view_len);
            kani::cover(view_len == 0, "empty remaining slice has an original-state witness");
            kani::cover(
                view_len > 0 && view_len == original_len,
                "whole remaining slice has a witness",
            );
        }
    }

    #[kani::proof]
    fn check_triplet_direct_next_allocation() {
        let prefix: usize = kani::any();
        let original_bytes: usize = kani::any();
        let start_bytes: usize = kani::any();
        let view_bytes: usize = kani::any();
        if original_bytes < usize::MAX - prefix
            && view_bytes <= original_bytes
            && start_bytes <= original_bytes - view_bytes
        {
            let direct_prefix = prefix + start_bytes;
            let trailing = original_bytes - start_bytes - view_bytes;
            assert!(direct_prefix + view_bytes + trailing == prefix + original_bytes);
            assert!(trailing < usize::MAX - (direct_prefix + view_bytes));
            kani::cover(start_bytes > 0 && trailing > 0 && view_bytes > 0, "interior triplet view");
            kani::cover(view_bytes == 0 && trailing > 0, "allocated empty triplet view");
            kani::cover(view_bytes == original_bytes && original_bytes > 0, "whole triplet view");
        }
    }

    // The unchecked call does not consume an item. Protocol tests must never use next/nth
    // afterward; those operations would violate the trait's caller obligations.
    macro_rules! gen_chunk_contract {
        ($iterator:ident, $ty:ty, $view:ident, $pointer:ident, $exact:expr) => {
            with_solver! { $iterator,
            #[kani::proof_for_contract(<$iterator<'_, $ty> as crate::iter::traits::iterator::Iterator>::__iterator_get_unchecked)]
            fn check_get_unchecked_contract() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let allocation = storage.allocation as *const $ty;
                let slice = storage.$view();
                let input_len = slice.len();
                let size = kani::any_where(|n: &usize| *n > 0);
                kani::cover(true, "admissible symbolic size");
                let mut iter = contract_iterator!($iterator, slice, size);
                let base = iter.v.$pointer() as *const $ty;
                let len = iter.v.len();
                // Every valid getter call satisfies these broad bounds, as
                // checked independently by check_getter_argument_bounds.
                if $exact {
                    kani::assume(size <= iter.v.len());
                    kani::cover(true, "an exact chunk fits the remaining input");
                }
                let index = kani::any_where(|index: &usize| *index < iter.v.len());
                kani::cover(true, "admissible broad getter index bound");
                if const { mem::size_of::<$ty>() != 0 } {
                    // Repeat the declared range before the contract wrapper, so
                    // its arithmetic also constrains the caller's SSA values.
                    // check_chunk_precondition_encodings proves equivalence;
                    // this excludes no call satisfying the native precondition.
                    kani::assume(size > 0 && index.checked_mul(size).is_some_and(|start| {
                        if $exact {
                            size <= len && start <= len.wrapping_sub(size)
                        } else {
                            start < len
                        }
                    }));
                    kani::cover(true, "declared getter input range is reachable");
                }
                // proof_for_contract checks the original body and its declared
                // spatial and state postconditions. Relative bounds below tie
                // every returned element to the remaining input and its observation.
                // Safe-step harnesses separately check the disjoint returned and
                // remaining regions without requiring full iterator semantics.
                // A fresh iterator has no earlier accesses; only permitted observations follow.
                let result = unsafe { iter.__iterator_get_unchecked(index) };
                // Prove a contained region, without specifying the exact chunk
                // selected by index. ZST regions contain no bytes to overlap.
                if const { mem::size_of::<$ty>() != 0 } {
                    let width = const { mem::size_of::<$ty>() };
                    let bytes = len * width;
                    let result_bytes = result.len() * width;
                    // Byte pointers avoid inverse stride division. Kani checks
                    // this operation's same-allocation and nonnegative-distance
                    // preconditions as part of this proof, before the bounds below.
                    let offset = unsafe {
                        result.as_ptr().cast::<u8>().offset_from_unsigned(base.cast::<u8>())
                    };
                    assert!(offset <= bytes);
                    assert!(result_bytes <= bytes.saturating_sub(offset));
                    kani::cover(
                        (offset == 0) & (input_len == 1) & (size == 1) & (base == allocation),
                        "zero byte displacement after checked region bounds",
                    );
                    kani::cover(
                        (offset > 0) & (input_len == 2) & (size == 1) & (base == allocation),
                        "positive byte displacement after checked region bounds",
                    );
                }
                // The contract checks whole-region access and forbids writes.
                // Check the observed representation directly, without adding a
                // separate client's reads or writes to this getter proof.
                assert!(region_is_readable(result.as_ptr(), result.len()));
                // Explicit small witnesses simplify cover queries. The safety
                // checks above retain their complete symbolic input domain.
                if const { element_validity_kind::<$ty>() != 0 } {
                    kani::cover(
                        (input_len == 1) & (size == 1) & (index == 0)
                            & (base == allocation)
                            & observes_region(result.as_ptr(), result.len()),
                        "observation in returned chunk",
                    );
                }
                kani::cover(index == 0 && size == 1, "first unchecked item");
                // Equivalent last-item tests, without reintroducing a division oracle.
                let remaining = if $exact {
                    iter.v.len().wrapping_sub(index.wrapping_mul(size))
                } else {
                    iter.v.len() - index.wrapping_mul(size)
                };
                if $exact {
                    kani::cover(remaining == size && size == 1 && index == 1, "last unchecked item");
                    kani::cover(index == 1 && size == 1, "nonzero unchecked index");
                    kani::cover(index == 0 && size == 1 && input_len == len, "empty preserved remainder");
                    kani::cover(index == 0 && size == 1 && input_len > len, "input outside remaining main region");
                } else {
                    kani::cover(remaining <= size && size == 1 && index == 1, "last unchecked item");
                    kani::cover(result.len() < size && size == 2 && index == 0, "partial chunk");
                }
            }
            }
        };
    }

    // Choose the allocation and views independently. This avoids carrying
    // the constructor's split operations into the exact getter proofs.
    fn triplet_getter_input<const REVERSE: bool, const WRITABLE: bool>()
    -> (SymbolicSlice<[u8; 3]>, *mut [u8; 3], usize) {
        const WIDTH: usize = size_of::<[u8; 3]>();
        const CAP: usize = isize::MAX as usize / WIDTH;
        // SAFETY: CBMC supplies the immutable allocation limit.
        let limit = unsafe { __CPROVER_max_malloc_size };
        let bytes = kani::any_where(|bytes: &usize| *bytes > 0 && *bytes < limit);
        kani::cover(true, "admissible backing extent");
        let len = kani::any_where(|len: &usize| *len > 0 && *len <= CAP && *len * WIDTH <= bytes);
        kani::cover(true, "nonempty main view");
        let main_bytes = len * WIDTH;
        let start = kani::any_where(|start: &usize| *start <= bytes - main_bytes);
        kani::cover(true, "main view fits the allocation");
        let space = if REVERSE { start } else { bytes - start - main_bytes };
        let rem_len = kani::any_where(|len: &usize| *len <= CAP && *len * WIDTH <= space);
        kani::cover(true, "remainder fits on its original side");
        let gap = kani::any_where(|gap: &usize| *gap <= space - rem_len * WIDTH);
        kani::cover(true, "admissible remainder offset");
        let rem_start = if REVERSE { gap } else { start + main_bytes + gap };
        assert!(if REVERSE {
            rem_start + rem_len * WIDTH <= start
        } else {
            start + main_bytes <= rem_start
        });
        kani::cover(rem_len > 0, "disjoint nonempty input views");

        let mut allocation = ptr::null_mut();
        // SAFETY: the requested size is positive and fits the backend's
        // pointer model. The output pointer is live and alignment is valid.
        let status = unsafe { posix_memalign(&mut allocation, size_of::<*mut u8>(), bytes) };
        kani::assume(status == 0);
        kani::cover(true, "existing getter allocation succeeds");
        // SAFETY: this is live, exclusively owned storage with no references.
        unsafe { __CPROVER_havoc_object(allocation) };

        let data = allocation.wrapping_add(start).cast::<[u8; 3]>();
        let rem = allocation.wrapping_add(rem_start).cast::<[u8; 3]>();
        // These predicates describe the valid input references. All triplet
        // bit patterns are valid, and the allocation was initialized above.
        kani::assume(
            crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(data, len))
                && crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(rem, rem_len)),
        );
        kani::cover(true, "readable input views");
        if const { WRITABLE } {
            kani::assume(
                crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(data, len))
                    && crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(rem, rem_len)),
            );
            kani::cover(true, "writable input views");
        }
        unsafe { SYMBOLIC_SLICE_ACTIVE = true };
        (SymbolicSlice { data, len, allocation }, rem, rem_len)
    }

    // Map the original partition and subview to the same backing object.
    // The placement argument holds for arbitrary byte ranges. The separate
    // scaling check relates element counts to their original byte ranges.
    #[kani::proof]
    #[kani::solver(cvc5)]
    fn check_triplet_getter_input_domain() {
        const WIDTH: usize = size_of::<[u8; 3]>();
        const CAP: usize = isize::MAX as usize / WIDTH;
        let elements: usize = kani::any();
        let split: usize = kani::any();
        if split <= elements && elements <= CAP {
            let bytes = elements * WIDTH;
            let before = split * WIDTH;
            let after = (elements - split) * WIDTH;
            assert!(before <= bytes && bytes <= isize::MAX as usize);
            assert_eq!(after, bytes - before);
            kani::cover(split > 0 && split < elements, "interior element split preserves bytes");
        }

        let input: usize = kani::any();
        let prefix: usize = kani::any();
        let start: usize = kani::any();
        let main: usize = kani::any();
        let partition: usize = kani::any();
        let reverse: bool = kani::any();
        // SAFETY: CBMC supplies the immutable allocation limit.
        let limit = unsafe { __CPROVER_max_malloc_size };
        if input <= isize::MAX as usize
            && input < limit
            && prefix < limit - input
            && partition <= input
            && start <= input
            && main > 0
            && main <= input - start
            && (if reverse { partition <= start } else { start + main <= partition })
        {
            let bytes = prefix + input;
            let data = prefix + start;
            let (rem_start, rem) =
                if reverse { (0, partition) } else { (partition, input - partition) };
            let remainder = prefix + rem_start;
            let space = if reverse { data } else { bytes - data - main };
            let gap = if reverse { remainder } else { remainder - data - main };
            assert!(0 < bytes && bytes < limit);
            assert!(main <= bytes && data <= bytes - main);
            assert!(rem <= space && gap <= space - rem);
            assert_eq!(if reverse { gap } else { data + main + gap }, remainder);
            kani::cover(reverse && rem > 0, "original nonempty leading remainder");
            kani::cover(!reverse && rem > 0, "original nonempty trailing remainder");
            kani::cover(rem == 0 && prefix > 0, "original interior view with empty remainder");
            kani::cover(start > 0 && start + main < input, "original interior main view");
        }
    }

    // A subregion of an accessible triplet slice has the same allocation
    // and access permissions. Prove this in element coordinates, independently
    // of the getter's calculation of its starting index.
    #[cfg_attr(kani, kani::modifies())]
    #[requires(
        size > 0 && size <= len && start <= len.wrapping_sub(size)
            && len <= isize::MAX as usize / 3
            && crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(base, len))
            && (!writable || crate::ub_checks::can_write(
                ptr::slice_from_raw_parts_mut(base.cast_mut(), len)
            ))
    )]
    #[ensures(|_| {
        let selected = base.wrapping_add(start);
        crate::ub_checks::same_allocation(base, selected)
            && crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(selected, size))
            && (!writable || crate::ub_checks::can_write(
                ptr::slice_from_raw_parts_mut(selected.cast_mut(), size)
            ))
    })]
    fn triplet_chunk_region(
        base: *const [u8; 3],
        len: usize,
        start: usize,
        size: usize,
        writable: bool,
    ) {
    }

    #[kani::proof_for_contract(triplet_chunk_region)]
    fn check_triplet_chunk_region() {
        reset_observation();
        let storage = SymbolicSlice::<[u8; 3]>::with_optional_suffix::<true>();
        let size = kani::any_where(|size: &usize| *size > 0 && *size <= storage.len);
        kani::cover(true, "positive chunk size fits the slice");
        let start = kani::any_where(|start: &usize| *start <= storage.len - size);
        kani::cover(true, "admissible chunk start");
        let writable = kani::any();
        triplet_chunk_region(storage.data, storage.len, start, size, writable);
        kani::cover(start == 0 && size == storage.len, "whole-region access");
        kani::cover(start > 0 && writable, "interior writable chunk");
        kani::cover(!writable, "read-only contract branch");
    }

    macro_rules! gen_triplet_exact_getter {
        ($iterator:ident, $raw_view:ident, $reverse:literal, $writable:literal $(, $marker:ident)?) => {
            #[kani::proof_for_contract(<$iterator<'_, [u8; 3]> as crate::iter::traits::iterator::Iterator>::__iterator_get_unchecked)]
            #[kani::solver(cadical)]
            #[kani::stub_verified(triplet_chunk_region)]
            fn check_get_unchecked_contract() {
                reset_observation();
                let (storage, rem, rem_len) = triplet_getter_input::<$reverse, $writable>();
                let base = storage.data.cast_const();
                let len = storage.len;
                let total = len + rem_len;
                let size = kani::any_where(|size: &usize| *size > 0 && *size <= len);
                kani::cover(true, "an exact chunk fits the remaining input");
                // SAFETY: both views have live, initialized, aligned storage,
                // and their byte ranges are disjoint.
                let mut iter = $iterator {
                    v: unsafe { $raw_view(storage.data, len) },
                    rem: unsafe { $raw_view(rem, rem_len) },
                    chunk_size: size,
                    $(_marker: $marker,)?
                };
                // Select exactly the indices allowed by the native range precondition.
                let index = kani::any_where(|index: &usize| {
                    *index < len && index.checked_mul(size).is_some_and(|skipped| skipped <= len - size)
                });
                kani::cover(true, "declared getter input range is reachable");
                let skipped = index.wrapping_mul(size);
                let remaining = len.wrapping_sub(skipped);
                let start = if $reverse { remaining.wrapping_sub(size) } else { skipped };

                triplet_chunk_region(base, len, start, size, $writable);
                kani::cover(true, "subregion lemma applies");
                // SAFETY: the selected complete range fits. No earlier
                // unchecked access has taken place on this iterator.
                let result = unsafe { iter.__iterator_get_unchecked(index) };
                assert_eq!(result.as_ptr(), base.wrapping_add(start));
                assert_eq!(result.len(), size);
                assert!(crate::ub_checks::same_allocation(base, result.as_ptr()));
                assert!(start <= len && result.len() <= len.saturating_sub(start));
                kani::cover(
                    (start == 0) & (total == 1) & (size == 1) & (base == storage.allocation.cast()),
                    "zero displacement after exact result checks",
                );
                kani::cover(
                    (start > 0) & (total == 2) & (size == 1) & (base == storage.allocation.cast()),
                    "positive displacement after exact result checks",
                );
                assert!(region_is_readable(result.as_ptr(), result.len()));
                kani::cover(index == 0 && size == 1, "first unchecked item");
                kani::cover(remaining == size && size == 1 && index == 1, "last unchecked item");
                kani::cover(index == 1 && size == 1, "nonzero unchecked index");
                kani::cover(index == 0 && size == 1 && rem_len == 0, "empty preserved remainder");
                kani::cover(index == 0 && size == 1 && rem_len > 0, "nonempty preserved remainder");
            }
        };
    }

    macro_rules! gen_exact_chunk_contract {
        (byte_triplet, $iterator:ident, $standard:tt, ($($triplet:tt)*)) => {
            gen_triplet_exact_getter!($iterator, $($triplet)*);
        };
        ($module:ident, $iterator:ident, ($ty:ty, $view:ident, $pointer:ident), $triplet:tt) => {
            gen_chunk_contract!($iterator, $ty, $view, $pointer, true);
        };
    }

    macro_rules! call_chunk_step {
        (next, $iter:ident, $n:ident) => {
            $iter.next()
        };
        (next_back, $iter:ident, $n:ident) => {
            $iter.next_back()
        };
        (nth, $iter:ident, $n:ident) => {
            $iter.nth($n)
        };
        (nth_back, $iter:ident, $n:ident) => {
            $iter.nth_back($n)
        };
    }

    macro_rules! step_index {
        (next, $n:ident) => {
            0
        };
        (next_back, $n:ident) => {
            0
        };
        (nth, $n:ident) => {
            $n
        };
        (nth_back, $n:ident) => {
            $n
        };
    }

    macro_rules! cover_step_overflow {
        (nth, $n:ident, $size:ident) => {
            kani::cover($n.checked_mul($size).is_none(), "nth multiplication overflow");
        };
        (nth_back, $n:ident, $size:ident) => {
            kani::cover($n.checked_mul($size).is_none(), "large nth_back index");
        };
        ($other:ident, $n:ident, $size:ident) => {};
    }

    macro_rules! check_chunk_step_result {
        (ChunksExactMut, nth_back, $ty:ty, $view:ident, $touch:ident, $base:ident, $len:ident,
         $remaining_ptr:ident, $remaining:ident, $result:ident, $size:ident,
         $reverse:expr, $exact:expr, $back:expr) => {
            if let Some(ref mut chunk) = $result {
                let chunk_ptr = chunk.as_ptr();
                let chunk_len = chunk.len();
                assert!(region_is_readable(chunk_ptr, chunk_len));
                check_writable_region!($view, chunk_ptr, chunk_len);
                // On success the remaining region is the original prefix,
                // and the returned region starts at its end. The length
                // bounds keep both regions in the original slice, so their
                // bytes cannot overlap. The same identities hold for ZSTs.
                assert!($remaining_ptr == $base);
                assert!(chunk_ptr == $base.wrapping_add($remaining));
                assert!(chunk_len <= $len.saturating_sub($remaining));
                if const { element_validity_kind::<$ty>() != 0 } {
                    kani::cover(observes_region(chunk_ptr, chunk_len), "observation in returned region");
                }
                $touch(chunk);
            }
        };
        (ChunksExactMut, next, $ty:ty, $view:ident, $touch:ident, $base:ident, $len:ident,
         $remaining_ptr:ident, $remaining:ident, $result:ident, $size:ident,
         $reverse:expr, $exact:expr, $back:expr) => {
            if const { mem::size_of::<$ty>() == 3 } {
                if let Some(ref mut chunk) = $result {
                    let chunk_len = chunk.len();
                    assert!(chunk_len <= $size);
                    assert!(chunk_len == $len.saturating_sub($remaining));
                    check_slice(chunk, $base, 0, chunk_len);
                    check_writable_region!($view, chunk.as_ptr(), chunk_len);
                    assert!($remaining_ptr == $base.wrapping_add(chunk_len));
                    $touch(chunk);
                } else {
                    assert!($remaining < $size);
                }
            } else {
                check_chunk_step_result!(@default $ty, $view, $touch, $base, $len,
                    $remaining_ptr, $remaining, $result, $size, $reverse, $exact, $back);
            }
        };
        ($iterator:ident, $method:ident, $ty:ty, $view:ident, $touch:ident, $base:ident, $len:ident,
         $remaining_ptr:ident, $remaining:ident, $result:ident, $size:ident,
         $reverse:expr, $exact:expr, $back:expr) => {
            check_chunk_step_result!(@default $ty, $view, $touch, $base, $len,
                $remaining_ptr, $remaining, $result, $size, $reverse, $exact, $back);
        };
        (@default $ty:ty, $view:ident, $touch:ident, $base:ident, $len:ident,
         $remaining_ptr:ident, $remaining:ident, $result:ident, $size:ident,
         $reverse:expr, $exact:expr, $back:expr) => {
                if let Some(ref mut chunk) = $result {
                    let chunk_len = chunk.len();
                    assert!(chunk_len <= $size);
                    assert!(chunk_len <= $len - $remaining);
                    let from_back = $reverse != $back;
                    let start = if from_back { $remaining } else { $len - $remaining - chunk_len };
                    check_slice(chunk, $base, start, chunk_len);
                    check_writable_region!($view, chunk.as_ptr(), chunk_len);
                    let remaining_start = if from_back { 0 } else { $len - $remaining };
                    assert!($remaining_ptr == $base.wrapping_add(remaining_start));
                    $touch(chunk);
                } else {
                    assert!(if $exact { $remaining < $size } else { $remaining == 0 });
                }
        };
    }

    // Check actual step accesses and the geometry of returned/remaining regions.
    // nth_back uses independently verified size_hint contracts. Their weak
    // results admit extra counts and checked panics; all actual accesses and
    // returned/remaining spatial safety checks still execute.
    // Our safety_check_no_assume obligations and Kani's pointer checks keep their
    // separate classes, so neither can be accepted as an expected panic.
    // The iterator bodies execute. Where a proof applies the verified raw
    // split contract, a separate proof executes that helper's actual body.
    macro_rules! gen_chunk_step {
        ($name:ident, $ty:ty, $iterator:ident, $method:ident, $view:ident, $pointer:ident,
         $reverse:expr, $exact:expr, $back:expr, $touch:ident $(, $attribute:meta)*) => {
            with_solver! { $iterator, $method,
            #[kani::proof]
            $(#[$attribute])*
            fn $name() {
                reset_observation();
                let mut storage = step_storage!($iterator, $method, $ty);
                let slice = storage.$view();
                let size = kani::any_where(|size: &usize| *size > 0);
                kani::cover(true, "admissible symbolic size");
                let mut iter = step_iterator!($iterator, $method, $ty, slice, size);
                let base = iter.v.$pointer() as *const $ty;
                let len = iter.v.len();
                let n: usize = kani::any();
                let mut result = call_chunk_step!($method, iter, n);
                let remaining = iter.v.len();
                assert!(remaining <= len);
                let remaining_ptr = iter.v.$pointer() as *const $ty;
                assert!(region_is_readable(remaining_ptr, remaining));
                check_writable_region!($view, remaining_ptr, remaining);
                check_chunk_step_result!(
                    $iterator, $method, $ty, $view, $touch, base, len,
                    remaining_ptr, remaining, result, size, $reverse, $exact, $back
                );
                kani::cover(result.is_some(), "chunk returned");
                kani::cover(result.is_none(), "no chunk returned");
                kani::cover(size > len, "chunk size exceeds remaining length");
                cover_step_overflow!($method, n, size);
            }
            }
        };
    }

    macro_rules! gen_exact_constructor {
        ($ty:ty, $iterator:ident, $view:ident, $pointer:ident, $reverse:expr) => {
            with_solver! {
            #[kani::proof]
            fn check_new() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let size = kani::any_where(|size: &usize| *size > 0);
                kani::cover(true, "admissible symbolic size");
                let iter = $iterator::new(slice, size);
                let main_len = iter.v.len();
                let rem_len = iter.rem.len();
                assert!(main_len <= len && rem_len == len - main_len);
                assert!(rem_len < size);
                let main_start = if $reverse { rem_len } else { 0 };
                let rem_start = if $reverse { 0 } else { main_len };
                assert!((iter.v.$pointer() as *const $ty) == base.wrapping_add(main_start));
                check_slice(&iter.rem, base, rem_start, rem_len);
                assert!(region_is_readable(iter.v.$pointer() as *const $ty, main_len));
                check_writable_region!($view, iter.v.$pointer() as *const $ty, main_len);
                check_writable_region!($view, iter.rem.as_ptr(), rem_len);
                kani::cover(rem_len == 0, "empty remainder");
                kani::cover(rem_len > 0, "nonempty remainder");
                kani::cover(size > len, "whole input is remainder");
            }
            }
        };
    }

    macro_rules! gen_chunk_last {
        ($ty:ty, $iterator:ident, $view:ident, $pointer:ident, $reverse:expr, $touch:ident) => {
            with_solver! {
            #[kani::proof]
            fn check_last() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let size = kani::any_where(|size: &usize| *size > 0);
                kani::cover(true, "admissible symbolic size");
                let mut iter = $iterator::new(slice, size);
                let base = iter.v.$pointer() as *const $ty;
                let len = iter.v.len();
                let mut result = iter.last();
                if let Some(ref mut chunk) = result {
                    assert!(chunk.len() > 0 && chunk.len() <= len);
                    let start = if $reverse { 0 } else { len - chunk.len() };
                    check_slice(chunk, base, start, chunk.len());
                    $touch(chunk);
                }
                kani::cover(result.is_some(), "last chunk returned");
                kani::cover(result.is_none(), "empty iterator");
            }
            }
        };
    }

    macro_rules! check_iter_step_remainder {
        (nth_back, $ty:ty, $view:ident, $iter:ident, $base:ident, $len:ident, $index:ident, $returned:ident, $back:expr) => {{
            let start = 0;
            let remaining = if $returned { $len - $index - 1 } else { 0 };
            check_iter_region!($ty, $view, $iter, $base, start, remaining);
        }};
        ($method:ident, $ty:ty, $view:ident, $iter:ident, $base:ident, $len:ident, $index:ident, $returned:ident, $back:expr) => {{
            if $returned {
                assert_eq!($iter.len(), $len - $index - 1);
                let remaining_start = if $back { 0 } else { $index + 1 };
                assert!($iter.ptr.as_ptr().cast_const() == $base.wrapping_add(remaining_start));
            } else {
                assert_eq!($iter.len(), 0);
            }
            assert!($iter.is_safe());
        }};
    }

    macro_rules! gen_iter_step {
        ($name:ident, $ty:ty, $iterator:ident, $view:ident, $method:ident, $back:expr) => {
            with_solver! {
            #[kani::proof]
            fn $name() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = $iterator::new(slice);
                let n: usize = kani::any();
                let index = step_index!($method, n);
                let result = call_chunk_step!($method, iter, n);
                assert_eq!(result.is_some(), index < len);
                let returned = result.is_some();
                if let Some(item) = result {
                    let offset = if $back { len - 1 - index } else { index };
                    assert!((item as *const $ty) == base.wrapping_add(offset));
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                }
                check_iter_step_remainder!($method, $ty, $view, iter, base, len, index, returned, $back);
                kani::cover(returned, "element returned and iterator remains safe");
                kani::cover(!returned, "element absent and iterator remains safe");
            }
            }
        };
    }

    macro_rules! gen_iter_advance {
        ($name:ident, $ty:ty, $iterator:ident, $view:ident, $method:ident, $back:expr) => {
            with_solver! {
            #[kani::proof]
            fn $name() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = $iterator::new(slice);
                let n: usize = kani::any();
                let advanced = n.min(len);
                let result = iter.$method(n);
                match result {
                    Ok(()) => assert!(n <= len),
                    Err(remaining) => {
                        assert!(n > len);
                        assert_eq!(remaining.get(), n - advanced);
                    }
                }
                assert_eq!(iter.len(), len - advanced);
                let start = if $back { 0 } else { advanced };
                assert!(iter.ptr.as_ptr().cast_const() == base.wrapping_add(start));
                assert!(iter.is_safe());
                kani::cover(n == 0, "advance zero");
                kani::cover(n == len, "advance exactly to end");
                kani::cover(n > len, "advance past end");
            }
            }
        };
    }

    macro_rules! gen_iter_family {
        ($ty:ty, $iterator:ident, $view:ident) => {
            gen_predicate_state!(
                check_position_owned_state,
                $ty,
                $iterator,
                $view,
                position,
                owned
            );
            gen_predicate_state!(
                check_position_borrowed_state,
                $ty,
                $iterator,
                $view,
                position,
                borrowed
            );
            gen_predicate_state!(
                check_rposition_owned_state,
                $ty,
                $iterator,
                $view,
                rposition,
                owned
            );
            gen_predicate_state!(
                check_rposition_borrowed_state,
                $ty,
                $iterator,
                $view,
                rposition,
                borrowed
            );
            with_solver! {
            #[kani::proof]
            fn check_new_and_queries() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let iter = $iterator::new(slice);
                assert!(iter.is_safe());
                check_slice(iter.make_slice(), base, 0, len);
                assert_eq!(iter.len(), len);
                assert_eq!(iter.is_empty(), len == 0);
                assert_eq!(iter.size_hint(), (len, Some(len)));
                assert_eq!(iter.count(), len);
                kani::cover(len == 0, "empty iterator");
                kani::cover(len > 1, "multiple elements");
            }
            }

            gen_iter_step!(check_next, $ty, $iterator, $view, next, false);
            gen_iter_step!(check_nth, $ty, $iterator, $view, nth, false);
            gen_iter_step!(check_next_back, $ty, $iterator, $view, next_back, true);
            gen_iter_step!(check_nth_back, $ty, $iterator, $view, nth_back, true);
            gen_iter_advance!(check_advance_by, $ty, $iterator, $view, advance_by, false);
            gen_iter_advance!(check_advance_back_by, $ty, $iterator, $view, advance_back_by, true);

            with_solver! {
            #[kani::proof]
            fn check_last() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let result = $iterator::new(slice).last();
                assert_eq!(result.is_some(), len > 0);
                if let Some(item) = result {
                    assert!((item as *const $ty) == base.wrapping_add(len - 1));
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                }
                kani::cover(len == 0, "last on empty iterator");
                kani::cover(len > 0, "last element returned");
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_fold() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                // Unit accumulator isolates access safety from arithmetic in the callback.
                $iterator::new(storage.$view()).fold((), |(), item| {
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                    kani::cover(true, "fold callback reached");
                });
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_for_each() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                $iterator::new(storage.$view()).for_each(|item| {
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                    kani::cover(true, "for_each callback reached");
                });
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_position() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = $iterator::new(slice);
                let result = iter.position(|item| {
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                    kani::any::<bool>()
                });
                if let Some(index) = result {
                    assert!(index < len);
                }
                check_predicate_remainder!(position, $ty, $view, iter, result, base, len);
                kani::cover(result.is_some(), "position match");
                kani::cover(result.is_none() && len > 0, "position no match on nonempty input");
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_rposition() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = $iterator::new(slice);
                let result = iter.rposition(|item| {
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                    kani::any::<bool>()
                });
                if let Some(index) = result {
                    assert!(index < len);
                }
                check_predicate_remainder!(rposition, $ty, $view, iter, result, base, len);
                kani::cover(result.is_some(), "rposition match");
                kani::cover(result.is_none() && len > 0, "rposition no match on nonempty input");
            }
            }
        };
    }

    macro_rules! predicate_argument {
        (owned, $state:ident) => {
            $state
        };
        (borrowed, $state:ident) => {
            &mut $state
        };
    }

    // Express the remaining interval directly, rather than recovering its
    // length by dividing a pointer distance by size_of::<T>().
    macro_rules! predicate_remainder {
        (position, $result:expr, $len:expr) => {
            match $result {
                Some(index) => (index + 1, $len - index - 1),
                None => ($len, 0),
            }
        };
        (rposition, $result:expr, $len:expr) => {
            (0, $result.unwrap_or(0))
        };
    }

    // Describe a known remaining interval without inverse pointer-distance queries.
    macro_rules! check_iter_region {
        ($ty:ty, $view:ident, $iter:ident, $base:ident, $start:ident, $remaining:ident) => {{
            let current = $base.wrapping_add($start);
            assert!($iter.ptr.as_ptr().cast_const() == current);
            if const { mem::size_of::<$ty>() == 0 } {
                assert_eq!($iter.end_or_len.addr(), $remaining);
            } else {
                assert!(($iter.end_or_len as *const $ty) == current.wrapping_add($remaining));
            }
            assert!(region_is_readable(current, $remaining));
            check_writable_region!($view, current, $remaining);
        }};
    }

    macro_rules! check_predicate_remainder {
        ($method:ident, $ty:ty, $view:ident, $iter:ident, $result:ident, $base:ident, $len:ident) => {{
            let (start, remaining) = predicate_remainder!($method, $result, $len);
            check_iter_region!($ty, $view, $iter, $base, start, remaining);
        }};
    }

    macro_rules! gen_predicate_state {
        ($name:ident, $ty:ty, $iterator:ident, $view:ident, $method:ident, $state:ident) => {
            with_solver! {
                #[kani::proof]
                fn $name() {
                    reset_observation();
                    let mut storage = SymbolicSlice::<$ty>::any();
                    let slice = storage.$view();
                    let base = slice.as_ptr();
                    let len = slice.len();
                    let mut iter = $iterator::new(slice);
                    let mut state = Predicate(kani::any());
                    let result = iter.$method(predicate_argument!($state, state));
                    if let Some(index) = result {
                        assert!(index < len);
                    }
                    check_predicate_remainder!($method, $ty, $view, iter, result, base, len);
                    kani::cover(result.is_some(), "stateful predicate matches");
                    kani::cover(result.is_none() && len > 0, "stateful predicate does not match");
                }
            }
        };
    }

    macro_rules! gen_iter_mut_views {
        ($ty:ty) => {
            with_solver! {
                #[kani::proof]
                fn check_for_each_owned_state() {
                    reset_observation();
                    let mut storage = SymbolicSlice::<$ty>::any();
                    IterMut::new(storage.as_mut_slice()).for_each(Toggle(kani::any()));
                    kani::cover(storage.len > 0, "nonempty iterator after owned-state for_each");
                }
            }

            with_solver! {
                #[kani::proof]
                fn check_fold_owned_state() {
                    reset_observation();
                    let mut storage = SymbolicSlice::<$ty>::any();
                    IterMut::new(storage.as_mut_slice()).fold((), Toggle(kani::any()));
                    kani::cover(storage.len > 0, "nonempty iterator after owned-state fold");
                }
            }

            with_solver! {
                #[kani::proof]
                fn check_fold_mutating_and_retaining() {
                    reset_observation();
                    let mut storage = SymbolicSlice::<$ty>::any();
                    let mut retained = None;
                    IterMut::new(storage.as_mut_slice())
                        .fold((), RetainFirst { retained: &mut retained });
                    if let Some(first) = retained {
                        assert!(element_is_readable(first as *const $ty));
                        *first = kani::any();
                        kani::cover(true, "first reference retained across fold callbacks");
                    }
                }
            }

            with_solver! {
            #[kani::proof]
            fn check_fold_mutating() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                IterMut::new(storage.as_mut_slice()).fold((), |(), item| {
                    assert!(element_is_readable(item as *const $ty));
                    *item = kani::any();
                    kani::cover(true, "fold writes through returned mutable reference");
                });
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_for_each_mutating() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                IterMut::new(storage.as_mut_slice()).for_each(|item| {
                    assert!(element_is_readable(item as *const $ty));
                    *item = kani::any();
                    kani::cover(true, "for_each writes through returned mutable reference");
                });
            }
            }

            // This also exercises writes through an external closure capture. Keep it
            // separate from the element-only callback above: loop frame inference must
            // account for the capture as well as the iterator's backing allocation.
            with_solver! {
            #[kani::proof]
            fn check_for_each_mutating_and_retaining() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut retained = None;
                IterMut::new(storage.as_mut_slice())
                    .for_each(RetainFirst { retained: &mut retained });
                if let Some(first) = retained {
                    assert!(element_is_readable(first as *const $ty));
                    *first = kani::any();
                    kani::cover(true, "first reference retained across later callbacks");
                }
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_into_slice() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let original_len = storage.len;
                // Every valid remaining interval can be constructed directly;
                // the original allocation and observation still include its
                // prefix and suffix. Advance methods have separate proofs.
                let slice = any_slice_mut(storage.as_mut_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let iter = IterMut::new(slice);
                let mut remaining = iter.into_slice();
                check_slice(&remaining, base, 0, len);
                touch_mut(&mut remaining);
                kani::cover(remaining.is_empty(), "empty remaining slice");
                kani::cover(!remaining.is_empty(), "nonempty remaining slice");
                kani::cover(len > 0 && len < original_len, "nonempty remaining subregion");
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_as_mut_slice() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let original_len = storage.len;
                let slice = any_slice_mut(storage.as_mut_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = IterMut::new(slice);
                {
                    let mut view = iter.as_mut_slice();
                    check_slice(&view, base, 0, len);
                    touch_mut(&mut view);
                }
                kani::safety_check_no_assume(iter.len() == len, "reborrow preserves the remaining length");
                kani::safety_check_no_assume(iter.is_safe(), "iterator remains safe after the reborrow");
                kani::cover(len > 0 && len < original_len, "nonempty reborrowed subregion");
                kani::cover(iter.next().is_some(), "iterator reused after reborrow ends");
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_retained_mutable_elements() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.as_mut_slice();
                let base = slice.as_ptr();
                let len = slice.len();
                kani::assume(len >= 2);
                kani::cover(true, "two retained ends are admissible");
                let mut iter = IterMut::new(slice);
                let first = iter.next().unwrap();
                let last = iter.next_back().unwrap();
                assert!((first as *const $ty) == base);
                assert!((last as *const $ty) == base.wrapping_add(len - 1));
                let mut middle = iter.into_slice();
                check_slice(&middle, base, 1, len - 2);
                *first = kani::any();
                touch_mut(&mut middle);
                *last = kani::any();
                kani::cover(len == 2, "two retained ends and empty middle");
                kani::cover(len > 2, "two retained ends and nonempty middle");
            }
            }
        };
    }

    macro_rules! gen_windows {
        ($ty:ty) => {
            with_solver! {
            #[kani::proof_for_contract(<Windows<'_, $ty> as crate::iter::traits::iterator::Iterator>::__iterator_get_unchecked)]
            fn check_get_unchecked_contract() {
                reset_observation();
                let storage = SymbolicSlice::<$ty>::any();
                let size: NonZero<usize> = kani::any();
                let mut iter = Windows::new(storage.as_slice(), size);
                let len = iter.v.len();
                let base = iter.v.as_ptr();
                let count = if len < size.get() { 0 } else { len - size.get() + 1 };
                check_exact_hint(&iter, count);
                let index: usize = kani::any();
                // SAFETY: target precondition is assumed by proof_for_contract; no history.
                let result = unsafe { iter.__iterator_get_unchecked(index) };
                check_slice(result, base, index, size.get());
                check_exact_hint(&iter, count);
                kani::cover(index == 0, "first window");
                kani::cover(index == count - 1, "last window");
            }
            }
        };
    }

    macro_rules! gen_array_windows_step {
        ($name:ident, $ty:ty, $n:expr, $method:ident, $back:expr) => {
            with_solver! {
            #[kani::proof]
            fn $name() {
                reset_observation();
                let storage = SymbolicSlice::<$ty>::any();
                let slice = storage.as_slice();
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = ArrayWindows::<$ty, $n>::new(slice);
                let n: usize = kani::any();
                let index = step_index!($method, n);
                let count = len.checked_sub($n).map_or(0, |n| n + 1);
                let result = call_chunk_step!($method, iter, n);
                assert_eq!(result.is_some(), index < count);
                let skipped = index.min(len);
                let remaining = len - skipped - usize::from(result.is_some());
                let remaining_start =
                    if $back { 0 } else { skipped + usize::from(result.is_some()) };
                assert_eq!(iter.v.len(), remaining);
                assert!(iter.v.as_ptr() == base.wrapping_add(remaining_start));
                if let Some(window) = result {
                    let start = if $back { len - index - $n } else { index };
                    check_slice(window, base, start, $n);
                }
                let expected_count = count.saturating_sub(index).saturating_sub(1);
                check_exact_hint(&iter, expected_count);
                kani::cover(result.is_some(), "array window returned");
                kani::cover(result.is_none(), "array window absent");
                kani::cover(len < $n, "input shorter than window");
                kani::cover(len == $n, "input exactly one window");
            }
            }
        };
    }

    macro_rules! gen_array_windows {
        ($ty:ty, $n:expr) => {
            // Native proof_for_contract cannot resolve const-generic Self yet
            // (kani#4999). Execute the real getter with its caller bounds here.
            with_solver! {
            #[kani::proof]
            fn check_get_unchecked() {
                reset_observation();
                let storage = SymbolicSlice::<$ty>::any();
                let slice = storage.as_slice();
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = ArrayWindows::<$ty, $n>::new(slice);
                // The instantiated widths are positive. A valid index selects
                // a complete array inside the remaining input.
                let count = len.checked_sub($n).map_or(0, |n| n + 1);
                let index = kani::any_where(|index: &usize| *index < count);
                kani::cover(true, "admissible unchecked array-window index");
                // SAFETY: index < len - N + 1. This fresh iterator has no
                // access history; only the result and iterator metadata follow.
                let window = unsafe { iter.__iterator_get_unchecked(index) };
                check_slice(window, base, index, $n);
                assert_eq!(iter.v.len(), len);
                assert!(iter.v.as_ptr() == base);
                kani::cover(index == 0, "first unchecked array window");
                kani::cover(index == count - 1, "last unchecked array window");
                kani::cover(index > 0, "nonzero unchecked array-window index");
            }
            }
            gen_array_windows_step!(check_next, $ty, $n, next, false);
            gen_array_windows_step!(check_nth, $ty, $n, nth, false);
            gen_array_windows_step!(check_next_back, $ty, $n, next_back, true);
            gen_array_windows_step!(check_nth_back, $ty, $n, nth_back, true);
        };
    }

    macro_rules! gen_split_step {
        ($name:ident, $ty:ty, $method:ident, $back:expr) => {
            with_solver! {
            #[kani::proof]
            fn $name() {
                reset_observation();
                let storage = SymbolicSlice::<$ty>::any();
                let slice = storage.as_slice();
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = Split::new(slice, |item| {
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                    kani::any::<bool>()
                });
                let finished: bool = kani::any();
                iter.finished = finished;
                let result = iter.$method();
                assert_eq!(result.is_some(), !finished);
                if let Some(part) = result {
                    assert!(part.len() <= len);
                    if iter.finished {
                        check_slice(part, base, 0, len);
                    } else if $back {
                        let split = len - part.len() - 1;
                        check_slice(part, base, split + 1, part.len());
                        check_slice(iter.v, base, 0, split);
                    } else {
                        check_slice(part, base, 0, part.len());
                        check_slice(iter.v, base, part.len() + 1, len - part.len() - 1);
                    }
                }
                kani::cover(finished, "already finished");
                kani::cover(!finished && iter.finished, "no separator remains");
                kani::cover(!iter.finished, "separator found");
                kani::cover(!finished && len == 0, "empty split yields one empty slice");
            }
            }
        };
    }

    // The reverse wrappers add one layer around the same Split{Mut} state.
    // Set up either finished state without relying on an earlier next call.
    macro_rules! splitn_inner {
        (rsplitn, $iter:ident) => {
            $iter.inner.iter.inner
        };
        (rsplitn_mut, $iter:ident) => {
            $iter.inner.iter.inner
        };
        ($iterator:ident, $iter:ident) => {
            $iter.inner.iter
        };
    }

    macro_rules! gen_splitn {
        ($ty:ty, $iterator:ident, $view:ident, $touch:ident) => {
            with_solver! {
            #[kani::proof]
            fn check_next() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let base = slice.as_ptr();
                let len = slice.len();
                let limit: usize = kani::any();
                let mut iter = slice.$iterator(limit, |item| {
                    assert!(element_is_readable(item as *const $ty));
                    let _value = *item;
                    kani::any::<bool>()
                });
                let finished: bool = kani::any();
                splitn_inner!($iterator, iter).finished = finished;
                let mut result = iter.next();
                assert_eq!(result.is_some(), limit != 0 && !finished);
                assert_eq!(iter.inner.count, limit.saturating_sub(1));
                if let Some(ref mut part) = result {
                    assert!(part.len() <= len);
                    if limit == 1 {
                        check_slice(&part, base, 0, len);
                    }
                    $touch(part);
                }
                kani::cover(limit == 0, "zero split limit");
                kani::cover(limit == 1 && !finished, "finish path");
                kani::cover(limit > 1 && !finished, "delegated next path");
                kani::cover(limit > 0 && finished, "exhausted inner iterator");
            }
            }

            with_solver! {
            #[kani::proof]
            fn check_size_hint() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = storage.$view();
                let len = slice.len();
                let limit: usize = kani::any();
                let mut iter = slice.$iterator(limit, |_| kani::any::<bool>());
                let finished: bool = kani::any();
                splitn_inner!($iterator, iter).finished = finished;
                // The complementary maximal-ZST harness checks the unfinished
                // len+1 panic. Finished states admit every length here.
                kani::assume(finished || len < usize::MAX);
                kani::cover(true, "non-overflowing or finished split hint is admissible");
                let hint = iter.size_hint();
                let expected = if finished {
                    (0, Some(0))
                } else {
                    (limit.min(1), Some((len + 1).min(limit)))
                };
                assert_eq!(hint, expected);
                kani::cover(limit == 0 && !finished, "unfinished zero-limit hint");
                kani::cover(limit == 1 && !finished, "unfinished one-limit hint");
                kani::cover(finished, "exhausted inner hint");
                if const { mem::size_of::<$ty>() == 0 } {
                    kani::cover(finished && len == usize::MAX, "maximal finished ZST hint");
                }
            }
            }
        };
    }

    macro_rules! gen_max_splitn_panic {
        (zst, $ty:ty, $iterator:ident, $view:ident) => {
            with_solver! {
            #[kani::proof]
            #[kani::should_panic]
            fn check_size_hint_maximal_zst_panics() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                kani::assume(storage.len == usize::MAX);
                kani::cover(true, "maximal ZST length is admissible");
                let slice = storage.$view();
                let limit: usize = kani::any();
                let iter = slice.$iterator(limit, |_| kani::any::<bool>());
                // Split{Mut}::size_hint computes len+1 even when limit is zero.
                // should_panic accepts panic failures only: a memory-safety
                // failure still makes this harness fail.
                kani::cover(limit == 0, "maximal ZST with a zero split limit");
                iter.size_hint();
            }
            }
        };
    }

    macro_rules! gen_internal_contracts {
        ($ty:ty, $iterator:ident, $view:ident) => {
            with_solver! {
            #[kani::proof_for_contract($iterator::post_inc_start)]
            fn check_post_inc_start_contract() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut iter = $iterator::new(storage.$view());
                let offset: usize = kani::any();
                let _ = unsafe { iter.post_inc_start(offset) };
                kani::cover(offset == 0, "zero forward pointer adjustment");
                kani::cover(offset > 0, "nonzero forward pointer adjustment");
            }
            }

            with_solver! {
            #[kani::proof_for_contract($iterator::pre_dec_end)]
            fn check_pre_dec_end_contract() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut iter = $iterator::new(storage.$view());
                let offset: usize = kani::any();
                let _ = unsafe { iter.pre_dec_end(offset) };
                kani::cover(offset == 0, "zero backward pointer adjustment");
                kani::cover(offset > 0, "nonzero backward pointer adjustment");
            }
            }

            with_solver! {
            #[kani::proof_for_contract($iterator::next_back_unchecked)]
            fn check_next_back_unchecked_contract() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut iter = $iterator::new(storage.$view());
                let result = unsafe { iter.next_back_unchecked() };
                assert!(element_is_readable(result as *const $ty));
                let _value = *result;
                kani::cover(true, "unchecked back element reached under precondition");
            }
            }
        };
    }

    // The iterator macro also contracts its TrustedRandomAccess entry point.
    // Exercise the real method once, then only inspect metadata and the result;
    // advancing the iterator afterward would violate the caller's protocol.
    macro_rules! gen_iter_get_unchecked_contract {
        ($ty:ty, $iterator:ident, $view:ident) => {
            with_solver! {
            #[kani::proof_for_contract(<$iterator<'_, $ty> as crate::iter::traits::iterator::Iterator>::__iterator_get_unchecked)]
            fn check_get_unchecked_contract() {
                reset_observation();
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut iter = $iterator::new(storage.$view());
                let base = iter.ptr.as_ptr().cast_const();
                let len = iter.len();
                let index: usize = kani::any();
                // SAFETY: proof_for_contract supplies the documented index bound.
                // There are no earlier accesses or repeated indices.
                let item = unsafe { iter.__iterator_get_unchecked(index) };
                assert!((item as *const $ty) == base.wrapping_add(index));
                assert!(element_is_readable(item as *const $ty));
                check_writable_region!($view, item as *const $ty, 1);
                let _value = *item;
                assert!(iter.ptr.as_ptr().cast_const() == base);
                assert_eq!(iter.len(), len);
                kani::cover(index == 0, "first unchecked iterator element");
                kani::cover(index > 0, "nonzero unchecked iterator index");
                kani::cover(index == len - 1, "last unchecked iterator element");
            }
            }
        };
    }

    // The mutable chunk hints use only raw slice metadata and chunk_size.
    // Exercise their contracts at every length and address bit pattern.
    macro_rules! gen_chunk_size_hint {
        ($iterator:ident, $ty:ty) => {
            with_solver! { $iterator, size_hint,
            #[kani::proof_for_contract(<$iterator<'_, $ty> as crate::iter::traits::iterator::Iterator>::size_hint)]
            fn check_size_hint_contract() {
                let address: usize = kani::any();
                let len: usize = kani::any();
                let size = kani::any_where(|size: &usize| *size > 0);
                kani::cover(true, "admissible positive chunk size");
                let mut iter = $iterator::new(&mut [], 1);
                iter.chunk_size = size;
                iter.v = ptr::slice_from_raw_parts_mut(address as *mut $ty, len);
                let hint = iter.size_hint();
                kani::cover(len == 0 && hint.0 == 0, "empty input hint");
                kani::cover(len > 0 && hint.0 > 0, "nonempty input with a chunk");
                kani::cover(len == usize::MAX && size == 1, "maximal raw slice length");
                kani::cover(address == 0 && len > 0, "metadata-only call with null data");
            }
            }
        };
    }

    macro_rules! gen_chunk_methods {
        ($ty:ty, $iterator:ident, $view:ident, $pointer:ident, $reverse:expr, $exact:expr, $touch:ident) => {
            gen_chunk_size_hint!($iterator, $ty);
            gen_chunk_step!(
                check_next, $ty, $iterator, next, $view, $pointer, $reverse, $exact, false, $touch
            );
            gen_chunk_step!(
                check_nth, $ty, $iterator, nth, $view, $pointer, $reverse, $exact, false, $touch
            );
            gen_chunk_step!(
                check_next_back,
                $ty,
                $iterator,
                next_back,
                $view,
                $pointer,
                $reverse,
                $exact,
                true,
                $touch
            );
            gen_chunk_step!(
                check_nth_back,
                $ty,
                $iterator,
                nth_back,
                $view,
                $pointer,
                $reverse,
                $exact,
                true,
                $touch,
                kani::should_panic,
                kani::stub_verified(
                    <$iterator<'_, $ty> as crate::iter::traits::iterator::Iterator>::size_hint
                )
            );
        };
    }

    impl kani::Arbitrary for *mut [[u8; 3]] {
        fn any() -> Self {
            // This is a raw wide pointer: both data bits and length are
            // unconstrained. The verified split postcondition constrains its
            // result to the original allocation and precise subslice.
            ptr::slice_from_raw_parts_mut(kani::any::<usize>() as *mut [u8; 3], kani::any())
        }
    }

    #[kani::proof_for_contract(<*mut [[u8; 3]]>::split_at_mut_unchecked)]
    fn check_triplet_split_at_mut_unchecked_contract() {
        reset_observation();
        // A split can itself consume a subslice, including the prefix returned
        // from a prior split. Model every aligned start and trailing byte extent.
        let mut storage = SymbolicSlice::<[u8; 3]>::with_optional_suffix::<true>();
        let slice = storage.as_mut_slice();
        let raw: *mut [[u8; 3]] = slice;
        let mid: usize = kani::any();
        let (head, tail) = unsafe { raw.split_at_mut_unchecked(mid) };
        kani::cover(head.len() == 0, "empty prefix");
        kani::cover(tail.len() == 0, "empty suffix");
        kani::cover(head.len() > 0 && tail.len() > 0, "interior split");
    }

    macro_rules! exact_nth_back_solver {
        (byte_triplet, $ty:ty, $harness:item) => {
            #[kani::solver(cadical)]
            #[kani::stub_verified(<*mut [$ty]>::split_at_mut_unchecked)]
            $harness
        };
        ($module:ident, $ty:ty, $harness:item) => {
            #[kani::solver(cvc5)]
            $harness
        };
    }

    macro_rules! triplet_step_split {
        (byte_triplet, $ty:ty, $solver:ident, $harness:item) => {
            #[kani::solver(cadical)]
            #[kani::stub_verified(<*mut [$ty]>::split_at_mut_unchecked)]
            $harness
        };
        ($module:ident, $ty:ty, $solver:ident, $harness:item) => {
            #[kani::solver($solver)]
            $harness
        };
    }

    macro_rules! gen_type_suite {
        ($module:ident, $ty:ty, $solver:ident $(, $zst:ident)?) => {
            mod $module {
                use super::*;
                macro_rules! with_solver {
                    (ChunksExactMut, nth_back, $harness:item) => {
                        exact_nth_back_solver!($module, $ty, $harness);
                    };
                    (ChunksExactMut, next_back, $harness:item) => {
                        triplet_step_split!($module, $ty, $solver, $harness);
                    };
                    (ChunksExactMut, nth, $harness:item) => {
                        triplet_step_split!($module, $ty, $solver, $harness);
                    };
                    (RChunksExactMut, nth, $harness:item) => {
                        triplet_step_split!($module, $ty, $solver, $harness);
                    };
                    (ChunksMut, nth_back, $harness:item) => {
                        triplet_step_split!($module, $ty, $solver, $harness);
                    };
                    (RChunksExactMut, nth_back, $harness:item) => {
                        triplet_step_split!($module, $ty, $solver, $harness);
                    };
                    (ChunksExactMut, size_hint, $harness:item) => {
                        #[kani::solver(cvc5)] $harness
                    };
                    ($iterator:ident, $method:ident, $harness:item) => {
                        #[kani::solver($solver)] $harness
                    };
                    ($iterator:ident, $harness:item) => {
                        chunk_getter_solver!($module, $iterator, $solver, $harness);
                    };
                    ($harness:item) => { #[kani::solver($solver)] $harness };
                }
                mod iter {
                    use super::*;
                    gen_iter_family!($ty, Iter, as_slice);
                    gen_internal_contracts!($ty, Iter, as_slice);
                    gen_iter_get_unchecked_contract!($ty, Iter, as_slice);
                }
                mod iter_mut {
                    use super::*;
                    gen_iter_family!($ty, IterMut, as_mut_slice);
                    gen_internal_contracts!($ty, IterMut, as_mut_slice);
                    gen_iter_get_unchecked_contract!($ty, IterMut, as_mut_slice);
                    gen_iter_mut_views!($ty);
                }
                mod split {
                    use super::*;
                    gen_split_step!(check_next, $ty, next, false);
                    gen_split_step!(check_next_back, $ty, next_back, true);
                }
                mod windows { use super::*; gen_windows!($ty); }
                mod chunks {
                    use super::*;
                    gen_chunk_contract!(Chunks, $ty, as_slice, as_ptr, false);
                    gen_chunk_step!(check_next_back, $ty, Chunks, next_back, as_slice, as_ptr, false, false, true, touch_shared);
                }
                mod chunks_mut {
                    use super::*;
                    gen_chunk_contract!(ChunksMut, $ty, as_mut_slice, as_mut_ptr, false);
                    gen_chunk_methods!($ty, ChunksMut, as_mut_slice, as_mut_ptr, false, false, touch_mut);
                }
                mod chunks_exact {
                    use super::*;
                    gen_exact_chunk_contract!(
                        $module, ChunksExact, ($ty, as_slice, as_ptr), (from_raw_parts, false, false)
                    );
                    gen_exact_constructor!($ty, ChunksExact, as_slice, as_ptr, false);
                }
                mod chunks_exact_mut {
                    use super::*;
                    gen_exact_chunk_contract!(
                        $module, ChunksExactMut, ($ty, as_mut_slice, as_mut_ptr),
                        (from_raw_parts_mut, false, true, PhantomData)
                    );
                    gen_chunk_methods!($ty, ChunksExactMut, as_mut_slice, as_mut_ptr, false, true, touch_mut);
                    gen_exact_constructor!($ty, ChunksExactMut, as_mut_slice, as_mut_ptr, false);
                }
                mod rchunks {
                    use super::*;
                    gen_chunk_contract!(RChunks, $ty, as_slice, as_ptr, false);
                    gen_chunk_step!(check_next, $ty, RChunks, next, as_slice, as_ptr, true, false, false, touch_shared);
                    gen_chunk_step!(check_next_back, $ty, RChunks, next_back, as_slice, as_ptr, true, false, true, touch_shared);
                }
                mod rchunks_mut {
                    use super::*;
                    gen_chunk_contract!(RChunksMut, $ty, as_mut_slice, as_mut_ptr, false);
                    gen_chunk_methods!($ty, RChunksMut, as_mut_slice, as_mut_ptr, true, false, touch_mut);
                    gen_chunk_last!($ty, RChunksMut, as_mut_slice, as_mut_ptr, true, touch_mut);
                }
                mod rchunks_exact {
                    use super::*;
                    gen_exact_chunk_contract!(
                        $module, RChunksExact, ($ty, as_slice, as_ptr), (from_raw_parts, true, false)
                    );
                    gen_exact_constructor!($ty, RChunksExact, as_slice, as_ptr, true);
                }
                mod rchunks_exact_mut {
                    use super::*;
                    gen_exact_chunk_contract!(
                        $module, RChunksExactMut, ($ty, as_mut_slice, as_mut_ptr), (from_raw_parts_mut, true, true)
                    );
                    gen_chunk_methods!($ty, RChunksExactMut, as_mut_slice, as_mut_ptr, true, true, touch_mut);
                    gen_exact_constructor!($ty, RChunksExactMut, as_mut_slice, as_mut_ptr, true);
                }
                mod array_windows_1 { use super::*; gen_array_windows!($ty, 1); }
                mod array_windows_2 { use super::*; gen_array_windows!($ty, 2); }
                mod array_windows_4 { use super::*; gen_array_windows!($ty, 4); }
                mod splitn {
                    use super::*;
                    gen_splitn!($ty, splitn, as_slice, touch_shared);
                    $(gen_max_splitn_panic!($zst, $ty, splitn, as_slice);)?
                }
                mod rsplitn {
                    use super::*;
                    gen_splitn!($ty, rsplitn, as_slice, touch_shared);
                    $(gen_max_splitn_panic!($zst, $ty, rsplitn, as_slice);)?
                }
                mod splitn_mut {
                    use super::*;
                    gen_splitn!($ty, splitn_mut, as_mut_slice, touch_mut);
                    $(gen_max_splitn_panic!($zst, $ty, splitn_mut, as_mut_slice);)?
                }
                mod rsplitn_mut {
                    use super::*;
                    gen_splitn!($ty, rsplitn_mut, as_mut_slice, touch_mut);
                    $(gen_max_splitn_panic!($zst, $ty, rsplitn_mut, as_mut_slice);)?
                }
            }
        };
    }

    gen_type_suite!(unit, (), cadical, zst);
    gen_type_suite!(byte, u8, cadical);
    gen_type_suite!(boolean, bool, cadical);
    gen_type_suite!(byte_triplet, [u8; 3], cadical);
    gen_type_suite!(padded, Padded, cadical);
    gen_type_suite!(aligned_zst, AlignedZst, cadical, zst);
    gen_type_suite!(aligned_word, AlignedWord, cadical);
}
