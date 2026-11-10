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
        && (self.size_hint() == old(self.size_hint()))
        && (self.size.get() == old(self.size.get()))
        && (crate::ub_checks::can_dereference(*result as *const [T]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        // SAFETY: the caller guarantees that `idx` selects a window in `self.v`.
        // Its byte offset fits in an isize because self.v is a valid slice. For a ZST,
        // that offset is zero even when the element index exceeds isize::MAX.
        // The returned subslice is valid for the lifetime 'a of self.v.
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a [T]| {
        (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
        && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx * old(self.chunk_size)))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.size_hint() == old(self.size_hint()))
        && (self.chunk_size == old(self.chunk_size))
        && (crate::ub_checks::can_dereference(*result as *const [T]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        let start = idx * self.chunk_size;
        // SAFETY: the caller guarantees that idx is a valid chunk index, so start
        // is in bounds of self.v and its multiplication cannot overflow usize. The
        // chosen len keeps the whole result within self.v. The byte offset fits in
        // isize; for a ZST it is zero even if start exceeds isize::MAX. The returned
        // subslice is therefore valid for the lifetime 'a of self.v.
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a mut [T]| {
        (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
        && (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add(idx * old(self.chunk_size)))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.size_hint() == old(self.size_hint()))
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a [T]| {
        (result.len() == old(self.chunk_size))
        && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx * old(self.chunk_size)))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.size_hint() == old(self.size_hint()))
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a mut [T]| {
        (result.len() == old(self.chunk_size))
        && (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add(idx * old(self.chunk_size)))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.size_hint() == old(self.size_hint()))
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

    #[requires(N > 0 && idx < self.len())]
    #[ensures(|result: &&'a [T; N]| {
        (result.len() == N)
        && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.size_hint() == old(self.size_hint()))
        && (crate::ub_checks::can_dereference(*result as *const [T; N]))
    })]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item {
        // SAFETY: the caller guarantees that idx selects a full array in self.v.
        // Its byte offset fits in isize; for a ZST it is zero even when idx exceeds
        // isize::MAX. The array created by cast_array stays within self.v and is
        // valid for its lifetime 'a.
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a [T]| {
        (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
        && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add((old(self.v.len()) - idx * old(self.chunk_size)).saturating_sub(old(self.chunk_size))))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.size_hint() == old(self.size_hint()))
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a mut [T]| {
        (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
        && (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add((old(self.v.len()) - idx * old(self.chunk_size)).saturating_sub(old(self.chunk_size))))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.size_hint() == old(self.size_hint()))
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a [T]| {
        (result.len() == old(self.chunk_size))
        && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add((old(self.v.len()) - idx * old(self.chunk_size)) - old(self.chunk_size)))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_ptr() == old(self.v.as_ptr()))
        && (self.size_hint() == old(self.size_hint()))
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

    #[requires(self.chunk_size > 0 && idx < self.len())]
    #[ensures(|result: &&'a mut [T]| {
        (result.len() == old(self.chunk_size))
        && (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add((old(self.v.len()) - idx * old(self.chunk_size)) - old(self.chunk_size)))
        && (self.v.len() == old(self.v.len()))
        && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
        && (self.size_hint() == old(self.size_hint()))
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
    use super::*;
    use crate::alloc::Layout;
    use crate::ffi::c_int;
    use crate::{kani, ptr};

    // Equivalent to index < ceil(len / size) for size > 0; see the forward,
    // reverse-implication and native-equivalence arithmetic proofs below.
    macro_rules! native_chunk_offset_facts {
        ($len:expr, $size:expr, $index:expr) => {
            $index.checked_mul($size).is_some() && $index.wrapping_mul($size) < $len
        };
    }

    // Equivalent to index < len / size for size > 0. Guard the subtraction even
    // for invalid indices; express the result as the available remaining range.
    macro_rules! native_exact_chunk_offset_facts {
        ($len:expr, $size:expr, $index:expr) => {
            $index.checked_mul($size).is_some()
                && $index.wrapping_mul($size) <= $len
                && $size <= $len - $index.wrapping_mul($size)
        };
    }

    // The checked end-range fact is proved independently; getter proofs may reuse
    // only this pure arithmetic lemma, while still executing the original getter.
    macro_rules! exact_chunk_end_facts {
        ($len:expr, $size:expr, $index:expr) => {{
            let start = $index.wrapping_mul($size);
            start.checked_add($size).is_some() && start.wrapping_add($size) <= $len
        }};
    }

    #[requires(size > 0 && native_exact_chunk_offset_facts!(len, size, index))]
    #[ensures(|_: &()| exact_chunk_end_facts!(len, size, index))]
    fn exact_chunk_end_arithmetic(len: usize, size: usize, index: usize) {}

    // A valid non-ZST slice has len * size_of::<T>() <= isize::MAX, hence
    // len <= isize::MAX. Keep this bridge linear: callers must prove the actual
    // computed offset is in their slice. No iterator harness assumes a smaller
    // length domain, and ZST getters do not call this lemma.
    #[requires(offset <= len && len <= isize::MAX as usize)]
    #[ensures(|_: &()| offset <= isize::MAX as usize)]
    fn offset_isize_arithmetic(offset: usize, len: usize) {}

    // Spatial subrange lemmas separate allocation geometry from index multiplication.
    // These do not establish lifetime ownership or the absence of conflicting borrows.
    // Each instantiated lemma must be proved before a getter proof reuses its contract.
    #[requires(
        start <= len && size <= len - start
            && crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(base, len))
    )]
    #[ensures(|_: &()| crate::ub_checks::can_dereference(
        ptr::slice_from_raw_parts(base.wrapping_add(start), size)
    ))]
    fn readable_subslice<T>(base: *const T, len: usize, start: usize, size: usize) {}

    // Bridge a readable byte region to a single element without chunk arithmetic.
    // This is spatial validity only; it does not establish borrow exclusivity.
    // A reference supplies the valid input region. Avoid using a memory
    // predicate as an assumption about an arbitrary raw pointer.
    #[requires(index < slice.len())]
    #[ensures(|_: &()| crate::ub_checks::can_dereference(slice.as_ptr().wrapping_add(index)))]
    fn readable_byte_at(slice: &[u8], index: usize) {}

    #[kani::proof_for_contract(readable_byte_at)]
    fn check_readable_byte_at_contract() {
        let storage = SymbolicSlice::<u8>::any();
        let slice = any_slice(storage.as_slice());
        let index: usize = kani::any();
        readable_byte_at(slice, index);
        kani::cover(index == 0, "first byte in a readable region");
        kani::cover(
            index > 0 && index == slice.len().wrapping_sub(1),
            "last byte after a nonempty prefix",
        );
        kani::cover(
            index > 0 && index.wrapping_add(1) < slice.len(),
            "interior byte in a readable region",
        );
    }

    // Keep the original conjunction as separate caller obligations so arithmetic
    // bounds and allocation validity can be discharged independently.
    #[requires(start <= len && size <= len - start)]
    #[requires(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(base.cast_const(), len)))]
    #[requires(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(base, len)))]
    #[ensures(|_: &()| {
        crate::ub_checks::can_dereference(
            ptr::slice_from_raw_parts(base.wrapping_add(start).cast_const(), size)
        ) && crate::ub_checks::can_write(
            ptr::slice_from_raw_parts_mut(base.wrapping_add(start), size)
        )
    })]
    fn writable_subslice<T>(base: *mut T, len: usize, start: usize, size: usize) {}

    // Describe a region by ordered endpoints. The body proves the original
    // subtraction-based subrange precondition before reusing its spatial fact.
    #[requires(start <= end && end <= len)]
    #[requires(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(base.cast_const(), len)))]
    #[requires(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(base, len)))]
    #[ensures(|_: &()| {
        crate::ub_checks::can_dereference(
            ptr::slice_from_raw_parts(base.wrapping_add(start).cast_const(), end - start)
        ) && crate::ub_checks::can_write(
            ptr::slice_from_raw_parts_mut(base.wrapping_add(start), end - start)
        )
    })]
    fn writable_interval<T>(base: *mut T, len: usize, start: usize, end: usize) {
        writable_subslice(base, len, start, end - start);
    }

    // Name the remaining prefix separately so its caller bounds do not share a
    // property ID with the returned chunk's arbitrary-start bounds.
    #[requires(prefix <= len)]
    #[requires(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(base.cast_const(), len)))]
    #[requires(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(base, len)))]
    #[ensures(|_: &()| {
        crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(base.cast_const(), prefix))
            && crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(base, prefix))
    })]
    fn writable_prefix<T>(base: *mut T, len: usize, prefix: usize) {
        writable_subslice(base, len, 0, prefix);
    }

    // Exact postconditions use total offset arithmetic. The entry precondition
    // proves that these products/subtractions do not wrap, as checked independently
    // by check_exact_postcondition_offset_equivalence. This avoids proving overflow
    // checks introduced only by evaluating the specification; the original getter's
    // own checked arithmetic and memory-safety checks remain unchanged.
    // Contract entry points for the real random-access implementations.
    //
    // These methods do not replace any runtime implementation. Each executes the original trait
    // method without a stub. Chunks use equivalent spatial bounds here to avoid
    // division in the proof precondition. All metadata fields are preserved exactly; since
    // size_hint only reads length and chunk_size, this also preserves size_hint. Its formula
    // is checked separately for non-exact families over every usize length using a ZST.
    // Exact families all have the audited metadata-only formula v.len() / chunk_size;
    // the forward/reverse/full-range proofs establish the corresponding index bound.
    //
    // The contracts describe a single call on a valid iterator. They do NOT encode the temporal
    // TrustedRandomAccess protocol: unique indices for non-Clone iterators, the next_back budget,
    // restrictions on later methods, clone history, or subtype coercions. See the safety audit below for
    // the safety audit and protocol harnesses. In particular, can_write is not an exclusivity proof.

    impl<'a, T> Windows<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(idx < self.len())]
        #[ensures(|result: &&'a [T]| {
            (result.len() == old(self.size.get()))
            && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx))
            && (self.v.len() == old(self.v.len()))
            && (self.v.as_ptr() == old(self.v.as_ptr()))
            && (self.size_hint() == old(self.size_hint()))
            && (self.size.get() == old(self.size.get()))
            && (crate::ub_checks::can_dereference(*result as *const [T]))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a [T] {
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> Chunks<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a [T]| {
            (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
            && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx * old(self.chunk_size)))
            && (self.v.len() == old(self.v.len()))
            && (self.v.as_ptr() == old(self.v.as_ptr()))
            && (self.chunk_size == old(self.chunk_size))
            && (crate::ub_checks::can_dereference(*result as *const [T]))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a [T] {
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> ChunksMut<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a mut [T]| {
            (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
            && (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add(idx * old(self.chunk_size)))
            && (self.v.len() == old(self.v.len()))
            && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
            && (self.chunk_size == old(self.chunk_size))
            && (crate::ub_checks::can_dereference(&**result as *const [T]))
            && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> ChunksExact<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_exact_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a [T]| {
            (result.len() == old(self.chunk_size))
        })]
        #[ensures(|result: &&'a [T]| {
            (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx.wrapping_mul(old(self.chunk_size))))
        })]
        #[ensures(|_result: &&'a [T]| {
            (self.v.len() == old(self.v.len()))
            && (self.v.as_ptr() == old(self.v.as_ptr()))
            && (self.chunk_size == old(self.chunk_size))
            && (self.rem.len() == old(self.rem.len()))
            && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        })]
        #[ensures(|result: &&'a [T]| {
            (crate::ub_checks::can_dereference(*result as *const [T]))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a [T] {
            exact_chunk_end_arithmetic(self.v.len(), self.chunk_size, idx);
            if !T::IS_ZST {
                // Prove both premises at this call, rather than assuming a length cap.
                // A valid non-ZST slice supplies len <= isize::MAX; the original
                // index precondition supplies the computed offset's range.
                let offset = idx * self.chunk_size;
                offset_isize_arithmetic(offset, self.v.len());
            }
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> ChunksExactMut<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_exact_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a mut [T]| {
            (result.len() == old(self.chunk_size))
        })]
        #[ensures(|result: &&'a mut [T]| {
            (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add(idx.wrapping_mul(old(self.chunk_size))))
        })]
        #[ensures(|_result: &&'a mut [T]| {
            (self.v.len() == old(self.v.len()))
            && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
            && (self.chunk_size == old(self.chunk_size))
            && (self.rem.len() == old(self.rem.len()))
            && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        })]
        #[ensures(|result: &&'a mut [T]| {
            (crate::ub_checks::can_dereference(&**result as *const [T]))
            && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
            exact_chunk_end_arithmetic(self.v.len(), self.chunk_size, idx);
            if !T::IS_ZST {
                // Prove both premises at this call, rather than assuming a length cap.
                // A valid non-ZST slice supplies len <= isize::MAX; the original
                // index precondition supplies the computed offset's range.
                let offset = idx * self.chunk_size;
                offset_isize_arithmetic(offset, self.v.len());
            }
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T, const N: usize> ArrayWindows<'a, T, N> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(N > 0 && idx < self.len())]
        #[ensures(|result: &&'a [T; N]| {
            (result.len() == N)
            && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(idx))
            && (self.v.len() == old(self.v.len()))
            && (self.v.as_ptr() == old(self.v.as_ptr()))
            && (self.size_hint() == old(self.size_hint()))
            && (crate::ub_checks::can_dereference(*result as *const [T; N]))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a [T; N] {
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> RChunks<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a [T]| {
            (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
            && (result.as_ptr() == old(self.v.as_ptr()).wrapping_add((old(self.v.len()) - idx * old(self.chunk_size)).saturating_sub(old(self.chunk_size))))
            && (self.v.len() == old(self.v.len()))
            && (self.v.as_ptr() == old(self.v.as_ptr()))
            && (self.chunk_size == old(self.chunk_size))
            && (crate::ub_checks::can_dereference(*result as *const [T]))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a [T] {
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> RChunksMut<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a mut [T]| {
            (result.len() == (old(self.v.len()) - idx * old(self.chunk_size)).min(old(self.chunk_size)))
            && (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add((old(self.v.len()) - idx * old(self.chunk_size)).saturating_sub(old(self.chunk_size))))
            && (self.v.len() == old(self.v.len()))
            && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
            && (self.chunk_size == old(self.chunk_size))
            && (crate::ub_checks::can_dereference(&**result as *const [T]))
            && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> RChunksExact<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_exact_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a [T]| {
            (result.len() == old(self.chunk_size))
        })]
        #[ensures(|result: &&'a [T]| {
            (result.as_ptr() == old(self.v.as_ptr()).wrapping_add(old(self.v.len()).wrapping_sub(idx.wrapping_mul(old(self.chunk_size))).wrapping_sub(old(self.chunk_size))))
        })]
        #[ensures(|_result: &&'a [T]| {
            (self.v.len() == old(self.v.len()))
            && (self.v.as_ptr() == old(self.v.as_ptr()))
            && (self.chunk_size == old(self.chunk_size))
            && (self.rem.len() == old(self.rem.len()))
            && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        })]
        #[ensures(|result: &&'a [T]| {
            (crate::ub_checks::can_dereference(*result as *const [T]))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a [T] {
            exact_chunk_end_arithmetic(self.v.len(), self.chunk_size, idx);
            if !T::IS_ZST {
                // Prove both premises at this call, rather than assuming a length cap.
                // A valid non-ZST slice supplies len <= isize::MAX; the original
                // index precondition supplies the computed offset's range.
                let offset = self.v.len() - idx * self.chunk_size - self.chunk_size;
                offset_isize_arithmetic(offset, self.v.len());
            }
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

    impl<'a, T> RChunksExactMut<'a, T> {
        /// # Safety
        ///
        /// The iterator must be valid and `idx` must be in bounds. The caller must also uphold
        /// every history-dependent obligation of `TrustedRandomAccess`, including those inherited
        /// through clones and lifetime coercions. The executable precondition captures only the
        /// local bounds requirement; it must not be read as a complete aliasing contract.
        #[requires(
            self.chunk_size > 0
                && native_exact_chunk_offset_facts!(self.v.len(), self.chunk_size, idx)
        )]
        #[ensures(|result: &&'a mut [T]| {
            (result.len() == old(self.chunk_size))
        })]
        #[ensures(|result: &&'a mut [T]| {
            (result.as_ptr() == old(self.v.as_mut_ptr().cast_const()).wrapping_add(old(self.v.len()).wrapping_sub(idx.wrapping_mul(old(self.chunk_size))).wrapping_sub(old(self.chunk_size))))
        })]
        #[ensures(|_result: &&'a mut [T]| {
            (self.v.len() == old(self.v.len()))
            && (self.v.as_mut_ptr().cast_const() == old(self.v.as_mut_ptr().cast_const()))
            && (self.chunk_size == old(self.chunk_size))
            && (self.rem.len() == old(self.rem.len()))
            && (self.rem.as_ptr() == old(self.rem.as_ptr()))
        })]
        #[ensures(|result: &&'a mut [T]| {
            (crate::ub_checks::can_dereference(&**result as *const [T]))
            && (crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(result.as_ptr().cast_mut(), result.len())))
        })]
        pub(super) unsafe fn kani_get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
            exact_chunk_end_arithmetic(self.v.len(), self.chunk_size, idx);
            if !T::IS_ZST {
                // Prove both premises at this call, rather than assuming a length cap.
                // A valid non-ZST slice supplies len <= isize::MAX; the original
                // index precondition supplies the computed offset's range.
                let offset = self.v.len() - idx * self.chunk_size - self.chunk_size;
                offset_isize_arithmetic(offset, self.v.len());
            }
            // SAFETY: the caller promises the original trait method's full contract.
            unsafe { <Self as Iterator>::__iterator_get_unchecked(self, idx) }
        }
    }

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

    fn any_iter<'a, T>(orig_slice: &'a [T]) -> Iter<'a, T> {
        let slice = any_slice(orig_slice);
        Iter::new(slice)
    }

    /// Macro that generates a harness for a given `Iter` method.
    ///
    /// Takes the name of the harness, the element type, and an expression to check.
    macro_rules! check_safe_abstraction {
        ($harness:ident, $elem_ty:ty, $call:expr) => {
            #[kani::proof]
            fn $harness() {
                let array: [$elem_ty; MAX_LEN] = kani::any();
                let mut iter = any_iter::<$elem_ty>(&array);
                let target = $call;
                target(&mut iter);
                kani::assert(iter.is_safe(), "Iter is safe");
            }
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
        ($harness:ident, $elem_ty:ty, $func:ident($($args:expr),*)) => {
            #[kani::proof_for_contract(Iter::$func)]
            fn $harness() {
                let array: [$elem_ty; MAX_LEN] = kani::any();
                let mut iter = any_iter::<$elem_ty>(&array);
                let _ = unsafe { iter.$func($($args),*) };
            }
        };
    }

    macro_rules! check_iter_with_ty {
        ($module:ident, $ty:ty, $max:expr) => {
            mod $module {
                use super::*;
                const MAX_LEN: usize = $max;

                #[kani::proof]
                fn check_new_iter() {
                    let array: [$ty; MAX_LEN] = kani::any();
                    let slice = any_slice::<$ty>(&array);
                    let mut iter = Iter::new(slice);
                    kani::assert(iter.is_safe(), "Iter is safe");
                }

                /// Count consumes the value, thus, invoke it directly.
                #[kani::proof]
                fn check_count() {
                    let array: [$ty; MAX_LEN] = kani::any();
                    let mut iter = any_iter::<$ty>(&array);
                    iter.count();
                }

                #[kani::proof]
                fn check_default() {
                    let iter: Iter<'_, $ty> = Iter::default();
                    kani::assert(iter.is_safe(), "Iter is safe");
                }

                check_unsafe_contracts!(check_next_back_unchecked, $ty, next_back_unchecked());
                check_unsafe_contracts!(check_post_inc_start, $ty, post_inc_start(kani::any()));
                check_unsafe_contracts!(check_pre_dec_end, $ty, pre_dec_end(kani::any()));

                // Public functions that call safe abstraction `make_slice`.
                check_safe_abstraction!(check_as_slice, $ty, |iter: &mut Iter<'_, $ty>| {
                    iter.as_slice();
                });
                check_safe_abstraction!(check_as_ref, $ty, |iter: &mut Iter<'_, $ty>| {
                    iter.as_ref();
                });

                check_safe_abstraction!(check_advance_back_by, $ty, |iter: &mut Iter<'_, $ty>| {
                    iter.advance_back_by(kani::any());
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

                // Ensure that clone always generates a safe object.
                check_safe_abstraction!(check_clone, $ty, |iter: &mut Iter<'_, $ty>| {
                    kani::assert(iter.clone().is_safe(), "Clone is safe");
                });
            }
        };
    }

    // Existing representative-type proofs are retained below.
    check_iter_with_ty!(verify_unit, (), isize::MAX as usize);
    check_iter_with_ty!(verify_u8, u8, u32::MAX as usize);
    check_iter_with_ty!(verify_char, char, 50);
    check_iter_with_ty!(verify_tup, (char, u8), 50);
    // Additional Challenge 18 verification artifacts.
    //
    // Safety audit of the older RQ-1..RQ-13 specification:
    // * RQ-1/2 are implementation guarantees, not additional assumptions about the caller. Since
    //   size() uses size_hint().0 and len() uses size_hint(), their mutual equality is not an
    //   independent oracle. Harnesses compare all three with a length computed from slice metadata.
    //   The trait also requires cheap size_hint(), a non-overridden size(), and the appropriate
    //   subtype/supertype trait implementations; per-call numeric contracts cannot express these.
    // * RQ-3 is the local index precondition. The chunk-size/type invariants justify deriving the
    //   full returned range from it. Contracts additionally describe the exact pointer and length,
    //   unchanged metadata (including exact remainders), and spatial read/write validity.
    // * RQ-4..RQ-9 concern call histories, not one invocation. In particular, after an unchecked
    //   access the allowed methods do not include next(), nth(), as_slice(), or Debug::fmt().
    //   A non-Clone iterator cannot reuse an index even when the earlier reference is no longer used.
    //   Each unchecked index imposes a next_back budget; the tightest index controls the budget.
    // * RQ-10 is a postcondition, not a caller assumption. The actual method retains it.
    //   Chunk proof entry points instead preserve every input metadata field, which implies
    //   the unchanged size_hint via the separately checked metadata-only count formula.
    //   Every proof entry point still calls the actual method without a stub.
    // * RQ-11..RQ-13 require sequence/ownership reasoning. The protocol harnesses exercise two
    //   distinct accesses, an allowed back step, drop, and lifetime shortening; shared iterators
    //   also exercise clone histories. These are NOT a full temporal or lifetime-ownership proof.
    // * can_dereference/can_write do not prove absence of conflicting live borrows, validity for
    //   the entire lifetime 'a, or all subtype coercions. Those obligations remain documented.
    //
    // Input model: symbolic lengths within Layout::array and CBMC's actual maximum object size,
    // initialized as independent nondeterministic bytes, restricted to valid T bit patterns;
    // no small tractability cap or unwind bound. ZST lengths remain
    // unrestricted. The non-ZST domain is the backend-representable domain, not every Rust layout.
    // POSIX allocation is modeled by Kani's C-FFI support. Verification is staged per harness;
    // selected harnesses have succeeded, but that does not establish the entire suite. Restricted
    // scalar types need element-validity quantifiers and a supporting SMT backend.
    // Backend object-size limits still apply.
    //
    // Scope: concrete Copy + Arbitrary types and N = 1, 2, 4. This is not a tool-level proof for
    // every T or N. In particular, no claim of completing the challenge's generic-T requirement
    // follows from these instantiations, the arithmetic lemmas, or the presence of loop contracts.

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
        } else if same_type_name(name, "char") {
            2
        } else if same_type_name(name, "(char, u8)") {
            3
        } else if same_type_name(name, "u8")
            || same_type_name(name, "()")
            || same_type_name(name, "core::slice::iter::verify::AlignedZst")
            || same_type_name(name, "core::slice::iter::verify::AlignedWord")
        {
            0
        } else {
            255
        }
    }

    // Element validity is separate from the allocation's bounds/alignment. Use pure
    // bit-pattern predicates for the restricted scalar types in this suite; expanding
    // can_dereference (with its allocation checks) inside a quantifier is prohibitively
    // expensive. The other suite types admit all initialized bit patterns. This helper
    // is verification-only and does not turn these instantiations into a generic proof.
    /// Checks value validity without reading through a potentially invalid T.
    ///
    /// # Safety
    /// The prefix of len elements must have live, readable, initialized storage, aligned for T.
    /// This does not require the stored bit patterns to be valid T values: that is what is tested.
    pub(super) unsafe fn valid_elements<T>(data: *const T, len: usize) -> bool {
        // Evaluate classification in rustc. Copy-capture the immutable base pointer in
        // quantified predicates so the formula need not follow a reference to this local.
        match const { element_validity_kind::<T>() } {
            0 => true,
            1 => kani::internal::kani_forall(0usize, len, move |index: usize| unsafe {
                *data.wrapping_add(index).cast::<u8>() <= 1
            }),
            2 => kani::internal::kani_forall(0usize, len, move |index: usize| unsafe {
                let bits = *data.wrapping_add(index).cast::<u32>();
                // This total, branchless encoding admits exactly the Unicode scalar values.
                // Keep it in sync with the independent interval-equivalence proof below;
                // matching from_u32's encoding also avoids a disjunction inside the quantifier.
                (bits ^ 0xD800).wrapping_sub(0x800) < 0x10F800
            }),
            3 => kani::internal::kani_forall(0usize, len, move |index: usize| unsafe {
                let field = data
                    .wrapping_add(index)
                    .cast::<u8>()
                    .wrapping_add(mem::offset_of!((char, u8), 0));
                let bits = *field.cast::<u32>();
                (bits ^ 0xD800).wrapping_sub(0x800) < 0x10F800
            }),
            // The constructor rejects unsupported types before reaching this predicate.
            _ => len == 0,
        }
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
        if current != initial_ptr.wrapping_add(front) {
            return false;
        }
        let remaining = initial_len - front - back;
        let end_matches = if T::IS_ZST {
            end_or_len as usize == remaining
        } else {
            end_or_len == initial_ptr.wrapping_add(initial_len - back) as *const T
        };
        end_matches
            && ((const { element_validity_kind::<T>() == 0 })
                || unsafe { valid_elements(current, remaining) })
    }

    /// Owns initialized symbolic storage, without depending on alloc from core.
    /// Copy avoids introducing element destructor loops unrelated to the iterator methods.
    struct SymbolicSlice<T: Copy> {
        data: *mut T,
        len: usize,
        allocated: bool,
    }

    impl<T: Copy + kani::Arbitrary> SymbolicSlice<T> {
        fn any() -> Self {
            assert!(
                const { element_validity_kind::<T>() != 255 },
                "SymbolicSlice needs a complete element-validity predicate for T",
            );
            let len: usize = kani::any();
            let layout = Layout::array::<T>(len);
            kani::assume(layout.is_ok());
            let layout = layout.unwrap();
            if layout.size() == 0 {
                // For a nonempty ZST slice, establish that T has an inhabitant as well.
                if len != 0 {
                    let _: T = kani::any();
                }
                let address: usize = kani::any();
                let data = address as *mut T;
                kani::assume(!data.is_null() && data.is_aligned());
                return Self { data, len, allocated: false };
            }

            // The pointer encoding reserves object-id bits. Requests outside its offset
            // domain are not representable allocations (and also violate loop-frame CAR
            // bounds). Read the backend's own limit so changing --object-bits stays coherent.
            // SAFETY: CBMC provides this immutable, initialized runtime constant.
            let model_limit = unsafe { __CPROVER_max_malloc_size };
            kani::assume(layout.size() < model_limit);
            let mut memory = ptr::null_mut();
            let alignment = layout.align().max(mem::size_of::<*mut u8>());
            // SAFETY: alignment is a power of two and a multiple of sizeof(void*), and out
            // points to a live local. Success returns a fresh allocation of layout.size().
            let status = unsafe { posix_memalign(&mut memory, alignment, layout.size()) };
            // We need valid existing slices, so allocation failure is not an input case.
            kani::assume(status == 0);
            let data = memory.cast::<T>();
            assert!(!data.is_null() && data.is_aligned());
            assert!(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(data, len)));
            // SAFETY: this is fresh, exclusively owned, live storage; no references have
            // been created yet. The CBMC primitive writes independent initialized bytes
            // throughout this allocation. Constrain restricted scalar representations
            // before creating a typed slice, just as kani::any constrains scalar inputs.
            // This removes an input-construction loop without bounding lengths or values.
            unsafe { __CPROVER_havoc_object(memory) };
            kani::assume(unsafe { valid_elements(data, len) });
            Self { data, len, allocated: true }
        }
    }

    impl<T: Copy> SymbolicSlice<T> {
        fn as_slice(&self) -> &[T] {
            // SAFETY: construction initializes the whole allocation; self owns it until drop.
            unsafe { from_raw_parts(self.data, self.len) }
        }

        fn as_mut_slice(&mut self) -> &mut [T] {
            // SAFETY: the mutable borrow prevents another view while this one is live.
            unsafe { from_raw_parts_mut(self.data, self.len) }
        }
    }

    impl<T: Copy> Drop for SymbolicSlice<T> {
        fn drop(&mut self) {
            if self.allocated {
                // SAFETY: data is the original successful POSIX allocation, freed once.
                // T is Copy, so no element destructor is skipped.
                unsafe { free(self.data.cast_const().cast::<u8>()) };
            }
        }
    }

    // Prove the compact encoding against the Unicode intervals for every u32, independently
    // of from_u32, whose implementation uses the same optimized encoding.
    #[kani::proof]
    fn check_char_bits_equivalence() {
        let bits: u32 = kani::any();
        let compact = (bits ^ 0xD800).wrapping_sub(0x800) < 0x10F800;
        let intervals = (bits <= 0xD7FF) | ((bits >= 0xE000) & (bits <= 0x10FFFF));
        assert_eq!(compact, intervals);
        kani::cover(bits == 0xD7FF, "last scalar before surrogates");
        kani::cover(bits == 0xD800 && !compact, "first surrogate excluded");
        kani::cover(bits == 0xDFFF && !compact, "last surrogate excluded");
        kani::cover(bits == 0xE000 && compact, "first scalar after surrogates");
        kani::cover(bits == 0x10FFFF && compact, "maximal Unicode scalar");
        kani::cover(bits == 0x110000 && !compact, "values above Unicode excluded");
        kani::cover(bits == u32::MAX && !compact, "maximal u32 excluded");
    }

    // This bounded regression checks quantified memory loads against from_u32. The scalar
    // proof above supplies the independent interval oracle; iterator/domain lengths stay symbolic.
    #[kani::proof]
    fn check_char_validity_predicate() {
        let words: [u32; 2] = kani::any();
        // SAFETY: u32 provides initialized storage with char's size/alignment, even when
        // the representations are invalid char values. Only raw u32 loads occur in the predicate.
        let valid = unsafe { valid_elements(words.as_ptr().cast::<char>(), words.len()) };
        let expected =
            crate::char::from_u32(words[0]).is_some() & crate::char::from_u32(words[1]).is_some();
        kani::assert(valid == expected, "character predicate matches Unicode scalar values");
        kani::cover(expected, "valid nonempty representations exist");
        kani::cover(!expected, "invalid representations exist");
    }

    #[kani::proof]
    fn check_char_input_domain() {
        let storage = SymbolicSlice::<char>::any();
        kani::cover(storage.len == 0, "empty iterator");
        kani::cover(storage.len > 1, "multiple elements");
        let index: usize = kani::any();
        if index < storage.len {
            // SAFETY: the fresh allocation contains initialized bytes for every element;
            // the symbolic index is in bounds, and char/u32 have the same layout here.
            let bits = unsafe { *storage.data.wrapping_add(index).cast::<u32>() };
            assert!(crate::char::from_u32(bits).is_some());
            kani::cover(true, "nonempty symbolic character read");
        }
    }

    fn any_slice_mut<T>(original: &mut [T]) -> &mut [T] {
        if kani::any() {
            let end = kani::any_where(|n: &usize| *n <= original.len());
            let start = kani::any_where(|n: &usize| *n <= end);
            &mut original[start..end]
        } else {
            let data = kani::any::<usize>() as *mut T;
            kani::assume(!data.is_null() && data.is_aligned());
            // SAFETY: empty slices require non-null, aligned pointers, not an allocation.
            unsafe { from_raw_parts_mut(data, 0) }
        }
    }

    macro_rules! symbolic_view {
        ($storage:ident, as_slice) => {
            any_slice($storage.as_slice())
        };
        ($storage:ident, as_mut_slice) => {
            any_slice_mut($storage.as_mut_slice())
        };
    }

    fn check_slice<T>(slice: &[T], base: *const T, start: usize, len: usize) {
        kani::assert(slice.len() == len, "slice length matches the expected length");
        kani::assert(
            slice.as_ptr() == base.wrapping_add(start),
            "slice pointer matches the expected start",
        );
        // Check real reads, not just metadata. Do not compare bytes: padding need not be init.
        // Keep each value check at its call site in the verification model.
        if let Some(first) = slice.first() {
            kani::assert(
                crate::ub_checks::can_dereference(first),
                "first slice element is readable",
            );
        }
        if let Some(last) = slice.last() {
            kani::assert(crate::ub_checks::can_dereference(last), "last slice element is readable");
        }
    }

    fn touch_shared<T: Copy>(slice: &mut &[T]) {
        if let Some(first) = slice.first() {
            let _value = *first;
        }
    }

    fn touch_mut<T: Copy + kani::Arbitrary>(slice: &mut &mut [T]) {
        if let Some(first) = slice.first_mut() {
            *first = kani::any();
        }
        if let Some(last) = slice.last_mut() {
            *last = kani::any();
        }
    }

    fn chunk_count(len: usize, size: usize, exact: bool) -> usize {
        assert!(size > 0);
        if exact { len / size } else { len.div_ceil(size) }
    }

    /// Reference arithmetic uses checked operations, independently of iterator size_hint().
    fn chunk_range(len: usize, size: usize, index: usize, reverse: bool) -> (usize, usize) {
        let offset = index.checked_mul(size).expect("valid chunk index cannot overflow");
        if reverse {
            let end = len.checked_sub(offset).expect("reverse offset is in bounds");
            let start = end.saturating_sub(size);
            (start, end - start)
        } else {
            let remaining = len.checked_sub(offset).expect("forward offset is in bounds");
            (offset, remaining.min(size))
        }
    }

    fn check_exact_hint<I>(iter: &I, count: usize)
    where
        I: ExactSizeIterator + TrustedRandomAccessNoCoerce,
    {
        kani::assert(
            iter.size_hint() == (count, Some(count)),
            "size_hint matches exact remaining count",
        );
        kani::assert(iter.len() == count, "len matches exact remaining count");
        kani::assert(
            TrustedRandomAccessNoCoerce::size(iter) == count,
            "trusted size matches exact remaining count",
        );
    }

    #[repr(align(16))]
    #[derive(Clone, Copy, kani::Arbitrary)]
    struct AlignedZst;

    #[repr(align(32))]
    #[derive(Clone, Copy, kani::Arbitrary)]
    struct AlignedWord(u8);

    // Diagnostic specialization: this proves only size == 1. Keep the arbitrary-size
    // contract harness below; a success here does not discharge its nonlinear arithmetic.
    #[kani::proof_for_contract(Chunks::kani_get_unchecked)]
    fn check_chunks_single_element_contract() {
        let storage = SymbolicSlice::<u8>::any();
        let mut iter = Chunks::new(storage.as_slice(), 1);
        let count = iter.len();
        let index: usize = kani::any();
        // SAFETY: proof_for_contract supplies the local precondition. Fresh state and
        // only permitted observations satisfy the separate temporal caller obligations.
        let mut result = unsafe { iter.kani_get_unchecked(index) };
        touch_shared(&mut result);
        kani::cover(index == 0, "first single-element chunk");
        kani::cover(index == count - 1, "last single-element chunk");
    }

    #[kani::proof_for_contract(Chunks::kani_get_unchecked)]
    fn check_chunks_zst_extreme_contract() {
        let storage = SymbolicSlice::<()>::any();
        let size = kani::any_where(|n: &usize| *n > 0);
        let mut iter = Chunks::new(storage.as_slice(), size);
        let len = iter.v.len();
        let index: usize = kani::any();
        // SAFETY: fresh state, the local precondition supplied by proof_for_contract,
        // and only permitted metadata observations after the unchecked access.
        let mut result = unsafe { iter.kani_get_unchecked(index) };
        touch_shared(&mut result);
        kani::cover(len == usize::MAX, "maximal ZST length");
        kani::cover(index > 0, "nonzero unchecked index");
        // ZST pointer addition has zero byte displacement, even for huge element indices.
        kani::cover(
            index.wrapping_mul(size) > isize::MAX as usize,
            "ZST element offset above isize::MAX",
        );
    }

    // Getter inputs deliberately overapproximate constructor states: every safe split
    // is admitted, including partitions whose main length is not a multiple of size.
    // Every original constructor partition is included (the arithmetic proofs below
    // establish its bounds). The getter's complete selected-range precondition suffices
    // even on these additional states. No constructor invariant is assumed away.
    //
    // Safe splitting preserves the allocation and mutable-region disjointness. Actual
    // constructors remain checked by gen_exact_constructor, and getter bodies execute
    // without stubs. This is a local getter proof, not a proof that the extra states
    // satisfy every other iterator method's invariants.
    fn any_exact_partition(len: usize) -> usize {
        kani::any_where(|split: &usize| *split <= len)
    }

    macro_rules! contract_iterator {
        (ChunksExact, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let main_len = any_exact_partition(slice.len());
            let (v, rem) = slice.split_at(main_len);
            ChunksExact { v, rem, chunk_size: size }
        }};
        (ChunksExactMut, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let main_len = any_exact_partition(slice.len());
            let (v, rem) = slice.split_at_mut(main_len);
            ChunksExactMut { v, rem, chunk_size: size, _marker: PhantomData }
        }};
        (RChunksExact, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let rem_len = any_exact_partition(slice.len());
            let (rem, v) = slice.split_at(rem_len);
            RChunksExact { v, rem, chunk_size: size }
        }};
        (RChunksExactMut, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let size = $size;
            let rem_len = any_exact_partition(slice.len());
            let (rem, v) = slice.split_at_mut(rem_len);
            RChunksExactMut { v, rem, chunk_size: size }
        }};
        ($iterator:ident, $slice:expr, $size:expr) => {
            $iterator::new($slice, $size)
        };
    }

    // The unchecked call does not consume an item. Protocol tests must never use next/nth
    // afterward; those operations would violate the trait's caller obligations.
    macro_rules! gen_chunk_contract {
        ($iterator:ident, $ty:ty, $view:ident, $pointer:ident, $reverse:expr, $exact:expr, $touch:ident) => {
            #[kani::proof_for_contract($iterator::kani_get_unchecked)]
            #[kani::stub_verified(exact_chunk_end_arithmetic)]
            #[kani::stub_verified(offset_isize_arithmetic)]
            fn check_get_unchecked_contract() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let input_len = slice.len();
                let size = kani::any_where(|n: &usize| *n > 0);
                let mut iter = contract_iterator!($iterator, slice, size);
                let index: usize = kani::any();
                // proof_for_contract checks the original body and all declared postconditions,
                // including the exact result pointer/length and unchanged iterator metadata.
                // Keep independent chunk-count/range oracles in the safe-step and protocol
                // harnesses below, rather than proving them again inside every contract proof.
                // A fresh iterator has no earlier accesses; only permitted observations follow.
                let mut result = unsafe { iter.kani_get_unchecked(index) };
                $touch(&mut result);
                kani::cover(index == 0, "first unchecked item");
                // Equivalent last-item tests, without reintroducing a division oracle.
                let remaining = if $exact {
                    iter.v.len().wrapping_sub(index.wrapping_mul(size))
                } else {
                    iter.v.len() - index.wrapping_mul(size)
                };
                if $exact {
                    kani::cover(remaining == size, "last unchecked item");
                    kani::cover(index > 0, "nonzero unchecked index");
                    kani::cover(input_len == iter.v.len(), "empty preserved remainder");
                    kani::cover(input_len > iter.v.len(), "nonempty preserved remainder");
                } else {
                    kani::cover(remaining <= size, "last unchecked item");
                    kani::cover(result.len() < size, "partial chunk");
                }
            }

            #[kani::proof]
            fn check_unchecked_protocol() {
                fn shorten<'long: 'short, 'short, T>(
                    iter: $iterator<'long, T>,
                ) -> $iterator<'short, T> {
                    iter
                }
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let size = kani::any_where(|n: &usize| *n > 0);
                let mut iter = $iterator::new(slice, size);
                let len = iter.v.len();
                let base = iter.v.$pointer() as *const $ty;
                let count = chunk_count(len, size, $exact);
                let first = kani::any_where(|n: &usize| *n < count);
                let second = kani::any_where(|n: &usize| *n < count && *n != first);
                // SAFETY: fresh state, in-bounds and distinct indices, and only methods
                // allowed by TrustedRandomAccess are used after the first unchecked call.
                let mut a = unsafe { iter.__iterator_get_unchecked(first) };
                let mut iter = shorten(iter);
                let mut b = unsafe { iter.__iterator_get_unchecked(second) };
                let (a_start, a_len) = chunk_range(len, size, first, $reverse);
                let (b_start, b_len) = chunk_range(len, size, second, $reverse);
                assert!(a_start + a_len <= b_start || b_start + b_len <= a_start);
                check_slice(&a, base, a_start, a_len);
                check_slice(&b, base, b_start, b_len);
                check_exact_hint(&iter, count);
                let budget = count - 1 - first.max(second);
                if budget > 0 && kani::any() {
                    let mut back = iter.next_back().unwrap();
                    let (start, len) = chunk_range(len, size, count - 1, $reverse);
                    check_slice(&back, base, start, len);
                    $touch(&mut back);
                    check_exact_hint(&iter, count - 1);
                    kani::cover(true, "permitted next_back with unchecked results alive");
                }
                // These uses keep both returned references live across the back access.
                $touch(&mut a);
                $touch(&mut b);
                drop(iter);
                $touch(&mut a);
                $touch(&mut b);
                kani::cover(first < second, "increasing unchecked indices");
                kani::cover(first > second, "decreasing unchecked indices");
            }
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

    // Expand these observations at each call site so pre-state and post-state
    // arithmetic are separate proof properties. Evaluate each argument once.
    macro_rules! check_exact_hint_at_callsite {
        ($iter:expr, $count:expr, $site:literal) => {{
            let iter = $iter;
            let count = $count;
            kani::assert(
                iter.size_hint() == (count, Some(count)),
                concat!($site, ": exact size_hint"),
            );
            kani::assert(iter.len() == count, concat!($site, ": exact len"));
            kani::assert(
                TrustedRandomAccessNoCoerce::size(iter) == count,
                concat!($site, ": exact trusted size"),
            );
        }};
    }

    // A single forward/backward exact step reduces the quotient by one.
    // Backward range oracles additionally need the last full chunk index bounds.
    macro_rules! prepare_exact_next_count {
        (next, $exact:expr, $len:expr, $size:expr) => {
            if $exact && $len >= $size {
                exact_next_count_arithmetic($len, $size);
            }
        };
        (next_back, $exact:expr, $len:expr, $size:expr) => {
            if $exact && $len >= $size {
                exact_next_count_arithmetic($len, $size);
                exact_last_chunk_start_arithmetic($len, $size);
            }
        };
        ($other:ident, $exact:expr, $len:expr, $size:expr) => {};
    }

    // Execute the real constructor after supplying only its proved scalar facts.
    // Exact nth and backward steps reuse constructor partition facts.
    macro_rules! prepare_exact_backward_partition {
        (next_back, $exact:expr, $len:expr, $size:expr) => {
            if $exact {
                exact_partition_arithmetic($len, $size);
            }
        };
        (nth, $exact:expr, $len:expr, $size:expr) => {
            if $exact {
                exact_partition_arithmetic($len, $size);
            }
        };
        (nth_back, $exact:expr, $len:expr, $size:expr) => {
            if $exact {
                exact_partition_arithmetic($len, $size);
            }
        };
        ($other:ident, $exact:expr, $len:expr, $size:expr) => {};
    }

    // This representation-level cut applies only to the suite's initialized,
    // unrestricted single-byte elements. Other element layouts remain unchanged.
    macro_rules! prepare_exact_backward_byte_offsets {
        (next_back, $exact:expr, $ty:ty, $base:expr, $len:expr, $size:expr) => {
            if $exact
                && const { mem::size_of::<$ty>() == 1 && element_validity_kind::<$ty>() == 0 }
                && $len >= $size
            {
                let len = $len;
                let size = $size;
                let base = $base;
                let logical_start = (len / size).wrapping_sub(1).wrapping_mul(size);
                let physical_start = len.wrapping_sub(size);
                // SAFETY: the fresh iterator has yielded no references. Its main
                // region is live and initialized, each element is one byte, and
                // the remainder is disjoint. This shared borrow ends in this block,
                // before the real method creates any mutable element references.
                let bytes = unsafe { from_raw_parts(base.cast::<u8>(), len) };
                equal_byte_offsets(bytes, logical_start, physical_start);
            }
        };
        ($other:ident, $exact:expr, $ty:ty, $base:expr, $len:expr, $size:expr) => {};
    }

    // Expose the proved scalar identity as a separate obligation before the
    // pointer comparison. The original range oracle and pointer assertion remain.
    macro_rules! check_exact_backward_offset {
        (next_back, $exact:expr, $reverse:expr, $start:expr, $len:expr, $size:expr) => {
            if $exact && !$reverse {
                kani::assert(
                    $start == $len - $size,
                    "last exact chunk oracle equals the subtraction offset",
                );
            }
        };
        ($other:ident, $exact:expr, $reverse:expr, $start:expr, $len:expr, $size:expr) => {};
    }

    // Keep exact oracle observations at the call site while
    // preserving the same four predicates and evaluating each argument once.
    macro_rules! check_chunk_step_slice {
        (nth_back, $exact:expr, $slice:expr, $base:expr, $start:expr, $len:expr) => {
            check_chunk_step_slice!(next_back, $exact, $slice, $base, $start, $len);
        };
        (nth, $exact:expr, $slice:expr, $base:expr, $start:expr, $len:expr) => {
            check_chunk_step_slice!(next_back, $exact, $slice, $base, $start, $len);
        };
        (next_back, $exact:expr, $slice:expr, $base:expr, $start:expr, $len:expr) => {{
            if $exact {
                let slice: &[_] = $slice;
                let base = $base;
                let start = $start;
                let len = $len;
                kani::assert(slice.len() == len, "slice length matches the expected length");
                kani::assert(
                    slice.as_ptr() == base.wrapping_add(start),
                    "slice pointer matches the expected start",
                );
                if let Some(first) = slice.first() {
                    kani::assert(
                        crate::ub_checks::can_dereference(first),
                        "first slice element is readable",
                    );
                }
                if let Some(last) = slice.last() {
                    kani::assert(
                        crate::ub_checks::can_dereference(last),
                        "last slice element is readable",
                    );
                }
            } else {
                check_slice($slice, $base, $start, $len);
            }
        }};
        ($other:ident, $exact:expr, $slice:expr, $base:expr, $start:expr, $len:expr) => {
            check_slice($slice, $base, $start, $len);
        };
    }

    // Materialize the scalar oracle facts before checking iterator metadata.
    // Every cut is an assertion; the original observations are retained.
    macro_rules! check_exact_nth_chunk_length {
        (nth_back, $exact:expr, $chunk_len:expr, $size:expr) => {
            if $exact {
                kani::assert($chunk_len == $size, "exact nth_back oracle returns a complete chunk");
            }
        };
        (nth, $exact:expr, $chunk_len:expr, $size:expr) => {
            if $exact {
                kani::assert($chunk_len == $size, "exact nth oracle returns a complete chunk");
            }
        };
        ($other:ident, $exact:expr, $chunk_len:expr, $size:expr) => {};
    }

    // Make the checked scalar length equality available before the pointer
    // observation. The contract's premises are still separate proof obligations.
    macro_rules! prepare_exact_nth_back_output_count {
        (nth_back, $exact:expr, $reverse:expr, $start:expr, $count:expr, $index:expr, $size:expr, $actual:expr) => {
            if $exact {
                let logical = $count - 1 - $index;
                let oracle = if $reverse { logical.wrapping_mul($size) } else { $start };
                exact_count_transfer_arithmetic($actual, oracle, $size, $count - $index - 1);
            }
        };
        ($other:ident, $exact:expr, $reverse:expr, $start:expr, $count:expr, $index:expr, $size:expr, $actual:expr) => {};
    }

    macro_rules! check_exact_nth_remaining_count {
        (nth_back, $exact:expr, $len:expr, $size:expr, $index:expr, $remaining:expr, $count:expr, $actual:expr) => {
            if $exact {
                let logical = $count - 1 - $index;
                let canonical = logical.wrapping_mul($size);
                kani::assert(
                    $remaining == canonical,
                    "exact nth_back remaining oracle equals the full-chunk offset",
                );
                kani::assert(
                    $remaining / $size == $count - $index - 1,
                    "exact nth_back remaining oracle has the expected quotient",
                );
            }
        };
        (nth, $exact:expr, $len:expr, $size:expr, $index:expr, $remaining:expr, $count:expr, $actual:expr) => {
            if $exact {
                let consumed = $index.wrapping_mul($size).wrapping_add($size);
                kani::assert(
                    $remaining == $len.wrapping_sub(consumed),
                    "exact nth remaining oracle equals total minus consumed",
                );
                kani::assert(
                    $remaining / $size == $count - $index - 1,
                    "exact nth remaining oracle has the expected quotient",
                );
                exact_count_transfer_arithmetic(
                    $actual,
                    $len.wrapping_sub(consumed),
                    $size,
                    $count - $index - 1,
                );
            }
        };
        ($other:ident, $exact:expr, $len:expr, $size:expr, $index:expr, $remaining:expr, $count:expr, $actual:expr) => {};
    }

    // This lemma classifies every index, including overflowing multiplication.
    // Other methods keep their existing preparation and observations.
    macro_rules! prepare_exact_nth_step {
        (nth_back, $exact:expr, $len:expr, $size:expr, $index:expr) => {
            if $exact && $index < $len / $size {
                let logical = $len / $size - 1 - $index;
                exact_native_index_arithmetic($len, $size, logical);
                native_range_end_arithmetic($len, logical.wrapping_mul($size), $size);
                exact_multiple_arithmetic($size, logical);
            }
        };
        (nth, $exact:expr, $len:expr, $size:expr, $index:expr) => {
            if $exact {
                exact_nth_step_arithmetic($len, $size, $index);
            }
        };
        ($other:ident, $exact:expr, $len:expr, $size:expr, $index:expr) => {};
    }

    // Supply only independently proved spatial facts for the fresh, initialized
    // one-byte main region. The temporary shared view ends before nth yields
    // mutable references; the original method and all its checks still execute.
    macro_rules! prepare_reverse_exact_nth_readable {
        (nth, $exact:expr, $reverse:expr, $ty:ty, $base:expr, $len:expr, $size:expr, $index:expr) => {
            if $exact
                && $reverse
                && const { mem::size_of::<$ty>() == 1 && element_validity_kind::<$ty>() == 0 }
                && $index < $len / $size
            {
                let offset = $index.wrapping_mul($size);
                kani::assert(
                    $index.checked_mul($size).is_some(),
                    "reverse nth index multiplication succeeds",
                );
                let end = offset.wrapping_add($size);
                kani::assert(
                    offset.checked_add($size).is_some(),
                    "reverse nth chunk end does not overflow",
                );
                kani::assert(end <= $len, "reverse nth chunk end is in bounds");
                kani::assert(offset < end, "positive chunk size advances the offset");
                kani::assert(
                    $len.wrapping_sub(offset) >= $size,
                    "reverse nth retained prefix contains a complete chunk",
                );
                let canonical = $len.wrapping_sub(end);
                let physical = $len.wrapping_sub(offset).wrapping_sub($size);
                kani::assert(physical == canonical, "reverse nth subtraction offsets agree");
                kani::assert(physical < $len, "reverse nth readable byte is in bounds");
                let region = ptr::slice_from_raw_parts(($base).cast::<u8>(), $len);
                kani::assert(
                    crate::ub_checks::can_dereference(region),
                    "fresh reverse nth main byte region is readable",
                );
                // SAFETY: this fresh iterator owns its live, initialized main region;
                // the checked region is readable and separated from rem. No output
                // is borrowed yet, and this shared view ends before the target call.
                let bytes = unsafe { from_raw_parts(($base).cast::<u8>(), $len) };
                equal_byte_offsets(bytes, canonical, physical);
                readable_byte_at(bytes, physical);
                kani::assert(
                    !bytes.as_ptr().wrapping_add(physical).is_null(),
                    "predicted reverse nth chunk starts at a non-null byte",
                );
                let last_in_chunk = $size.wrapping_sub(1);
                kani::assert(
                    physical.checked_add(last_in_chunk).is_some(),
                    "reverse nth last byte offset does not overflow",
                );
                let last = physical.wrapping_add(last_in_chunk);
                kani::assert(last < $len, "reverse nth last byte is in bounds");
                compose_byte_offsets(bytes, physical, last_in_chunk);
                readable_byte_at(bytes, last);
            }
        };
        ($other:ident, $exact:expr, $reverse:expr, $ty:ty, $base:expr, $len:expr, $size:expr, $index:expr) => {};
    }

    // Establish the reverse nth state and terminal address before asking the
    // memory model about the returned chunk. These are checked cuts only; the
    // original slice observations and post-state checks still run below.
    macro_rules! prepare_reverse_exact_nth_output {
        (nth, $exact:expr, $reverse:expr, $ty:ty, $chunk:expr, $base:expr,
         $len:expr, $size:expr, $index:expr, $start:expr, $count:expr, $actual:expr) => {
            if $exact && $reverse {
                check_exact_nth_remaining_count!(
                    nth, true, $len, $size, $index, $start, $count, $actual
                );
                if const { mem::size_of::<$ty>() == 1 && element_validity_kind::<$ty>() == 0 } {
                    let physical =
                        $len.wrapping_sub($index.wrapping_mul($size)).wrapping_sub($size);
                    kani::assert(
                        $start == physical,
                        "reverse nth oracle start equals the physical offset",
                    );
                    kani::assert(
                        ($chunk).len() == $size,
                        "reverse nth returned length equals the chunk size",
                    );
                    kani::assert(
                        ($chunk).as_ptr() == ($base).wrapping_add(physical),
                        "reverse nth returned pointer equals the prepared chunk start",
                    );
                    let last = physical.wrapping_add($size.wrapping_sub(1));
                    kani::assert(
                        ($chunk).as_ptr().wrapping_add(($chunk).len().wrapping_sub(1))
                            == ($base).wrapping_add(last),
                        "reverse nth terminal address equals the prepared readable byte",
                    );
                }
            }
        };
        ($other:ident, $exact:expr, $reverse:expr, $ty:ty, $chunk:expr, $base:expr,
         $len:expr, $size:expr, $index:expr, $start:expr, $count:expr, $actual:expr) => {};
    }

    // Observe the same last reference in the address cut and the memory
    // predicate. Other specializations use the original observation macro.
    macro_rules! check_chunk_step_slice_at_output {
        (nth, $exact:expr, $reverse:expr, $ty:ty, $slice:expr, $base:expr, $start:expr, $len:expr) => {{
            if $exact
                && $reverse
                && const { mem::size_of::<$ty>() == 1 && element_validity_kind::<$ty>() == 0 }
            {
                let slice: &[$ty] = $slice;
                let base = $base;
                let start = $start;
                let len = $len;
                kani::assert(slice.len() == len, "slice length matches the expected length");
                kani::assert(
                    slice.as_ptr() == base.wrapping_add(start),
                    "slice pointer matches the expected start",
                );
                if let Some(first) = slice.first() {
                    kani::assert(
                        crate::ub_checks::can_dereference(first),
                        "first slice element is readable",
                    );
                }
                if let Some(last) = slice.last() {
                    let last_index = start.wrapping_add(len.wrapping_sub(1));
                    kani::assert(
                        ptr::from_ref(last) == base.wrapping_add(last_index),
                        "reverse nth checked last reference uses the prepared readable byte",
                    );
                    kani::assert(
                        crate::ub_checks::can_dereference(last),
                        "last slice element is readable",
                    );
                }
            } else {
                check_chunk_step_slice!(nth, $exact, $slice, $base, $start, $len);
            }
        }};
        ($other:ident, $exact:expr, $reverse:expr, $ty:ty, $slice:expr, $base:expr, $start:expr, $len:expr) => {
            check_chunk_step_slice!($other, $exact, $slice, $base, $start, $len);
        };
    }

    // Check both directions under explicit guards before the original
    // equivalence assertion. Neither branch restricts the harness inputs.
    macro_rules! check_reverse_exact_nth_presence {
        (nth, $exact:expr, $reverse:expr, $result:expr, $index:expr, $count:expr) => {
            if $exact && $reverse {
                let present = $result.is_some();
                if $index < $count {
                    kani::assert(present, "reverse exact nth returns Some for an in-bounds index");
                } else {
                    kani::assert(
                        !present,
                        "reverse exact nth returns None for an out-of-bounds index",
                    );
                }
            }
        };
        ($other:ident, $exact:expr, $reverse:expr, $result:expr, $index:expr, $count:expr) => {};
    }

    macro_rules! gen_chunk_step {
        ($name:ident, $ty:ty, $iterator:ident, $method:ident, $view:ident, $pointer:ident,
         $reverse:expr, $exact:expr, $back:expr, $touch:ident) => {
            #[kani::proof]
            #[kani::stub_verified(exact_next_count_arithmetic)]
            #[kani::stub_verified(exact_partition_arithmetic)]
            #[kani::stub_verified(exact_last_chunk_start_arithmetic)]
            #[kani::stub_verified(equal_byte_offsets)]
            #[kani::stub_verified(exact_nth_step_arithmetic)]
            #[kani::stub_verified(exact_count_transfer_arithmetic)]
            #[kani::stub_verified(exact_native_index_arithmetic)]
            #[kani::stub_verified(native_range_end_arithmetic)]
            #[kani::stub_verified(exact_multiple_arithmetic)]
            #[kani::stub_verified(readable_byte_at)]
            #[kani::stub_verified(compose_byte_offsets)]
            fn $name() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let size = kani::any_where(|n: &usize| *n > 0);
                prepare_exact_backward_partition!($method, $exact, slice.len(), size);
                let mut iter = $iterator::new(slice, size);
                let len = iter.v.len();
                let base = iter.v.$pointer() as *const $ty;
                let count = chunk_count(len, size, $exact);
                check_exact_hint_at_callsite!(&iter, count, "before step");
                let n: usize = kani::any();
                let index = step_index!($method, n);
                prepare_exact_nth_step!($method, $exact, len, size, index);
                prepare_reverse_exact_nth_readable!(
                    $method, $exact, $reverse, $ty, base, len, size, index
                );
                prepare_exact_next_count!($method, $exact, len, size);
                prepare_exact_backward_byte_offsets!($method, $exact, $ty, base, len, size);
                let mut result = call_chunk_step!($method, iter, n);
                check_reverse_exact_nth_presence!($method, $exact, $reverse, result, index, count);
                kani::assert(
                    result.is_some() == (index < count),
                    "chunk returned iff requested index is in bounds",
                );
                if let Some(ref mut chunk) = result {
                    let logical = if $back { count - 1 - index } else { index };
                    let (start, chunk_len) = chunk_range(len, size, logical, $reverse);
                    check_exact_nth_chunk_length!($method, $exact, chunk_len, size);
                    check_exact_backward_offset!($method, $exact, $reverse, start, len, size);
                    prepare_exact_nth_back_output_count!(
                        $method,
                        $exact,
                        $reverse,
                        start,
                        count,
                        index,
                        size,
                        iter.v.len()
                    );
                    prepare_reverse_exact_nth_output!(
                        $method,
                        $exact,
                        $reverse,
                        $ty,
                        chunk,
                        base,
                        len,
                        size,
                        index,
                        start,
                        count,
                        iter.v.len()
                    );
                    check_chunk_step_slice_at_output!(
                        $method, $exact, $reverse, $ty, &chunk, base, start, chunk_len
                    );
                    let (remaining_start, remaining_len) = if $reverse == $back {
                        (start + chunk_len, len - start - chunk_len)
                    } else {
                        (0, start)
                    };
                    check_exact_nth_remaining_count!(
                        $method,
                        $exact,
                        len,
                        size,
                        index,
                        remaining_len,
                        count,
                        iter.v.len()
                    );
                    kani::assert(
                        iter.v.len() == remaining_len,
                        "remaining slice has expected length",
                    );
                    kani::assert(
                        (iter.v.$pointer() as *const $ty) == base.wrapping_add(remaining_start),
                        "remaining slice starts at expected element",
                    );
                    check_exact_hint_at_callsite!(&iter, count - index - 1, "after Some");
                    $touch(chunk);
                } else {
                    // next/next_back may leave an already empty iterator unchanged.
                    kani::assert(iter.v.len() == 0, "exhausted iterator has no remaining elements");
                    check_exact_hint_at_callsite!(&iter, 0, "after None");
                }
                kani::cover(result.is_some(), "chunk returned");
                kani::cover(result.is_none(), "iterator exhausted");
                kani::cover(size > len, "chunk size larger than remaining slice");
                cover_step_overflow!($method, n, size);
            }
        };
    }

    // These three cases partition every input of nth_back. The original unsplit
    // harness remains available; only the case harnesses assume a case condition.
    macro_rules! assume_chunks_mut_nth_back_case {
        (empty, $iter:ident, $len:ident, $n:ident) => {
            kani::assume($len == 0);
        };
        (exhausted, $iter:ident, $len:ident, $n:ident) => {
            kani::assume($len > 0);
            kani::assume($n >= $iter.len());
        };
        (present, $iter:ident, $len:ident, $n:ident) => {
            kani::assume($len > 0);
            kani::assume($n < $iter.len());
        };
        (present_with_bounds, $iter:ident, $len:ident, $n:ident) => {
            assume_chunks_mut_nth_back_case!(present, $iter, $len, $n);
            nth_back_chunk_start_arithmetic($len, $iter.chunk_size, $n);
        };
        (present_with_regions, $iter:ident, $len:ident, $n:ident) => {
            assume_chunks_mut_nth_back_case!(present, $iter, $len, $n);
            let size = $iter.chunk_size;
            let count = $iter.len();
            // Reuse this exact count in the start contract and its postcondition.
            let start = nth_back_div_ceil_start_arithmetic($len, size, count, $n);
            // Discharge the arithmetic connection before adding spatial predicates.
            // These are checked proof obligations, not input assumptions.
            let checked_start = (count - 1 - $n) * size;
            kani::assert(checked_start == start, "implementation start equals proved start");
            clipped_chunk_end_arithmetic($len, start, size);
            // Match the actual nth_back endpoint and length in the spatial fact.
            let end = match start.checked_add(size) {
                Some(sum) => cmp::min($len, sum),
                None => $len,
            };
            let checked_end = match checked_start.checked_add(size) {
                Some(sum) => cmp::min($len, sum),
                None => $len,
            };
            kani::assert(checked_end == end, "implementation end equals proved end");
            // Retain the original checked subtraction at the caller as well.
            let _checked_length = end - start;
            // Caller bounds and whole-input validity remain proof obligations.
            // Only the already proved u8 spatial contracts are reused here.
            writable_interval($iter.v.as_mut_ptr(), $len, start, end);
            writable_prefix($iter.v.as_mut_ptr(), $len, start);
            kani::assert(
                $iter.v.len() == $len && $iter.chunk_size == size,
                "region lemmas preserve iterator metadata",
            );
            kani::assert($iter.len() == count, "region lemmas preserve iterator count");
        };
    }

    macro_rules! cover_chunks_mut_memory_step {
        ($method:ident, $result:ident, $len:ident, $size:ident, $n:ident) => {
            kani::cover($result.is_some(), "chunk returned");
            kani::cover($result.is_none(), "iterator exhausted");
            kani::cover($size > $len, "chunk size larger than the input slice");
            cover_step_overflow!($method, $n, $size);
        };
        ($method:ident, $result:ident, $len:ident, $size:ident, $n:ident, empty) => {
            kani::assert($result.is_none(), "empty input returns None");
            kani::cover($result.is_none(), "empty input case is reachable");
        };
        ($method:ident, $result:ident, $len:ident, $size:ident, $n:ident, exhausted) => {
            kani::assert($result.is_none(), "out-of-range index returns None");
            kani::cover($result.is_none(), "exhausted index case is reachable");
            kani::cover($size > $len, "oversized chunk with out-of-range index");
            cover_step_overflow!($method, $n, $size);
        };
        ($method:ident, $result:ident, $len:ident, $size:ident, $n:ident, present_with_regions) => {
            cover_chunks_mut_memory_step!($method, $result, $len, $size, $n, present);
        };
        ($method:ident, $result:ident, $len:ident, $size:ident, $n:ident, present_with_bounds) => {
            cover_chunks_mut_memory_step!($method, $result, $len, $size, $n, present);
        };
        ($method:ident, $result:ident, $len:ident, $size:ident, $n:ident, present) => {
            kani::assert($result.is_some(), "in-range index returns a chunk");
            kani::cover($n == 0, "last chunk selected");
            kani::cover($n > 0, "earlier chunk selected");
            kani::cover($size > $len, "oversized chunk still yields the input slice");
        };
    }

    #[kani::proof]
    fn check_chunks_mut_nth_back_case_partition() {
        let len: usize = kani::any();
        // The partition is exhaustive for every count, including the actual len().
        // No quotient formula or slice-length bound is needed for this Boolean fact.
        let count: usize = kani::any();
        let n: usize = kani::any();
        let empty = len == 0;
        let exhausted = len > 0 && n >= count;
        let present = len > 0 && n < count;
        kani::assert(empty || exhausted || present, "nth_back cases cover every input");
        kani::assert(
            !(empty && exhausted) && !(empty && present) && !(exhausted && present),
            "nth_back cases are disjoint",
        );
        kani::cover(empty, "empty case");
        kani::cover(exhausted, "exhausted case");
        kani::cover(present, "present case");
        kani::cover(len == usize::MAX && present, "partition includes maximal lengths");
    }

    // Keep the quotient-based functional checks in gen_chunk_step. These harnesses
    // check the actual memory operations and the two disjoint remaining/output regions
    // without calling size_hint before or after the target method.
    macro_rules! gen_chunks_mut_memory_step {
        (@with_nth_back_regions $name:ident) => {
            gen_chunks_mut_memory_step!(
                @body $name, u8, nth_back, true,
                [kani::stub_verified(nth_back_div_ceil_start_arithmetic),
                 kani::stub_verified(clipped_chunk_end_arithmetic),
                 kani::stub_verified(writable_interval::<u8>),
                 kani::stub_verified(writable_prefix::<u8>)], present_with_regions
            );
        };
        (@with_nth_back_bounds $name:ident) => {
            gen_chunks_mut_memory_step!(
                @body $name, u8, nth_back, true,
                [kani::stub_verified(nth_back_chunk_start_arithmetic)], present_with_bounds
            );
        };
        ($name:ident, $ty:ty, $method:ident, $back:expr $(, $case:ident)?) => {
            gen_chunks_mut_memory_step!(@body $name, $ty, $method, $back, [] $(, $case)?);
        };
        (@body $name:ident, $ty:ty, $method:ident, $back:expr,
         [$($attribute:meta),*] $(, $case:ident)?) => {
            #[kani::proof]
            $(#[$attribute])*
            fn $name() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice_mut(storage.as_mut_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let size = kani::any_where(|size: &usize| *size > 0);
                let n: usize = kani::any();
                let mut iter = ChunksMut::new(slice, size);
                $(assume_chunks_mut_nth_back_case!($case, iter, len, n);)?
                let mut result = call_chunk_step!($method, iter, n);
                let remaining = iter.v.len();
                kani::assert(remaining <= len, "remaining region stays within the original slice");
                if let Some(ref mut chunk) = result {
                    let chunk_len = chunk.len();
                    kani::assert(
                        chunk_len > 0 && chunk_len <= size,
                        "returned chunk has a valid length",
                    );
                    kani::assert(
                        chunk_len <= len - remaining,
                        "returned chunk and remaining region fit in the original slice",
                    );
                    let start = if $back { remaining } else { len - remaining - chunk_len };
                    check_slice(chunk, base, start, chunk_len);
                    let remaining_start = if $back { 0 } else { len - remaining };
                    kani::assert(
                        iter.v.as_mut_ptr() == base.wrapping_add(remaining_start) as *mut $ty,
                        "remaining region is disjoint from the returned chunk",
                    );
                    // The exact positions above describe disjoint subslices of the input.
                    // Check writes while the returned reference is still live as well.
                    kani::assert(
                        crate::ub_checks::can_dereference(iter.v)
                            && crate::ub_checks::can_write(iter.v),
                        "remaining region stays readable and writable",
                    );
                    touch_mut(chunk);
                } else {
                    kani::assert(remaining == 0, "None exhausts the remaining region");
                }
                cover_chunks_mut_memory_step!($method, result, len, size, n $(, $case)?);
            }
        };
    }

    // Keep the quotient-based functional harnesses alongside these access checks.
    // Every input length and positive chunk size remains symbolic. The original
    // iterator method executes, including its overflow and exhaustion branches.
    macro_rules! gen_chunk_memory_step {
        ($name:ident, $ty:ty, $iterator:ident, $method:ident, $view:ident,
         $pointer:ident, $reverse:expr, $back:expr, $mutable:expr, $touch:ident) => {
            #[kani::proof]
            fn $name() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let base = slice.as_ptr();
                let len = slice.len();
                let size = kani::any_where(|size: &usize| *size > 0);
                let n: usize = kani::any();
                let mut iter = $iterator::new(slice, size);
                let mut result = call_chunk_step!($method, iter, n);
                let remaining = iter.v.len();
                kani::assert(remaining <= len, "remaining region stays within the original slice");
                if let Some(ref mut chunk) = result {
                    let chunk_len = chunk.len();
                    kani::assert(
                        chunk_len > 0 && chunk_len <= size,
                        "returned chunk length is valid",
                    );
                    kani::assert(chunk_len <= len - remaining, "output and remaining regions fit");
                    let from_back = $reverse != $back;
                    let start = if from_back { remaining } else { len - remaining - chunk_len };
                    check_slice(chunk, base, start, chunk_len);
                    let remaining_start = if from_back { 0 } else { len - remaining };
                    let remaining_ptr = iter.v.$pointer() as *const $ty;
                    kani::assert(
                        remaining_ptr == base.wrapping_add(remaining_start),
                        "remaining region is disjoint from the returned chunk",
                    );
                    kani::assert(
                        crate::ub_checks::can_dereference(crate::ptr::slice_from_raw_parts(
                            remaining_ptr,
                            remaining,
                        )),
                        "remaining region stays readable",
                    );
                    if $mutable {
                        kani::assert(
                            crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(
                                remaining_ptr.cast_mut(),
                                remaining,
                            )),
                            "remaining region stays writable",
                        );
                    }
                    $touch(chunk);
                } else {
                    kani::assert(remaining == 0, "None exhausts the remaining region");
                }
                cover_chunks_mut_memory_step!($method, result, len, size, n);
            }
        };
    }

    gen_chunks_mut_memory_step!(@with_nth_back_bounds check_chunks_mut_nth_back_memory_present_with_bounds_byte);
    gen_chunks_mut_memory_step!(@with_nth_back_regions check_chunks_mut_nth_back_memory_present_with_regions_byte);

    // Reuse the independently proved arithmetic contract without replacing the
    // original method. Preparation is conditional; the target still receives all
    // inputs, including empty slices and out-of-range indices.
    #[kani::proof]
    #[kani::stub_verified(nth_back_div_ceil_start_arithmetic)]
    fn check_rchunks_mut_nth_back_memory_with_bounds_byte() {
        let mut storage = SymbolicSlice::<u8>::any();
        let slice = any_slice_mut(storage.as_mut_slice());
        let base = slice.as_ptr();
        let len = slice.len();
        let size = kani::any_where(|size: &usize| *size > 0);
        let n: usize = kani::any();
        let mut iter = RChunksMut::new(slice, size);
        let count = iter.len();
        if n < count {
            kani::assert(len > 0, "in-range reverse index requires a nonempty slice");
            let offset = nth_back_div_ceil_start_arithmetic(len, size, count, n);
            let checked_offset = (count - 1 - n) * size;
            kani::assert(
                checked_offset == offset,
                "reverse implementation offset matches proved offset",
            );
            let end = len - checked_offset;
            kani::assert(end > 0 && end <= len, "reverse split endpoint is in bounds");
            kani::assert(
                iter.v.len() == len && iter.chunk_size == size && iter.len() == count,
                "arithmetic preparation preserves the iterator metadata",
            );
        }
        let mut result = iter.nth_back(n);
        let remaining = iter.v.len();
        kani::assert(remaining <= len, "remaining region stays within the original slice");
        if let Some(ref mut chunk) = result {
            let chunk_len = chunk.len();
            kani::assert(chunk_len > 0 && chunk_len <= size, "returned chunk length is valid");
            kani::assert(chunk_len <= len - remaining, "output and remaining regions fit");
            let start = len - remaining - chunk_len;
            check_slice(chunk, base, start, chunk_len);
            kani::assert(
                iter.v.as_mut_ptr().cast_const() == base.wrapping_add(len - remaining),
                "remaining region is disjoint from the returned chunk",
            );
            kani::assert(
                crate::ub_checks::can_dereference(iter.v) && crate::ub_checks::can_write(iter.v),
                "remaining region stays readable and writable",
            );
            touch_mut(chunk);
        } else {
            kani::assert(remaining == 0, "None exhausts the remaining region");
        }
        cover_chunks_mut_memory_step!(nth_back, result, len, size, n);
    }

    // Diagnostic control: arbitrary valid slice and n, but a unit chunk size.
    // This does not replace the symbolic-size harness or establish all chunk sizes.
    #[kani::proof]
    fn check_chunks_mut_nth_back_unit_stride_byte() {
        let mut storage = SymbolicSlice::<u8>::any();
        let slice = any_slice_mut(storage.as_mut_slice());
        let base = slice.as_ptr();
        let len = slice.len();
        let n: usize = kani::any();
        let mut iter = ChunksMut::new(slice, 1);
        let mut result = iter.nth_back(n);
        kani::assert(result.is_some() == (n < len), "unit-stride nth_back presence");
        if let Some(ref mut chunk) = result {
            let start = len - 1 - n;
            check_slice(chunk, base, start, 1);
            kani::assert(iter.v.len() == start, "unit-stride remaining length");
            kani::assert(iter.v.as_mut_ptr() == base as *mut u8, "remaining pointer unchanged");
            kani::assert(
                crate::ub_checks::can_dereference(iter.v) && crate::ub_checks::can_write(iter.v),
                "unit-stride remaining region remains readable and writable",
            );
            touch_mut(chunk);
        } else {
            kani::assert(iter.v.len() == 0, "unit-stride None exhausts the iterator");
        }
        kani::cover(result.is_some(), "unit-stride chunk returned");
        kani::cover(result.is_none(), "unit-stride iterator exhausted");
        kani::cover(n > 0 && n < len, "unit-stride nonzero in-range index");
    }

    // A consumed/skipped chunk can separate the current main region from rem.
    // A safe split first separates their ownership; then an arbitrary main
    // subslice admits gaps on either side, as well as arbitrary valid empty views.
    macro_rules! exact_mut_memory_iterator {
        (ChunksExactMut, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let split = any_exact_partition(slice.len());
            let (main, rem) = slice.split_at_mut(split);
            let v = any_slice_mut(main);
            ChunksExactMut { v, rem, chunk_size: $size, _marker: PhantomData }
        }};
        (RChunksExactMut, $slice:expr, $size:expr) => {{
            let slice = $slice;
            let split = any_exact_partition(slice.len());
            let (rem, main) = slice.split_at_mut(split);
            let v = any_slice_mut(main);
            RChunksExactMut { v, rem, chunk_size: $size }
        }};
    }

    // Local access-safety checks admit every disjoint main/remainder partition,
    // including main lengths not divisible by size. This overapproximates the
    // states produced by the real constructors: no constructor state is excluded.
    // Constructor/divisibility and exact iterator semantics remain checked by
    // gen_exact_constructor and gen_chunk_step, rather than assumed here.
    macro_rules! gen_exact_mut_memory_step {
        ($name:ident, $ty:ty, $iterator:ident, $method:ident, $reverse:expr, $back:expr) => {
            #[kani::proof]
            fn $name() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice_mut(storage.as_mut_slice());
                let input_len = slice.len();
                let size = kani::any_where(|size: &usize| *size > 0);
                let mut iter = exact_mut_memory_iterator!($iterator, slice, size);
                let base = iter.v.as_mut_ptr().cast_const();
                let len = iter.v.len();
                let rem_ptr = iter.rem.as_ptr();
                let rem_len = iter.rem.len();
                let n: usize = kani::any();
                let mut result = call_chunk_step!($method, iter, n);
                let remaining = iter.v.len();
                kani::assert(
                    remaining <= len,
                    "exact remaining region stays within the main slice",
                );
                kani::assert(
                    iter.rem.as_ptr() == rem_ptr && iter.rem.len() == rem_len,
                    "exact iterator preserves remainder metadata",
                );
                kani::assert(
                    crate::ub_checks::can_dereference(iter.v)
                        && crate::ub_checks::can_write(iter.v),
                    "exact remaining region stays readable and writable",
                );
                if let Some(ref mut chunk) = result {
                    let chunk_len = chunk.len();
                    kani::assert(chunk_len == size, "exact iterator returns a full chunk");
                    kani::assert(
                        chunk_len <= len - remaining,
                        "exact output and remaining regions fit",
                    );
                    let from_back = $reverse != $back;
                    let start = if from_back { remaining } else { len - remaining - chunk_len };
                    check_slice(chunk, base, start, chunk_len);
                    let remaining_start = if from_back { 0 } else { len - remaining };
                    kani::assert(
                        iter.v.as_mut_ptr().cast_const() == base.wrapping_add(remaining_start),
                        "exact remaining region is disjoint from the returned chunk",
                    );
                    // The initial safe split separates rem from the whole main
                    // region. Keep the returned reference live across these writes.
                    touch_mut(&mut iter.rem);
                    touch_mut(chunk);
                } else {
                    // Extra admitted states can contain a short, unconsumed main
                    // prefix/suffix. This is not an assertion of iterator semantics.
                    kani::assert(remaining < size, "no full exact chunk remains");
                    touch_mut(&mut iter.rem);
                }
                kani::cover(result.is_some(), "exact chunk returned");
                kani::cover(result.is_none(), "no exact chunk returned");
                kani::cover(rem_len > 0, "nonempty disjoint remainder");
                kani::cover(
                    len > 0 && len < size,
                    "overapproximation includes a short main region",
                );
                kani::cover(
                    result.is_some() && rem_len > 0 && len < input_len - rem_len,
                    "chunk returned with a discarded gap and a nonempty remainder",
                );
                cover_step_overflow!($method, n, size);
            }
        };
    }

    macro_rules! gen_exact_mut_memory_methods {
        ($ty:ty, $iterator:ident, $reverse:expr) => {
            gen_exact_mut_memory_step!(
                check_next_memory_safety,
                $ty,
                $iterator,
                next,
                $reverse,
                false
            );
            gen_exact_mut_memory_step!(
                check_nth_memory_safety,
                $ty,
                $iterator,
                nth,
                $reverse,
                false
            );
            gen_exact_mut_memory_step!(
                check_next_back_memory_safety,
                $ty,
                $iterator,
                next_back,
                $reverse,
                true
            );
            gen_exact_mut_memory_step!(
                check_nth_back_memory_safety,
                $ty,
                $iterator,
                nth_back,
                $reverse,
                true
            );
        };
    }

    // Reuse only independently proved scalar bounds. Input generation, the real
    // nth_back body, output checks, remainder writes and all covers are unchanged
    // from gen_exact_mut_memory_step; no iterator or memory operation is stubbed.
    macro_rules! gen_exact_mut_nth_back_bounds {
        ($name:ident, $iterator:ident, $reverse:expr $(, $extra:meta)*) => {
            #[kani::proof]
            #[kani::stub_verified(exact_native_index_arithmetic)]
            #[kani::stub_verified(native_range_end_arithmetic)]
            #[kani::stub_verified(readable_byte_at)]
            $(#[$extra])*
            fn $name() {
                let mut storage = SymbolicSlice::<u8>::any();
                let slice = any_slice_mut(storage.as_mut_slice());
                let input_len = slice.len();
                let size = kani::any_where(|size: &usize| *size > 0);
                let mut iter = exact_mut_memory_iterator!($iterator, slice, size);
                let base = iter.v.as_mut_ptr().cast_const();
                let len = iter.v.len();
                let rem_ptr = iter.rem.as_ptr();
                let rem_len = iter.rem.len();
                let n: usize = kani::any();
                let count = len / size;
                if n < count {
                    if $reverse {
                        // The reverse body uses count - n, whose inclusive upper
                        // endpoint is not covered by the forward index lemma.
                        let selected = count - n;
                        reverse_exact_offset_arithmetic(len, size, selected);
                        let start = len.wrapping_sub(selected.wrapping_mul(size));
                        native_range_end_arithmetic(len, start, size);
                    } else {
                        let index = count - 1 - n;
                        exact_native_index_arithmetic(len, size, index);
                        native_range_end_arithmetic(len, index.wrapping_mul(size), size);
                    }
                }
                let mut result = call_chunk_step!(nth_back, iter, n);
                let remaining = iter.v.len();
                kani::assert(remaining <= len, "exact remaining region stays within the main slice");
                kani::assert(
                    iter.rem.as_ptr() == rem_ptr && iter.rem.len() == rem_len,
                    "exact iterator preserves remainder metadata",
                );
                kani::assert(
                    crate::ub_checks::can_dereference(iter.v) && crate::ub_checks::can_write(iter.v),
                    "exact remaining region stays readable and writable",
                );
                if let Some(ref mut chunk) = result {
                    let chunk_len = chunk.len();
                    kani::assert(chunk_len == size, "exact iterator returns a full chunk");
                    kani::assert(chunk_len <= len - remaining, "exact output and remaining regions fit");
                    let from_back = $reverse != true;
                    let start = if from_back { remaining } else { len - remaining - chunk_len };
                    if chunk_len > 0 {
                        // The real method's returned-reference checks remain enabled.
                        // These pure calls borrow the actual output only for the call;
                        // they neither access the iterator nor retain another reference.
                        readable_byte_at(chunk, 0);
                        readable_byte_at(chunk, chunk_len - 1);
                    }
                    check_slice(chunk, base, start, chunk_len);
                    let remaining_start = if from_back { 0 } else { len - remaining };
                    kani::assert(
                        iter.v.as_mut_ptr().cast_const() == base.wrapping_add(remaining_start),
                        "exact remaining region is disjoint from the returned chunk",
                    );
                    // The initial safe split separates rem from the whole main
                    // region. Keep the returned reference live across these writes.
                    touch_mut(&mut iter.rem);
                    touch_mut(chunk);
                } else {
                    // Extra admitted states can contain a short, unconsumed main
                    // prefix/suffix. This is not an assertion of iterator semantics.
                    kani::assert(remaining < size, "no full exact chunk remains");
                    touch_mut(&mut iter.rem);
                }
                kani::cover(result.is_some(), "exact chunk returned");
                kani::cover(result.is_none(), "no exact chunk returned");
                kani::cover(rem_len > 0, "nonempty disjoint remainder");
                kani::cover(len > 0 && len < size, "overapproximation includes a short main region");
                kani::cover(
                    result.is_some() && rem_len > 0 && len < input_len - rem_len,
                    "chunk returned with a discarded gap and a nonempty remainder",
                );
                cover_step_overflow!(nth_back, n, size);
            }
        };
    }

    gen_exact_mut_nth_back_bounds!(
        check_chunks_exact_mut_nth_back_memory_with_bounds_byte,
        ChunksExactMut,
        false
    );
    gen_exact_mut_nth_back_bounds!(
        check_rchunks_exact_mut_nth_back_memory_with_bounds_byte,
        RChunksExactMut,
        true,
        kani::stub_verified(reverse_exact_offset_arithmetic)
    );

    macro_rules! gen_exact_constructor_check {
        ($name:ident, $ty:ty, $iterator:ident, $view:ident, $pointer:ident, $reverse:expr, $arithmetic:expr) => {
            #[kani::proof]
            #[kani::stub_verified(exact_partition_arithmetic)]
            fn $name() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let base = slice.as_ptr();
                let len = slice.len();
                let size = kani::any_where(|n: &usize| *n > 0);
                // Only this pure arithmetic lemma is abstracted. The constructor and its
                // unsafe slice operations still execute; their pointers and lengths are checked.
                exact_partition_arithmetic(len, size);
                let iter = $iterator::new(slice, size);
                let remainder = len % size;
                let main_len = len - remainder;
                assert_eq!(iter.v.len(), main_len);
                let main_start = if $reverse { remainder } else { 0 };
                let rem_start = if $reverse { 0 } else { main_len };
                assert!((iter.v.$pointer() as *const $ty) == base.wrapping_add(main_start));
                check_slice(&iter.rem, base, rem_start, remainder);
                assert!(iter.rem.len() < size);
                if $arithmetic {
                    assert_eq!(iter.v.len() % size, 0);
                    check_exact_hint(&iter, len / size);
                }
                kani::cover(remainder == 0, "exact division");
                kani::cover(remainder > 0, "nonempty remainder");
                kani::cover(len == 0, "empty exact iterator");
                kani::cover(size > len, "whole input is remainder");
            }
        };
    }

    macro_rules! gen_exact_constructor {
        ($ty:ty, $iterator:ident, $view:ident, $pointer:ident, $reverse:expr) => {
            // Preserve the full semantic check as well as a separate proof of the actual
            // constructor's unsafe operations and returned partition. The latter does not
            // establish the extra divisibility/count identities exercised by check_new.
            gen_exact_constructor_check!(
                check_new, $ty, $iterator, $view, $pointer, $reverse, true
            );
            gen_exact_constructor_check!(
                check_new_partition,
                $ty,
                $iterator,
                $view,
                $pointer,
                $reverse,
                false
            );
        };
    }

    // Access-safety proof for the consuming last() method. Keep its independent
    // quotient-based functional oracle in gen_chunk_last as a separate obligation.
    macro_rules! gen_rchunks_mut_last_memory {
        ($ty:ty) => {
            #[kani::proof]
            fn check_last_memory_safety() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice_mut(storage.as_mut_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let size = kani::any_where(|size: &usize| *size > 0);
                let mut result = RChunksMut::new(slice, size).last();
                kani::assert(
                    result.is_some() == (len > 0),
                    "last returns a chunk iff input is nonempty",
                );
                if let Some(ref mut chunk) = result {
                    let chunk_len = chunk.len();
                    kani::assert(
                        chunk_len > 0 && chunk_len <= size && chunk_len <= len,
                        "last returns a nonempty prefix within the input and chunk size",
                    );
                    check_slice(chunk, base, 0, chunk_len);
                    kani::assert(
                        crate::ub_checks::can_dereference(&**chunk as *const [$ty])
                            && crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(
                                chunk.as_mut_ptr(),
                                chunk_len,
                            )),
                        "last chunk stays readable and writable",
                    );
                    touch_mut(chunk);
                    kani::cover(chunk_len < size, "partial leading chunk");
                }
                kani::cover(result.is_some(), "last chunk returned");
                kani::cover(result.is_none(), "last on empty input");
                kani::cover(size > len, "chunk size larger than input");
            }
        };
    }

    macro_rules! gen_chunk_last {
        ($ty:ty, $iterator:ident, $view:ident, $pointer:ident, $reverse:expr, $touch:ident) => {
            #[kani::proof]
            fn check_last() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let size = kani::any_where(|n: &usize| *n > 0);
                let iter = $iterator::new(slice, size);
                let len = iter.v.len();
                let base = iter.v.$pointer() as *const $ty;
                let count = chunk_count(len, size, false);
                let mut result = iter.last();
                assert_eq!(result.is_some(), count != 0);
                if let Some(ref mut chunk) = result {
                    let (start, chunk_len) = chunk_range(len, size, count - 1, $reverse);
                    check_slice(&chunk, base, start, chunk_len);
                    $touch(chunk);
                }
                kani::cover(result.is_some(), "last chunk returned");
                kani::cover(result.is_none(), "last on empty iterator");
            }
        };
    }

    macro_rules! gen_shared_clone_protocol {
        ($ty:ty, $iterator:ident, $reverse:expr, $exact:expr) => {
            #[kani::proof]
            fn check_clone_protocol() {
                let storage = SymbolicSlice::<$ty>::any();
                let size = kani::any_where(|n: &usize| *n > 0);
                let mut iter = $iterator::new(storage.as_slice(), size);
                let len = iter.v.len();
                let count = chunk_count(len, size, $exact);
                let index = kani::any_where(|n: &usize| *n < count);
                // SAFETY: shared Clone iterators permit repeated indices, but the back
                // budget and restricted method set still apply to each clone separately.
                let item = unsafe { iter.__iterator_get_unchecked(index) };
                let mut budget = count - index - 1;
                if budget > 0 && kani::any() {
                    let _ = iter.next_back();
                    budget -= 1;
                }
                let mut cloned = iter.clone();
                assert_eq!(cloned.size_hint(), iter.size_hint());
                // Calls before cloning count against both; calls after cloning are separate.
                if budget > 0 && kani::any() {
                    assert!(iter.next_back().is_some());
                    assert!(cloned.next_back().is_some());
                    kani::cover(true, "independent back step on both clones");
                }
                let again = unsafe { cloned.__iterator_get_unchecked(index) };
                assert_eq!(item.len(), again.len());
                assert!(item.as_ptr() == again.as_ptr());
                drop(iter);
                drop(cloned);
                check_slice(item, item.as_ptr(), 0, item.len());
                kani::cover(true, "shared result survives clone drop");
            }
        };
    }

    macro_rules! gen_iter_step {
        ($name:ident, $ty:ty, $iterator:ident, $view:ident, $method:ident, $back:expr) => {
            #[kani::proof]
            fn $name() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = $iterator::new(slice);
                let n: usize = kani::any();
                let index = step_index!($method, n);
                let result = call_chunk_step!($method, iter, n);
                assert_eq!(result.is_some(), index < len);
                if let Some(item) = result {
                    let offset = if $back { len - 1 - index } else { index };
                    assert!((item as *const $ty) == base.wrapping_add(offset));
                    let _value = *item;
                    assert_eq!(iter.len(), len - index - 1);
                    let remaining_start = if $back { 0 } else { index + 1 };
                    assert!(iter.ptr.as_ptr().cast_const() == base.wrapping_add(remaining_start));
                    kani::cover(true, "element returned");
                } else {
                    assert_eq!(iter.len(), 0);
                    kani::cover(true, "element absent");
                }
                assert!(iter.is_safe());
            }
        };
    }

    macro_rules! gen_iter_advance {
        ($name:ident, $ty:ty, $iterator:ident, $view:ident, $method:ident, $back:expr) => {
            #[kani::proof]
            fn $name() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
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
        };
    }

    macro_rules! gen_iter_family {
        ($ty:ty, $iterator:ident, $view:ident) => {
            #[kani::proof]
            fn check_new_and_queries() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
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

            gen_iter_step!(check_next, $ty, $iterator, $view, next, false);
            gen_iter_step!(check_nth, $ty, $iterator, $view, nth, false);
            gen_iter_step!(check_next_back, $ty, $iterator, $view, next_back, true);
            gen_iter_step!(check_nth_back, $ty, $iterator, $view, nth_back, true);
            gen_iter_advance!(check_advance_by, $ty, $iterator, $view, advance_by, false);
            gen_iter_advance!(check_advance_back_by, $ty, $iterator, $view, advance_back_by, true);

            #[kani::proof]
            fn check_last() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let base = slice.as_ptr();
                let len = slice.len();
                let result = $iterator::new(slice).last();
                assert_eq!(result.is_some(), len > 0);
                if let Some(item) = result {
                    assert!((item as *const $ty) == base.wrapping_add(len - 1));
                    let _value = *item;
                }
                kani::cover(len == 0, "last on empty iterator");
                kani::cover(len > 0, "last element returned");
            }

            #[kani::proof]
            fn check_fold() {
                let mut storage = SymbolicSlice::<$ty>::any();
                // Unit accumulator isolates access safety from arithmetic in the callback.
                $iterator::new(symbolic_view!(storage, $view)).fold((), |(), item| {
                    assert!(crate::ub_checks::can_dereference(item as *const $ty));
                    let _value = *item;
                    kani::cover(true, "fold callback reached");
                });
            }

            #[kani::proof]
            fn check_for_each() {
                let mut storage = SymbolicSlice::<$ty>::any();
                $iterator::new(symbolic_view!(storage, $view)).for_each(|item| {
                    assert!(crate::ub_checks::can_dereference(item as *const $ty));
                    let _value = *item;
                    kani::cover(true, "for_each callback reached");
                });
            }

            #[kani::proof]
            fn check_position() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = $iterator::new(slice);
                let result = iter.position(|item| {
                    let _value = *item;
                    kani::any::<bool>()
                });
                if let Some(index) = result {
                    assert!(index < len);
                    assert_eq!(iter.len(), len - index - 1);
                    assert!(iter.ptr.as_ptr().cast_const() == base.wrapping_add(index + 1));
                } else {
                    assert_eq!(iter.len(), 0);
                }
                assert!(iter.is_safe());
                kani::cover(result.is_some(), "position match");
                kani::cover(result.is_none() && len > 0, "position no match on nonempty input");
            }

            #[kani::proof]
            fn check_rposition() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let len = slice.len();
                let mut iter = $iterator::new(slice);
                let result = iter.rposition(|item| {
                    let _value = *item;
                    kani::any::<bool>()
                });
                if let Some(index) = result {
                    assert!(index < len);
                    assert_eq!(iter.len(), index);
                } else {
                    assert_eq!(iter.len(), 0);
                }
                assert!(iter.is_safe());
                kani::cover(result.is_some(), "rposition match");
                kani::cover(result.is_none() && len > 0, "rposition no match on nonempty input");
            }
        };
    }

    macro_rules! gen_iter_mut_views {
        ($ty:ty) => {
            #[kani::proof]
            fn check_fold_mutating() {
                let mut storage = SymbolicSlice::<$ty>::any();
                IterMut::new(any_slice_mut(storage.as_mut_slice())).fold((), |(), item| {
                    *item = kani::any();
                    kani::cover(true, "fold writes through returned mutable reference");
                });
            }

            #[kani::proof]
            fn check_for_each_mutating() {
                let mut storage = SymbolicSlice::<$ty>::any();
                IterMut::new(any_slice_mut(storage.as_mut_slice())).for_each(|item| {
                    *item = kani::any();
                    kani::cover(true, "for_each writes through returned mutable reference");
                });
            }

            // This also exercises writes through an external closure capture. Keep it
            // separate from the element-only callback above: loop frame inference must
            // account for the capture as well as the iterator's backing allocation.
            #[kani::proof]
            fn check_for_each_mutating_and_retaining() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut retained = None;
                IterMut::new(any_slice_mut(storage.as_mut_slice())).for_each(|item| {
                    if retained.is_none() {
                        retained = Some(item);
                    } else {
                        *item = kani::any();
                    }
                });
                if let Some(first) = retained {
                    *first = kani::any();
                    kani::cover(true, "first reference retained across later callbacks");
                }
            }

            #[kani::proof]
            fn check_into_slice() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice_mut(storage.as_mut_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = IterMut::new(slice);
                let front = kani::any_where(|n: &usize| *n <= len);
                let back = kani::any_where(|n: &usize| *n <= len - front);
                assert!(iter.advance_by(front).is_ok());
                assert!(iter.advance_back_by(back).is_ok());
                let mut remaining = iter.into_slice();
                check_slice(&remaining, base, front, len - front - back);
                touch_mut(&mut remaining);
                kani::cover(remaining.is_empty(), "empty remaining slice");
                kani::cover(!remaining.is_empty(), "nonempty remaining slice");
            }

            #[kani::proof]
            fn check_as_mut_slice() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice_mut(storage.as_mut_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = IterMut::new(slice);
                let n = kani::any_where(|n: &usize| *n <= len);
                kani::assert(iter.advance_by(n).is_ok(), "advance stays within the slice");
                {
                    let mut view = iter.as_mut_slice();
                    check_slice(&view, base, n, len - n);
                    touch_mut(&mut view);
                }
                kani::assert(iter.len() == len - n, "reborrow preserves the remaining length");
                kani::assert(iter.is_safe(), "iterator remains safe after the reborrow");
                kani::cover(iter.next().is_some(), "iterator reused after reborrow ends");
            }

            #[kani::proof]
            fn check_retained_mutable_elements() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice_mut(storage.as_mut_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                kani::assume(len >= 2);
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
        };
    }

    macro_rules! gen_windows {
        ($ty:ty) => {
            #[kani::proof_for_contract(Windows::kani_get_unchecked)]
            fn check_get_unchecked_contract() {
                let storage = SymbolicSlice::<$ty>::any();
                let size: NonZero<usize> = kani::any();
                let mut iter = Windows::new(any_slice(storage.as_slice()), size);
                let len = iter.v.len();
                let base = iter.v.as_ptr();
                let count = if len < size.get() { 0 } else { len - size.get() + 1 };
                check_exact_hint(&iter, count);
                let index: usize = kani::any();
                // SAFETY: target precondition is assumed by proof_for_contract; no history.
                let result = unsafe { iter.kani_get_unchecked(index) };
                check_slice(result, base, index, size.get());
                check_exact_hint(&iter, count);
                kani::cover(index == 0, "first window");
                kani::cover(index == count - 1, "last window");
            }

            #[kani::proof]
            fn check_clone_protocol() {
                fn shorten<'long: 'short, 'short, T>(
                    iter: Windows<'long, T>,
                ) -> Windows<'short, T> {
                    iter
                }
                let storage = SymbolicSlice::<$ty>::any();
                let size: NonZero<usize> = kani::any();
                let mut iter = Windows::new(any_slice(storage.as_slice()), size);
                let count = iter.len();
                let index = kani::any_where(|n: &usize| *n < count);
                // SAFETY: bounds hold; only the permitted methods follow.
                let first = unsafe { iter.__iterator_get_unchecked(index) };
                let mut budget = count - index - 1;
                if budget > 0 && kani::any() {
                    assert!(iter.next_back().is_some());
                    budget -= 1;
                }
                let mut cloned = shorten(iter.clone());
                if budget > 0 {
                    assert!(iter.next_back().is_some());
                    assert!(cloned.next_back().is_some());
                    kani::cover(true, "independent clone budgets");
                }
                let second = unsafe { cloned.__iterator_get_unchecked(index) };
                assert_eq!(first.len(), second.len());
                assert!(first.as_ptr() == second.as_ptr());
                drop(iter);
                drop(cloned);
                check_slice(first, first.as_ptr(), 0, size.get());
            }
        };
    }

    macro_rules! gen_array_windows_step {
        ($name:ident, $ty:ty, $n:expr, $method:ident, $back:expr) => {
            #[kani::proof]
            fn $name() {
                let storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice(storage.as_slice());
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
        };
    }

    macro_rules! gen_array_windows {
        ($ty:ty, $n:expr) => {
            #[kani::proof_for_contract(ArrayWindows::<$ty, $n>::kani_get_unchecked)]
            fn check_get_unchecked_contract() {
                let storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice(storage.as_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = ArrayWindows::<$ty, $n>::new(slice);
                let count = len.checked_sub($n).map_or(0, |n| n + 1);
                let index: usize = kani::any();
                let result = unsafe { iter.kani_get_unchecked(index) };
                check_slice(result, base, index, $n);
                check_exact_hint(&iter, count);
                kani::cover(index == 0, "first array window");
                kani::cover(index == count - 1, "last array window");
            }
            gen_array_windows_step!(check_next, $ty, $n, next, false);
            gen_array_windows_step!(check_nth, $ty, $n, nth, false);
            gen_array_windows_step!(check_next_back, $ty, $n, next_back, true);
            gen_array_windows_step!(check_nth_back, $ty, $n, nth_back, true);
        };
    }

    macro_rules! gen_split_step {
        ($name:ident, $ty:ty, $method:ident, $back:expr) => {
            #[kani::proof]
            fn $name() {
                let storage = SymbolicSlice::<$ty>::any();
                let slice = any_slice(storage.as_slice());
                let base = slice.as_ptr();
                let len = slice.len();
                let mut iter = Split::new(slice, |item| {
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
        };
    }

    macro_rules! gen_splitn {
        ($ty:ty, $iterator:ident, $view:ident, $touch:ident) => {
            #[kani::proof]
            fn check_next() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let base = slice.as_ptr();
                let len = slice.len();
                let limit: usize = kani::any();
                let mut iter = slice.$iterator(limit, |item| {
                    let _value = *item;
                    kani::any::<bool>()
                });
                let mut result = iter.next();
                assert_eq!(result.is_some(), limit != 0);
                assert_eq!(iter.inner.count, limit.saturating_sub(1));
                if let Some(ref mut part) = result {
                    assert!(part.len() <= len);
                    if limit == 1 {
                        check_slice(&part, base, 0, len);
                    }
                    $touch(part);
                }
                kani::cover(limit == 0, "zero split limit");
                kani::cover(limit == 1, "finish path");
                kani::cover(limit > 1, "delegated next path");
            }

            #[kani::proof]
            fn check_size_hint() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let slice = symbolic_view!(storage, $view);
                let len = slice.len();
                let limit: usize = kani::any();
                let iter = slice.$iterator(limit, |_| kani::any::<bool>());
                // Do not assume len < usize::MAX: the existing Split size_hint uses len+1.
                // This harness intentionally retains that ZST boundary as a potential failure.
                let hint = iter.size_hint();
                let upper = len.checked_add(1).map_or(limit, |n| n.min(limit));
                assert_eq!(hint, (limit.min(1), Some(upper)));
                kani::cover(limit == 0, "zero-limit hint");
                kani::cover(limit == 1, "one-limit hint");
                if mem::size_of::<$ty>() == 0 {
                    kani::cover(len == usize::MAX, "maximal ZST length is not excluded");
                }
            }
        };
    }

    // Relate a subview's local indices to its original allocation, using only usize
    // arithmetic. Prove this before using its contract in the mutable-view harnesses.
    macro_rules! remaining_interval_facts {
        ($source_len:expr, $start:expr, $end:expr, $front:expr, $back:expr) => {{
            let first = $start + $front;
            let remaining_end = $end - $back;
            let remaining = $end - $start - $front - $back;
            first <= remaining_end
                && remaining_end <= $source_len
                && remaining_end - first == remaining
                && (remaining == 0
                    || (first < $source_len
                        && remaining_end - 1 < $source_len
                        && first + (remaining - 1) == remaining_end - 1))
        }};
    }

    #[requires(
        start <= end && end <= source_len
            && front <= end - start && back <= end - start - front
    )]
    #[ensures(|_: &()| remaining_interval_facts!(source_len, start, end, front, back))]
    fn remaining_interval_arithmetic(
        source_len: usize,
        start: usize,
        end: usize,
        front: usize,
        back: usize,
    ) {
    }

    // Consuming one full chunk reduces the quotient by exactly one, even when
    // len is not a multiple of size. Keep this scalar theorem out of heap queries.
    macro_rules! exact_next_count_facts {
        ($len:expr, $size:expr) => {{
            let count = $len / $size;
            count > 0 && $len.wrapping_sub($size) / $size == count.wrapping_sub(1)
        }};
    }

    #[requires(size > 0 && size <= len)]
    #[ensures(|_: &()| exact_next_count_facts!(len, size))]
    fn exact_next_count_arithmetic(len: usize, size: usize) {}

    #[kani::proof_for_contract(exact_next_count_arithmetic)]
    fn check_exact_next_count_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        exact_next_count_arithmetic(len, size);
        kani::cover(len == usize::MAX && size == 1, "maximal scalar chunk count");
        kani::cover(len == 5 && size == 2, "quotient decrement with a remainder");
        kani::cover(len == size && size > 1, "last multi-element chunk consumed");
    }

    // Independently check the exact reformulation used to split Option equality
    // into an overflow obligation and a scalar-value obligation.
    #[kani::proof]
    fn check_checked_native_option_equivalence() {
        let left: usize = kani::any();
        let right: usize = kani::any();
        let expected: usize = kani::any();
        let product = left.checked_mul(right);
        let sum = left.checked_add(right);
        kani::assert(
            (product == Some(expected))
                == (product.is_some() && left.wrapping_mul(right) == expected),
            "checked multiplication Some equality is exactly overflow and value equality",
        );
        kani::assert(
            (sum == Some(expected)) == (sum.is_some() && left.wrapping_add(right) == expected),
            "checked addition Some equality is exactly overflow and value equality",
        );
        kani::cover(product.is_none(), "multiplication overflow in equivalence proof");
        kani::cover(sum.is_none(), "addition overflow in equivalence proof");
        kani::cover(product == Some(expected), "matching multiplication result");
        kani::cover(
            sum.is_some() && left.wrapping_add(right) != expected,
            "non-overflowing but different addition result",
        );
    }

    // Keep the Euclidean identity in widened arithmetic. For usize at most
    // 64 bits, a product of two operands plus a remainder fits in u128.
    macro_rules! euclidean_decomposition_facts {
        ($value:expr, $divisor:expr) => {{
            let quotient = $value / $divisor;
            let remainder = $value % $divisor;
            (quotient as u128).wrapping_mul($divisor as u128).wrapping_add(remainder as u128)
                == $value as u128
        }};
    }

    #[requires(usize::BITS <= 64 && divisor > 0)]
    #[ensures(|_: &()| euclidean_decomposition_facts!(value, divisor))]
    fn euclidean_decomposition_arithmetic(value: usize, divisor: usize) {}

    #[kani::proof_for_contract(euclidean_decomposition_arithmetic)]
    fn check_euclidean_decomposition_contract() {
        let value: usize = kani::any();
        let divisor: usize = kani::any();
        euclidean_decomposition_arithmetic(value, divisor);
        kani::cover(value == usize::MAX && divisor == 1, "maximal Euclidean quotient");
        kani::cover(value == usize::MAX && divisor == usize::MAX, "maximal divisor");
        kani::cover(value == 7 && divisor == 3, "nonzero Euclidean remainder");
    }

    // State the same Euclidean identity directly in the caller's native word
    // arithmetic, keeping the widened range identity available independently.
    #[requires(divisor > 0)]
    #[ensures(|_: &()| {
        let quotient = value / divisor;
        let remainder = value % divisor;
        quotient.wrapping_mul(divisor).wrapping_add(remainder) == value
    })]
    fn native_euclidean_decomposition_arithmetic(value: usize, divisor: usize) {}

    #[kani::proof_for_contract(native_euclidean_decomposition_arithmetic)]
    fn check_native_euclidean_decomposition_contract() {
        let value: usize = kani::any();
        let divisor: usize = kani::any();
        native_euclidean_decomposition_arithmetic(value, divisor);
        kani::cover(value == usize::MAX && divisor == 1, "maximal native Euclidean quotient");
        kani::cover(value == usize::MAX && divisor == usize::MAX, "maximal native divisor");
        kani::cover(value == 7 && divisor == 3, "nonzero native Euclidean remainder");
    }

    // Positive multiplication preserves and reflects order. Widening avoids
    // native-word wraparound while keeping all operands arbitrary usize values.
    #[requires(usize::BITS <= 64 && factor > 0)]
    #[ensures(|_: &()| {
        (left <= right)
            == ((left as u128).wrapping_mul(factor as u128)
                <= (right as u128).wrapping_mul(factor as u128))
    })]
    fn positive_wide_mul_order_arithmetic(left: usize, right: usize, factor: usize) {}

    #[kani::proof_for_contract(positive_wide_mul_order_arithmetic)]
    fn check_positive_wide_mul_order_contract() {
        let left: usize = kani::any();
        let right: usize = kani::any();
        let factor: usize = kani::any();
        positive_wide_mul_order_arithmetic(left, right, factor);
        kani::cover(
            left == 0 && right == usize::MAX && factor == usize::MAX,
            "increasing order with maximal wide factor",
        );
        kani::cover(
            left == usize::MAX && right == usize::MAX && factor == usize::MAX,
            "equal maximal wide products",
        );
        kani::cover(
            left == usize::MAX && right == 0 && factor == usize::MAX,
            "decreasing order with maximal wide factor",
        );
    }

    // Distributivity in the native modular integer ring includes overflow and
    // underflow. Prove it without the caller's division and contract context.
    #[ensures(|_: &()| {
        left.wrapping_sub(right).wrapping_mul(factor)
            == left.wrapping_mul(factor).wrapping_sub(right.wrapping_mul(factor))
    })]
    fn native_mul_difference_arithmetic(left: usize, right: usize, factor: usize) {}

    #[kani::proof_for_contract(native_mul_difference_arithmetic)]
    fn check_native_mul_difference_contract() {
        let left: usize = kani::any();
        let right: usize = kani::any();
        let factor: usize = kani::any();
        native_mul_difference_arithmetic(left, right, factor);
        kani::cover(left < right, "modular subtraction underflows");
        kani::cover(left.checked_mul(factor).is_none(), "modular multiplication overflows");
        kani::cover(left == 8 && right == 3 && factor == 2, "ordinary multiplication difference");
    }

    // Separate cancellation of a native, non-overflowing product from the
    // iterator's state transition and remaining-count proof.
    macro_rules! exact_multiple_facts {
        ($size:expr, $index:expr) => {{
            let product = $index.wrapping_mul($size);
            product % $size == 0 && product / $size == $index
        }};
    }

    #[requires(size > 0 && index.checked_mul(size).is_some())]
    #[ensures(|_: &()| exact_multiple_facts!(size, index))]
    fn exact_multiple_arithmetic(size: usize, index: usize) {}

    #[kani::proof_for_contract(exact_multiple_arithmetic)]
    fn check_exact_multiple_contract() {
        let size: usize = kani::any();
        let index: usize = kani::any();
        exact_multiple_arithmetic(size, index);
        kani::cover(size == 1 && index == usize::MAX, "maximal non-overflowing product");
        kani::cover(index == 0 && size > 1, "zero product with a multi-element chunk size");
        kani::cover(size == 2 && index == 3, "nonzero multi-element product");
    }

    // Subtracting complete chunks subtracts their quotients. Keep this theorem
    // free of multiplication so it can be proved independently of index offsets.
    macro_rules! exact_quotient_difference_facts {
        ($len:expr, $size:expr, $offset:expr) => {{
            let count = $len / $size;
            let removed = $offset / $size;
            removed <= count
                && $len.wrapping_sub($offset) / $size == count.wrapping_sub(removed)
                && ($offset < $len) == (removed < count)
        }};
    }

    #[requires(size > 0 && offset <= len && len % size == 0 && offset % size == 0)]
    #[ensures(|_: &()| exact_quotient_difference_facts!(len, size, offset))]
    fn exact_quotient_difference_arithmetic(len: usize, size: usize, offset: usize) {
        euclidean_decomposition_arithmetic(len, size);
        euclidean_decomposition_arithmetic(offset, size);
        native_euclidean_decomposition_arithmetic(len, size);
        native_euclidean_decomposition_arithmetic(offset, size);
        let count = len / size;
        let removed = offset / size;
        if count > 0 {
            reverse_native_offset_arithmetic(len, size, count);
        }
        if removed > 0 {
            reverse_native_offset_arithmetic(offset, size, removed);
        }
        kani::assert(
            count.checked_mul(size).is_some(),
            "length quotient product does not overflow",
        );
        kani::assert(
            count.wrapping_mul(size) == len,
            "exact length reconstructs from its quotient",
        );
        kani::assert(
            removed.checked_mul(size).is_some(),
            "offset quotient product does not overflow",
        );
        kani::assert(
            removed.wrapping_mul(size) == offset,
            "complete-chunk offset reconstructs from its quotient",
        );
        positive_wide_mul_order_arithmetic(removed, count, size);
        positive_wide_mul_order_arithmetic(count, removed, size);
        kani::assert(removed <= count, "complete-chunk quotients are ordered");
        let remaining = count - removed;
        positive_wide_mul_order_arithmetic(remaining, count, size);
        if remaining > 0 {
            reverse_native_offset_arithmetic(len, size, remaining);
        }
        kani::assert(
            remaining.checked_mul(size).is_some(),
            "remaining quotient product does not overflow",
        );
        native_mul_difference_arithmetic(count, removed, size);
        kani::assert(
            remaining.wrapping_mul(size) == len - offset,
            "quotient difference reconstructs the remaining length",
        );
        exact_multiple_arithmetic(size, remaining);
    }

    #[kani::proof_for_contract(exact_quotient_difference_arithmetic)]
    #[kani::stub_verified(native_mul_difference_arithmetic)]
    #[kani::stub_verified(positive_wide_mul_order_arithmetic)]
    #[kani::stub_verified(native_euclidean_decomposition_arithmetic)]
    #[kani::stub_verified(reverse_native_offset_arithmetic)]
    #[kani::stub_verified(euclidean_decomposition_arithmetic)]
    #[kani::stub_verified(exact_multiple_arithmetic)]
    fn check_exact_quotient_difference_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        let offset: usize = kani::any();
        exact_quotient_difference_arithmetic(len, size, offset);
        kani::cover(
            len == usize::MAX && size == 1 && offset == usize::MAX,
            "maximal scalar exact quotient difference",
        );
        kani::cover(offset == 0 && len > 0, "skip no complete chunks");
        kani::cover(len == 6 && size == 2 && offset == 2, "skip some complete chunks");
        kani::cover(len == 0 && offset == 0, "empty exact region");
    }

    // Classify every nth index without bounding it. Exact iterators hold only
    // complete chunks; a successful nth removes index + 1 of those chunks.
    macro_rules! exact_nth_step_facts {
        ($len:expr, $size:expr, $index:expr) => {{
            let count = $len / $size;
            let (start, overflow) = $index.overflowing_mul($size);
            if $index < count {
                let end = start.wrapping_add($size);
                !overflow
                    && start.checked_add($size).is_some()
                    && end <= $len
                    && $len.wrapping_sub(end) / $size == count.wrapping_sub($index).wrapping_sub(1)
            } else {
                overflow || start >= $len
            }
        }};
    }

    #[requires(size > 0 && len % size == 0)]
    #[ensures(|_: &()| exact_nth_step_facts!(len, size, index))]
    fn exact_nth_step_arithmetic(len: usize, size: usize, index: usize) {
        if index < len / size {
            exact_native_index_arithmetic(len, size, index);
            let start = index.wrapping_mul(size);
            native_range_end_arithmetic(len, start, size);
            exact_multiple_arithmetic(size, index);
            exact_quotient_difference_arithmetic(len, size, start);
            exact_next_count_arithmetic(len - start, size);
        } else if index.checked_mul(size).is_some() {
            let start = index.wrapping_mul(size);
            exact_multiple_arithmetic(size, index);
            if start < len {
                // Its quotient would be a valid index, contradicting this arm.
                exact_quotient_difference_arithmetic(len, size, start);
            }
        }
    }

    #[kani::proof_for_contract(exact_nth_step_arithmetic)]
    #[kani::stub_verified(native_range_end_arithmetic)]
    #[kani::stub_verified(exact_multiple_arithmetic)]
    #[kani::stub_verified(exact_quotient_difference_arithmetic)]
    #[kani::stub_verified(exact_native_index_arithmetic)]
    #[kani::stub_verified(exact_next_count_arithmetic)]
    fn check_exact_nth_step_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        let index: usize = kani::any();
        exact_nth_step_arithmetic(len, size, index);
        kani::cover(
            len == usize::MAX && size == 1 && index == usize::MAX - 1,
            "maximal scalar length and last valid nth index",
        );
        kani::cover(len == 6 && size == 2 && index == 1, "nth skips a multi-element chunk");
        kani::cover(index == len / size, "nth first exhausted index");
        kani::cover(index.checked_mul(size).is_none(), "nth index multiplication overflows");
    }

    // Transfer a proved quotient through equality of two scalar lengths.
    // Keeping each premise separate lets the caller prove the real iterator's
    // length relation without re-solving it inside unsigned division.
    #[requires(size > 0)]
    #[requires(actual == oracle)]
    #[requires(size > 0 && oracle / size == count)]
    #[ensures(|_: &()| actual == oracle && actual / size == count)]
    fn exact_count_transfer_arithmetic(actual: usize, oracle: usize, size: usize, count: usize) {}

    #[kani::proof_for_contract(exact_count_transfer_arithmetic)]
    fn check_exact_count_transfer_contract() {
        let actual: usize = kani::any();
        let oracle: usize = kani::any();
        let size: usize = kani::any();
        let count: usize = kani::any();
        exact_count_transfer_arithmetic(actual, oracle, size, count);
        kani::cover(actual == 0, "transfer an empty remaining count");
        kani::cover(actual == 6 && size == 2 && count == 3, "transfer a multi-element chunk count");
        kani::cover(actual == usize::MAX && size == 1, "transfer the maximal scalar length");
    }

    // Compose two byte offsets independently of iterator multiplication and
    // division. This only states pointer identity and does not grant access.
    #[requires(first <= data.len())]
    #[requires(first <= data.len() && second <= data.len() - first)]
    #[ensures(|_: &()| {
        data.as_ptr().wrapping_add(first).wrapping_add(second)
            == data.as_ptr().wrapping_add(first.wrapping_add(second))
    })]
    fn compose_byte_offsets(data: &[u8], first: usize, second: usize) {}

    #[kani::proof_for_contract(compose_byte_offsets)]
    fn check_compose_byte_offsets_contract() {
        let storage = SymbolicSlice::<u8>::any();
        let data = any_slice(storage.as_slice());
        let first: usize = kani::any();
        let second: usize = kani::any();
        compose_byte_offsets(data, first, second);
        kani::cover(first == 0 && second == 0, "compose zero byte offsets");
        kani::cover(
            first > 0 && second > 0 && first + second < data.len(),
            "compose interior byte offsets",
        );
        kani::cover(first + second == data.len(), "compose one-past-end byte offsets");
    }

    // Equal in-bounds byte offsets preserve pointer identity independently of
    // the scalar arithmetic used to compute them. No element bytes are read.
    #[requires(!data.is_empty() && left == right && left <= data.len())]
    #[ensures(|_: &()| data.as_ptr().wrapping_add(left) == data.as_ptr().wrapping_add(right))]
    fn equal_byte_offsets(data: &[u8], left: usize, right: usize) {}

    #[kani::proof_for_contract(equal_byte_offsets)]
    fn check_equal_byte_offsets_contract() {
        let storage = SymbolicSlice::<u8>::any();
        let data = any_slice(storage.as_slice());
        let left: usize = kani::any();
        let right: usize = kani::any();
        equal_byte_offsets(data, left, right);
        kani::cover(left == 0, "equal offsets at slice start");
        kani::cover(left > 0 && left < data.len(), "equal interior offsets");
        kani::cover(left == data.len(), "equal one-past-end offsets");
    }

    // Relate the quotient-based last-chunk oracle to the implementation's
    // subtraction, including proof that the oracle's multiplication fits usize.
    macro_rules! exact_last_chunk_start_facts {
        ($len:expr, $size:expr) => {{
            let count = $len / $size;
            count > 0 && count.wrapping_sub(1).checked_mul($size) == Some($len.wrapping_sub($size))
        }};
    }

    #[requires(size > 0 && size <= len && len % size == 0)]
    #[ensures(|_: &()| exact_last_chunk_start_facts!(len, size))]
    fn exact_last_chunk_start_arithmetic(len: usize, size: usize) {}

    #[kani::proof_for_contract(exact_last_chunk_start_arithmetic)]
    fn check_exact_last_chunk_start_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        exact_last_chunk_start_arithmetic(len, size);
        kani::cover(len == usize::MAX && size == 1, "maximal scalar last-chunk start");
        kani::cover(len == 6 && size == 2, "last of multiple full chunks");
        kani::cover(len == size && size > 1, "single full chunk starts at zero");
    }

    // Share exactly the same formula between the contract and its independent ordinary proof.
    macro_rules! exact_partition_facts {
        ($len:expr, $size:expr) => {{
            let remainder = $len % $size;
            remainder <= $len && remainder < $size && {
                let main_len = $len - remainder;
                main_len % $size == 0 && main_len / $size == $len / $size
            }
        }};
    }

    // This pure lemma is proved separately before using stub_verified at a function harness.
    // Its postcondition states ordinary usize arithmetic facts, with no allocation or T bounds.
    #[requires(size > 0)]
    #[ensures(|_: &()| exact_partition_facts!(len, size))]
    fn exact_partition_arithmetic(len: usize, size: usize) {}

    // Getter proofs need only the split bounds, not the quotient/divisibility facts
    // used by the constructor's full semantic proof. Keeping that dependency small
    // avoids adding unrelated divisions to the getter's symbolic execution.
    macro_rules! remainder_bounds_facts {
        ($len:expr, $size:expr) => {{
            let remainder = $len % $size;
            remainder <= $len && remainder < $size
        }};
    }

    #[requires(size > 0)]
    #[ensures(|_: &()| remainder_bounds_facts!(len, size))]
    fn remainder_bounds_arithmetic(len: usize, size: usize) {}

    // Widening separates the division theorem from native-word overflow checks. With
    // usize at most 64 bits, the product and product + size both fit in u128.
    macro_rules! chunk_index_facts {
        ($len:expr, $size:expr, $index:expr) => {{
            let product = ($index as u128).wrapping_mul($size as u128);
            product < $len as u128
        }};
    }

    #[requires(
        usize::BITS <= 64 && size > 0 && len > 0
            && index < len / size + usize::from(len % size != 0)
    )]
    #[ensures(|_: &()| chunk_index_facts!(len, size, index))]
    fn chunk_index_arithmetic(len: usize, size: usize, index: usize) {}

    macro_rules! exact_chunk_index_facts {
        ($len:expr, $size:expr, $index:expr) => {{
            let product = ($index as u128).wrapping_mul($size as u128);
            product.wrapping_add($size as u128) <= $len as u128
        }};
    }

    #[requires(usize::BITS <= 64 && size > 0 && index < len / size)]
    #[ensures(|_: &()| exact_chunk_index_facts!(len, size, index))]
    fn exact_chunk_index_arithmetic(len: usize, size: usize, index: usize) {}

    // Guard subtraction explicitly, avoiding a wrapped sum in the mathematical
    // description of the full chunk range. No allocation or element type is involved.
    macro_rules! full_chunk_range_facts {
        ($len:expr, $size:expr, $index:expr) => {{
            let product = ($index as u128).wrapping_mul($size as u128);
            product <= $len as u128 && $size as u128 <= ($len as u128) - product
        }};
    }

    // Total forms of the guarded range predicates. Under the leading bound,
    // wrapping_sub equals ordinary subtraction; outside it both predicates are
    // false. Independent usize/u128 proofs below check that equivalence.
    macro_rules! full_chunk_range_total_facts {
        ($len:expr, $size:expr, $index:expr) => {{
            let product = ($index as u128).wrapping_mul($size as u128);
            product <= $len as u128 && $size as u128 <= ($len as u128).wrapping_sub(product)
        }};
    }

    macro_rules! native_exact_chunk_offset_total_facts {
        ($len:expr, $size:expr, $index:expr) => {
            $index.checked_mul($size).is_some()
                && $index.wrapping_mul($size) <= $len
                && $size <= $len.wrapping_sub($index.wrapping_mul($size))
        };
    }

    macro_rules! check_guarded_subtraction {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            fn $name() {
                let len: $ty = kani::any();
                let start: $ty = kani::any();
                let size: $ty = kani::any();
                let ordinary = start <= len && size <= len - start;
                let total = start <= len && size <= len.wrapping_sub(start);
                assert_eq!(ordinary, total);
                kani::cover(len == <$ty>::MAX && start == 0 && size == 1, "maximal guarded length");
                kani::cover(len == 1 && start == 1 && size == 0, "empty remaining range");
                kani::cover(len == 0 && start == 1 && size == 0, "out-of-range start rejected");
            }
        };
    }

    check_guarded_subtraction!(check_guarded_subtraction_usize, usize);
    check_guarded_subtraction!(check_guarded_subtraction_u128, u128);

    // Convert the independently proved widened exact-index bound to the native
    // operations used by nth_back. This bridge contains no division or pointers.
    #[requires(usize::BITS <= 64 && size > 0 && full_chunk_range_total_facts!(len, size, index))]
    #[ensures(|_: &()| native_exact_chunk_offset_total_facts!(len, size, index))]
    fn native_exact_chunk_offset_arithmetic(len: usize, size: usize, index: usize) {
        native_chunk_offset_arithmetic(len, size, index);
    }

    #[kani::proof_for_contract(native_exact_chunk_offset_arithmetic)]
    #[kani::stub_verified(native_chunk_offset_arithmetic)]
    fn check_native_exact_chunk_offset_contract() {
        native_exact_chunk_offset_arithmetic(kani::any(), kani::any(), kani::any());
    }

    // Keep the floor-division theorem separate from native-word overflow checks.
    // The ordinary forward-implication proof checks this same range predicate.
    #[requires(usize::BITS <= 64 && size > 0 && index < len / size)]
    #[ensures(|_: &()| full_chunk_range_total_facts!(len, size, index))]
    fn full_exact_chunk_index_arithmetic(len: usize, size: usize, index: usize) {}

    #[kani::proof_for_contract(full_exact_chunk_index_arithmetic)]
    fn check_full_exact_chunk_index_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        let index: usize = kani::any();
        full_exact_chunk_index_arithmetic(len, size, index);
        kani::cover(
            len == usize::MAX && size == 1 && index == 0,
            "maximal length in scalar exact-index theorem",
        );
        kani::cover(index == 0 && size == 1 && len == 1, "first exact chunk");
        // A witness guides only this reachability query; the safety domain above
        // still ranges over every len, positive size and in-range index.
        kani::cover(index == 1 && size == 1 && len == 2, "nonzero exact chunk index");
    }

    // Expose only native offset facts to memory proofs. The two independently
    // proved scalar callees keep widened multiplication out of their callers.
    #[requires(usize::BITS <= 64 && size > 0 && index < len / size)]
    #[ensures(|_: &()| native_exact_chunk_offset_total_facts!(len, size, index))]
    fn exact_native_index_arithmetic(len: usize, size: usize, index: usize) {
        full_exact_chunk_index_arithmetic(len, size, index);
        native_exact_chunk_offset_arithmetic(len, size, index);
    }

    #[kani::proof_for_contract(exact_native_index_arithmetic)]
    #[kani::stub_verified(full_exact_chunk_index_arithmetic)]
    #[kani::stub_verified(native_exact_chunk_offset_arithmetic)]
    fn check_exact_native_index_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        let index: usize = kani::any();
        exact_native_index_arithmetic(len, size, index);
        kani::cover(
            len == usize::MAX && size == 1 && index == 0,
            "maximal length in scalar native-index theorem",
        );
        kani::cover(len == 3 && size == 1 && index == 1, "nonzero exact native index");
        kani::cover(len == 4 && size == 2 && index == 0, "multi-element exact chunks");
    }

    // Reverse exact iteration uses k = count - n, including k == count.
    // Keep the division theorem separate from native-word overflow reasoning.
    macro_rules! reverse_full_offset_facts {
        ($len:expr, $size:expr, $chunks:expr) => {
            ($chunks as u128).wrapping_mul($size as u128) <= $len as u128
        };
    }

    macro_rules! reverse_native_offset_facts {
        ($len:expr, $size:expr, $chunks:expr) => {
            $chunks.checked_mul($size).is_some()
                && $size <= $chunks.wrapping_mul($size)
                && $chunks.wrapping_mul($size) <= $len
        };
    }

    #[requires(usize::BITS <= 64 && size > 0 && chunks <= len / size)]
    #[ensures(|_: &()| reverse_full_offset_facts!(len, size, chunks))]
    fn reverse_full_offset_arithmetic(len: usize, size: usize, chunks: usize) {}

    #[requires(usize::BITS <= 64 && size > 0 && chunks > 0)]
    #[requires(reverse_full_offset_facts!(len, size, chunks))]
    #[ensures(|_: &()| reverse_native_offset_facts!(len, size, chunks))]
    fn reverse_native_offset_arithmetic(len: usize, size: usize, chunks: usize) {}

    #[requires(usize::BITS <= 64 && size > 0 && chunks > 0 && chunks <= len / size)]
    #[ensures(|_: &()| reverse_native_offset_facts!(len, size, chunks))]
    fn reverse_exact_offset_arithmetic(len: usize, size: usize, chunks: usize) {
        reverse_full_offset_arithmetic(len, size, chunks);
        reverse_native_offset_arithmetic(len, size, chunks);
    }

    #[kani::proof_for_contract(reverse_full_offset_arithmetic)]
    fn check_reverse_full_offset_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        let chunks: usize = kani::any();
        reverse_full_offset_arithmetic(len, size, chunks);
        kani::cover(
            len == usize::MAX && size == 1 && chunks == usize::MAX,
            "maximal reverse offset in widened scalar arithmetic",
        );
        kani::cover(len == 5 && size == 2 && chunks == 2, "nondivisible reverse main length");
        kani::cover(len == 0 && size == 1 && chunks == 0, "zero selected chunks in widened bound");
    }

    #[kani::proof_for_contract(reverse_native_offset_arithmetic)]
    fn check_reverse_native_offset_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        let chunks: usize = kani::any();
        reverse_native_offset_arithmetic(len, size, chunks);
        kani::cover(
            len == usize::MAX && size == 1 && chunks == usize::MAX,
            "maximal native reverse offset",
        );
        kani::cover(len == 5 && size == 2 && chunks == 2, "native reverse offset with a remainder");
    }

    #[kani::proof_for_contract(reverse_exact_offset_arithmetic)]
    #[kani::stub_verified(reverse_full_offset_arithmetic)]
    #[kani::stub_verified(reverse_native_offset_arithmetic)]
    fn check_reverse_exact_offset_contract() {
        let len: usize = kani::any();
        let size: usize = kani::any();
        let chunks: usize = kani::any();
        reverse_exact_offset_arithmetic(len, size, chunks);
        kani::cover(
            len == usize::MAX && size == 1 && chunks == usize::MAX,
            "maximal reverse offset in composed scalar arithmetic",
        );
        kani::cover(
            len == 5 && size == 2 && chunks == 2,
            "reverse offset with a nondivisible main length",
        );
        kani::cover(
            len == 6 && size == 2 && chunks == 1,
            "reverse offset after skipped full chunks",
        );
    }

    // Separate endpoint addition from the multiplication/division that chooses
    // the chunk. This theorem has only three arbitrary usize values and no
    // pointers; all operations in its contract are total.
    #[requires(start <= len && size <= len.wrapping_sub(start))]
    #[ensures(|_: &()| {
        let end = start.wrapping_add(size);
        start.checked_add(size).is_some() && start <= end && end <= len
    })]
    fn native_range_end_arithmetic(len: usize, start: usize, size: usize) {}

    #[kani::proof_for_contract(native_range_end_arithmetic)]
    fn check_native_range_end_contract() {
        let len: usize = kani::any();
        let start: usize = kani::any();
        let size: usize = kani::any();
        native_range_end_arithmetic(len, start, size);
        kani::cover(
            len == usize::MAX && start == usize::MAX && size == 0,
            "empty range at the maximal endpoint",
        );
        kani::cover(len == usize::MAX && start == 0 && size == usize::MAX, "full maximal range");
        kani::cover(len == 3 && start == 1 && size == 1, "nonempty interior range");
    }

    // Bridge the widened integer theorem to the exact native operations in the getter.
    // There is no division here, so it can be proved independently of the index-count lemma.
    #[requires(usize::BITS <= 64 && chunk_index_facts!(len, size, index))]
    #[ensures(|_: &()| native_chunk_offset_facts!(len, size, index))]
    fn native_chunk_offset_arithmetic(len: usize, size: usize, index: usize) {}

    // Keep the quotient/remainder representation used by chunk_index_arithmetic.
    // The div_ceil bridge below relates it to the real ChunksMut::size_hint.
    // This lemma has no allocation, element type, or artificial input-size bound.
    macro_rules! nth_back_chunk_start_facts {
        ($len:expr, $size:expr, $n:expr) => {{
            let count = $len / $size + usize::from($len % $size != 0);
            $n < count && native_chunk_offset_facts!($len, $size, count - 1 - $n)
        }};
    }

    #[requires(
        usize::BITS <= 64 && size > 0 && len > 0
            && n < len / size + usize::from(len % size != 0)
    )]
    #[ensures(|_: &()| nth_back_chunk_start_facts!(len, size, n))]
    fn nth_back_chunk_start_arithmetic(len: usize, size: usize, n: usize) {
        let count = len / size + usize::from(len % size != 0);
        let index = count - 1 - n;
        chunk_index_arithmetic(len, size, index);
        native_chunk_offset_arithmetic(len, size, index);
    }

    // Isolate the representation identity from multiplication and pointer facts.
    #[requires(size > 0)]
    #[ensures(|_: &()| {
        len.div_ceil(size) == len / size + usize::from(len % size != 0)
    })]
    fn chunk_count_expression_arithmetic(len: usize, size: usize) {
        chunk_count_arithmetic(len, size);
    }

    // Pass the actual iterator count explicitly. The caller proves its equality
    // with div_ceil once; the postconditions reuse the same count without division.
    #[requires(
        usize::BITS <= 64 && size > 0 && len > 0
            && count == len.div_ceil(size) && n < count
    )]
    #[ensures(|_: &usize| {
        n < count && native_chunk_offset_facts!(len, size, count - 1 - n)
    })]
    #[ensures(|start: &usize| {
        *start == (count - 1 - n) * size && *start < len
    })]
    fn nth_back_div_ceil_start_arithmetic(
        len: usize,
        size: usize,
        count: usize,
        n: usize,
    ) -> usize {
        chunk_count_expression_arithmetic(len, size);
        let index = count - 1 - n;
        chunk_index_arithmetic(len, size, index);
        native_chunk_offset_arithmetic(len, size, index);
        index * size
    }

    // Relate the implementation's checked-add endpoint to the subtraction-based
    // subslice length, including the usize addition-overflow branch.
    macro_rules! clipped_chunk_end_facts {
        ($len:expr, $start:expr, $size:expr) => {{
            let end = match $start.checked_add($size) {
                Some(sum) => cmp::min($len, sum),
                None => $len,
            };
            $start <= end && end - $start == cmp::min($len - $start, $size)
        }};
    }

    #[requires(start <= len)]
    #[ensures(|_: &()| clipped_chunk_end_facts!(len, start, size))]
    fn clipped_chunk_end_arithmetic(len: usize, start: usize, size: usize) {}

    // size_hint() computes a quotient and conditionally adds one. Establish this bound
    // before calling len(), including before proof_for_contract evaluates its precondition.
    macro_rules! chunk_count_facts {
        ($len:expr, $size:expr) => {{
            let quotient = $len / $size;
            let remainder = $len % $size;
            quotient <= $len && (remainder == 0 || quotient < usize::MAX)
        }};
    }

    #[requires(size > 0)]
    #[ensures(|_: &()| chunk_count_facts!(len, size))]
    fn chunk_count_arithmetic(len: usize, size: usize) {}

    // Length-only lemmas have no allocations, element types, or slice-length bounds. They
    // establish arithmetic facts only; the function harnesses above connect them to memory.
    mod arithmetic {
        use super::*;

        #[kani::proof]
        fn check_clipped_chunk_end_arithmetic() {
            let len: usize = kani::any();
            let start = kani::any_where(|start: &usize| *start <= len);
            let size: usize = kani::any();
            assert!(clipped_chunk_end_facts!(len, start, size));
            kani::cover(start.checked_add(size).is_none(), "endpoint addition overflows");
            kani::cover(size <= len - start, "whole chunk fits");
            kani::cover(size > len - start, "chunk is clipped");
            kani::cover(len == usize::MAX, "maximal symbolic length");
        }

        #[kani::proof_for_contract(clipped_chunk_end_arithmetic)]
        fn check_clipped_chunk_end_contract() {
            clipped_chunk_end_arithmetic(kani::any(), kani::any(), kani::any());
        }

        #[kani::proof_for_contract(nth_back_chunk_start_arithmetic)]
        #[kani::stub_verified(chunk_index_arithmetic)]
        #[kani::stub_verified(native_chunk_offset_arithmetic)]
        fn check_nth_back_chunk_start_contract() {
            nth_back_chunk_start_arithmetic(kani::any(), kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_offset_isize_arithmetic() {
            // The lemma has this declared domain. Getter callers must discharge
            // it from a valid non-ZST slice, without additional input assumptions.
            let len = kani::any_where(|n: &usize| *n <= isize::MAX as usize);
            let offset = kani::any_where(|n: &usize| *n <= len);
            assert!(offset <= isize::MAX as usize);
            kani::cover(offset == isize::MAX as usize, "maximal non-ZST offset");
            kani::cover(offset == 0, "zero offset");
        }

        #[kani::proof_for_contract(offset_isize_arithmetic)]
        fn check_offset_isize_contract() {
            offset_isize_arithmetic(kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_exact_postcondition_offset_equivalence() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let index: usize = kani::any();
            kani::assume(native_exact_chunk_offset_facts!(len, size, index));
            // Keep the ordinary operations here: their generated overflow checks
            // establish that replacing only the spec arithmetic is equivalent.
            let forward = index * size;
            let backward = len - forward - size;
            assert_eq!(forward, index.wrapping_mul(size));
            assert_eq!(backward, len.wrapping_sub(index.wrapping_mul(size)).wrapping_sub(size),);
            kani::cover(len == usize::MAX, "full usize length");
            kani::cover(index > 0, "nonzero index");
            kani::cover(size == 1, "unit-size chunk");
        }

        #[kani::proof]
        fn check_readable_subslice_byte() {
            let storage = SymbolicSlice::<u8>::any();
            let slice = any_slice(storage.as_slice());
            let len = slice.len();
            let start = kani::any_where(|n: &usize| *n <= len);
            let size = kani::any_where(|n: &usize| *n <= len - start);
            let region = ptr::slice_from_raw_parts(slice.as_ptr().wrapping_add(start), size);
            assert!(crate::ub_checks::can_dereference(region));
            kani::cover(size > 0, "nonempty readable subrange");
            kani::cover(start > 0, "interior readable subrange");
        }

        #[kani::proof_for_contract(readable_subslice::<u8>)]
        fn check_readable_subslice_contract_byte() {
            let storage = SymbolicSlice::<u8>::any();
            let slice = any_slice(storage.as_slice());
            readable_subslice(slice.as_ptr(), slice.len(), kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_writable_subslice_byte() {
            let mut storage = SymbolicSlice::<u8>::any();
            let slice = any_slice_mut(storage.as_mut_slice());
            let len = slice.len();
            let start = kani::any_where(|n: &usize| *n <= len);
            let size = kani::any_where(|n: &usize| *n <= len - start);
            let region =
                ptr::slice_from_raw_parts_mut(slice.as_mut_ptr().wrapping_add(start), size);
            assert!(crate::ub_checks::can_dereference(region.cast_const()));
            assert!(crate::ub_checks::can_write(region));
            kani::cover(size > 0, "nonempty writable subrange");
            kani::cover(start > 0, "interior writable subrange");
        }

        #[kani::proof_for_contract(writable_subslice::<u8>)]
        fn check_writable_subslice_contract_byte() {
            let mut storage = SymbolicSlice::<u8>::any();
            let slice = any_slice_mut(storage.as_mut_slice());
            writable_subslice(slice.as_mut_ptr(), slice.len(), kani::any(), kani::any());
        }

        #[kani::proof_for_contract(chunk_count_expression_arithmetic)]
        #[kani::stub_verified(chunk_count_arithmetic)]
        fn check_chunk_count_expression_contract() {
            let len: usize = kani::any();
            let size: usize = kani::any();
            chunk_count_expression_arithmetic(len, size);
            kani::cover(len == 0, "zero length");
            kani::cover(len == usize::MAX, "maximal length");
            kani::cover(size > len, "chunk size exceeds length");
        }

        #[kani::proof_for_contract(nth_back_div_ceil_start_arithmetic)]
        #[kani::stub_verified(chunk_index_arithmetic)]
        #[kani::stub_verified(native_chunk_offset_arithmetic)]
        #[kani::stub_verified(chunk_count_expression_arithmetic)]
        #[kani::stub_verified(chunk_count_arithmetic)]
        fn check_nth_back_div_ceil_start_contract() {
            let len: usize = kani::any();
            // This is already a conjunct of the target contract's precondition.
            let size = kani::any_where(|size: &usize| *size > 0);
            let n: usize = kani::any();
            // Make the existing overflow bound available before div_ceil is
            // evaluated while entering the target contract.
            chunk_count_arithmetic(len, size);
            let count: usize = kani::any();
            nth_back_div_ceil_start_arithmetic(len, size, count, n);
            kani::cover(len == usize::MAX, "maximal length");
            kani::cover(n > 0, "nonzero valid reverse index");
            kani::cover(size > len, "chunk size exceeds slice length");
        }

        #[kani::proof_for_contract(writable_interval::<u8>)]
        #[kani::stub_verified(writable_subslice::<u8>)]
        fn check_writable_interval_contract_byte() {
            let mut storage = SymbolicSlice::<u8>::any();
            let slice = any_slice_mut(storage.as_mut_slice());
            let len = slice.len();
            let start: usize = kani::any();
            let end: usize = kani::any();
            writable_interval(slice.as_mut_ptr(), len, start, end);
            kani::cover(start == end, "empty interval");
            kani::cover(start == 0 && end == len, "whole input interval");
            kani::cover(start > 0 && start < end && end < len, "proper interior interval");
        }

        #[kani::proof_for_contract(writable_prefix::<u8>)]
        #[kani::stub_verified(writable_subslice::<u8>)]
        fn check_writable_prefix_contract_byte() {
            let mut storage = SymbolicSlice::<u8>::any();
            let slice = any_slice_mut(storage.as_mut_slice());
            let len = slice.len();
            let prefix: usize = kani::any();
            writable_prefix(slice.as_mut_ptr(), len, prefix);
            kani::cover(prefix == 0, "empty prefix");
            kani::cover(prefix == len, "whole input prefix");
            kani::cover(prefix > 0 && prefix < len, "proper nonempty prefix");
        }

        #[kani::proof]
        fn check_exact_chunk_end_arithmetic() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let index: usize = kani::any();
            kani::assume(native_exact_chunk_offset_facts!(len, size, index));
            assert!(exact_chunk_end_facts!(len, size, index));
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof_for_contract(exact_chunk_end_arithmetic)]
        fn check_exact_chunk_end_contract() {
            exact_chunk_end_arithmetic(kani::any(), kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_remaining_interval_arithmetic() {
            let source_len: usize = kani::any();
            let end = kani::any_where(|n: &usize| *n <= source_len);
            let start = kani::any_where(|n: &usize| *n <= end);
            let front = kani::any_where(|n: &usize| *n <= end - start);
            let back = kani::any_where(|n: &usize| *n <= end - start - front);
            assert!(remaining_interval_facts!(source_len, start, end, front, back));
            kani::cover(source_len == usize::MAX, "full usize source length");
            kani::cover(end - start - front - back == 0, "empty remaining interval");
            kani::cover(
                start > 0 && front > 0 && back > 0 && end - start - front - back > 0,
                "nonempty interior interval after consumption at both ends",
            );
        }

        #[kani::proof_for_contract(remaining_interval_arithmetic)]
        fn check_remaining_interval_contract() {
            remaining_interval_arithmetic(
                kani::any(),
                kani::any(),
                kani::any(),
                kani::any(),
                kani::any(),
            );
        }

        #[kani::proof]
        fn check_exact_partition_arithmetic() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            assert!(exact_partition_facts!(len, size));
        }

        #[kani::proof_for_contract(exact_partition_arithmetic)]
        fn check_exact_partition_contract() {
            exact_partition_arithmetic(kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_remainder_bounds_arithmetic() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            assert!(remainder_bounds_facts!(len, size));
            kani::cover(len == usize::MAX, "full usize length");
            kani::cover(len % size == 0, "empty remainder");
            kani::cover(len % size > 0, "nonempty remainder");
        }

        #[kani::proof_for_contract(remainder_bounds_arithmetic)]
        fn check_remainder_bounds_contract() {
            remainder_bounds_arithmetic(kani::any(), kani::any());
        }

        // Every original (length, size) input has a representable tuple (count,
        // remainder). This also checks the original constructor partition bounds.
        #[kani::proof]
        fn check_exact_partition_parameterization_forward() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let count = len / size;
            let remainder = len % size;
            let main = count.checked_mul(size);
            assert!(main.is_some());
            let main = main.unwrap();
            assert!(main.checked_add(remainder) == Some(len));
            assert!(remainder < size);
            kani::cover(len == usize::MAX, "full usize length");
            kani::cover(remainder > 0, "nonempty remainder");
        }

        // Link the checked native representation to the wider integer model without
        // division. This establishes both directions of the input-domain translation.
        #[kani::proof]
        fn check_exact_partition_native_encoding() {
            assert!(usize::BITS <= 64);
            let size: usize = kani::any();
            let count: usize = kani::any();
            let remainder: usize = kani::any();
            let product = (count as u128).wrapping_mul(size as u128);
            let sum = product.wrapping_add(remainder as u128);
            let native_main = count.checked_mul(size);
            assert!(native_main.is_some() == (product <= usize::MAX as u128));
            if let Some(main) = native_main {
                assert!(main as u128 == product);
                let native_len = main.checked_add(remainder);
                assert!(native_len.is_some() == (sum <= usize::MAX as u128));
                if let Some(len) = native_len {
                    assert!(len as u128 == sum);
                }
            }
        }

        // Conversely, every representable tuple yields the real constructor's partition.
        // The native-encoding proof establishes that these wide bounds are exactly
        // checked_mul/checked_add bounds, not a smaller domain.
        #[kani::proof]
        fn check_exact_partition_parameterization_reverse() {
            assert!(usize::BITS <= 64);
            let size = kani::any_where(|n: &usize| *n > 0);
            let count: usize = kani::any();
            let remainder = kani::any_where(|n: &usize| *n < size);
            let main = (count as u128).wrapping_mul(size as u128);
            kani::assume(main <= usize::MAX as u128);
            let total = main.wrapping_add(remainder as u128);
            kani::assume(total <= usize::MAX as u128);
            let len = total as usize;
            assert!(len / size == count);
            assert!(len % size == remainder);
            assert!(main <= len as u128 && remainder <= len);
            assert!(main as usize == len - remainder);
        }

        #[kani::proof]
        fn check_chunk_index_arithmetic() {
            assert!(usize::BITS <= 64);
            let len = kani::any_where(|n: &usize| *n > 0);
            let size = kani::any_where(|n: &usize| *n > 0);
            let count = len / size + usize::from(len % size != 0);
            let index = kani::any_where(|n: &usize| *n < count);
            assert!(chunk_index_facts!(len, size, index));
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof_for_contract(chunk_index_arithmetic)]
        fn check_chunk_index_contract() {
            chunk_index_arithmetic(kani::any(), kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_exact_chunk_index_arithmetic() {
            assert!(usize::BITS <= 64);
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let index = kani::any_where(|n: &usize| *n < len / size);
            assert!(exact_chunk_index_facts!(len, size, index));
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof_for_contract(exact_chunk_index_arithmetic)]
        fn check_exact_chunk_index_contract() {
            exact_chunk_index_arithmetic(kani::any(), kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_exact_chunk_index_forward_implication() {
            assert!(usize::BITS <= 64);
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let index = kani::any_where(|n: &usize| *n < len / size);
            assert!(full_chunk_range_facts!(len, size, index));
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof]
        fn check_exact_chunk_index_reverse_implication() {
            assert!(usize::BITS <= 64);
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let index: usize = kani::any();
            kani::assume(full_chunk_range_facts!(len, size, index));
            assert!(index < len / size);
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof]
        fn check_native_exact_chunk_offset_equivalence() {
            assert!(usize::BITS <= 64);
            let len: usize = kani::any();
            let size: usize = kani::any();
            let index: usize = kani::any();
            let wide = full_chunk_range_facts!(len, size, index);
            assert!(wide == native_exact_chunk_offset_facts!(len, size, index));
            kani::cover(size > 0 && wide, "full chunk in bounds");
            kani::cover(!wide, "out-of-bounds or overflowing chunk");
            kani::cover(len == 0, "empty remaining slice");
        }

        #[kani::proof]
        fn check_native_chunk_offset_arithmetic() {
            assert!(usize::BITS <= 64);
            let len: usize = kani::any();
            let size: usize = kani::any();
            let index: usize = kani::any();
            kani::assume(chunk_index_facts!(len, size, index));
            assert!(native_chunk_offset_facts!(len, size, index));
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof_for_contract(native_chunk_offset_arithmetic)]
        fn check_native_chunk_offset_contract() {
            native_chunk_offset_arithmetic(kani::any(), kani::any(), kani::any());
        }

        #[kani::proof]
        fn check_chunk_count_arithmetic() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            assert!(chunk_count_facts!(len, size));
            kani::cover(len == usize::MAX, "full usize length");
            kani::cover(len == 0, "empty slice count");
            kani::cover(len % size != 0, "rounded-up chunk count");
        }

        #[kani::proof_for_contract(chunk_count_arithmetic)]
        fn check_chunk_count_contract() {
            chunk_count_arithmetic(kani::any(), kani::any());
        }

        // The other direction of check_chunk_index_arithmetic: the spatial bound
        // admits no index that the Iterator contract rejects. No length cap is used.
        #[kani::proof]
        fn check_chunk_index_reverse_implication() {
            assert!(usize::BITS <= 64);
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let index: usize = kani::any();
            kani::assume(chunk_index_facts!(len, size, index));
            let count = len / size + usize::from(len % size != 0);
            assert!(index < count);
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof]
        fn check_native_chunk_offset_equivalence() {
            assert!(usize::BITS <= 64);
            let len: usize = kani::any();
            let size: usize = kani::any();
            let index: usize = kani::any();
            let wide = chunk_index_facts!(len, size, index);
            assert_eq!(wide, native_chunk_offset_facts!(len, size, index));
            kani::cover(wide, "in-bounds product");
            kani::cover(!wide, "out-of-bounds or overflowing product");
        }

        // Execute each family's actual metadata methods independently on unrestricted
        // ZST lengths. This checks the count formula without allocating backing memory.
        macro_rules! check_chunk_count_api {
            ($name:ident, $iterator:ident, $view:ident) => {
                #[kani::proof]
                #[kani::stub_verified(chunk_count_arithmetic)]
                fn $name() {
                    let len: usize = kani::any();
                    let size = kani::any_where(|n: &usize| *n > 0);
                    chunk_count_arithmetic(len, size);
                    // SAFETY: unit is inhabited and zero-sized. The dangling pointer is
                    // non-null and aligned, and the borrowed region covers zero bytes.
                    let slice = unsafe { $view(NonNull::<()>::dangling().as_ptr(), len) };
                    let iter = $iterator::new(slice, size);
                    let count = len / size + usize::from(len % size != 0);
                    let (lower, upper) = iter.size_hint();
                    assert!(lower == count && upper == Some(count));
                    assert!(iter.len() == count);
                    assert!(TrustedRandomAccessNoCoerce::size(&iter) == count);
                    kani::cover(len == usize::MAX, "maximal ZST count");
                    kani::cover(len == 0, "empty ZST count");
                }
            };
        }

        check_chunk_count_api!(check_chunks_size_hint_formula, Chunks, from_raw_parts);
        check_chunk_count_api!(check_rchunks_size_hint_formula, RChunks, from_raw_parts);
        check_chunk_count_api!(check_chunks_mut_size_hint_formula, ChunksMut, from_raw_parts_mut);
        check_chunk_count_api!(check_rchunks_mut_size_hint_formula, RChunksMut, from_raw_parts_mut);

        // Keep the full usize domain; use SMT rather than bit-blasting variable division.
        #[kani::proof]
        #[kani::solver(z3)]
        #[kani::stub_verified(chunk_index_arithmetic)]
        fn check_forward_chunk_range() {
            let len = kani::any_where(|n: &usize| *n > 0);
            let size = kani::any_where(|n: &usize| *n > 0);
            // Use the iterator's actual count formula, preserving every valid index.
            let count = len / size + usize::from(len % size != 0);
            let index = kani::any_where(|n: &usize| *n < count);
            chunk_index_arithmetic(len, size, index);
            let (start, count) = chunk_range(len, size, index, false);
            assert!(start < len);
            assert!(count > 0 && count <= size);
            assert!(start.checked_add(count).is_some());
            assert!(start + count <= len);
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof]
        fn check_reverse_chunk_range() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let index = kani::any_where(|n: &usize| *n < len.div_ceil(size));
            let (start, count) = chunk_range(len, size, index, true);
            assert!(count > 0 && count <= size);
            assert!(start.checked_add(count).is_some());
            assert!(start + count <= len);
            kani::cover(len == usize::MAX, "full usize length");
        }

        #[kani::proof]
        fn check_exact_chunk_range() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            kani::assume(len % size == 0);
            let index = kani::any_where(|n: &usize| *n < len / size);
            let reverse: bool = kani::any();
            let (start, count) = chunk_range(len, size, index, reverse);
            assert_eq!(count, size);
            assert!(start.checked_add(count).is_some());
            assert!(start + count <= len);
        }

        #[kani::proof]
        fn check_disjoint_chunk_indices() {
            let len: usize = kani::any();
            let size = kani::any_where(|n: &usize| *n > 0);
            let first = kani::any_where(|n: &usize| *n < len.div_ceil(size));
            let second = kani::any_where(|n: &usize| *n < len.div_ceil(size) && *n != first);
            let reverse: bool = kani::any();
            let (a, a_len) = chunk_range(len, size, first, reverse);
            let (b, b_len) = chunk_range(len, size, second, reverse);
            assert!(a + a_len <= b || b + b_len <= a);
        }
    }

    macro_rules! gen_internal_contracts {
        ($ty:ty, $iterator:ident, $view:ident) => {
            #[kani::proof_for_contract($iterator::post_inc_start)]
            fn check_post_inc_start_contract() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut iter = $iterator::new(symbolic_view!(storage, $view));
                let offset: usize = kani::any();
                let _ = unsafe { iter.post_inc_start(offset) };
                kani::cover(offset == 0, "zero forward pointer adjustment");
                kani::cover(offset > 0, "nonzero forward pointer adjustment");
            }

            #[kani::proof_for_contract($iterator::pre_dec_end)]
            fn check_pre_dec_end_contract() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut iter = $iterator::new(symbolic_view!(storage, $view));
                let offset: usize = kani::any();
                let _ = unsafe { iter.pre_dec_end(offset) };
                kani::cover(offset == 0, "zero backward pointer adjustment");
                kani::cover(offset > 0, "nonzero backward pointer adjustment");
            }

            #[kani::proof_for_contract($iterator::next_back_unchecked)]
            fn check_next_back_unchecked_contract() {
                let mut storage = SymbolicSlice::<$ty>::any();
                let mut iter = $iterator::new(symbolic_view!(storage, $view));
                let result = unsafe { iter.next_back_unchecked() };
                let _value = *result;
                kani::cover(true, "unchecked back element reached under precondition");
            }
        };
    }

    macro_rules! gen_chunk_methods {
        ($ty:ty, $iterator:ident, $view:ident, $pointer:ident, $reverse:expr, $exact:expr, $touch:ident) => {
            gen_chunk_contract!($iterator, $ty, $view, $pointer, $reverse, $exact, $touch);
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
                $touch
            );
        };
    }

    macro_rules! gen_type_suite {
        ($module:ident, $ty:ty) => {
            mod $module {
                use super::*;
                mod iter {
                    use super::*;
                    gen_iter_family!($ty, Iter, as_slice);
                    gen_internal_contracts!($ty, Iter, as_slice);
                }
                mod iter_mut {
                    use super::*;
                    gen_iter_family!($ty, IterMut, as_mut_slice);
                    gen_internal_contracts!($ty, IterMut, as_mut_slice);
                    gen_iter_mut_views!($ty);
                }
                mod split {
                    use super::*;
                    gen_split_step!(check_next, $ty, next, false);
                    gen_split_step!(check_next_back, $ty, next_back, true);
                }
                mod windows {
                    use super::*;
                    gen_windows!($ty);
                }
                mod chunks {
                    use super::*;
                    gen_chunk_methods!($ty, Chunks, as_slice, as_ptr, false, false, touch_shared);
                    gen_chunk_memory_step!(
                        check_next_back_memory_safety,
                        $ty,
                        Chunks,
                        next_back,
                        as_slice,
                        as_ptr,
                        false,
                        true,
                        false,
                        touch_shared
                    );
                    gen_shared_clone_protocol!($ty, Chunks, false, false);
                }
                mod chunks_mut {
                    use super::*;
                    gen_chunk_methods!(
                        $ty,
                        ChunksMut,
                        as_mut_slice,
                        as_mut_ptr,
                        false,
                        false,
                        touch_mut
                    );
                    gen_chunks_mut_memory_step!(check_next_memory_safety, $ty, next, false);
                    gen_chunks_mut_memory_step!(check_nth_memory_safety, $ty, nth, false);
                    gen_chunks_mut_memory_step!(
                        check_next_back_memory_safety,
                        $ty,
                        next_back,
                        true
                    );
                    gen_chunks_mut_memory_step!(check_nth_back_memory_safety, $ty, nth_back, true);
                    gen_chunks_mut_memory_step!(
                        check_nth_back_memory_empty,
                        $ty,
                        nth_back,
                        true,
                        empty
                    );
                    gen_chunks_mut_memory_step!(
                        check_nth_back_memory_exhausted,
                        $ty,
                        nth_back,
                        true,
                        exhausted
                    );
                    gen_chunks_mut_memory_step!(
                        check_nth_back_memory_present,
                        $ty,
                        nth_back,
                        true,
                        present
                    );
                }
                mod chunks_exact {
                    use super::*;
                    gen_chunk_methods!(
                        $ty,
                        ChunksExact,
                        as_slice,
                        as_ptr,
                        false,
                        true,
                        touch_shared
                    );
                    gen_exact_constructor!($ty, ChunksExact, as_slice, as_ptr, false);
                    gen_shared_clone_protocol!($ty, ChunksExact, false, true);
                }
                mod chunks_exact_mut {
                    use super::*;
                    gen_chunk_methods!(
                        $ty,
                        ChunksExactMut,
                        as_mut_slice,
                        as_mut_ptr,
                        false,
                        true,
                        touch_mut
                    );
                    gen_exact_mut_memory_methods!($ty, ChunksExactMut, false);
                    gen_exact_constructor!($ty, ChunksExactMut, as_mut_slice, as_mut_ptr, false);
                }
                mod rchunks {
                    use super::*;
                    gen_chunk_methods!($ty, RChunks, as_slice, as_ptr, true, false, touch_shared);
                    gen_chunk_memory_step!(
                        check_next_memory_safety,
                        $ty,
                        RChunks,
                        next,
                        as_slice,
                        as_ptr,
                        true,
                        false,
                        false,
                        touch_shared
                    );
                    gen_chunk_memory_step!(
                        check_next_back_memory_safety,
                        $ty,
                        RChunks,
                        next_back,
                        as_slice,
                        as_ptr,
                        true,
                        true,
                        false,
                        touch_shared
                    );
                    gen_shared_clone_protocol!($ty, RChunks, true, false);
                }
                mod rchunks_mut {
                    use super::*;
                    gen_chunk_methods!(
                        $ty,
                        RChunksMut,
                        as_mut_slice,
                        as_mut_ptr,
                        true,
                        false,
                        touch_mut
                    );
                    gen_chunk_memory_step!(
                        check_next_memory_safety,
                        $ty,
                        RChunksMut,
                        next,
                        as_mut_slice,
                        as_mut_ptr,
                        true,
                        false,
                        true,
                        touch_mut
                    );
                    gen_chunk_memory_step!(
                        check_nth_memory_safety,
                        $ty,
                        RChunksMut,
                        nth,
                        as_mut_slice,
                        as_mut_ptr,
                        true,
                        false,
                        true,
                        touch_mut
                    );
                    gen_chunk_memory_step!(
                        check_next_back_memory_safety,
                        $ty,
                        RChunksMut,
                        next_back,
                        as_mut_slice,
                        as_mut_ptr,
                        true,
                        true,
                        true,
                        touch_mut
                    );
                    gen_chunk_memory_step!(
                        check_nth_back_memory_safety,
                        $ty,
                        RChunksMut,
                        nth_back,
                        as_mut_slice,
                        as_mut_ptr,
                        true,
                        true,
                        true,
                        touch_mut
                    );
                    gen_rchunks_mut_last_memory!($ty);
                    gen_chunk_last!($ty, RChunksMut, as_mut_slice, as_mut_ptr, true, touch_mut);
                }
                mod rchunks_exact {
                    use super::*;
                    gen_chunk_methods!(
                        $ty,
                        RChunksExact,
                        as_slice,
                        as_ptr,
                        true,
                        true,
                        touch_shared
                    );
                    gen_exact_constructor!($ty, RChunksExact, as_slice, as_ptr, true);
                    gen_shared_clone_protocol!($ty, RChunksExact, true, true);
                }
                mod rchunks_exact_mut {
                    use super::*;
                    gen_chunk_methods!(
                        $ty,
                        RChunksExactMut,
                        as_mut_slice,
                        as_mut_ptr,
                        true,
                        true,
                        touch_mut
                    );
                    gen_exact_mut_memory_methods!($ty, RChunksExactMut, true);
                    gen_exact_constructor!($ty, RChunksExactMut, as_mut_slice, as_mut_ptr, true);
                }
                mod array_windows_1 {
                    use super::*;
                    gen_array_windows!($ty, 1);
                }
                mod array_windows_2 {
                    use super::*;
                    gen_array_windows!($ty, 2);
                }
                mod array_windows_4 {
                    use super::*;
                    gen_array_windows!($ty, 4);
                }
                mod splitn {
                    use super::*;
                    gen_splitn!($ty, splitn, as_slice, touch_shared);
                }
                mod rsplitn {
                    use super::*;
                    gen_splitn!($ty, rsplitn, as_slice, touch_shared);
                }
                mod splitn_mut {
                    use super::*;
                    gen_splitn!($ty, splitn_mut, as_mut_slice, touch_mut);
                }
                mod rsplitn_mut {
                    use super::*;
                    gen_splitn!($ty, rsplitn_mut, as_mut_slice, touch_mut);
                }
            }
        };
    }

    gen_type_suite!(unit, ());
    gen_type_suite!(byte, u8);
    gen_type_suite!(boolean, bool);
    gen_type_suite!(character, char);
    gen_type_suite!(padded, (char, u8));
    gen_type_suite!(aligned_zst, AlignedZst);
    gen_type_suite!(aligned_word, AlignedWord);
}
