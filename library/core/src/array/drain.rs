<<<<<<< HEAD
use safety::requires;

use crate::iter::{TrustedLen, UncheckedIterator};
#[cfg(kani)]
use crate::kani;
use crate::mem::ManuallyDrop;
use crate::ptr::drop_in_place;
use crate::slice;
=======
use crate::marker::{Destruct, PhantomData};
use crate::mem::{ManuallyDrop, SizedTypeProperties, conjure_zst};
use crate::ptr::{NonNull, drop_in_place, from_raw_parts_mut, null_mut};
>>>>>>> subtree/library

impl<'l, 'f, T, U, const N: usize, F: FnMut(T) -> U> Drain<'l, 'f, T, N, F> {
    /// This function returns a function that lets you index the given array in const.
    /// As implemented it can optimize better than iterators, and can be constified.
    /// It acts like a sort of guard (owns the array) and iterator combined, which can be implemented
    /// as it is a struct that implements const fn;
    /// in that regard it is somewhat similar to an array::Iter implementing `UncheckedIterator`.
    /// The only method you're really allowed to call is `next()`,
    /// anything else is more or less UB, hence this function being unsafe.
    /// Moved elements will not be dropped.
    /// This will also not actually store the array.
    ///
    /// SAFETY: must only be called `N` times. Thou shalt not drop the array either.
    // FIXME(const-hack): this is a hack for `let guard = Guard(array); |i| f(guard[i])`.
    #[rustc_const_unstable(feature = "array_try_map", issue = "79711")]
    pub(super) const unsafe fn new(array: &'l mut ManuallyDrop<[T; N]>, f: &'f mut F) -> Self {
        // dont drop the array, transfers "ownership" to Self
        let ptr: NonNull<T> = NonNull::from_mut(array).cast();
        // SAFETY:
        // Adding `slice.len()` to the starting pointer gives a pointer
        // at the end of `slice`. `end` will never be dereferenced, only checked
        // for direct pointer equality with `ptr` to check if the drainer is done.
        unsafe {
            let end = if T::IS_ZST { null_mut() } else { ptr.as_ptr().add(N) };
            Self { ptr, end, f, l: PhantomData }
        }
    }
}

/// See [`Drain::new`]; this is our fake iterator.
#[rustc_const_unstable(feature = "array_try_map", issue = "79711")]
#[unstable(feature = "array_try_map", issue = "79711")]
pub(super) struct Drain<'l, 'f, T, const N: usize, F> {
    // FIXME(const-hack): This is essentially a slice::IterMut<'static>, replace when possible.
    /// The pointer to the next element to return, or the past-the-end location
    /// if the drainer is empty.
    ///
    /// This address will be used for all ZST elements, never changed.
    /// As we "own" this array, we dont need to store any lifetime.
    ptr: NonNull<T>,
    /// For non-ZSTs, the non-null pointer to the past-the-end element.
    /// For ZSTs, this is null.
    end: *mut T,

    f: &'f mut F,
    l: PhantomData<&'l mut [T; N]>,
}

#[rustc_const_unstable(feature = "array_try_map", issue = "79711")]
#[unstable(feature = "array_try_map", issue = "79711")]
impl<T, U, const N: usize, F> const FnOnce<(usize,)> for &mut Drain<'_, '_, T, N, F>
where
    F: [const] FnMut(T) -> U,
{
    type Output = U;

    /// This implementation is useless.
    extern "rust-call" fn call_once(mut self, args: (usize,)) -> Self::Output {
        self.call_mut(args)
    }
}
#[rustc_const_unstable(feature = "array_try_map", issue = "79711")]
#[unstable(feature = "array_try_map", issue = "79711")]
impl<T, U, const N: usize, F> const FnMut<(usize,)> for &mut Drain<'_, '_, T, N, F>
where
    F: [const] FnMut(T) -> U,
{
    // FIXME(const-hack): ideally this would be an unsafe fn `next()`, and to use it you would instead `|_| unsafe { drain.next() }`.
    extern "rust-call" fn call_mut(
        &mut self,
        (_ /* ignore argument */,): (usize,),
    ) -> Self::Output {
        if T::IS_ZST {
            // its UB to call this more than N times, so returning more ZSTs is valid.
            // SAFETY: its a ZST? we conjur.
            (self.f)(unsafe { conjure_zst::<T>() })
        } else {
            // increment before moving; if `f` panics, we drop the rest.
            let p = self.ptr;
            // SAFETY: caller guarantees never called more than N times (see `Drain::new`)
            self.ptr = unsafe { self.ptr.add(1) };
            // SAFETY: we are allowed to move this.
            (self.f)(unsafe { p.read() })
        }
    }
}
#[rustc_const_unstable(feature = "array_try_map", issue = "79711")]
#[unstable(feature = "array_try_map", issue = "79711")]
impl<T: [const] Destruct, const N: usize, F> const Drop for Drain<'_, '_, T, N, F> {
    fn drop(&mut self) {
<<<<<<< HEAD
        // SAFETY: By the type invariant, we're allowed to drop all these.
        unsafe { drop_in_place(self.0.as_mut_slice()) }
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        let p: *const T = self.0.next()?;
        // SAFETY: The iterator was already advanced, so we won't drop this later.
        Some(unsafe { p.read() })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.len();
        (n, Some(n))
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }
}

// SAFETY: This is a 1:1 wrapper for a slice iterator, which is also `TrustedLen`.
unsafe impl<T> TrustedLen for Drain<'_, T> {}

impl<T> UncheckedIterator for Drain<'_, T> {
    #[requires(self.0.len() > 0)]
    unsafe fn next_unchecked(&mut self) -> T {
        // SAFETY: `Drain` is 1:1 with the inner iterator, so if the caller promised
        // that there's an element left, the inner iterator has one too.
        let p: *const T = unsafe { self.0.next_unchecked() };
        // SAFETY: The iterator was already advanced, so we won't drop this later.
        unsafe { p.read() }
=======
        if !T::IS_ZST {
            // SAFETY: we cant read more than N elements
            let slice = unsafe {
                from_raw_parts_mut::<[T]>(
                    self.ptr.as_ptr(),
                    // SAFETY: `start <= end`
                    self.end.offset_from_unsigned(self.ptr.as_ptr()),
                )
            };

            // SAFETY: By the type invariant, we're allowed to drop all these. (we own it, after all)
            unsafe { drop_in_place(slice) }
        }
>>>>>>> subtree/library
    }
}
