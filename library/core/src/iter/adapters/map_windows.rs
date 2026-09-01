use crate::iter::FusedIterator;
#[cfg(kani)]
use crate::kani;
use crate::mem::MaybeUninit;
use crate::ub_checks::Invariant;
use crate::{fmt, ptr};

/// An iterator over the mapped windows of another iterator.
///
/// This `struct` is created by the [`Iterator::map_windows`]. See its
/// documentation for more information.
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[unstable(feature = "iter_map_windows", reason = "recently added", issue = "87155")]
pub struct MapWindows<I: Iterator, F, const N: usize> {
    f: F,
    inner: MapWindowsInner<I, N>,
}

struct MapWindowsInner<I: Iterator, const N: usize> {
    // We fuse the inner iterator because there shouldn't be "holes" in
    // the sliding window. Once the iterator returns a `None`, we make
    // our `MapWindows` iterator return `None` forever.
    iter: Option<I>,
    // Since iterators are assumed lazy, i.e. it only yields an item when
    // `Iterator::next()` is called, and `MapWindows` is not an exception.
    //
    // Before the first iteration, we keep the buffer `None`. When the user
    // first call `next` or other methods that makes the iterator advance,
    // we collect the first `N` items yielded from the inner iterator and
    // put it into the buffer.
    //
    // When the inner iterator has returned a `None` (i.e. fused), we take
    // away this `buffer` and leave it `None` to reclaim its resources.
    //
    // FIXME: should we shrink the size of `buffer` using niche optimization?
    buffer: Option<Buffer<I::Item, N>>,
}

// `Buffer` uses two times of space to reduce moves among the iterations.
// `Buffer<T, N>` is semantically `[MaybeUninit<T>; 2 * N]`. However, due
// to limitations of const generics, we use this different type. Note that
// it has the same underlying memory layout.
struct Buffer<T, const N: usize> {
    // Invariant: `self.buffer[self.start..self.start + N]` is initialized,
    // with all other elements being uninitialized. This also
    // implies that `self.start <= N`.
    buffer: [[MaybeUninit<T>; N]; 2],
    start: usize,
}

impl<I: Iterator, F, const N: usize> MapWindows<I, F, N> {
    pub(in crate::iter) fn new(iter: I, f: F) -> Self {
        assert!(N != 0, "array in `Iterator::map_windows` must contain more than 0 elements");

        // Only ZST arrays' length can be so large.
        if size_of::<I::Item>() == 0 {
            assert!(
                N.checked_mul(2).is_some(),
                "array size of `Iterator::map_windows` is too large"
            );
        }

        Self { inner: MapWindowsInner::new(iter), f }
    }
}

impl<I: Iterator, const N: usize> MapWindowsInner<I, N> {
    #[inline]
    fn new(iter: I) -> Self {
        Self { iter: Some(iter), buffer: None }
    }

    fn next_window(&mut self) -> Option<&[I::Item; N]> {
        let iter = self.iter.as_mut()?;
        match self.buffer {
            // It is the first time to advance. We collect
            // the first `N` items from `self.iter` to initialize `self.buffer`.
            None => self.buffer = Buffer::try_from_iter(iter),
            Some(ref mut buffer) => match iter.next() {
                None => {
                    // Fuse the inner iterator since it yields a `None`.
                    self.iter.take();
                    self.buffer.take();
                }
                // Advance the iterator. We first call `next` before changing our buffer
                // at all. This means that if `next` panics, our invariant is upheld and
                // our `Drop` impl drops the correct elements.
                Some(item) => buffer.push(item),
            },
        }
        self.buffer.as_ref().map(Buffer::as_array_ref)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(ref iter) = self.iter else { return (0, Some(0)) };
        let (lo, hi) = iter.size_hint();
        if self.buffer.is_some() {
            // If the first `N` items are already yielded by the inner iterator,
            // the size hint is then equal to the that of the inner iterator's.
            (lo, hi)
        } else {
            // If the first `N` items are not yet yielded by the inner iterator,
            // the first `N` elements should be counted as one window, so both bounds
            // should subtract `N - 1`.
            (lo.saturating_sub(N - 1), hi.map(|hi| hi.saturating_sub(N - 1)))
        }
    }
}

impl<T, const N: usize> Buffer<T, N> {
    fn try_from_iter(iter: &mut impl Iterator<Item = T>) -> Option<Self> {
        let first_half = crate::array::iter_next_chunk(iter).ok()?;
        let buffer =
            [MaybeUninit::new(first_half).transpose(), [const { MaybeUninit::uninit() }; N]];
        Some(Self { buffer, start: 0 })
    }

    #[inline]
    fn buffer_ptr(&self) -> *const MaybeUninit<T> {
        self.buffer.as_ptr().cast()
    }

    #[inline]
    fn buffer_mut_ptr(&mut self) -> *mut MaybeUninit<T> {
        self.buffer.as_mut_ptr().cast()
    }

    #[inline]
    fn as_array_ref(&self) -> &[T; N] {
        debug_assert!(self.start + N <= 2 * N);

        // SAFETY: our invariant guarantees these elements are initialized.
        unsafe { &*self.buffer_ptr().add(self.start).cast() }
    }

    #[inline]
    fn as_uninit_array_mut(&mut self) -> &mut MaybeUninit<[T; N]> {
        debug_assert!(self.start + N <= 2 * N);

        // SAFETY: our invariant guarantees these elements are in bounds.
        unsafe { &mut *self.buffer_mut_ptr().add(self.start).cast() }
    }

    /// Pushes a new item `next` to the back, and pops the front-most one.
    ///
    /// All the elements will be shifted to the front end when pushing reaches
    /// the back end.
    fn push(&mut self, next: T) {
        let buffer_mut_ptr = self.buffer_mut_ptr();
        debug_assert!(self.start + N <= 2 * N);

        let to_drop = if self.start == N {
            // We have reached the end of our buffer and have to copy
            // everything to the start. Example layout for N = 3.
            //
            //    0   1   2   3   4   5            0   1   2   3   4   5
            //  ┌───┬───┬───┬───┬───┬───┐        ┌───┬───┬───┬───┬───┬───┐
            //  │ - │ - │ - │ a │ b │ c │   ->   │ b │ c │ n │ - │ - │ - │
            //  └───┴───┴───┴───┴───┴───┘        └───┴───┴───┴───┴───┴───┘
            //                ↑                    ↑
            //              start                start

            // SAFETY: the two pointers are valid for reads/writes of N -1
            // elements because our array's size is semantically 2 * N. The
            // regions also don't overlap for the same reason.
            //
            // We leave the old elements in place. As soon as `start` is set
            // to 0, we treat them as uninitialized and treat their copies
            // as initialized.
            let to_drop = unsafe {
                ptr::copy_nonoverlapping(buffer_mut_ptr.add(self.start + 1), buffer_mut_ptr, N - 1);
                (*buffer_mut_ptr.add(N - 1)).write(next);
                buffer_mut_ptr.add(self.start)
            };
            self.start = 0;
            to_drop
        } else {
            // SAFETY: `self.start` is < N as guaranteed by the invariant
            // plus the check above. Even if the drop at the end panics,
            // the invariant is upheld.
            //
            // Example layout for N = 3:
            //
            //    0   1   2   3   4   5            0   1   2   3   4   5
            //  ┌───┬───┬───┬───┬───┬───┐        ┌───┬───┬───┬───┬───┬───┐
            //  │ - │ a │ b │ c │ - │ - │   ->   │ - │ - │ b │ c │ n │ - │
            //  └───┴───┴───┴───┴───┴───┘        └───┴───┴───┴───┴───┴───┘
            //        ↑                                    ↑
            //      start                                start
            //
            let to_drop = unsafe {
                (*buffer_mut_ptr.add(self.start + N)).write(next);
                buffer_mut_ptr.add(self.start)
            };
            self.start += 1;
            to_drop
        };

        // SAFETY: the index is valid and this is element `a` in the
        // diagram above and has not been dropped yet.
        unsafe { ptr::drop_in_place(to_drop.cast_init()) };
    }
}

impl<T: Clone, const N: usize> Clone for Buffer<T, N> {
    fn clone(&self) -> Self {
        let mut buffer = Buffer {
            buffer: [[const { MaybeUninit::uninit() }; N], [const { MaybeUninit::uninit() }; N]],
            start: self.start,
        };
        buffer.as_uninit_array_mut().write(self.as_array_ref().clone());
        buffer
    }
}

impl<I, const N: usize> Clone for MapWindowsInner<I, N>
where
    I: Iterator + Clone,
    I::Item: Clone,
{
    fn clone(&self) -> Self {
        Self { iter: self.iter.clone(), buffer: self.buffer.clone() }
    }
}

impl<T, const N: usize> Drop for Buffer<T, N> {
    fn drop(&mut self) {
        // SAFETY: our invariant guarantees that N elements starting from
        // `self.start` are initialized. We drop them here.
        unsafe {
            let initialized_part: *mut [T] = crate::ptr::slice_from_raw_parts_mut(
                self.buffer_mut_ptr().add(self.start).cast(),
                N,
            );
            ptr::drop_in_place(initialized_part);
        }
    }
}

#[unstable(feature = "iter_map_windows", reason = "recently added", issue = "87155")]
impl<I, F, R, const N: usize> Iterator for MapWindows<I, F, N>
where
    I: Iterator,
    F: FnMut(&[I::Item; N]) -> R,
{
    type Item = R;

    fn next(&mut self) -> Option<Self::Item> {
        let window = self.inner.next_window()?;
        let out = (self.f)(window);
        Some(out)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// Note that even if the inner iterator not fused, the `MapWindows` is still fused,
// because we don't allow "holes" in the mapping window.
#[unstable(feature = "iter_map_windows", reason = "recently added", issue = "87155")]
impl<I, F, R, const N: usize> FusedIterator for MapWindows<I, F, N>
where
    I: Iterator,
    F: FnMut(&[I::Item; N]) -> R,
{
}

#[unstable(feature = "iter_map_windows", reason = "recently added", issue = "87155")]
impl<I, F, R, const N: usize> ExactSizeIterator for MapWindows<I, F, N>
where
    I: ExactSizeIterator,
    F: FnMut(&[I::Item; N]) -> R,
{
}

#[unstable(feature = "iter_map_windows", reason = "recently added", issue = "87155")]
impl<I: Iterator + fmt::Debug, F, const N: usize> fmt::Debug for MapWindows<I, F, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MapWindows").field("iter", &self.inner.iter).finish()
    }
}

#[unstable(feature = "iter_map_windows", reason = "recently added", issue = "87155")]
impl<I, F, const N: usize> Clone for MapWindows<I, F, N>
where
    I: Iterator + Clone,
    F: Clone,
    I::Item: Clone,
{
    fn clone(&self) -> Self {
        Self { f: self.f.clone(), inner: self.inner.clone() }
    }
}

#[unstable(feature = "ub_checks", issue = "none")]
impl<T, const N: usize> Invariant for Buffer<T, N> {
    fn is_safe(&self) -> bool {
        self.start + N <= 2 * N
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    fn any_buffer<T: Copy + kani::Arbitrary, const N: usize>() -> (Buffer<T, N>, [T; N]) {
        // Symbolize a valid starting position for the active window.
        let start = kani::any_where(|start: &usize| *start <= N);

        // Symbolize the values that occupy the active window.
        let values: [T; N] = kani::any();
        let mut storage = [[MaybeUninit::uninit(); N]; 2];

        // Initialize exactly storage[start .. start + N] without raw pointers.
        for offset in 0..N {
            let index = start + offset;
            if index < N {
                storage[0][index].write(values[offset]);
            } else {
                storage[1][index - N].write(values[offset]);
            }
        }

        (Buffer { buffer: storage, start }, values)
    }

    // Harnesses for `as_array_ref` for Buffer
    macro_rules! generate_buffer_as_array_ref_harness {
        ($name:ident, $ty:ty, $n:expr) => {
            #[kani::proof]
            fn $name() {
                // Build a symbolic Buffer satisfying its representation invariant.
                let (buffer, expected) = any_buffer::<$ty, $n>();

                // Call the safe function under test.
                let window = buffer.as_array_ref();
            }
        };
    }

    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_u8_n1, u8, 1);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_u8_n2, u8, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_u8_n4, u8, 4);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_u16, u16, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_u32, u32, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_u64, u64, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_u128, u128, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_i8, i8, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_i16, i16, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_i32, i32, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_i64, i64, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_i128, i128, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_bool, bool, 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_unit, (), 2);
    generate_buffer_as_array_ref_harness!(harness_buffer_as_array_ref_array, [u8; 4], 2);

    // Harnesses for `as_uninit_array_mut` for Buffer
    macro_rules! generate_buffer_as_uninit_array_mut_harness {
        ($name:ident, $ty:ty, $n:expr) => {
            #[kani::proof]
            fn $name() {
                // Build a valid symbolic Buffer without raw pointers.
                let (mut buffer, _) = any_buffer::<$ty, $n>();

                // Symbolize a fully initialized replacement window.
                let replacement: [$ty; $n] = kani::any();

                // Write through the safe function's returned MaybeUninit reference.
                buffer.as_uninit_array_mut().write(replacement);
            }
        };
    }

    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_u8_n1, u8, 1);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_u8_n2, u8, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_u8_n4, u8, 4);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_u16, u16, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_u32, u32, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_u64, u64, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_u128, u128, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_i8, i8, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_i16, i16, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_i32, i32, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_i64, i64, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_i128, i128, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_bool, bool, 2);
    generate_buffer_as_uninit_array_mut_harness!(harness_buffer_as_uninit_array_mut_unit, (), 2);
    generate_buffer_as_uninit_array_mut_harness!(
        harness_buffer_as_uninit_array_mut_array,
        [u8; 4],
        2
    );

    // Harnesses for `push` for Buffer.
    macro_rules! generate_buffer_push_harness {
        ($name:ident, $ty:ty, $n:expr) => {
            #[kani::proof]
            fn $name() {
                // Build a valid Buffer with a symbolic active-window position.
                let (mut buffer, before) = any_buffer::<$ty, $n>();
                // Symbolize the item appended to the window.
                let next: $ty = kani::any();
                // Call the safe function under test.
                buffer.push(next);
            }
        };
    }

    generate_buffer_push_harness!(harness_buffer_push_u8_n1, u8, 1);
    generate_buffer_push_harness!(harness_buffer_push_u8_n2, u8, 2);
    generate_buffer_push_harness!(harness_buffer_push_u8_n4, u8, 4);
    generate_buffer_push_harness!(harness_buffer_push_u16, u16, 2);
    generate_buffer_push_harness!(harness_buffer_push_u32, u32, 2);
    generate_buffer_push_harness!(harness_buffer_push_u64, u64, 2);
    generate_buffer_push_harness!(harness_buffer_push_u128, u128, 2);
    generate_buffer_push_harness!(harness_buffer_push_i8, i8, 2);
    generate_buffer_push_harness!(harness_buffer_push_i16, i16, 2);
    generate_buffer_push_harness!(harness_buffer_push_i32, i32, 2);
    generate_buffer_push_harness!(harness_buffer_push_i64, i64, 2);
    generate_buffer_push_harness!(harness_buffer_push_i128, i128, 2);
    generate_buffer_push_harness!(harness_buffer_push_bool, bool, 2);
    generate_buffer_push_harness!(harness_buffer_push_unit, (), 2);
    generate_buffer_push_harness!(harness_buffer_push_array, [u8; 4], 2);

    // Harnesses for `Drop::drop` for Buffer.
    macro_rules! generate_buffer_drop_harness {
        ($name:ident, $ty:ty, $n:expr) => {
            #[kani::proof]
            fn $name() {
                // Build a valid Buffer with a symbolic active-window position.
                let (buffer, _) = any_buffer::<$ty, $n>();

                // Invoke Buffer::drop through the safe drop function.
                crate::mem::drop(buffer);
            }
        };
    }

    generate_buffer_drop_harness!(harness_buffer_drop_u8_n1, u8, 1);
    generate_buffer_drop_harness!(harness_buffer_drop_u8_n2, u8, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_u8_n4, u8, 4);
    generate_buffer_drop_harness!(harness_buffer_drop_u16, u16, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_u32, u32, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_u64, u64, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_u128, u128, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_i8, i8, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_i16, i16, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_i32, i32, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_i64, i64, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_i128, i128, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_bool, bool, 2);
    generate_buffer_drop_harness!(harness_buffer_drop_unit, (), 2);
    generate_buffer_drop_harness!(harness_buffer_drop_array, [u8; 4], 2);
}
