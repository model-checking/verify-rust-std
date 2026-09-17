// Source projection checked by check_sources.py. Do not edit manually.

use crate::mem::MaybeUninit;

use crate::{fmt, ptr};

struct Buffer<T, const N: usize> {
    // Invariant: `self.buffer[self.start..self.start + N]` is initialized,
    // with all other elements being uninitialized. This also
    // implies that `self.start <= N`.
    buffer: [[MaybeUninit<T>; N]; 2],
    start: usize,
}

impl<T, const N: usize> Buffer<T, N> {

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
