//! This module contains a variety of sort implementations that are optimized for small lengths.

use crate::mem::{self, ManuallyDrop, MaybeUninit};
use crate::slice::sort::shared::FreezeMarker;
use crate::{hint, intrinsics, ptr, slice};

// It's important to differentiate between SMALL_SORT_THRESHOLD performance for
// small slices and small-sort performance sorting small sub-slices as part of
// the main quicksort loop. For the former, testing showed that the
// representative benchmarks for real-world performance are cold CPU state and
// not single-size hot benchmarks. For the latter the CPU will call them many
// times, so hot benchmarks are fine and more realistic. And it's worth it to
// optimize sorting small sub-slices with more sophisticated solutions than
// insertion sort.

/// Using a trait allows us to specialize on `Freeze` which in turn allows us to make safe
/// abstractions.
pub(crate) trait StableSmallSortTypeImpl: Sized {
    /// For which input length <= return value of this function, is it valid to call `small_sort`.
    fn small_sort_threshold() -> usize;

    /// Sorts `v` using strategies optimized for small sizes.
    fn small_sort<F: FnMut(&Self, &Self) -> bool>(
        v: &mut [Self],
        scratch: &mut [MaybeUninit<Self>],
        is_less: &mut F,
    );
}

impl<T> StableSmallSortTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        // Optimal number of comparisons, and good perf.
        SMALL_SORT_FALLBACK_THRESHOLD
    }

    #[inline(always)]
    default fn small_sort<F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        _scratch: &mut [MaybeUninit<T>],
        is_less: &mut F,
    ) {
        if v.len() >= 2 {
            insertion_sort_shift_left(v, 1, is_less);
        }
    }
}

impl<T: FreezeMarker> StableSmallSortTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        SMALL_SORT_GENERAL_THRESHOLD
    }

    #[inline(always)]
    fn small_sort<F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        scratch: &mut [MaybeUninit<T>],
        is_less: &mut F,
    ) {
        small_sort_general_with_scratch(v, scratch, is_less);
    }
}

/// Using a trait allows us to specialize on `Freeze` which in turn allows us to make safe
/// abstractions.
pub(crate) trait UnstableSmallSortTypeImpl: Sized {
    /// For which input length <= return value of this function, is it valid to call `small_sort`.
    fn small_sort_threshold() -> usize;

    /// Sorts `v` using strategies optimized for small sizes.
    fn small_sort<F: FnMut(&Self, &Self) -> bool>(v: &mut [Self], is_less: &mut F);
}

impl<T> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        SMALL_SORT_FALLBACK_THRESHOLD
    }

    #[inline(always)]
    default fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        small_sort_fallback(v, is_less);
    }
}

impl<T: FreezeMarker> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        <T as UnstableSmallSortFreezeTypeImpl>::small_sort_threshold()
    }

    #[inline(always)]
    fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        <T as UnstableSmallSortFreezeTypeImpl>::small_sort(v, is_less);
    }
}

/// FIXME(const_trait_impl) use original ipnsort approach with choose_unstable_small_sort,
/// as found here <https://github.com/Voultapher/sort-research-rs/blob/438fad5d0495f65d4b72aa87f0b62fc96611dff3/ipnsort/src/smallsort.rs#L83C10-L83C36>.
pub(crate) trait UnstableSmallSortFreezeTypeImpl: Sized + FreezeMarker {
    fn small_sort_threshold() -> usize;

    fn small_sort<F: FnMut(&Self, &Self) -> bool>(v: &mut [Self], is_less: &mut F);
}

impl<T: FreezeMarker> UnstableSmallSortFreezeTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            SMALL_SORT_GENERAL_THRESHOLD
        } else {
            SMALL_SORT_FALLBACK_THRESHOLD
        }
    }

    #[inline(always)]
    default fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            small_sort_general(v, is_less);
        } else {
            small_sort_fallback(v, is_less);
        }
    }
}

/// SAFETY: Only used for run-time optimization heuristic.
#[rustc_unsafe_specialization_marker]
trait CopyMarker {}

impl<T: Copy> CopyMarker for T {}

impl<T: FreezeMarker + CopyMarker> UnstableSmallSortFreezeTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        if has_efficient_in_place_swap::<T>()
            && (size_of::<T>() * SMALL_SORT_NETWORK_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE
        {
            SMALL_SORT_NETWORK_THRESHOLD
        } else if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            SMALL_SORT_GENERAL_THRESHOLD
        } else {
            SMALL_SORT_FALLBACK_THRESHOLD
        }
    }

    #[inline(always)]
    fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        if has_efficient_in_place_swap::<T>()
            && (size_of::<T>() * SMALL_SORT_NETWORK_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE
        {
            small_sort_network(v, is_less);
        } else if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            small_sort_general(v, is_less);
        } else {
            small_sort_fallback(v, is_less);
        }
    }
}

/// Optimal number of comparisons, and good perf.
const SMALL_SORT_FALLBACK_THRESHOLD: usize = 16;

/// From a comparison perspective 20 was ~2% more efficient for fully random input, but for
/// wall-clock performance choosing 32 yielded better performance overall.
///
/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
const SMALL_SORT_GENERAL_THRESHOLD: usize = 32;

/// [`small_sort_general`] uses [`sort8_stable`] as primitive and does a kind of ping-pong merge,
/// where the output of the first two [`sort8_stable`] calls is stored at the end of the scratch
/// buffer. This simplifies panic handling and avoids additional copies. This affects the required
/// scratch buffer size.
///
/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
pub(crate) const SMALL_SORT_GENERAL_SCRATCH_LEN: usize = SMALL_SORT_GENERAL_THRESHOLD + 16;

/// SAFETY: If you change this value, you have to adjust [`small_sort_network`] !
const SMALL_SORT_NETWORK_THRESHOLD: usize = 32;
const SMALL_SORT_NETWORK_SCRATCH_LEN: usize = SMALL_SORT_NETWORK_THRESHOLD;

/// Using a stack array, could cause a stack overflow if the type `T` is very large. To be
/// conservative we limit the usage of small-sorts that require a stack array to types that fit
/// within this limit.
const MAX_STACK_ARRAY_SIZE: usize = 4096;

fn small_sort_fallback<T, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
    if v.len() >= 2 {
        insertion_sort_shift_left(v, 1, is_less);
    }
}

fn small_sort_general<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
    let mut stack_array = MaybeUninit::<[T; SMALL_SORT_GENERAL_SCRATCH_LEN]>::uninit();

    // SAFETY: The memory is backed by `stack_array`, and the operation is safe as long as the len
    // is the same.
    let scratch = unsafe {
        slice::from_raw_parts_mut(
            stack_array.as_mut_ptr() as *mut MaybeUninit<T>,
            SMALL_SORT_GENERAL_SCRATCH_LEN,
        )
    };

    small_sort_general_with_scratch(v, scratch, is_less);
}

fn small_sort_general_with_scratch<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    is_less: &mut F,
) {
    let len = v.len();
    if len < 2 {
        return;
    }

    if scratch.len() < len + 16 {
        intrinsics::abort();
    }

    let v_base = v.as_mut_ptr();
    let len_div_2 = len / 2;

    // SAFETY: See individual comments.
    unsafe {
        let scratch_base = scratch.as_mut_ptr() as *mut T;

        let presorted_len = if const { size_of::<T>() <= 16 } && len >= 16 {
            // SAFETY: scratch_base is valid and has enough space.
            sort8_stable(v_base, scratch_base, scratch_base.add(len), is_less);
            sort8_stable(
                v_base.add(len_div_2),
                scratch_base.add(len_div_2),
                scratch_base.add(len + 8),
                is_less,
            );

            8
        } else if len >= 8 {
            // SAFETY: scratch_base is valid and has enough space.
            sort4_stable(v_base, scratch_base, is_less);
            sort4_stable(v_base.add(len_div_2), scratch_base.add(len_div_2), is_less);

            4
        } else {
            ptr::copy_nonoverlapping(v_base, scratch_base, 1);
            ptr::copy_nonoverlapping(v_base.add(len_div_2), scratch_base.add(len_div_2), 1);

            1
        };

        for offset in [0, len_div_2] {
            // SAFETY: at this point dst is initialized with presorted_len elements.
            // We extend this to desired_len, src is valid for desired_len elements.
            let src = v_base.add(offset);
            let dst = scratch_base.add(offset);
            let desired_len = if offset == 0 { len_div_2 } else { len - len_div_2 };

            for i in presorted_len..desired_len {
                ptr::copy_nonoverlapping(src.add(i), dst.add(i), 1);
                insert_tail(dst, dst.add(i), is_less);
            }
        }

        // SAFETY: see comment in `CopyOnDrop::drop`.
        let drop_guard = CopyOnDrop { src: scratch_base, dst: v_base, len };

        // SAFETY: at this point scratch_base is fully initialized, allowing us
        // to use it as the source of our merge back into the original array.
        // If a panic occurs we ensure the original array is restored to a valid
        // permutation of the input through drop_guard. This technique is similar
        // to ping-pong merging.
        bidirectional_merge(
            &*ptr::slice_from_raw_parts(drop_guard.src, drop_guard.len),
            drop_guard.dst,
            is_less,
        );
        mem::forget(drop_guard);
    }
}

struct CopyOnDrop<T> {
    src: *const T,
    dst: *mut T,
    len: usize,
}

impl<T> Drop for CopyOnDrop<T> {
    fn drop(&mut self) {
        // SAFETY: `src` must contain `len` initialized elements, and dst must
        // be valid to write `len` elements.
        unsafe {
            ptr::copy_nonoverlapping(self.src, self.dst, self.len);
        }
    }
}

fn small_sort_network<T, F>(v: &mut [T], is_less: &mut F)
where
    T: FreezeMarker,
    F: FnMut(&T, &T) -> bool,
{
    // This implementation is tuned to be efficient for integer types.

    let len = v.len();
    if len < 2 {
        return;
    }

    if len > SMALL_SORT_NETWORK_SCRATCH_LEN {
        intrinsics::abort();
    }

    let mut stack_array = MaybeUninit::<[T; SMALL_SORT_NETWORK_SCRATCH_LEN]>::uninit();

    let len_div_2 = len / 2;
    let no_merge = len < 18;

    let v_base = v.as_mut_ptr();
    let initial_region_len = if no_merge { len } else { len_div_2 };
    // SAFETY: Both possible values of `initial_region_len` are in-bounds.
    let mut region = unsafe { &mut *ptr::slice_from_raw_parts_mut(v_base, initial_region_len) };

    // Avoid compiler unrolling, we *really* don't want that to happen here for binary-size reasons.
    loop {
        let presorted_len = if region.len() >= 13 {
            sort13_optimal(region, is_less);
            13
        } else if region.len() >= 9 {
            sort9_optimal(region, is_less);
            9
        } else {
            1
        };

        insertion_sort_shift_left(region, presorted_len, is_less);

        if no_merge {
            return;
        }

        if region.as_ptr() != v_base {
            break;
        }

        // SAFETY: The right side of `v` based on `len_div_2` is guaranteed in-bounds.
        unsafe {
            region = &mut *ptr::slice_from_raw_parts_mut(v_base.add(len_div_2), len - len_div_2)
        };
    }

    // SAFETY: We checked that T is Freeze and thus observation safe.
    // Should is_less panic v was not modified in parity_merge and retains it's original input.
    // scratch and v must not alias and scratch has v.len() space.
    unsafe {
        let scratch_base = stack_array.as_mut_ptr() as *mut T;
        bidirectional_merge(
            &mut *ptr::slice_from_raw_parts_mut(v_base, len),
            scratch_base,
            is_less,
        );
        ptr::copy_nonoverlapping(scratch_base, v_base, len);
    }
}

/// Swap two values in the slice pointed to by `v_base` at the position `a_pos` and `b_pos` if the
/// value at position `b_pos` is less than the one at position `a_pos`.
///
/// Purposefully not marked `#[inline]`, despite us wanting it to be inlined for integers like
/// types. `is_less` could be a huge function and we want to give the compiler an option to
/// not inline this function. For the same reasons that this function is very perf critical
/// it should be in the same module as the functions that use it.
unsafe fn swap_if_less<T, F>(v_base: *mut T, a_pos: usize, b_pos: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: the caller must guarantee that `a_pos` and `b_pos` each added to `v_base` yield valid
    // pointers into `v_base`, and are properly aligned, and part of the same allocation.
    unsafe {
        let v_a = v_base.add(a_pos);
        let v_b = v_base.add(b_pos);

        // PANIC SAFETY: if is_less panics, no scratch memory was created and the slice should still be
        // in a well defined state, without duplicates.

        // Important to only swap if it is more and not if it is equal. is_less should return false for
        // equal, so we don't swap.
        let should_swap = is_less(&*v_b, &*v_a);

        // This is a branchless version of swap if.
        // The equivalent code with a branch would be:
        //
        // if should_swap {
        //     ptr::swap(v_a, v_b, 1);
        // }

        // The goal is to generate cmov instructions here.
        let v_a_swap = hint::select_unpredictable(should_swap, v_b, v_a);
        let v_b_swap = hint::select_unpredictable(should_swap, v_a, v_b);

        let v_b_swap_tmp = ManuallyDrop::new(ptr::read(v_b_swap));
        ptr::copy(v_a_swap, v_a, 1);
        ptr::copy_nonoverlapping(&*v_b_swap_tmp, v_b, 1);
    }
}

/// Sorts the first 9 elements of `v` with a fast fixed function.
///
/// Should `is_less` generate substantial amounts of code the compiler can choose to not inline
/// `swap_if_less`. If the code of a sort impl changes so as to call this function in multiple
/// places, `#[inline(never)]` is recommended to keep binary-size in check. The current design of
/// `small_sort_network` makes sure to only call this once.
fn sort9_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() < 9 {
        intrinsics::abort();
    }

    let v_base = v.as_mut_ptr();

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 3, is_less);
        swap_if_less(v_base, 1, 7, is_less);
        swap_if_less(v_base, 2, 5, is_less);
        swap_if_less(v_base, 4, 8, is_less);
        swap_if_less(v_base, 0, 7, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 3, 8, is_less);
        swap_if_less(v_base, 5, 6, is_less);
        swap_if_less(v_base, 0, 2, is_less);
        swap_if_less(v_base, 1, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 1, 4, is_less);
        swap_if_less(v_base, 3, 6, is_less);
        swap_if_less(v_base, 5, 7, is_less);
        swap_if_less(v_base, 0, 1, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 3, 5, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 6, 7, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
    }
}

/// Sorts the first 13 elements of `v` with a fast fixed function.
///
/// Should `is_less` generate substantial amounts of code the compiler can choose to not inline
/// `swap_if_less`. If the code of a sort impl changes so as to call this function in multiple
/// places, `#[inline(never)]` is recommended to keep binary-size in check. The current design of
/// `small_sort_network` makes sure to only call this once.
fn sort13_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() < 13 {
        intrinsics::abort();
    }

    let v_base = v.as_mut_ptr();

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 12, is_less);
        swap_if_less(v_base, 1, 10, is_less);
        swap_if_less(v_base, 2, 9, is_less);
        swap_if_less(v_base, 3, 7, is_less);
        swap_if_less(v_base, 5, 11, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 1, 6, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 11, is_less);
        swap_if_less(v_base, 7, 9, is_less);
        swap_if_less(v_base, 8, 10, is_less);
        swap_if_less(v_base, 0, 4, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 6, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 11, 12, is_less);
        swap_if_less(v_base, 4, 6, is_less);
        swap_if_less(v_base, 5, 9, is_less);
        swap_if_less(v_base, 8, 11, is_less);
        swap_if_less(v_base, 10, 12, is_less);
        swap_if_less(v_base, 0, 5, is_less);
        swap_if_less(v_base, 3, 8, is_less);
        swap_if_less(v_base, 4, 7, is_less);
        swap_if_less(v_base, 6, 11, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 0, 1, is_less);
        swap_if_less(v_base, 2, 5, is_less);
        swap_if_less(v_base, 6, 9, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 10, 11, is_less);
        swap_if_less(v_base, 1, 3, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 7, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 6, 7, is_less);
        swap_if_less(v_base, 8, 9, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
    }
}

/// Sorts range [begin, tail] assuming [begin, tail) is already sorted.
///
/// # Safety
/// begin < tail and p must be valid and initialized for all begin <= p <= tail.
unsafe fn insert_tail<T, F: FnMut(&T, &T) -> bool>(begin: *mut T, tail: *mut T, is_less: &mut F) {
    // SAFETY: see individual comments.
    unsafe {
        // SAFETY: in-bounds as tail > begin.
        let mut sift = tail.sub(1);
        if !is_less(&*tail, &*sift) {
            return;
        }

        // SAFETY: after this read tail is never read from again, as we only ever
        // read from sift, sift < tail and we only ever decrease sift. Thus this is
        // effectively a move, not a copy. Should a panic occur, or we have found
        // the correct insertion position, gap_guard ensures the element is moved
        // back into the array.
        let tmp = ManuallyDrop::new(tail.read());
        let mut gap_guard = CopyOnDrop { src: &*tmp, dst: tail, len: 1 };

        loop {
            // SAFETY: we move sift into the gap (which is valid), and point the
            // gap guard destination at sift, ensuring that if a panic occurs the
            // gap is once again filled.
            ptr::copy_nonoverlapping(sift, gap_guard.dst, 1);
            gap_guard.dst = sift;

            if sift == begin {
                break;
            }

            // SAFETY: we checked that sift != begin, thus this is in-bounds.
            sift = sift.sub(1);
            if !is_less(&tmp, &*sift) {
                break;
            }
        }
    }
}

/// Sort `v` assuming `v[..offset]` is already sorted.
pub fn insertion_sort_shift_left<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    offset: usize,
    is_less: &mut F,
) {
    let len = v.len();
    if offset == 0 || offset > len {
        intrinsics::abort();
    }

    // SAFETY: see individual comments.
    unsafe {
        // We write this basic loop directly using pointers, as when we use a
        // for loop LLVM likes to unroll this loop which we do not want.
        // SAFETY: v_end is the one-past-end pointer, and we checked that
        // offset <= len, thus tail is also in-bounds.
        let v_base = v.as_mut_ptr();
        let v_end = v_base.add(len);
        let mut tail = v_base.add(offset);
        while tail != v_end {
            // SAFETY: v_base and tail are both valid pointers to elements, and
            // v_base < tail since we checked offset != 0.
            insert_tail(v_base, tail, is_less);

            // SAFETY: we checked that tail is not yet the one-past-end pointer.
            tail = tail.add(1);
        }
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 4 reads and
/// `dst` is valid for 4 writes. The result will be stored in `dst[0..4]`.
pub unsafe fn sort4_stable<T, F: FnMut(&T, &T) -> bool>(
    v_base: *const T,
    dst: *mut T,
    is_less: &mut F,
) {
    // By limiting select to picking pointers, we are guaranteed good cmov code-gen
    // regardless of type T's size. Further this only does 5 instead of 6
    // comparisons compared to a stable transposition 4 element sorting-network,
    // and always copies each element exactly once.

    // SAFETY: all pointers have offset at most 3 from v_base and dst, and are
    // thus in-bounds by the precondition.
    unsafe {
        // Stably create two pairs a <= b and c <= d.
        let c1 = is_less(&*v_base.add(1), &*v_base);
        let c2 = is_less(&*v_base.add(3), &*v_base.add(2));
        let a = v_base.add(c1 as usize);
        let b = v_base.add(!c1 as usize);
        let c = v_base.add(2 + c2 as usize);
        let d = v_base.add(2 + (!c2 as usize));

        // Compare (a, c) and (b, d) to identify max/min. We're left with two
        // unknown elements, but because we are a stable sort we must know which
        // one is leftmost and which one is rightmost.
        // c3, c4 | min max unknown_left unknown_right
        //  0,  0 |  a   d    b         c
        //  0,  1 |  a   b    c         d
        //  1,  0 |  c   d    a         b
        //  1,  1 |  c   b    a         d
        let c3 = is_less(&*c, &*a);
        let c4 = is_less(&*d, &*b);
        let min = hint::select_unpredictable(c3, c, a);
        let max = hint::select_unpredictable(c4, b, d);
        let unknown_left = hint::select_unpredictable(c3, a, hint::select_unpredictable(c4, c, b));
        let unknown_right = hint::select_unpredictable(c4, d, hint::select_unpredictable(c3, b, c));

        // Sort the last two unknown elements.
        let c5 = is_less(&*unknown_right, &*unknown_left);
        let lo = hint::select_unpredictable(c5, unknown_right, unknown_left);
        let hi = hint::select_unpredictable(c5, unknown_left, unknown_right);

        ptr::copy_nonoverlapping(min, dst, 1);
        ptr::copy_nonoverlapping(lo, dst.add(1), 1);
        ptr::copy_nonoverlapping(hi, dst.add(2), 1);
        ptr::copy_nonoverlapping(max, dst.add(3), 1);
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 8 reads and
/// writes, `scratch_base` and `dst` MUST be valid for 8 writes. The result will
/// be stored in `dst[0..8]`.
unsafe fn sort8_stable<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v_base: *mut T,
    dst: *mut T,
    scratch_base: *mut T,
    is_less: &mut F,
) {
    // SAFETY: these pointers are all in-bounds by the precondition of our function.
    unsafe {
        sort4_stable(v_base, scratch_base, is_less);
        sort4_stable(v_base.add(4), scratch_base.add(4), is_less);
    }

    // SAFETY: scratch_base[0..8] is now initialized, allowing us to merge back
    // into dst.
    unsafe {
        bidirectional_merge(&*ptr::slice_from_raw_parts(scratch_base, 8), dst, is_less);
    }
}

#[inline(always)]
unsafe fn merge_up<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T) {
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.add(1);
    // } else {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.add(1);
    // }
    // dst = dst.add(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        let is_l = !is_less(&*right_src, &*left_src);
        let src = if is_l { left_src } else { right_src };
        ptr::copy_nonoverlapping(src, dst, 1);
        right_src = right_src.add(!is_l as usize);
        left_src = left_src.add(is_l as usize);
        dst = dst.add(1);
    }

    (left_src, right_src, dst)
}

#[inline(always)]
unsafe fn merge_down<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T) {
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.wrapping_sub(1);
    // } else {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.wrapping_sub(1);
    // }
    // dst = dst.sub(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        let is_l = !is_less(&*right_src, &*left_src);
        let src = if is_l { right_src } else { left_src };
        ptr::copy_nonoverlapping(src, dst, 1);
        right_src = right_src.wrapping_sub(is_l as usize);
        left_src = left_src.wrapping_sub(!is_l as usize);
        dst = dst.sub(1);
    }

    (left_src, right_src, dst)
}

/// Merge v assuming v[..len / 2] and v[len / 2..] are sorted.
///
/// Original idea for bi-directional merging by Igor van den Hoven (quadsort),
/// adapted to only use merge up and down. In contrast to the original
/// parity_merge function, it performs 2 writes instead of 4 per iteration.
///
/// # Safety
/// The caller must guarantee that `dst` is valid for v.len() writes.
/// Also `v.as_ptr()` and `dst` must not alias and v.len() must be >= 2.
///
/// Note that T must be Freeze, the comparison function is evaluated on outdated
/// temporary 'copies' that may not end up in the final array.
unsafe fn bidirectional_merge<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v: &[T],
    dst: *mut T,
    is_less: &mut F,
) {
    // It helps to visualize the merge:
    //
    // Initial:
    //
    //  |dst (in dst)
    //  |left               |right
    //  v                   v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //                     ^                   ^
    //                     |left_rev           |right_rev
    //                                         |dst_rev (in dst)
    //
    // After:
    //
    //                      |dst (in dst)
    //        |left         |           |right
    //        v             v           v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //       ^             ^           ^
    //       |left_rev     |           |right_rev
    //                     |dst_rev (in dst)
    //
    // In each iteration one of left or right moves up one position, and one of
    // left_rev or right_rev moves down one position, whereas dst always moves
    // up one position and dst_rev always moves down one position. Assuming
    // the input was sorted and the comparison function is correctly implemented
    // at the end we will have left == left_rev + 1, and right == right_rev + 1,
    // fully consuming the input having written it to dst.

    let len = v.len();
    let src = v.as_ptr();

    let len_div_2 = len / 2;

    // SAFETY: The caller has to ensure that len >= 2.
    unsafe {
        intrinsics::assume(len_div_2 != 0); // This can avoid useless code-gen.
    }

    // SAFETY: no matter what the result of the user-provided comparison function
    // is, all 4 read pointers will always be in-bounds. Writing `dst` and `dst_rev`
    // will always be in bounds if the caller guarantees that `dst` is valid for
    // `v.len()` writes.
    unsafe {
        let mut left = src;
        let mut right = src.add(len_div_2);
        let mut dst = dst;

        let mut left_rev = src.add(len_div_2 - 1);
        let mut right_rev = src.add(len - 1);
        let mut dst_rev = dst.add(len - 1);

        for _ in 0..len_div_2 {
            (left, right, dst) = merge_up(left, right, dst, is_less);
            (left_rev, right_rev, dst_rev) = merge_down(left_rev, right_rev, dst_rev, is_less);
        }

        let left_end = left_rev.wrapping_add(1);
        let right_end = right_rev.wrapping_add(1);

        // Odd length, so one element is left unconsumed in the input.
        if !len.is_multiple_of(2) {
            let left_nonempty = left < left_end;
            let last_src = if left_nonempty { left } else { right };
            ptr::copy_nonoverlapping(last_src, dst, 1);
            left = left.add(left_nonempty as usize);
            right = right.add((!left_nonempty) as usize);
        }

        // We now should have consumed the full input exactly once. This can only fail if the
        // user-provided comparison function fails to implement a strict weak ordering. In that case
        // we panic and never access the inconsistent state in dst.
        if left != left_end || right != right_end {
            panic_on_ord_violation();
        }
    }
}

#[cfg_attr(not(panic = "immediate-abort"), inline(never), cold)]
#[cfg_attr(panic = "immediate-abort", inline)]
fn panic_on_ord_violation() -> ! {
    // This is indicative of a logic bug in the user-provided comparison function or Ord
    // implementation. They are expected to implement a total order as explained in the Ord
    // documentation.
    //
    // By panicking we inform the user, that they have a logic bug in their program. If a strict
    // weak ordering is not given, the concept of comparison based sorting cannot yield a sorted
    // result. E.g.: a < b < c < a
    //
    // The Ord documentation requires users to implement a total order. Arguably that's
    // unnecessarily strict in the context of sorting. Issues only arise if the weaker requirement
    // of a strict weak ordering is violated.
    //
    // The panic message talks about a total order because that's what the Ord documentation talks
    // about and requires, so as to not confuse users.
    panic!("user-provided comparison function does not correctly implement a total order");
}

#[must_use]
pub(crate) const fn has_efficient_in_place_swap<T>() -> bool {
    // Heuristic that holds true on all tested 64-bit capable architectures.
    size_of::<T>() <= 8 // size_of::<u64>()
}

#[unstable(feature = "kani", issue = "none")]
#[cfg(kani)]
mod verify {
    use super::*;
    use crate::cell::Cell;
    use crate::kani;

    // ------------------------------------------------------------------
    // Correctness oracles.
    //
    // Sortedness alone is NOT sorting correctness: an implementation that
    // overwrote the slice with a constant would satisfy it. Every correctness
    // harness below therefore asserts BOTH:
    //   * `assert_sorted`      -- the output is non-decreasing, and
    //   * `assert_permutation` -- the output is a multiset-permutation of the
    //                             input.
    //
    // Both oracles work on arrays of comparison *keys* extracted from the
    // elements, so the same code serves `i32`, `Cell<i32>`, a non-`Copy`
    // wrapper, `u128` and `[u64; 11]`.
    // ------------------------------------------------------------------

    /// Assert `keys` is non-decreasing under the harness comparator (`a < b`).
    fn assert_sorted<K: PartialOrd, const LEN: usize>(keys: &[K; LEN]) {
        for i in 1..LEN {
            assert!(!(keys[i] < keys[i - 1]));
        }
    }

    /// Assert `after` is a permutation of `before`.
    ///
    /// For each value occurring in `before`, the number of occurrences in
    /// `after` must equal the number of occurrences in `before`. Since the two
    /// arrays have the same (const) length, this is exactly multiset equality.
    fn assert_permutation<K: PartialEq, const LEN: usize>(after: &[K; LEN], before: &[K; LEN]) {
        for i in 0..LEN {
            let mut in_after = 0usize;
            let mut in_before = 0usize;
            for j in 0..LEN {
                if after[j] == before[i] {
                    in_after += 1;
                }
                if before[j] == before[i] {
                    in_before += 1;
                }
            }
            assert!(in_after == in_before);
        }
    }

    /// `Freeze` but deliberately not `Copy`, so that it selects the *default*
    /// `UnstableSmallSortFreezeTypeImpl` impl rather than the `CopyMarker` one.
    struct NonCopyI32(i32);

    // ------------------------------------------------------------------
    // Group A: sorting-correctness sweeps over the whole dispatch tree.
    //
    // The small-sort API is bounded by design (`SMALL_SORT_FALLBACK_THRESHOLD`
    // = 16, `SMALL_SORT_GENERAL_THRESHOLD` = `SMALL_SORT_NETWORK_THRESHOLD` =
    // 32), so "arbitrary valid length" is covered by one harness per concrete
    // length in the valid range, each with fully symbolic contents.
    // ------------------------------------------------------------------

    /// `<i32 as StableSmallSortTypeImpl>::small_sort`.
    ///
    /// `i32` is `Freeze`, so this selects the `FreezeMarker` impl ->
    /// `small_sort_general_with_scratch`. The sweep runs to the measured
    /// SAT-tractability frontier (see the PR text) and covers the `len < 2`
    /// no-op, `len < 8` copy-1 + insertion, and `8 <= len` `sort4_stable`-pair
    /// branches, each followed by the per-half insertion sort and
    /// `bidirectional_merge`; the `16 <= len` `sort8_stable`-pair branch is
    /// beyond the composed-proof frontier and its primitive is verified
    /// directly in Group C. Scratch is `SMALL_SORT_GENERAL_SCRATCH_LEN` (48)
    /// long, exactly what the real callers pass.
    macro_rules! check_ss_stable_i32 {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [i32; LEN] = kani::any();
                let before = v;
                let mut scratch: [MaybeUninit<i32>; SMALL_SORT_GENERAL_SCRATCH_LEN] =
                    [const { MaybeUninit::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];

                <i32 as StableSmallSortTypeImpl>::small_sort(
                    &mut v,
                    &mut scratch,
                    &mut |a: &i32, b: &i32| a < b,
                );

                assert_sorted(&v);
                assert_permutation(&v, &before);
            }
        };
    }

    check_ss_stable_i32!(check_ss_stable_i32_len_0, 0, 2);
    check_ss_stable_i32!(check_ss_stable_i32_len_1, 1, 3);
    check_ss_stable_i32!(check_ss_stable_i32_len_2, 2, 4);
    check_ss_stable_i32!(check_ss_stable_i32_len_3, 3, 5);
    check_ss_stable_i32!(check_ss_stable_i32_len_4, 4, 6);
    check_ss_stable_i32!(check_ss_stable_i32_len_5, 5, 7);
    check_ss_stable_i32!(check_ss_stable_i32_len_6, 6, 8);
    check_ss_stable_i32!(check_ss_stable_i32_len_7, 7, 9);
    check_ss_stable_i32!(check_ss_stable_i32_len_8, 8, 10);

    /// `<i32 as UnstableSmallSortTypeImpl>::small_sort`.
    ///
    /// `i32` is `Freeze`, so this goes through the `FreezeMarker` impl, which
    /// delegates to `<i32 as UnstableSmallSortFreezeTypeImpl>::small_sort`.
    /// `i32` is also `Copy` with `size_of` 4, so the `CopyMarker` impl applies
    /// and `has_efficient_in_place_swap::<i32>()` is true -> `small_sort_network`.
    /// The sweep runs to the measured SAT-tractability frontier (see the PR
    /// text): `len < 2` (no-op) and the single-region insertion band; the
    /// `sort9_optimal` band is covered at 8-bit width below and its primitive
    /// directly in Group C, while the `sort13_optimal` and two-region +
    /// `bidirectional_merge` paths are beyond the composed-proof frontier at
    /// any width.
    ///
    /// This harness discharges success criteria 2 and 3 simultaneously.
    macro_rules! check_ss_unstable_i32 {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [i32; LEN] = kani::any();
                let before = v;

                <i32 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &i32, b: &i32| {
                    a < b
                });

                assert_sorted(&v);
                assert_permutation(&v, &before);
            }
        };
    }

    check_ss_unstable_i32!(check_ss_unstable_i32_len_0, 0, 2);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_1, 1, 3);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_2, 2, 4);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_3, 3, 5);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_4, 4, 6);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_5, 5, 7);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_6, 6, 8);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_7, 7, 9);
    check_ss_unstable_i32!(check_ss_unstable_i32_len_8, 8, 10);

    /// `<u8 as UnstableSmallSortTypeImpl>::small_sort` — same `small_sort_network`
    /// path as the `i32` sweep (`u8` is `Copy`+`Freeze`, size 1, efficient swap),
    /// at 8-bit element width.
    ///
    /// Rationale: the `sort9_optimal` swap chain is a comparison network whose
    /// SAT encoding at 32-bit width exceeds the CI budget (see the PR text for
    /// measurements); the network structure is element-width-independent, so
    /// this 8-bit harness carries the `sort9_optimal` region of the dispatch
    /// tree end-to-end, and Group C verifies the primitive directly.
    macro_rules! check_ss_unstable_u8 {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [u8; LEN] = kani::any();
                let before = v;

                <u8 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &u8, b: &u8| a < b);

                assert_sorted(&v);
                assert_permutation(&v, &before);
            }
        };
    }

    check_ss_unstable_u8!(check_ss_unstable_u8_len_9, 9, 11);

    /// `<Cell<i32> as StableSmallSortTypeImpl>::small_sort`.
    ///
    /// `Cell<i32>` is **not** `Freeze`, so this selects the *default*
    /// `StableSmallSortTypeImpl` impl, whose threshold is
    /// `SMALL_SORT_FALLBACK_THRESHOLD` (16) and which runs
    /// `insertion_sort_shift_left(v, 1, ..)` for `len >= 2`.
    macro_rules! check_ss_stable_cell {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [Cell<i32>; LEN] = crate::array::from_fn(|_| Cell::new(kani::any()));
                let before: [i32; LEN] = crate::array::from_fn(|i| v[i].get());
                let mut scratch: [MaybeUninit<Cell<i32>>; SMALL_SORT_GENERAL_SCRATCH_LEN] =
                    [const { MaybeUninit::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];

                <Cell<i32> as StableSmallSortTypeImpl>::small_sort(
                    &mut v,
                    &mut scratch,
                    &mut |a: &Cell<i32>, b: &Cell<i32>| a.get() < b.get(),
                );

                let after: [i32; LEN] = crate::array::from_fn(|i| v[i].get());
                assert_sorted(&after);
                assert_permutation(&after, &before);
            }
        };
    }

    check_ss_stable_cell!(check_ss_stable_cell_len_0, 0, 2);
    check_ss_stable_cell!(check_ss_stable_cell_len_1, 1, 3);
    check_ss_stable_cell!(check_ss_stable_cell_len_2, 2, 4);
    check_ss_stable_cell!(check_ss_stable_cell_len_3, 3, 5);
    check_ss_stable_cell!(check_ss_stable_cell_len_7, 7, 9);

    /// `<Cell<i32> as UnstableSmallSortTypeImpl>::small_sort`.
    ///
    /// `Cell<i32>` is not `Freeze`, so this selects the *default*
    /// `UnstableSmallSortTypeImpl` impl -> `small_sort_fallback` (insertion
    /// sort), with threshold `SMALL_SORT_FALLBACK_THRESHOLD` (16).
    macro_rules! check_ss_unstable_cell {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [Cell<i32>; LEN] = crate::array::from_fn(|_| Cell::new(kani::any()));
                let before: [i32; LEN] = crate::array::from_fn(|i| v[i].get());

                <Cell<i32> as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &Cell<
                    i32,
                >,
                                                                                   b: &Cell<
                    i32,
                >| {
                    a.get() < b.get()
                });

                let after: [i32; LEN] = crate::array::from_fn(|i| v[i].get());
                assert_sorted(&after);
                assert_permutation(&after, &before);
            }
        };
    }

    check_ss_unstable_cell!(check_ss_unstable_cell_len_0, 0, 2);
    check_ss_unstable_cell!(check_ss_unstable_cell_len_1, 1, 3);
    check_ss_unstable_cell!(check_ss_unstable_cell_len_2, 2, 4);
    check_ss_unstable_cell!(check_ss_unstable_cell_len_7, 7, 9);

    /// `<NonCopyI32 as UnstableSmallSortFreezeTypeImpl>::small_sort`.
    ///
    /// `NonCopyI32` is `Freeze` but not `Copy`, so the `CopyMarker`
    /// specialization does not apply and the *default*
    /// `UnstableSmallSortFreezeTypeImpl` impl is used. `size_of` is 4, so
    /// `4 * 48 <= 4096` and the `small_sort_general` branch is taken (threshold
    /// 32). This is the harness for success criterion 3 on the default impl.
    macro_rules! check_ss_unstable_noncopy {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [NonCopyI32; LEN] = crate::array::from_fn(|_| NonCopyI32(kani::any()));
                let before: [i32; LEN] = crate::array::from_fn(|i| v[i].0);

                <NonCopyI32 as UnstableSmallSortFreezeTypeImpl>::small_sort(
                    &mut v,
                    &mut |a: &NonCopyI32, b: &NonCopyI32| a.0 < b.0,
                );

                let after: [i32; LEN] = crate::array::from_fn(|i| v[i].0);
                assert_sorted(&after);
                assert_permutation(&after, &before);
            }
        };
    }

    check_ss_unstable_noncopy!(check_ss_unstable_noncopy_len_0, 0, 2);
    check_ss_unstable_noncopy!(check_ss_unstable_noncopy_len_1, 1, 3);
    check_ss_unstable_noncopy!(check_ss_unstable_noncopy_len_2, 2, 4);
    check_ss_unstable_noncopy!(check_ss_unstable_noncopy_len_3, 3, 5);
    check_ss_unstable_noncopy!(check_ss_unstable_noncopy_len_7, 7, 9);
    check_ss_unstable_noncopy!(check_ss_unstable_noncopy_len_8, 8, 10);

    /// `<u128 as UnstableSmallSortTypeImpl>::small_sort`.
    ///
    /// `u128` is `Copy` + `Freeze` with `size_of` 16, so
    /// `has_efficient_in_place_swap::<u128>()` is false while
    /// `16 * 48 <= 4096` holds: this is the `small_sort_general` branch of the
    /// `CopyMarker` impl (as opposed to the network branch taken by `i32`).
    macro_rules! check_ss_unstable_u128 {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [u128; LEN] = kani::any();
                let before = v;

                <u128 as UnstableSmallSortTypeImpl>::small_sort(
                    &mut v,
                    &mut |a: &u128, b: &u128| a < b,
                );

                assert_sorted(&v);
                assert_permutation(&v, &before);
            }
        };
    }

    check_ss_unstable_u128!(check_ss_unstable_u128_len_2, 2, 4);

    /// `<[u64; 11] as UnstableSmallSortTypeImpl>::small_sort`.
    ///
    /// `size_of::<[u64; 11]>()` is 88, and `88 * 48 = 4224 > 4096
    /// (MAX_STACK_ARRAY_SIZE)`, so the `CopyMarker` impl falls all the way
    /// through to `small_sort_fallback`.
    ///
    /// The comparator only looks at element `[0]`, so the sortedness and
    /// permutation oracles are stated over the `[0]` values. That is the
    /// correct statement for this comparator: elements comparing equal on `[0]`
    /// are interchangeable under an *unstable* sort, so no stronger multiset
    /// claim on the full 11-word value is available here.
    macro_rules! check_ss_unstable_big {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [[u64; 11]; LEN] = kani::any();
                let before: [u64; LEN] = crate::array::from_fn(|i| v[i][0]);

                <[u64; 11] as UnstableSmallSortTypeImpl>::small_sort(
                    &mut v,
                    &mut |a: &[u64; 11], b: &[u64; 11]| a[0] < b[0],
                );

                let after: [u64; LEN] = crate::array::from_fn(|i| v[i][0]);
                assert_sorted(&after);
                assert_permutation(&after, &before);
            }
        };
    }

    check_ss_unstable_big!(check_ss_unstable_big_len_2, 2, 4);
    check_ss_unstable_big!(check_ss_unstable_big_len_3, 3, 5);

    // ------------------------------------------------------------------
    // Group B: the remaining success-criteria functions.
    // ------------------------------------------------------------------

    /// `swap_if_less` (success criterion 4).
    ///
    /// The `# Safety` comment requires the caller to pass positions that yield
    /// valid, aligned, same-allocation pointers, which is exactly what is
    /// assumed here (in-bounds indices of one array). The in-tree callers
    /// (`sort9_optimal` / `sort13_optimal`) always pass *distinct* positions,
    /// but distinctness is not part of the documented precondition and is not
    /// needed for safety, so it is deliberately not assumed. Beyond absence of
    /// UB we check the functional contract: the pair is left ordered and its
    /// multiset is preserved, and no other element of the buffer is disturbed.
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::solver(kissat)]
    pub fn check_ss_swap_if_less() {
        const LEN: usize = 8;
        let mut v: [i32; LEN] = kani::any();
        let before = v;

        let a_pos: usize = kani::any();
        let b_pos: usize = kani::any();
        kani::assume(a_pos < LEN && b_pos < LEN);

        // SAFETY: `a_pos` and `b_pos` are in-bounds indices of `v`.
        unsafe {
            swap_if_less(v.as_mut_ptr(), a_pos, b_pos, &mut |a: &i32, b: &i32| a < b);
        }

        // The pair is a permutation of the original pair ...
        assert!(
            (v[a_pos] == before[a_pos] && v[b_pos] == before[b_pos])
                || (v[a_pos] == before[b_pos] && v[b_pos] == before[a_pos])
        );
        // ... and is now ordered.
        assert!(!(v[b_pos] < v[a_pos]));
        // Nothing else moved.
        for i in 0..LEN {
            if i != a_pos && i != b_pos {
                assert!(v[i] == before[i]);
            }
        }
    }

    /// `sort4_stable` (success criterion 6).
    ///
    /// The `SAFETY` precondition is "`v_base` valid for 4 reads, `dst` valid for
    /// 4 writes", which is discharged by using a 4-element array and a
    /// 4-element `MaybeUninit` destination. The result must be a sorted
    /// permutation of the input, and `dst[0..4]` must be fully initialised
    /// (reading it back would be UB otherwise).
    #[kani::proof]
    #[kani::unwind(6)]
    #[kani::solver(kissat)]
    pub fn check_ss_sort4_stable() {
        const LEN: usize = 4;
        let v: [i32; LEN] = kani::any();
        let mut dst: [MaybeUninit<i32>; LEN] = [const { MaybeUninit::uninit() }; LEN];

        // SAFETY: `v` is valid for 4 reads and `dst` is valid for 4 writes.
        unsafe {
            sort4_stable(v.as_ptr(), dst.as_mut_ptr() as *mut i32, &mut |a: &i32, b: &i32| a < b);
        }

        // SAFETY: `sort4_stable` initialises all of `dst[0..4]`.
        let after: [i32; LEN] = crate::array::from_fn(|i| unsafe { dst[i].assume_init() });
        assert_sorted(&after);
        assert_permutation(&after, &v);
    }

    /// `insertion_sort_shift_left` (success criterion 5).
    ///
    /// `offset` is symbolic over the entire range the function accepts without
    /// aborting (`1..=len`); no presortedness is assumed, so absence of UB is
    /// proven for every accepted offset with arbitrary contents.
    ///
    /// The permutation property holds unconditionally. Full sortedness is only
    /// *promised* when `v[..offset]` is already sorted (the documented
    /// premise), so it is asserted as an implication rather than under an
    /// assumption -- that way the unsorted-prefix case is still explored for UB.
    macro_rules! check_ss_insertion_sort_shift_left {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            pub fn $name() {
                const LEN: usize = $len;
                let mut v: [i32; LEN] = kani::any();
                let before = v;

                let offset: usize = kani::any();
                kani::assume(offset >= 1 && offset <= LEN);

                // Was the documented premise `v[..offset]` sorted satisfied?
                let mut prefix_sorted = true;
                for i in 1..LEN {
                    if i < offset && before[i] < before[i - 1] {
                        prefix_sorted = false;
                    }
                }

                insertion_sort_shift_left(&mut v, offset, &mut |a: &i32, b: &i32| a < b);

                assert_permutation(&v, &before);
                if prefix_sorted {
                    assert_sorted(&v);
                }
            }
        };
    }

    check_ss_insertion_sort_shift_left!(check_ss_insertion_sort_shift_left_len_1, 1, 3);
    check_ss_insertion_sort_shift_left!(check_ss_insertion_sort_shift_left_len_2, 2, 4);
    check_ss_insertion_sort_shift_left!(check_ss_insertion_sort_shift_left_len_3, 3, 5);
    check_ss_insertion_sort_shift_left!(check_ss_insertion_sort_shift_left_len_4, 4, 6);

    // ------------------------------------------------------------------
    // Group C: direct callee harnesses.
    //
    // The composed `small_sort` bodies are SAT-intractable past a length
    // frontier (measured; see the PR text). The challenge notes that "function
    // contracts and loop contracts of those callee functions may be required" —
    // these harnesses verify each callee of the beyond-frontier branches
    // directly, at its exact call-site length and full element width, under its
    // documented precondition.
    // ------------------------------------------------------------------

    /// `sort8_stable` — the primitive of the general path's `len >= 16` branch,
    /// at its only call-site shape (8 elements), full `i32` width.
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::solver(kissat)]
    pub fn check_ss_sort8_stable() {
        let mut v: [i32; 8] = kani::any();
        let before = v;
        let mut dst: [MaybeUninit<i32>; 8] = [const { MaybeUninit::uninit() }; 8];
        let mut scratch: [MaybeUninit<i32>; 8] = [const { MaybeUninit::uninit() }; 8];

        // SAFETY: `v` is valid for 8 reads and writes; `dst` and `scratch` are
        // valid for 8 writes; none alias.
        unsafe {
            sort8_stable(
                v.as_mut_ptr(),
                dst.as_mut_ptr() as *mut i32,
                scratch.as_mut_ptr() as *mut i32,
                &mut |a: &i32, b: &i32| a < b,
            );
        }

        // SAFETY: `sort8_stable` initialises all of `dst[0..8]`.
        let after: [i32; 8] = crate::array::from_fn(|i| unsafe { dst[i].assume_init() });
        assert_sorted(&after);
        assert_permutation(&after, &before);
    }

    /// `sort9_optimal` — the network primitive of the `9 <= region < 13` band,
    /// directly at its guard length.
    #[kani::proof]
    #[kani::unwind(11)]
    #[kani::solver(kissat)]
    pub fn check_ss_sort9_optimal() {
        let mut v: [u8; 9] = kani::any();
        let before = v;
        sort9_optimal(&mut v, &mut |a: &u8, b: &u8| a < b);
        assert_sorted(&v);
        assert_permutation(&v, &before);
    }

    /// `has_efficient_in_place_swap` (success criterion 7).
    ///
    /// A `const fn` with no memory operations; the only thing to prove is that
    /// it is UB-free and reports the documented `size_of::<T>() <= 8` heuristic,
    /// which is what steers the `CopyMarker` dispatch between
    /// `small_sort_network` and `small_sort_general`.
    #[kani::proof]
    pub fn check_ss_has_efficient_in_place_swap() {
        assert!(has_efficient_in_place_swap::<i32>());
        assert!(has_efficient_in_place_swap::<u64>());
        assert!(!has_efficient_in_place_swap::<u128>());
        assert!(!has_efficient_in_place_swap::<[u64; 11]>());
    }
}
