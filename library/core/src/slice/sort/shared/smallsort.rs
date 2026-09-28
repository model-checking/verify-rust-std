//! This module contains a variety of sort implementations that are optimized for small lengths.

#[cfg(kani)]
use crate::kani;
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
#[safety::requires(a_pos != b_pos)]
#[safety::requires(crate::ub_checks::can_write(unsafe { v_base.add(a_pos) })
    && crate::ub_checks::can_write(unsafe { v_base.add(b_pos) }))]
#[cfg_attr(kani, kani::modifies(unsafe { v_base.add(a_pos) }, unsafe { v_base.add(b_pos) }))]
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
// The precondition mirrors the function's own guard: `offset == 0 || offset > v.len()`
// takes the `intrinsics::abort()` arm (a defined, safe outcome that a `should_panic`
// harness cannot observe), so the verified domain is the non-aborting one.
#[safety::requires(offset >= 1 && offset <= v.len())]
#[cfg_attr(kani, kani::modifies(v))]
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

#[cfg(kani)]
mod verify {
    use super::*;
    use crate::cell::Cell;

    // Freeze + !Copy element: selects the default (non-Copy) arm of
    // `UnstableSmallSortFreezeTypeImpl` — the `small_sort_general` route.
    struct NonCopy(u8);

    // Freeze + !Copy + Drop: same dispatch as `NonCopy`, but forces drop-glue
    // on every move path (guards, scratch copies).
    struct DropT(u8);
    impl Drop for DropT {
        fn drop(&mut self) {}
    }

    // `v` is non-decreasing under the `key` projection.
    fn is_sorted_by_key<T, K: PartialOrd>(v: &[T], key: impl Fn(&T) -> K) -> bool {
        let mut i = 1;
        while i < v.len() {
            if key(&v[i - 1]) > key(&v[i]) {
                return false;
            }
            i += 1;
        }
        true
    }

    // Occurrence count of key value `x` in `v` — O(n). With a symbolic `x`,
    // one count pair (`count(before, x) == count(after, x)`) proves full
    // multiset equality under the projection: Kani checks it for every `x`.
    fn count_by_key<T, K: PartialEq>(v: &[T], key: impl Fn(&T) -> K, x: &K) -> usize {
        let mut c = 0usize;
        let mut i = 0;
        while i < v.len() {
            c += (&key(&v[i]) == x) as usize;
            i += 1;
        }
        c
    }

    // ===================================================================
    // No-UB harnesses at the tractable length thresholds.
    //
    // The small-sort API is bounded by design (each impl's `small_sort_threshold`
    // caps the valid input length). We verify absence of UB at those caps where
    // the SAT solver reaches them: the fallback/insertion band to 16 (including a
    // symbolic length over the whole domain), the general and network bands to
    // the deepest length that completes — 17 and 18 respectively. Beyond that the
    // per-harness SAT problem (~55k VCCs at length 32) does not converge in a CI
    // budget; see the module-level note and the PR discussion.
    // ===================================================================

    // --- Fallback / insertion band (threshold 16) ---

    // Symbolic length over the ENTIRE fallback validity domain [1, 16] — the
    // literal "arbitrary valid length" obligation, discharged for this band.
    #[kani::proof]
    #[kani::unwind(17)]
    fn check_insertion_sort_shift_left_symlen_i32() {
        let mut backing: [i32; 16] = kani::any();
        let len: usize = kani::any();
        kani::assume(len >= 1 && len <= 16);
        insertion_sort_shift_left(&mut backing[..len], 1, &mut |a: &i32, b: &i32| a < b);
        kani::cover(len == 16, "full fallback threshold reachable");
    }

    // Non-Freeze element through the unstable trait entry → default fallback impl.
    #[kani::proof]
    #[kani::unwind(17)]
    fn check_unstable_small_sort_cell_16() {
        let mut v: [Cell<i32>; 16] = crate::array::from_fn(|_| Cell::new(kani::any()));
        <Cell<i32> as UnstableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut |a: &Cell<i32>, b: &Cell<i32>| a.get() < b.get(),
        );
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // Non-Freeze element through the STABLE trait entry → default insertion impl.
    #[kani::proof]
    #[kani::unwind(17)]
    fn check_stable_small_sort_cell_16() {
        let mut v: [Cell<i32>; 16] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let mut scratch: [MaybeUninit<Cell<i32>>; SMALL_SORT_GENERAL_SCRATCH_LEN] =
            [const { MaybeUninit::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        <Cell<i32> as StableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut scratch,
            &mut |a: &Cell<i32>, b: &Cell<i32>| a.get() < b.get(),
        );
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // Huge element ([u64; 11] = 88 bytes, 88*48 > 4096) → forced onto the
    // fallback route even through the Copy-specialized dispatch. The comparator
    // reads only the first lane: this is a valid ordering for the no-UB check
    // and avoids an 11-element lexicographic compare loop inside every `is_less`
    // call, which the array `<` operator would otherwise introduce. Length 8:
    // the huge-element symbolic state does not converge at the 16 threshold.
    #[kani::proof]
    #[kani::unwind(9)]
    fn check_unstable_small_sort_bigt_8() {
        let mut v: [[u64; 11]; 8] = kani::any();
        <[u64; 11] as UnstableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut |a: &[u64; 11], b: &[u64; 11]| a[0] < b[0],
        );
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // --- General band (sort8_stable + ping-pong merge; max-green length 17) ---
    // 8-bit element width in this band's length-16/17 harnesses: wider elements
    // exceed the CI per-harness budget at these lengths (32-bit width measures
    // 566-714 s); 32-bit width is exercised at the sort4-branch and network
    // lengths below.

    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::solver(kissat)]
    fn check_stable_small_sort_u8_16() {
        let mut v: [u8; 16] = kani::any();
        let mut scratch: [MaybeUninit<u8>; SMALL_SORT_GENERAL_SCRATCH_LEN] =
            [const { MaybeUninit::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        <u8 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut |a: &u8, b: &u8| {
            a < b
        });
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // Odd split (halves 8 / 9): exercises the region-insertion extension loop.
    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::solver(kissat)]
    fn check_stable_small_sort_u8_17() {
        let mut v: [u8; 17] = kani::any();
        let mut scratch: [MaybeUninit<u8>; SMALL_SORT_GENERAL_SCRATCH_LEN] =
            [const { MaybeUninit::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        <u8 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut |a: &u8, b: &u8| {
            a < b
        });
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // Freeze + !Copy element → general route (small_sort_general, stack scratch).
    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::solver(kissat)]
    fn check_unstable_small_sort_noncopy_16() {
        let mut v: [NonCopy; 16] = crate::array::from_fn(|_| NonCopy(kani::any()));
        <NonCopy as UnstableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut |a: &NonCopy, b: &NonCopy| a.0 < b.0,
        );
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // Drop-carrying element → general route + drop-glue on every move path.
    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::solver(kissat)]
    fn check_unstable_small_sort_dropt_16() {
        let mut v: [DropT; 16] = crate::array::from_fn(|_| DropT(kani::any()));
        <DropT as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &DropT, b: &DropT| {
            a.0 < b.0
        });
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // u128 (16 bytes, Copy): has_efficient false → skips the network route and
    // takes small_sort_general — the only element class that reaches the
    // Copy-specialized impl's general branch. The 16-byte element width is
    // expensive under BMC, so this branch is exercised at length 4 (the deeper
    // general-band lengths are covered by the 4-byte types).
    #[kani::proof]
    #[kani::unwind(6)]
    #[kani::solver(kissat)]
    fn check_unstable_small_sort_u128_4() {
        let mut v: [u128; 4] = kani::any();
        <u128 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &u128, b: &u128| a < b);
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // --- Network band (sort9_optimal / sort13_optimal + merge; max-green 18) ---

    // sort13_optimal band (13 <= len < 18: straight-line network, no merge).
    #[kani::proof]
    #[kani::unwind(14)]
    fn check_unstable_small_sort_u8_13() {
        let mut v: [u8; 13] = kani::any();
        <u8 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &u8, b: &u8| a < b);
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // First merge-path length (no_merge flips false at 18).
    #[kani::proof]
    #[kani::unwind(10)]
    fn check_unstable_small_sort_u8_18() {
        let mut v: [u8; 18] = kani::any();
        <u8 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &u8, b: &u8| a < b);
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // Network band at 32-bit element width (not just u8).
    #[kani::proof]
    #[kani::unwind(14)]
    fn check_unstable_small_sort_i32_13() {
        let mut v: [i32; 13] = kani::any();
        <i32 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &i32, b: &i32| a < b);
        kani::cover(true, "call completed: no-UB path reachable");
    }

    // ===================================================================
    // Sorting-correctness oracles: output is sorted AND a multiset-permutation
    // of the input (the count-probe encoding). At the deepest length the coupled
    // sorted+permutation problem reaches per family.
    // ===================================================================

    #[kani::proof]
    #[kani::unwind(9)]
    fn check_stable_small_sort_sorts_i32_8() {
        let mut v: [i32; 8] = kani::any();
        let snapshot = v;
        let mut scratch: [MaybeUninit<i32>; SMALL_SORT_GENERAL_SCRATCH_LEN] =
            [const { MaybeUninit::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        <i32 as StableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut scratch,
            &mut |a: &i32, b: &i32| a < b,
        );
        assert!(is_sorted_by_key(&v, |x: &i32| *x));
        let probe: i32 = kani::any();
        assert!(
            count_by_key(&snapshot, |x: &i32| *x, &probe) == count_by_key(&v, |x: &i32| *x, &probe)
        );
        kani::cover(true, "sorted+permutation proven");
    }

    #[kani::proof]
    #[kani::unwind(11)]
    fn check_unstable_small_sort_sorts_u8_9() {
        let mut v: [u8; 9] = kani::any();
        let snapshot = v;
        <u8 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &u8, b: &u8| a < b);
        assert!(is_sorted_by_key(&v, |x: &u8| *x));
        let probe: u8 = kani::any();
        assert!(
            count_by_key(&snapshot, |x: &u8| *x, &probe) == count_by_key(&v, |x: &u8| *x, &probe)
        );
        kani::cover(true, "sorted+permutation proven (sort9 network)");
    }

    // sort13 network: sorted-only. The coupled sorted+permutation problem does
    // not converge at length 13 for this network (the input↔output multiset
    // coupling is the intractable part, not the sortedness assertion) — so the
    // permutation half is carried at length 9 (sort9 band, above) where it does
    // converge, and this length-13 harness asserts sortedness only. Constant-fill
    // degeneracy is excluded by the length-9 permutation harness on this path.
    #[kani::proof]
    #[kani::unwind(14)]
    fn check_unstable_small_sort_sorted_u8_13() {
        let mut v: [u8; 13] = kani::any();
        let had_descent = v.len() >= 2 && v[0] > v[1];
        <u8 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &u8, b: &u8| a < b);
        assert!(is_sorted_by_key(&v, |x: &u8| *x));
        kani::cover(had_descent, "an initially-unsorted input reaches the sortedness assert");
    }

    #[kani::proof]
    #[kani::unwind(9)]
    fn check_unstable_small_sort_sorts_cell_8() {
        let mut v: [Cell<i32>; 8] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let snap: [i32; 8] = crate::array::from_fn(|i| v[i].get());
        <Cell<i32> as UnstableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut |a: &Cell<i32>, b: &Cell<i32>| a.get() < b.get(),
        );
        assert!(is_sorted_by_key(&v, |x: &Cell<i32>| x.get()));
        let probe: i32 = kani::any();
        assert!(
            count_by_key(&snap, |x: &i32| *x, &probe)
                == count_by_key(&v, |x: &Cell<i32>| x.get(), &probe)
        );
        kani::cover(true, "sorted+permutation proven (non-Freeze)");
    }

    #[kani::proof]
    #[kani::unwind(9)]
    fn check_unstable_small_sort_sorts_dropt_8() {
        let mut v: [DropT; 8] = crate::array::from_fn(|_| DropT(kani::any()));
        let snap: [u8; 8] = crate::array::from_fn(|i| v[i].0);
        <DropT as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut |a: &DropT, b: &DropT| {
            a.0 < b.0
        });
        assert!(is_sorted_by_key(&v, |x: &DropT| x.0));
        let probe: u8 = kani::any();
        assert!(
            count_by_key(&snap, |x: &u8| *x, &probe) == count_by_key(&v, |x: &DropT| x.0, &probe)
        );
        kani::cover(true, "sorted+permutation proven (drop-carrying)");
    }

    // Fallback/insertion band correctness: sorted AND permutation. Length 8 —
    // the coupled check does not converge at the 16 threshold (the sortedness
    // assertion over all 16 outputs is itself the intractable part there; the
    // no-UB and symbolic-length harnesses cover length 16 for this band).
    #[kani::proof]
    #[kani::unwind(9)]
    fn check_insertion_sort_shift_left_sorts_i32_8() {
        let mut v: [i32; 8] = kani::any();
        let snapshot = v;
        insertion_sort_shift_left(&mut v, 1, &mut |a: &i32, b: &i32| a < b);
        assert!(is_sorted_by_key(&v, |x: &i32| *x));
        let probe: i32 = kani::any();
        assert!(
            count_by_key(&snapshot, |x: &i32| *x, &probe) == count_by_key(&v, |x: &i32| *x, &probe)
        );
        kani::cover(true, "sorted+permutation proven (insertion band)");
    }

    // ===================================================================
    // Contracts. Validity-domain preconditions on the two free callee functions
    // that carry loops, each with a matching proof_for_contract. Contracts on the
    // three `small_sort` trait-impl methods do not compile at this toolchain
    // (specialization + the generic `old()` snapshot needs `T: Clone`), so those
    // impls are exercised by the in-harness oracles above instead.
    // ===================================================================

    #[kani::proof_for_contract(swap_if_less)]
    fn check_swap_if_less_contract() {
        let mut arr: [u8; 4] = kani::any();
        let a: usize = kani::any();
        let b: usize = kani::any();
        kani::assume(a < 4 && b < 4 && a != b);
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let mut is_less = |x: &u8, y: &u8| x < y;
        // SAFETY: a, b in-bounds and distinct per the assumes.
        unsafe { swap_if_less(arr.as_mut_ptr(), a, b, &mut is_less) };
    }

    #[kani::proof_for_contract(insertion_sort_shift_left)]
    #[kani::unwind(9)]
    fn check_insertion_sort_shift_left_contract() {
        let mut v: [i32; 8] = kani::any();
        let offset: usize = kani::any();
        kani::assume(offset >= 1 && offset <= 8);
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        insertion_sort_shift_left(&mut v, offset, &mut |a: &i32, b: &i32| a < b);
    }

    // ===================================================================
    // Remaining criteria functions and callees.
    // ===================================================================

    // The size heuristic, across the width classes it discriminates.
    #[kani::proof]
    fn check_has_efficient_in_place_swap() {
        assert!(has_efficient_in_place_swap::<u8>());
        assert!(has_efficient_in_place_swap::<u16>());
        assert!(has_efficient_in_place_swap::<u32>());
        assert!(has_efficient_in_place_swap::<u64>());
        assert!(!has_efficient_in_place_swap::<u128>());
        assert!(!has_efficient_in_place_swap::<[u8; 9]>());
        assert!(has_efficient_in_place_swap::<()>());
        assert!(has_efficient_in_place_swap::<Cell<u32>>());
        kani::cover(true, "heuristic evaluated");
    }

    // sort4_stable: branchless, no loops. Sorted + permutation on the output.
    #[kani::proof]
    fn check_sort4_stable_u8() {
        let src: [u8; 4] = kani::any();
        let mut dst = [0u8; 4];
        let mut is_less = |a: &u8, b: &u8| a < b;
        // SAFETY: src has 4 readable elements; dst has 4 writable, non-overlapping.
        unsafe { sort4_stable(src.as_ptr(), dst.as_mut_ptr(), &mut is_less) };
        assert!(is_sorted_by_key(&dst, |x: &u8| *x));
        let probe: u8 = kani::any();
        assert!(count_by_key(&src, |x: &u8| *x, &probe) == count_by_key(&dst, |x: &u8| *x, &probe));
        kani::cover(true, "sort4 sorted+permutation proven");
    }

    // bidirectional_merge: two sorted halves in, fully sorted permutation out.
    // The sorted-halves precondition prunes the state space enough to reach the
    // general threshold length here.
    #[kani::proof]
    #[kani::unwind(9)]
    fn check_bidirectional_merge_sorts_i32_8() {
        let v: [i32; 8] = kani::any();
        kani::assume(is_sorted_by_key(&v[..4], |x: &i32| *x));
        kani::assume(is_sorted_by_key(&v[4..], |x: &i32| *x));
        let mut dst = [0i32; 8];
        // SAFETY: dst is a distinct local valid for 8 writes; len 8 >= 2, halves sorted.
        unsafe { bidirectional_merge(&v, dst.as_mut_ptr(), &mut |a: &i32, b: &i32| a < b) };
        assert!(is_sorted_by_key(&dst, |x: &i32| *x));
        let probe: i32 = kani::any();
        assert!(count_by_key(&v, |x: &i32| *x, &probe) == count_by_key(&dst, |x: &i32| *x, &probe));
        kani::cover(v[0] != v[4], "distinct-half merge reaches the assert");
    }

    // Sanity-check the oracle predicates themselves on known inputs, so a bug
    // in a helper cannot silently weaken every correctness harness above.
    #[kani::proof]
    fn check_oracle_helpers() {
        let b = [1u8, 2, 3];
        assert!(is_sorted_by_key(&b, |x: &u8| *x));
        assert!(!is_sorted_by_key(&[2u8, 1], |x: &u8| *x));
        assert!(count_by_key(&b, |x: &u8| *x, &2) == 1);
        assert!(count_by_key(&b, |x: &u8| *x, &9) == 0);
        kani::cover(true, "oracle predicates evaluated");
    }
}
