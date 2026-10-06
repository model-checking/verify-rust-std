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
#[unsafe(rustc_allow_lifetime_dependent_specialization)]
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
            slice::from_raw_parts(drop_guard.src, drop_guard.len),
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
    let mut region = unsafe { slice::from_raw_parts_mut(v_base, initial_region_len) };

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
        unsafe { region = slice::from_raw_parts_mut(v_base.add(len_div_2), len - len_div_2) };
    }

    // SAFETY: We checked that T is Freeze and thus observation safe.
    // Should is_less panic v was not modified in parity_merge and retains it's original input.
    // scratch and v must not alias and scratch has v.len() space.
    unsafe {
        let scratch_base = stack_array.as_mut_ptr() as *mut T;
        bidirectional_merge(slice::from_raw_parts_mut(v_base, len), scratch_base, is_less);
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
#[safety::requires(
    size_of::<T>() == 0
        || (
            a_pos <= isize::MAX as usize / size_of::<T>()
                && b_pos <= isize::MAX as usize / size_of::<T>()
        )
)]
#[safety::requires({
    let v_a = v_base.wrapping_add(a_pos);
    let v_b = v_base.wrapping_add(b_pos);

    if size_of::<T>() == 0 {
        !v_base.is_null()
            && crate::ub_checks::can_dereference(v_a)
            && crate::ub_checks::can_dereference(v_b)
            && crate::ub_checks::can_write(v_a)
            && crate::ub_checks::can_write(v_b)
    } else {
        crate::ub_checks::same_allocation(v_base, v_a)
            && crate::ub_checks::same_allocation(v_base, v_b)
            && crate::ub_checks::can_dereference(v_a)
            && crate::ub_checks::can_dereference(v_b)
            && crate::ub_checks::can_write(v_a)
            && crate::ub_checks::can_write(v_b)
    }
})]
#[cfg_attr(
    kani,
    kani::modifies(
        v_base.wrapping_add(a_pos),
        v_base.wrapping_add(b_pos),
        is_less
    )
)]
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
#[safety::requires(crate::ub_checks::can_dereference(crate::ptr::slice_from_raw_parts(
    v_base, 4
)))]
#[safety::requires(crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(dst, 4)))]
#[safety::requires(crate::ub_checks::maybe_is_nonoverlapping(
    v_base as *const (),
    dst as *const (),
    size_of::<T>(),
    4,
))]
#[cfg_attr(kani, kani::modifies(crate::ptr::slice_from_raw_parts_mut(dst, 4), is_less))]
#[safety::ensures(|_| crate::ub_checks::can_dereference(
    crate::ptr::slice_from_raw_parts(dst as *const T, 4)
))]
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
        bidirectional_merge(slice::from_raw_parts(scratch_base, 8), dst, is_less);
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
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;
    use crate::cell::Cell;

    struct NonCopyU8(u8);

    const LARGE_ELEMENT_SIZE: usize = 87;

    struct LargeNonCopy([u8; LARGE_ELEMENT_SIZE]);

    fn is_sorted_by_key<T, K: PartialOrd, F: Fn(&T) -> K>(v: &[T], key: F) -> bool {
        let mut i = 1;
        while i < v.len() {
            if key(&v[i]) < key(&v[i - 1]) {
                return false;
            }
            i += 1;
        }
        true
    }

    fn count_by_key<T, K: PartialEq, F: Fn(&T) -> K>(v: &[T], key: F, probe: &K) -> usize {
        let mut count = 0;
        let mut i = 0;
        while i < v.len() {
            count += (key(&v[i]) == *probe) as usize;
            i += 1;
        }
        count
    }

    fn assert_permutation_by_key<
        T,
        U,
        K: PartialEq + kani::Arbitrary,
        F: Fn(&T) -> K,
        G: Fn(&U) -> K,
    >(
        before: &[T],
        after: &[U],
        before_key: F,
        after_key: G,
    ) {
        assert_eq!(before.len(), after.len());
        let probe: K = kani::any();
        assert_eq!(
            count_by_key(before, &before_key, &probe),
            count_by_key(after, &after_key, &probe),
        );
    }

    fn nondeterministic_cmp<T>(_: &T, _: &T) -> bool {
        kani::any()
    }

    // ---------------------------------------------------------------------
    // Safety contracts for the raw-pointer and public helper functions.
    // ---------------------------------------------------------------------

    macro_rules! gen_swap_if_less_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(swap_if_less)]
            fn $name() {
                let mut values: [$ty; 13] = kani::any();
                let a_pos = kani::any::<u8>() as usize;
                let b_pos = kani::any::<u8>() as usize;
                let decision: bool = kani::any();
                let mut calls = 0u8;
                let mut is_less = move |_: &$ty, _: &$ty| {
                    calls = calls.wrapping_add(1);
                    decision
                };
                unsafe {
                    swap_if_less(values.as_mut_ptr(), a_pos, b_pos, &mut is_less);
                }
                kani::cover(true, "swap_if_less call completes");
                kani::cover(a_pos == b_pos, "equal positions are reachable");
                kani::cover(a_pos != b_pos, "distinct positions are reachable");
                kani::cover(
                    a_pos == 0 && b_pos == 12,
                    "maximum real call-site distance is reachable",
                );
                kani::cover(decision, "swap branch is reachable");
                kani::cover(!decision, "no-swap branch is reachable");
            }
        };
    }

    gen_swap_if_less_harness!(harness_swap_if_less_u8, u8);
    gen_swap_if_less_harness!(harness_swap_if_less_u128, u128);

    #[kani::proof]
    fn harness_swap_if_less_unit() {
        let mut values = [(); 13];
        let a_pos = kani::any::<u8>() as usize;
        let b_pos = kani::any::<u8>() as usize;
        kani::assume(a_pos < 13 && b_pos < 13);
        kani::cover(a_pos < 13 && b_pos < 13, "valid ZST positions are reachable");
        let mut is_less = nondeterministic_cmp::<()>;
        unsafe {
            swap_if_less(values.as_mut_ptr(), a_pos, b_pos, &mut is_less);
        }
        kani::cover(true, "ZST swap_if_less call completes");
        kani::cover(a_pos == b_pos, "equal ZST positions are reachable");
        kani::cover(a_pos != b_pos, "distinct ZST positions are reachable");
        kani::cover(a_pos == 0 && b_pos == 12, "maximum real call-site distance is reachable");
    }

    macro_rules! gen_sort4_stable_contract_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(sort4_stable)]
            fn $name() {
                let input: [$ty; 4] = kani::any();
                let mut output = [const { MaybeUninit::<$ty>::uninit() }; 4];
                let mut calls = 0u8;
                let mut is_less = move |_: &$ty, _: &$ty| {
                    calls = calls.wrapping_add(1);
                    kani::any::<bool>()
                };
                unsafe {
                    sort4_stable(input.as_ptr(), output.as_mut_ptr().cast::<$ty>(), &mut is_less);
                }
                kani::cover(true, "sort4_stable call completes");
            }
        };
    }

    gen_sort4_stable_contract_harness!(harness_sort4_stable_u8, u8);
    gen_sort4_stable_contract_harness!(harness_sort4_stable_u128, u128);

    #[kani::proof]
    fn harness_sort4_stable_unit() {
        let input = [(); 4];
        let mut output = [const { MaybeUninit::<()>::uninit() }; 4];
        let mut is_less = nondeterministic_cmp::<()>;
        unsafe {
            sort4_stable(input.as_ptr(), output.as_mut_ptr().cast::<()>(), &mut is_less);
        }
        kani::cover(true, "ZST sort4_stable call completes");
    }

    #[kani::proof]
    #[kani::unwind(19)]
    fn harness_insertion_sort_shift_left() {
        const MAX_LEN: usize = 17;
        let mut backing: [i32; MAX_LEN] = kani::any();
        let len: usize = kani::any();
        kani::assume(len >= 1 && len <= MAX_LEN);
        kani::cover(len == 1, "minimum length is reachable");
        kani::cover(len == 16, "fallback threshold is reachable");
        kani::cover(len == 17, "maximum network insertion region is reachable");
        let offset: usize = kani::any();
        kani::assume(offset >= 1 && offset <= len);
        kani::cover(offset == 1, "minimum offset is reachable");
        kani::cover(offset == len, "maximum offset is reachable");
        let mut is_less = nondeterministic_cmp::<i32>;
        insertion_sort_shift_left(&mut backing[..len], offset, &mut is_less);
        kani::cover(true, "insertion_sort_shift_left completes");
    }

    #[kani::proof]
    fn harness_has_efficient_in_place_swap() {
        assert!(has_efficient_in_place_swap::<()>());
        assert!(has_efficient_in_place_swap::<u8>());
        assert!(has_efficient_in_place_swap::<u16>());
        assert!(has_efficient_in_place_swap::<u32>());
        assert!(has_efficient_in_place_swap::<u64>());
        assert!(!has_efficient_in_place_swap::<u128>());
        assert!(!has_efficient_in_place_swap::<[u8; 9]>());
        assert!(has_efficient_in_place_swap::<Cell<u32>>());

        kani::cover(true, "has_efficient_in_place_swap harness completes");
    }

    // ---------------------------------------------------------------------
    // Symbolic length and specialization coverage for the three trait APIs.
    // ---------------------------------------------------------------------

    #[kani::proof]
    #[kani::unwind(18)]
    fn harness_stable_small_sort_nonfreeze() {
        const MAX_LEN: usize = SMALL_SORT_FALLBACK_THRESHOLD;

        let mut backing: [Cell<i32>; MAX_LEN] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let len: usize = kani::any();
        kani::assume(len <= MAX_LEN);
        kani::cover(len == MAX_LEN, "full non-Freeze threshold is reachable");
        kani::cover(len == 0, "empty slice is reachable");
        kani::cover(len == 1, "single-element slice is reachable");
        kani::cover(len == 2, "insertion path is reachable");
        let mut scratch =
            [const { MaybeUninit::<Cell<i32>>::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        let mut is_less = nondeterministic_cmp::<Cell<i32>>;
        <Cell<i32> as StableSmallSortTypeImpl>::small_sort(
            &mut backing[..len],
            &mut scratch,
            &mut is_less,
        );
        kani::cover(true, "Stable non-Freeze small_sort completes");
    }

    macro_rules! gen_stable_freeze_harness {
        (
            $name:ident,
            $ty:ty,
            $less:expr,
            $key:expr
        ) => {
            #[kani::proof]
            #[kani::unwind(34)]
            #[kani::solver(kissat)]
            fn $name() {
                const MAX_LEN: usize = SMALL_SORT_GENERAL_THRESHOLD;

                let mut values: [$ty; MAX_LEN] = kani::any();
                let before = values;

                let len_u8: u8 = kani::any();
                kani::assume(len_u8 <= MAX_LEN as u8);
                let len = len_u8 as usize;

                assert_eq!(<$ty as StableSmallSortTypeImpl>::small_sort_threshold(), MAX_LEN,);

                kani::cover(len_u8 == 0, "empty slice is reachable");
                kani::cover(len_u8 == 8, "sort4 threshold is reachable");
                kani::cover(len_u8 == 16, "length 16 is reachable");
                kani::cover(len_u8 == 17, "odd split is reachable");
                kani::cover(len_u8 == MAX_LEN as u8, "full Stable Freeze threshold is reachable");

                let mut scratch = [MaybeUninit::<$ty>::uninit(); SMALL_SORT_GENERAL_SCRATCH_LEN];

                let mut is_less = $less;

                <$ty as StableSmallSortTypeImpl>::small_sort(
                    &mut values[..len],
                    &mut scratch,
                    &mut is_less,
                );

                // Sorting postcondition.
                assert!(is_sorted_by_key(&values[..len], $key,));

                // Permutation postcondition.
                assert_permutation_by_key(
                    &before[..len],
                    &values[..len],
                    |x: &$ty| *x,
                    |x: &$ty| *x,
                );

                // Reaching here also means Kani found no UB on this path.
                kani::cover(true, "Stable Freeze UB + sortedness + permutation");
            }
        };
    }

    gen_stable_freeze_harness!(
        harness_stable_small_sort_freeze_small,
        u8,
        |a: &u8, b: &u8| a < b,
        |x: &u8| *x
    );
    gen_stable_freeze_harness!(
        harness_stable_small_sort_freeze_large,
        [u8; 17],
        |a: &[u8; 17], b: &[u8; 17]| a[0] < b[0],
        |x: &[u8; 17]| x[0]
    );

    #[kani::proof]
    #[kani::unwind(18)]
    fn harness_stable_small_sort_nonfreeze_sorted() {
        const MAX_LEN: usize = SMALL_SORT_FALLBACK_THRESHOLD;

        let mut values: [Cell<u8>; MAX_LEN] = crate::array::from_fn(|_| Cell::new(kani::any()));

        let len_u8: u8 = kani::any();
        kani::assume(len_u8 <= MAX_LEN as u8);
        kani::cover(len_u8 == MAX_LEN as u8, "full sortedness domain is reachable");
        kani::cover(len_u8 == 0, "empty slice is reachable");
        kani::cover(len_u8 == 1, "single-element slice is reachable");

        let len = len_u8 as usize;

        let mut scratch: [MaybeUninit<Cell<u8>>; 0] = [];

        <Cell<u8> as StableSmallSortTypeImpl>::small_sort(
            &mut values[..len],
            &mut scratch,
            &mut |a: &Cell<u8>, b: &Cell<u8>| a.get() < b.get(),
        );

        if len_u8 >= 2 {
            let i: u8 = kani::any();

            kani::assume(i < len_u8 - 1);
            kani::cover(i < len_u8 - 1, "an arbitrary adjacent output pair is reachable");

            let i = i as usize;

            assert!(values[i].get() <= values[i + 1].get(), "output must be nondecreasing",);
        }

        kani::cover(true, "Stable non-Freeze sortedness proven for symbolic length");
    }

    #[derive(Clone, Copy)]
    struct Tagged {
        key: u8,
        tag: u8,
    }

    macro_rules! stable_nonfreeze_permutation {
        ($name:ident, $len:expr, $unwind:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $name() {
                const LEN: usize = $len;

                let mut values: [Cell<Tagged>; LEN] =
                    crate::array::from_fn(|i| Cell::new(Tagged { key: kani::any(), tag: i as u8 }));

                let mut scratch: [MaybeUninit<Cell<Tagged>>; 0] = [];

                <Cell<Tagged> as StableSmallSortTypeImpl>::small_sort(
                    &mut values,
                    &mut scratch,
                    &mut |a: &Cell<Tagged>, b: &Cell<Tagged>| a.get().key < b.get().key,
                );

                let mut mask = 0u32;

                for value in &values {
                    mask |= 1u32 << value.get().tag;
                }

                assert_eq!(mask, if LEN == 0 { 0 } else { (1u32 << LEN) - 1 },);

                kani::cover(true, "permutation proof completes");
            }
        };
    }

    stable_nonfreeze_permutation!(stable_nonfreeze_perm_0, 0, 2);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_1, 1, 3);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_2, 2, 4);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_3, 3, 5);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_4, 4, 6);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_5, 5, 7);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_6, 6, 8);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_7, 7, 9);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_8, 8, 10);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_9, 9, 11);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_10, 10, 12);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_11, 11, 13);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_12, 12, 14);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_13, 13, 15);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_14, 14, 16);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_15, 15, 17);
    stable_nonfreeze_permutation!(stable_nonfreeze_perm_16, 16, 18);

    macro_rules! gen_unstable_copy_route_harness {
        (
            $name:ident,
            $trait_name:ident,
            $ty:ty,
            $max_len:expr,
            $unwind:literal,
            $less:expr,
            $key:expr
        ) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            fn $name() {
                const MAX_LEN: usize = $max_len;

                let mut values: [$ty; MAX_LEN] = kani::any();
                let before = values;

                let len_u8: u8 = kani::any();
                kani::assume(len_u8 <= MAX_LEN as u8);
                let len = len_u8 as usize;

                assert_eq!(<$ty as $trait_name>::small_sort_threshold(), MAX_LEN,);

                kani::cover(len_u8 == 0, "empty slice is reachable");
                kani::cover(len_u8 == MAX_LEN as u8, "full route threshold is reachable");

                let mut is_less = $less;

                <$ty as $trait_name>::small_sort(&mut values[..len], &mut is_less);

                assert!(is_sorted_by_key(&values[..len], $key,));

                assert_permutation_by_key(
                    &before[..len],
                    &values[..len],
                    |x: &$ty| *x,
                    |x: &$ty| *x,
                );

                kani::cover(true, "UB + sortedness + permutation");
            }
        };
    }

    gen_unstable_copy_route_harness!(
        harness_unstable_small_sort_copy_network,
        UnstableSmallSortTypeImpl,
        u8,
        SMALL_SORT_NETWORK_THRESHOLD,
        34,
        |a: &u8, b: &u8| a < b,
        |x: &u8| *x
    );
    gen_unstable_copy_route_harness!(
        harness_unstable_small_sort_copy_general,
        UnstableSmallSortTypeImpl,
        u128,
        SMALL_SORT_GENERAL_THRESHOLD,
        34,
        |a: &u128, b: &u128| a < b,
        |x: &u128| *x
    );
    gen_unstable_copy_route_harness!(
        harness_unstable_small_sort_copy_general_large_element,
        UnstableSmallSortTypeImpl,
        [u8; 17],
        SMALL_SORT_GENERAL_THRESHOLD,
        34,
        |a: &[u8; 17], b: &[u8; 17]| a[0] < b[0],
        |x: &[u8; 17]| x[0]
    );
    gen_unstable_copy_route_harness!(
        harness_unstable_small_sort_copy_fallback,
        UnstableSmallSortTypeImpl,
        [u8; LARGE_ELEMENT_SIZE],
        SMALL_SORT_FALLBACK_THRESHOLD,
        18,
        |a: &[u8; LARGE_ELEMENT_SIZE], b: &[u8; LARGE_ELEMENT_SIZE]| a[0] < b[0],
        |x: &[u8; LARGE_ELEMENT_SIZE]| x[0]
    );

    macro_rules! gen_unstable_noncopy_route_harness {
        (
            $name:ident,
            $trait_name:ident,
            $ty:ty,
            $snapshot_ty:ty,
            $max_len:expr,
            $unwind:literal,
            $constructor:expr,
            $less:expr,
            $key:expr,
            $snapshot:expr
        ) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::solver(kissat)]
            fn $name() {
                const MAX_LEN: usize = $max_len;

                let mut values: [$ty; MAX_LEN] = crate::array::from_fn(|_| $constructor);

                let before: [$snapshot_ty; MAX_LEN] =
                    crate::array::from_fn(|i| ($snapshot)(&values[i]));

                let len_u8: u8 = kani::any();
                kani::assume(len_u8 <= MAX_LEN as u8);
                let len = len_u8 as usize;

                assert_eq!(<$ty as $trait_name>::small_sort_threshold(), MAX_LEN,);

                kani::cover(len_u8 == 0, "empty slice is reachable");
                kani::cover(len_u8 == MAX_LEN as u8, "full route threshold is reachable");

                let mut is_less = $less;

                <$ty as $trait_name>::small_sort(&mut values[..len], &mut is_less);

                assert!(is_sorted_by_key(&values[..len], $key,));

                assert_permutation_by_key(
                    &before[..len],
                    &values[..len],
                    |x: &$snapshot_ty| *x,
                    $snapshot,
                );

                kani::cover(true, "UB + sortedness + permutation");
            }
        };
    }

    gen_unstable_noncopy_route_harness!(
        harness_unstable_small_sort_noncopy_general,
        UnstableSmallSortTypeImpl,
        NonCopyU8,
        u8,
        SMALL_SORT_GENERAL_THRESHOLD,
        34,
        NonCopyU8(kani::any()),
        |a: &NonCopyU8, b: &NonCopyU8| a.0 < b.0,
        |x: &NonCopyU8| x.0,
        |x: &NonCopyU8| x.0
    );
    gen_unstable_noncopy_route_harness!(
        harness_unstable_small_sort_noncopy_fallback,
        UnstableSmallSortTypeImpl,
        LargeNonCopy,
        [u8; LARGE_ELEMENT_SIZE],
        SMALL_SORT_FALLBACK_THRESHOLD,
        18,
        LargeNonCopy(kani::any()),
        |a: &LargeNonCopy, b: &LargeNonCopy| a.0[0] < b.0[0],
        |x: &LargeNonCopy| x.0[0],
        |x: &LargeNonCopy| x.0
    );

    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::solver(kissat)]
    fn harness_unstable_small_sort_nonfreeze() {
        const MAX_LEN: usize = SMALL_SORT_FALLBACK_THRESHOLD;

        let mut values: [Cell<u8>; MAX_LEN] = crate::array::from_fn(|_| Cell::new(kani::any()));

        let before: [u8; MAX_LEN] = crate::array::from_fn(|i| values[i].get());

        let len_u8: u8 = kani::any();
        kani::assume(len_u8 <= MAX_LEN as u8);
        let len = len_u8 as usize;

        assert_eq!(<Cell<u8> as UnstableSmallSortTypeImpl>::small_sort_threshold(), MAX_LEN,);

        kani::cover(len_u8 == 0, "empty non-Freeze slice is reachable");
        kani::cover(len_u8 == MAX_LEN as u8, "full non-Freeze threshold is reachable");

        <Cell<u8> as UnstableSmallSortTypeImpl>::small_sort(&mut values[..len], &mut |a: &Cell<
            u8,
        >,
                                                                                      b: &Cell<
            u8,
        >| {
            a.get() < b.get()
        });

        assert!(is_sorted_by_key(&values[..len], |x: &Cell<u8>| x.get(),));

        assert_permutation_by_key(
            &before[..len],
            &values[..len],
            |x: &u8| *x,
            |x: &Cell<u8>| x.get(),
        );

        kani::cover(true, "Unstable non-Freeze UB + sortedness + permutation");
    }

    // <T as UnstableSmallSortFreezeTypeImpl>::small_sort
    gen_unstable_copy_route_harness!(
        harness_unstable_freeze_small_sort_copy_network,
        UnstableSmallSortFreezeTypeImpl,
        u8,
        SMALL_SORT_NETWORK_THRESHOLD,
        34,
        |a: &u8, b: &u8| a < b,
        |x: &u8| *x
    );

    gen_unstable_copy_route_harness!(
        harness_unstable_freeze_small_sort_copy_general,
        UnstableSmallSortFreezeTypeImpl,
        u128,
        SMALL_SORT_GENERAL_THRESHOLD,
        34,
        |a: &u128, b: &u128| a < b,
        |x: &u128| *x
    );
    gen_unstable_copy_route_harness!(
        harness_unstable_freeze_small_sort_copy_general_large_element,
        UnstableSmallSortFreezeTypeImpl,
        [u8; 17],
        SMALL_SORT_GENERAL_THRESHOLD,
        34,
        |a: &[u8; 17], b: &[u8; 17]| a[0] < b[0],
        |x: &[u8; 17]| x[0]
    );

    gen_unstable_copy_route_harness!(
        harness_unstable_freeze_small_sort_copy_fallback,
        UnstableSmallSortFreezeTypeImpl,
        [u8; LARGE_ELEMENT_SIZE],
        SMALL_SORT_FALLBACK_THRESHOLD,
        18,
        |a: &[u8; LARGE_ELEMENT_SIZE], b: &[u8; LARGE_ELEMENT_SIZE]| a[0] < b[0],
        |x: &[u8; LARGE_ELEMENT_SIZE]| x[0]
    );

    gen_unstable_noncopy_route_harness!(
        harness_unstable_freeze_small_sort_noncopy_general,
        UnstableSmallSortFreezeTypeImpl,
        NonCopyU8,
        u8,
        SMALL_SORT_GENERAL_THRESHOLD,
        34,
        NonCopyU8(kani::any()),
        |a: &NonCopyU8, b: &NonCopyU8| a.0 < b.0,
        |x: &NonCopyU8| x.0,
        |x: &NonCopyU8| x.0
    );

    gen_unstable_noncopy_route_harness!(
        harness_unstable_freeze_small_sort_noncopy_fallback,
        UnstableSmallSortFreezeTypeImpl,
        LargeNonCopy,
        [u8; LARGE_ELEMENT_SIZE],
        SMALL_SORT_FALLBACK_THRESHOLD,
        18,
        LargeNonCopy(kani::any()),
        |a: &LargeNonCopy, b: &LargeNonCopy| a.0[0] < b.0[0],
        |x: &LargeNonCopy| x.0[0],
        |x: &LargeNonCopy| x.0
    );
}
