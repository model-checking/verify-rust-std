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

#[cfg_attr(kani, safety::ensures(|_| verify::count(v.as_ptr(), v.len(), is_less as *const F)
    == old(verify::count(v.as_ptr(), v.len(), is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted(v.as_ptr(), v.len(), is_less as *const F)))]
#[safety::requires(v.len() <= SMALL_SORT_FALLBACK_THRESHOLD)]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, true)))]
#[cfg_attr(kani, kani::modifies(v, verify::comparator_frame(is_less, v.as_ptr())))]
fn small_sort_fallback<T, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
    if v.len() >= 2 {
        insertion_sort_shift_left(v, 1, is_less);
    }
}

#[cfg_attr(kani, safety::ensures(|_| verify::count(v.as_ptr(), v.len(), is_less as *const F)
    == old(verify::count(v.as_ptr(), v.len(), is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted(v.as_ptr(), v.len(), is_less as *const F)))]
#[safety::requires(v.len() <= SMALL_SORT_GENERAL_THRESHOLD)]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, true)))]
#[cfg_attr(kani, kani::modifies(v, verify::comparator_frame(is_less, v.as_ptr())))]
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

#[cfg_attr(kani, safety::ensures(|_| verify::count(v.as_ptr(), v.len(), is_less as *const F)
    == old(verify::count(v.as_ptr(), v.len(), is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted(v.as_ptr(), v.len(), is_less as *const F)))]
#[safety::requires(v.len() <= SMALL_SORT_GENERAL_THRESHOLD)]
#[safety::requires(v.len() < 2 || scratch.len() >= v.len() + 16)]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, true)))]
#[cfg_attr(kani, kani::modifies(v, scratch, verify::comparator_frame(is_less, v.as_ptr())))]
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
        intrinsics::abort_immediate();
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

#[cfg_attr(kani, safety::ensures(|_| verify::count(v.as_ptr(), v.len(), is_less as *const F)
    == old(verify::count(v.as_ptr(), v.len(), is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted(v.as_ptr(), v.len(), is_less as *const F)))]
#[safety::requires(v.len() <= SMALL_SORT_NETWORK_THRESHOLD)]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, true)))]
#[cfg_attr(kani, kani::modifies(v, verify::comparator_frame(is_less, v.as_ptr())))]
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
        intrinsics::abort_immediate();
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
#[cfg_attr(kani, safety::ensures(|_| verify::count((v as *const [T]).cast::<T>(), 9, is_less as *const F)
    == old(verify::count((v as *const [T]).cast::<T>(), 9, is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted((v as *const [T]).cast::<T>(), 9, is_less as *const F)))]
#[safety::requires(v.len() >= 9)]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, true)))]
#[cfg_attr(kani, kani::modifies(ptr::slice_from_raw_parts_mut(v.as_mut_ptr(), 9),
    verify::comparator_frame(is_less, v.as_ptr())))]
fn sort9_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() < 9 {
        intrinsics::abort_immediate();
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
#[cfg_attr(kani, safety::ensures(|_| verify::count((v as *const [T]).cast::<T>(), 13, is_less as *const F)
    == old(verify::count((v as *const [T]).cast::<T>(), 13, is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted((v as *const [T]).cast::<T>(), 13, is_less as *const F)))]
#[safety::requires(v.len() >= 13)]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, true)))]
#[cfg_attr(kani, kani::modifies(ptr::slice_from_raw_parts_mut(v.as_mut_ptr(), 13),
    verify::comparator_frame(is_less, v.as_ptr())))]
fn sort13_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() < 13 {
        intrinsics::abort_immediate();
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
#[cfg_attr(kani, safety::ensures(|_| verify::count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less as *const F)
    == old(verify::count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less as *const F)))]
#[safety::requires(offset > 0 && offset <= v.len())]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, true)))]
#[cfg_attr(kani, safety::requires(verify::insertion_domain(v.as_ptr(), v.len(), is_less as *const F)))]
#[cfg_attr(kani, safety::requires(verify::sorted(v.as_ptr(), offset, is_less as *const F)))]
#[cfg_attr(kani, kani::modifies(v, verify::comparator_frame(is_less, v.as_ptr())))]
pub fn insertion_sort_shift_left<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    offset: usize,
    is_less: &mut F,
) {
    let len = v.len();
    if offset == 0 || offset > len {
        intrinsics::abort_immediate();
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
#[cfg_attr(kani, safety::ensures(|_| verify::count(dst, 4, is_less as *const F)
    == old(verify::count(v_base, 4, is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted(dst, 4, is_less as *const F)))]
#[safety::ensures(|_| crate::ub_checks::can_dereference(
    crate::ptr::slice_from_raw_parts(dst as *const T, 4)
))]
#[safety::requires(crate::ub_checks::can_dereference(crate::ptr::slice_from_raw_parts(
    v_base, 4
)))]
#[safety::requires(crate::ub_checks::can_write(crate::ptr::slice_from_raw_parts_mut(dst, 4)))]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v_base, is_less as *const F, false)))]
#[safety::requires(crate::ub_checks::maybe_is_nonoverlapping(
    v_base as *const (),
    dst as *const (),
    size_of::<T>(),
    4,
))]
#[cfg_attr(
    kani,
    kani::modifies(
        crate::ptr::slice_from_raw_parts_mut(dst, 4),
        verify::comparator_frame(is_less, v_base)
    )
)]
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
#[cfg_attr(kani, safety::ensures(|_| verify::count(dst, 8, is_less as *const F)
    == old(verify::count(v_base, 8, is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted(dst, 8, is_less as *const F)))]
#[safety::requires(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(v_base, 8)))]
#[safety::requires(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(dst, 8)))]
#[safety::requires(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(scratch_base, 8)))]
#[safety::requires(crate::ub_checks::maybe_is_nonoverlapping(v_base.cast(), scratch_base.cast(), size_of::<T>(), 8))]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v_base, is_less as *const F, false)))]
#[safety::requires(crate::ub_checks::maybe_is_nonoverlapping(dst.cast(), scratch_base.cast(), size_of::<T>(), 8))]
#[cfg_attr(
    kani,
    kani::modifies(
        ptr::slice_from_raw_parts_mut(dst, 8),
        ptr::slice_from_raw_parts_mut(scratch_base, 8),
        verify::comparator_frame(is_less, v_base)
    )
)]
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
#[cfg_attr(kani, safety::ensures(|_| verify::count(dst, ptr::metadata(v as *const [T]), is_less as *const F)
    == old(verify::count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less as *const F))))]
#[cfg_attr(kani, safety::ensures(|_| verify::sorted(dst, ptr::metadata(v as *const [T]), is_less as *const F)))]
#[safety::ensures(|_| crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(dst, v.len())))]
#[safety::requires(v.len() >= 2)]
#[cfg_attr(kani, safety::requires(verify::comparator_frame_domain(v.as_ptr(), is_less as *const F, false)))]
#[cfg_attr(kani, safety::requires(verify::model_domain(v.as_ptr(), v.len(), is_less as *const F)))]
#[cfg_attr(kani, safety::requires(verify::sorted_halves(v.as_ptr(), v.len(), is_less as *const F)))]
#[safety::requires(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(dst, v.len())))]
#[safety::requires(crate::ub_checks::maybe_is_nonoverlapping(
    v.as_ptr().cast(), dst.cast(), size_of::<T>(), v.len()))]
#[cfg_attr(kani, kani::modifies(ptr::slice_from_raw_parts_mut(dst, v.len()),
    verify::comparator_frame(is_less, v.as_ptr())))]
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
    // Verification method and scope
    //
    // Harnesses execute the production bodies above, composing independently
    // proved callees with stub_verified. The three *_entry contracts call the
    // real trait methods: the pinned Kani cannot target their method-generic
    // specializations directly. These are forwarding contracts, not contracts
    // attached to the original trait methods.
    //
    // Functional entry proofs use concrete ordered, read-only callbacks, checking
    // nondecreasing keys and preservation of full-value counts. Each proof chooses
    // an arbitrary probe, so preservation holds for every value, including any
    // payload ignored by the ordering key. Modelled callbacks keep that probe
    // unchanged. Subsidiary profiles can track order or counts separately;
    // disabled observers and the blanket Comparator make no extra claim.
    // Closed safety callbacks allow arbitrary comparison results, including Cell
    // argument mutation. Their summaries do not imply sorting or permutation.
    //
    // Covered domains for the concrete type/callback profiles below (these
    // are proof bounds, not new runtime limits on the public functions):
    // - u8 stable/general and unstable/network entries: every length 0..=32;
    //   Cell<u8> fallback entries: 0..=16. Other native profiles cover their
    //   asserted small_sort_threshold(), which selects a 16- or 32-element route.
    // - insertion_sort_shift_left: functional u8 lengths 1..=17 and Cell<u8>
    //   lengths 1..=16; memory safety for i32 and mutating Cell<u8> at 1..=32.
    //   Every valid offset is symbolic. Unit slices also cover arbitrary valid
    //   usize lengths/offsets; this does not extend the non-ZST proof domain.
    // - swap_if_less: both positions in a 13-element fixture, including equal
    //   positions; the u8 model refinement also covers interior bases within 32
    //   elements. Unit swap positions are arbitrary usize values.
    // - sort4_stable: four readable source and four writable destination values;
    //   internal sort8/9/13 helpers cover their respective fixed regions.
    //   bidirectional_merge covers every live length 2..=32.
    // - has_efficient_in_place_swap has no length input; its root checks the
    //   listed concrete size/layout cases, rather than quantifying over all T.
    // Ranges are symbolic or exhaustively enumerated with compile-time checks.
    // Element values stay arbitrary, subject to the actual callee preconditions
    // (e.g. a sorted insertion prefix or sorted merge halves). Bounded loops
    // retain their unwinding assertions; no unbounded loop proof is claimed.
    //
    // Stub discipline:
    // - Reuse a contract only for its proved type, callback and length domain.
    //   The sized insertion adapters forward to proved insert_window/insert_tail
    //   contracts and frame only the initialized prefix, not unused scratch.
    // - checked_read/copy/copy_nonoverlapping keep the real intrinsic effects,
    //   assert memory obligations, and have independent primitive refinements.
    //   Their proved copy domain is at most 32 byte/ZST elements or one wider T.
    // - swap_branch_model and the byte merge-step models have real-body
    //   refinements checking effects, callback arguments/state and cursors.
    //   Merge trace wrappers execute those steps and assert the independently
    //   proved certificate; they do not assume the expected output.
    // - SafetyInsertHavoc is only for its listed closed callbacks and valid,
    //   padding-free, non-dropping element types. Arbitrary initialized prefix
    //   bytes overapproximate the real result, with the same frame. Separate
    //   real-helper and model contract roots cover each 17-/32-element profile;
    //   a proof of the model alone would not justify replacing the real helper.
    //   This havoc is never used to establish sorting/count postconditions.
    // - The unit insertion summary preserves the actual single callback call.
    // Mandatory safety-model guards use safety_check so should_panic cannot
    // accept them as the expected panic. Byte trace assertions are used only
    // in ordinary, non-panicking functional proofs. Boundary/partition covers
    // check reachability; they do not replace assertions or prove completeness.
    //
    // Limits: these are concrete instantiations, not a theorem for every T/F.
    // Larger legal non-ZST insertion/swap inputs are not covered. Panic unwinding
    // is not modeled; extra uninit-checks/valid-value-checks have not been run.
    // Harnesses for all seven targets do not imply completion of every literal
    // Challenge 8 requirement.

    use super::*;
    use crate::cell::Cell;
    use crate::{kani, ptr};

    #[safety::ensures(|_| pair_count(v_base, a_pos, b_pos, is_less as *const F)
        == old(pair_count(v_base, a_pos, b_pos, is_less as *const F)))]
    #[safety::ensures(|_| key_at(v_base, a_pos, is_less as *const F)
        == old(min_key(v_base, a_pos, b_pos, is_less as *const F)))]
    #[safety::ensures(|_| key_at(v_base, b_pos, is_less as *const F)
        == old(max_key(v_base, a_pos, b_pos, is_less as *const F)))]
    #[safety::ensures(|_| {
        crate::ub_checks::can_dereference(v_base.wrapping_add(a_pos))
            && crate::ub_checks::can_dereference(v_base.wrapping_add(b_pos))
    })]
    #[safety::requires(comparator_frame_domain(v_base, is_less as *const F, true))]
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
    #[kani::modifies(
        v_base.wrapping_add(a_pos),
        v_base.wrapping_add(b_pos),
        comparator_frame(is_less, v_base)
    )]
    unsafe fn swap_contract<T, F>(v_base: *mut T, a_pos: usize, b_pos: usize, is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        unsafe { super::swap_if_less(v_base, a_pos, b_pos, is_less) }
    }

    #[safety::ensures(|_| count(begin, inclusive_len(begin, tail), is_less as *const F)
        == old(count(begin, inclusive_len(begin, tail), is_less as *const F)))]
    #[safety::ensures(|_| sorted(begin, inclusive_len(begin, tail), is_less as *const F))]
    // Preserve initialized, valid values even for safety-only comparators.
    #[safety::ensures(|_| crate::ub_checks::can_dereference(
        ptr::slice_from_raw_parts(begin as *const T, inclusive_len(begin, tail))
    ))]
    #[safety::requires(
        insertion_region(begin, tail)
        && insertion_domain(begin, inclusive_len(begin, tail), is_less as *const F)
        && sorted(begin, inclusive_len(begin, tail) - 1, is_less as *const F)
    )]
    #[safety::requires(comparator_frame_domain(begin, is_less as *const F, true))]
    #[kani::modifies(
        ptr::slice_from_raw_parts_mut(begin, inclusive_len(begin, tail)),
        comparator_frame(is_less, begin)
    )]
    unsafe fn insert_tail_contract<T, F: FnMut(&T, &T) -> bool>(
        begin: *mut T,
        tail: *mut T,
        is_less: &mut F,
    ) {
        unsafe { super::insert_tail(begin, tail, is_less) }
    }

    pub(super) trait Comparator<T> {
        fn modelled() -> bool;
        fn tracks_order() -> bool;
        fn tracks_count() -> bool;
        fn key(value: &T) -> u128;
        fn matches(&self, value: &T) -> bool;
    }

    impl<T, F> Comparator<T> for F {
        default fn modelled() -> bool {
            false
        }
        default fn tracks_order() -> bool {
            false
        }
        default fn tracks_count() -> bool {
            false
        }
        default fn key(_: &T) -> u128 {
            0
        }
        default fn matches(&self, _: &T) -> bool {
            false
        }
    }

    // Only the listed concrete callback types get functional summaries. In
    // particular, an arbitrary user callback must never inherit a purity premise.
    macro_rules! comparator {
        ($name:ident, $ty:ty, $model:ty, |$x:ident| $project:expr, |$m:ident| $key:expr) => {
            comparator!($name, $ty, $model, |$x| $project, |$m| $key, true, true, false);
        };
        ($name:ident, $ty:ty, $model:ty, |$x:ident| $project:expr, |$m:ident| $key:expr,
            $order:expr, $count:expr, $arbitrary:expr) => {
            #[derive(kani::Arbitrary)]
            pub(super) struct $name {
                pub(super) probe: $model,
            }

            impl Comparator<$ty> for $name {
                fn modelled() -> bool {
                    true
                }
                fn tracks_order() -> bool {
                    $order
                }
                fn tracks_count() -> bool {
                    $count
                }
                fn key($x: &$ty) -> u128 {
                    let $m: $model = $project;
                    ($key) as u128
                }
                fn matches(&self, $x: &$ty) -> bool {
                    $project == self.probe
                }
            }

            impl<'a, 'b> FnOnce<(&'a $ty, &'b $ty)> for $name {
                type Output = bool;
                extern "rust-call" fn call_once(mut self, args: (&'a $ty, &'b $ty)) -> bool {
                    self.call_mut(args)
                }
            }
            impl<'a, 'b> FnMut<(&'a $ty, &'b $ty)> for $name {
                extern "rust-call" fn call_mut(&mut self, (a, b): (&'a $ty, &'b $ty)) -> bool {
                    if $arbitrary {
                        kani::any()
                    } else {
                        <Self as Comparator<$ty>>::key(a) < <Self as Comparator<$ty>>::key(b)
                    }
                }
            }
        };
    }

    comparator!(ByteOrder, u8, u8, |x| *x, |m| m);
    comparator!(ByteSorted, u8, u8, |x| *x, |m| m, true, false, false);
    comparator!(BytePermutation, u8, u8, |x| *x, |m| m, false, true, true);
    comparator!(WordSafety, i32, i32, |x| *x, |m| m, false, false, true);
    comparator!(WideOrder, u128, u128, |x| *x, |m| m);
    comparator!(BytesOrder, [u8; 17], [u8; 17], |x| *x, |m| m[0]);
    comparator!(CellOrder, crate::cell::Cell<u8>, u8, |x| x.get(), |m| m);

    // A closure can write through captures without changing its own bytes.
    // Therefore an arbitrary F cannot use the frame below. Accept only the
    // concrete pure observers and the closed safety callbacks defined here;
    // Cell argument mutation additionally needs the input in the write frame.
    trait ComparatorFrame {
        fn supported(mutable_arguments: bool) -> bool;
    }
    impl<F> ComparatorFrame for F {
        default fn supported(_: bool) -> bool {
            false
        }
    }
    impl<T> ComparatorFrame for CheckedSafety<T> {
        fn supported(_: bool) -> bool {
            true
        }
    }
    impl<T> ComparatorFrame for LocalSafetyComparator<T> {
        fn supported(_: bool) -> bool {
            true
        }
    }
    impl ComparatorFrame for MutatingCellSafety {
        fn supported(mutable_arguments: bool) -> bool {
            mutable_arguments
        }
    }
    pub(super) fn comparator_frame_domain<T, F: FnMut(&T, &T) -> bool>(
        _: *const T,
        _: *const F,
        mutable_arguments: bool,
    ) -> bool {
        <F as Comparator<T>>::modelled() || <F as ComparatorFrame>::supported(mutable_arguments)
    }

    /// Modelled comparators keep their probe immutable. The other supported
    /// callbacks may modify their own state; their types have no external captures.
    pub(super) fn comparator_frame<T, F: Comparator<T>>(cmp: &mut F, _: *const T) -> *mut [u8] {
        let bytes = if F::modelled() { 0 } else { size_of::<F>() };
        ptr::slice_from_raw_parts_mut((cmp as *mut F).cast::<u8>(), bytes)
    }

    pub(super) fn key_at<T, F: Comparator<T>>(base: *const T, index: usize, _: *const F) -> u128 {
        if !F::tracks_order() {
            return 0;
        }
        // SAFETY: used only for initialized elements in the function's read set.
        F::key(unsafe { &*base.wrapping_add(index) })
    }

    pub(super) fn min_key<T, F: Comparator<T>>(
        base: *const T,
        a: usize,
        b: usize,
        cmp: *const F,
    ) -> u128 {
        key_at(base, a, cmp).min(key_at(base, b, cmp))
    }

    pub(super) fn max_key<T, F: Comparator<T>>(
        base: *const T,
        a: usize,
        b: usize,
        cmp: *const F,
    ) -> u128 {
        key_at(base, a, cmp).max(key_at(base, b, cmp))
    }

    pub(super) fn pair_count<T, F: Comparator<T>>(
        base: *const T,
        a: usize,
        b: usize,
        cmp: *const F,
    ) -> usize {
        if !F::tracks_count() {
            return 0;
        }
        // SAFETY: both positions are initialized by the swap contract's precondition.
        unsafe {
            (&*cmp).matches(&*base.wrapping_add(a)) as usize
                + (&*cmp).matches(&*base.wrapping_add(b)) as usize
        }
    }

    comparator!(NonCopyOrder, NonCopyU8, u8, |x| x.0, |m| m);

    // Logical observations read values only, never padding or unused scratch.
    // These observers are loop-free. Sortedness uses a balanced conjunction;
    // occurrence counts preserve a common expression for each prefix.
    // The explicit domain check prevents silent truncation above 32 elements.
    const _: () = {
        assert!(SMALL_SORT_GENERAL_THRESHOLD == 32);
        assert!(SMALL_SORT_NETWORK_THRESHOLD == 32);
        assert!(SMALL_SORT_FALLBACK_THRESHOLD <= 16);
    };

    macro_rules! fold_32 {
        ($node:ident) => {
            $node!((
                ((((0, 1), (2, 3)), ((4, 5), (6, 7))), (((8, 9), (10, 11)), ((12, 13), (14, 15)))),
                (
                    (((16, 17), (18, 19)), ((20, 21), (22, 23))),
                    (((24, 25), (26, 27)), ((28, 29), (30, 31)))
                )
            ))
        };
    }

    pub(super) fn sorted<T, F: Comparator<T>>(base: *const T, len: usize, _: *const F) -> bool {
        if !F::tracks_order() {
            return true;
        }
        kani::safety_check(
            len <= SMALL_SORT_GENERAL_THRESHOLD,
            "SmallSort observation exceeds its 32-element proof domain",
        );
        macro_rules! ordered {
            (($left:tt, $right:tt)) => {
                ordered!($left) && ordered!($right)
            };
            (0) => {
                true
            };
            ($index:literal) => {
                $index >= len
                    || F::key(unsafe { &*base.wrapping_add($index - 1) })
                        <= F::key(unsafe { &*base.wrapping_add($index) })
            };
        }
        fold_32!(ordered)
    }

    pub(super) fn count<T, F: Comparator<T>>(base: *const T, len: usize, cmp: *const F) -> usize {
        if !F::tracks_count() {
            return 0;
        }
        kani::safety_check(
            len <= SMALL_SORT_GENERAL_THRESHOLD,
            "SmallSort observation exceeds its 32-element proof domain",
        );
        // Keep this loop-free, but associate additions from the left. The sum
        // for a prefix is then an exact subexpression of the next prefix sum,
        // matching the way insert_tail extends its sorted region.
        macro_rules! prefix_count {
            ($sum:expr;) => { $sum };
            ($sum:expr; $index:literal $(, $rest:literal)*) => {
                prefix_count!(
                    ($sum).wrapping_add(if $index < len {
                        unsafe { (&*cmp).matches(&*base.wrapping_add($index)) as u8 }
                    } else { 0u8 });
                    $($rest),*
                )
            };
        }
        // At most 32 Boolean contributions: wrapping addition equals the exact
        // mathematical sum. The independent count oracle checks this domain.
        // Defined arithmetic also avoids repeated overflow reachability probes
        // inside every use of this pure observation.
        prefix_count!(0u8; 0, 1, 2, 3, 4, 5, 6, 7,
            8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31) as usize
    }

    pub(super) fn sorted_halves<T, F: Comparator<T>>(
        base: *const T,
        len: usize,
        cmp: *const F,
    ) -> bool {
        let mid = len / 2;
        sorted(base, mid, cmp) && sorted(base.wrapping_add(mid), len - mid, cmp)
    }

    pub(super) fn model_domain<T, F: Comparator<T>>(_: *const T, len: usize, _: *const F) -> bool {
        !F::modelled() || len <= SMALL_SORT_GENERAL_THRESHOLD
    }

    // General sort inserts into halves of at most 16 elements. The network
    // sorts at most 17 elements without splitting, or two halves of at most 16.
    // State this exact scope on the reusable functional insertion contracts.
    // Memory-only comparators do not use either bounded sorting observation.
    pub(super) fn insertion_domain<T, F: Comparator<T>>(
        _: *const T,
        len: usize,
        _: *const F,
    ) -> bool {
        !(F::tracks_order() || F::tracks_count()) || len <= SMALL_SORT_NETWORK_THRESHOLD / 2 + 1
    }

    pub(super) fn inclusive_len<T>(begin: *const T, tail: *const T) -> usize {
        if size_of::<T>() == 0 {
            return 0;
        }
        (tail.addr().wrapping_sub(begin.addr()) / size_of::<T>()).wrapping_add(1)
    }

    pub(super) fn insertion_region<T>(begin: *const T, tail: *const T) -> bool {
        size_of::<T>() != 0
            && begin.addr() < tail.addr()
            && tail.addr().wrapping_sub(begin.addr()) % size_of::<T>() == 0
            && crate::ub_checks::same_allocation(begin, tail)
            && crate::ub_checks::can_dereference(tail)
            && crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(
                begin,
                inclusive_len(begin, tail),
            ))
            && crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(
                begin.cast_mut(),
                inclusive_len(begin, tail),
            ))
    }

    #[kani::proof_for_contract(super::sort9_optimal)]
    #[kani::solver(cadical)]
    #[kani::stub(super::swap_if_less, swap_branch_model)]
    #[kani::unwind(34)]
    fn modular_sort9_byte() {
        let mut values: [u8; 9] = kani::any();
        let mut cmp = ByteOrder { probe: kani::any() };
        super::sort9_optimal(&mut values, &mut cmp);
    }

    #[kani::proof_for_contract(super::sort13_optimal)]
    #[kani::stub(super::swap_if_less, use_swap13_contract)]
    #[kani::stub_verified(swap13_contract)]
    #[kani::unwind(34)]
    fn modular_sort13_byte() {
        let mut values: [u8; 13] = kani::any();
        let mut cmp = ByteOrder { probe: kani::any() };
        super::sort13_optimal(&mut values, &mut cmp);
    }

    // Each root uses the same comparator type as the corresponding consumer.
    #[kani::proof_for_contract(super::sort4_stable)]
    #[kani::unwind(34)]
    fn modular_sort4_byte() {
        let values: [u8; 4] = kani::any();
        let mut output = [MaybeUninit::<u8>::uninit(); 4];
        let mut cmp = ByteOrder { probe: kani::any() };
        unsafe { super::sort4_stable(values.as_ptr(), output.as_mut_ptr().cast(), &mut cmp) };
    }

    #[kani::proof_for_contract(super::bidirectional_merge)]
    #[kani::unwind(50)]
    fn modular_merge_byte_scratch() {
        let values: [u8; 8] = kani::any();
        let mut cmp = ByteOrder { probe: kani::any() };
        kani::assume(sorted_halves(values.as_ptr(), 8, &cmp));
        let mut scratch = [MaybeUninit::<u8>::uninit(); 48];
        let source = kani::any::<u8>() as usize;
        let dest = kani::any::<u8>() as usize;
        kani::assume(source <= 40 && dest <= 40);
        kani::assume(source + 8 <= dest || dest + 8 <= source);
        let base = scratch.as_mut_ptr().cast::<u8>();
        unsafe {
            ptr::copy_nonoverlapping(values.as_ptr(), base.add(source), 8);
            super::bidirectional_merge(
                slice::from_raw_parts(base.add(source), 8),
                base.add(dest),
                &mut cmp,
            );
        }
        kani::cover(
            source == 40 && dest == 0,
            "sorted-half and disjoint-region assumptions admit a boundary merge",
        );
    }

    #[kani::proof_for_contract(swap_contract)]
    fn swap_byte_order() {
        let mut values: [u8; 32] = kani::any();
        let a = kani::any::<u8>() as usize;
        let b = kani::any::<u8>() as usize;
        kani::assume(a < values.len() && b < values.len());
        let mut cmp = ByteOrder { probe: kani::any() };
        unsafe { swap_contract(values.as_mut_ptr(), a, b, &mut cmp) };
        kani::cover(a == b, "coincident positions");
    }
    // Cell<T> and UnsafeCell<T> are repr(transparent). Moving an array of T
    // into the corresponding Cell array therefore preserves every value and
    // every possible input; ManuallyDrop prevents a second owner from dropping T.
    // Unlike repeated Cell::any calls, the element type's optimized array
    // generator can supply the whole array to a contract havoc in one step.
    fn cells_from_array<T, const N: usize>(values: [T; N]) -> [Cell<T>; N] {
        assert_eq!(size_of::<[T; N]>(), size_of::<[Cell<T>; N]>());
        assert_eq!(align_of::<[T; N]>(), align_of::<[Cell<T>; N]>());
        let values = ManuallyDrop::new(values);
        unsafe { ptr::read((&*values as *const [T; N]).cast::<[Cell<T>; N]>()) }
    }

    impl<T: kani::Arbitrary> kani::Arbitrary for Cell<T> {
        fn any() -> Self {
            Cell::new(kani::any())
        }
        fn any_array<const N: usize>() -> [Self; N] {
            cells_from_array(kani::any::<[T; N]>())
        }
    }

    #[kani::proof]
    #[kani::unwind(34)]
    fn cell_array_generator_preserves_values() {
        let input: [u8; 32] = kani::any();
        let cells = cells_from_array(input);
        let mut i = 0;
        while i < input.len() {
            assert_eq!(cells[i].get(), input[i]);
            i += 1;
        }
        let empty: [Cell<u8>; 0] = cells_from_array([]);
        assert_eq!(empty.len(), 0);
    }

    #[derive(kani::Arbitrary)]
    struct NonCopyU8(u8);

    const LARGE_ELEMENT_SIZE: usize = 87;

    #[derive(kani::Arbitrary)]
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

    fn nondeterministic_cmp<T>(_: &T, _: &T) -> bool {
        kani::any()
    }

    // ---------------------------------------------------------------------
    // Safety contracts for the raw-pointer and public helper functions.
    // ---------------------------------------------------------------------

    macro_rules! gen_swap_if_less_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(swap_contract)]
            fn $name() {
                let mut values: [$ty; 13] = kani::any();
                let a_pos = kani::any::<u8>() as usize;
                let b_pos = kani::any::<u8>() as usize;
                let mut is_less = LocalSafetyComparator::<$ty> {
                    calls: 0,
                    decision: kani::any(),
                    random: false,
                    marker: crate::marker::PhantomData,
                };
                unsafe {
                    swap_contract(values.as_mut_ptr(), a_pos, b_pos, &mut is_less);
                }
                assert_eq!(is_less.calls, 1);

                kani::cover(
                    a_pos == 0 && b_pos == 12,
                    "maximum real call-site distance is reachable",
                );
            }
        };
    }

    gen_swap_if_less_harness!(harness_swap_if_less_u8, u8);
    gen_swap_if_less_harness!(harness_swap_if_less_u128, u128);

    #[kani::proof]
    fn harness_swap_if_less_unit() {
        let mut values = [(); 13];
        let a_pos = kani::any::<usize>();
        let b_pos = kani::any::<usize>();

        let mut is_less = nondeterministic_cmp::<()>;
        unsafe {
            swap_if_less(values.as_mut_ptr(), a_pos, b_pos, &mut is_less);
        }
        kani::cover(a_pos == usize::MAX && b_pos == 0, "ZST swap accepts arbitrary positions");
    }

    macro_rules! gen_sort4_stable_contract_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(sort4_stable)]
            fn $name() {
                let input: [$ty; 4] = kani::any();
                let mut output = [const { MaybeUninit::<$ty>::uninit() }; 4];
                let mut is_less = LocalSafetyComparator::<$ty> {
                    calls: 0,
                    decision: false,
                    random: true,
                    marker: crate::marker::PhantomData,
                };
                unsafe {
                    sort4_stable(input.as_ptr(), output.as_mut_ptr().cast::<$ty>(), &mut is_less);
                }
                assert_eq!(is_less.calls, 5);
                kani::cover(true, "the real sort4 body returns with its closed callback frame");
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

    // SmallSort needs at most 17 elements, while the general sort frontends
    // also call this helper for lengths up to 20. This safety-only root covers
    // every current call site, including arbitrary comparison outcomes.
    #[kani::proof]
    #[kani::stub(super::insert_tail, insert_tail_safety_havoc)]
    #[kani::unwind(34)]
    fn harness_insertion_sort_shift_left() {
        const MAX_LEN: usize = 32;
        let mut backing: [i32; MAX_LEN] = kani::any();
        let len = kani::any::<u8>() as usize;
        kani::assume(len >= 1 && len <= MAX_LEN);

        let offset = kani::any::<u8>() as usize;
        kani::assume(offset >= 1 && offset <= len);

        let mut is_less = WordSafety { probe: kani::any() };
        insertion_sort_shift_left(&mut backing[..len], offset, &mut is_less);
        assert!(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(
            backing.as_ptr(),
            len,
        )));
        kani::cover(len == MAX_LEN && offset == 1, "maximum insertion length returns");
    }

    #[kani::proof_for_contract(insert_tail_contract)]
    #[kani::unwind(34)]
    fn harness_insert_tail_safety() {
        let mut values: [i32; 32] = kani::any();
        let last = kani::any::<u8>() as usize;
        kani::assume(1 <= last && last < values.len());
        let mut cmp = WordSafety { probe: kani::any() };
        unsafe {
            insert_tail_contract(values.as_mut_ptr(), values.as_mut_ptr().add(last), &mut cmp);
        }
    }

    #[kani::proof]
    #[kani::unwind(2)]
    fn harness_insertion_sort_shift_left_unit() {
        let mut value = ();
        let len = kani::any::<usize>();
        let offset = kani::any::<usize>();
        kani::assume(1 <= offset && offset <= len);
        // A valid zero-sized slice needs no storage, regardless of its length.
        let values = unsafe { slice::from_raw_parts_mut(&mut value, len) };
        let mut cmp = nondeterministic_cmp::<()>;
        insertion_sort_shift_left(values, offset, &mut cmp);
        kani::cover(len == usize::MAX && offset == len, "ZST insertion accepts arbitrary lengths");
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
    }

    // This oracle fixture has distinct ordering and payload fields, so the
    // independent count check below can detect changes to an ignored payload.
    #[derive(Clone, Copy, PartialEq, Eq, kani::Arbitrary)]
    struct Tagged {
        key: u8,
        tag: u8,
    }

    // Emit covers only for representative roots. A false constant condition
    // still creates an unreachable cover in the pinned Kani, so use macro
    // selection instead of repeating a cover in every fixed-size case.
    macro_rules! representative_return_cover {
        (insert_span_byte_17, $moves:expr) => {
            kani::cover($moves, "maximal insertion moves the last value to the front");
        };
        (insertion_window_byte_17, $offset:expr) => {
            kani::cover($offset == 1, "maximal complete insertion sort returns");
        };
        ($name:ident, $len:expr) => {};
        (swap13_case_00_12) => {
            kani::cover(true, "complete prefix contract returns");
        };
        (insert_span_cell_17) => {
            kani::cover(true, "the maximal Cell insertion span returns");
        };
        (insert_span_wide_17) => {
            kani::cover(true, "the maximal wide insertion span returns");
        };
        (insert_span_bytes_17) => {
            kani::cover(true, "the maximal bytes insertion span returns");
        };
        (insert_span_noncopy_17) => {
            kani::cover(true, "the maximal noncopy insertion span returns");
        };
        ($name:ident) => {};
    }

    #[kani::proof_for_contract(super::sort4_stable)]
    #[kani::unwind(34)]
    fn modular_sort4_byte_regions() {
        let values: [u8; 4] = kani::any();
        let mut source_storage = [const { MaybeUninit::<u8>::uninit() }; 32];
        let mut output = [const { MaybeUninit::<u8>::uninit() }; 48];
        let source = kani::any::<u8>() as usize;
        let dest = kani::any::<u8>() as usize;
        kani::assume(source <= 28 && dest <= 44);
        let mut cmp = ByteOrder { probe: kani::any() };
        unsafe {
            let source_base = source_storage.as_mut_ptr().add(source).cast::<u8>();
            ptr::copy_nonoverlapping(values.as_ptr(), source_base, 4);
            super::sort4_stable(source_base, output.as_mut_ptr().add(dest).cast(), &mut cmp)
        };
    }
    #[kani::proof_for_contract(super::sort4_stable)]
    #[kani::unwind(34)]
    fn modular_sort4_wide() {
        let values: [u128; 4] = kani::any();
        let mut output = [const { MaybeUninit::<u128>::uninit() }; 4];
        let mut cmp = WideOrder { probe: kani::any() };
        unsafe { super::sort4_stable(values.as_ptr(), output.as_mut_ptr().cast(), &mut cmp) };
    }
    #[kani::proof_for_contract(super::sort4_stable)]
    #[kani::unwind(34)]
    fn modular_sort4_bytes() {
        let values: [[u8; 17]; 4] = kani::any();
        let mut output = [const { MaybeUninit::<[u8; 17]>::uninit() }; 4];
        let mut cmp = BytesOrder { probe: kani::any() };
        unsafe { super::sort4_stable(values.as_ptr(), output.as_mut_ptr().cast(), &mut cmp) };
    }
    #[kani::proof_for_contract(super::sort4_stable)]
    #[kani::unwind(34)]
    fn modular_sort4_noncopy_regions() {
        let values: [NonCopyU8; 4] = kani::any();
        let mut source_storage = [const { MaybeUninit::<NonCopyU8>::uninit() }; 32];
        let mut output = [const { MaybeUninit::<NonCopyU8>::uninit() }; 48];
        let source = kani::any::<u8>() as usize;
        let dest = kani::any::<u8>() as usize;
        kani::assume(source <= 28 && dest <= 44);
        let mut cmp = NonCopyOrder { probe: kani::any() };
        unsafe {
            let source_base = source_storage.as_mut_ptr().add(source).cast::<NonCopyU8>();
            ptr::copy_nonoverlapping(values.as_ptr(), source_base, 4);
            super::sort4_stable(source_base, output.as_mut_ptr().add(dest).cast(), &mut cmp)
        };
    }
    // Each type keeps the whole functional insertion domain, with arbitrary
    // values in exact regions of every span2..17. Constant geometry avoids
    // combining all start/end offsets into one SAT instance.
    macro_rules! typed_insert_span_cases {
        ($ty:ty, $cmp:ident, $make:expr, $bound:literal;
            $($name:ident: $len:literal),+ $(,)?) => {
            const _: () = {
                let lengths = [$($len),+];
                assert!(lengths.len() == 16);
                let mut i = 0;
                while i < lengths.len() { assert!(lengths[i] == i + 2); i += 1; }
            };
            $(
                #[kani::proof_for_contract(insert_tail_contract)]
                #[kani::unwind($bound)]
                fn $name() {
                    assert!(<$cmp as Comparator<$ty>>::modelled());
                    assert!(<$cmp as Comparator<$ty>>::tracks_order());
                    assert!(<$cmp as Comparator<$ty>>::tracks_count());
                    let mut values: [$ty; $len] = crate::array::from_fn(|_| $make);
                    let mut cmp = $cmp { probe: kani::any() };
                    let base = values.as_mut_ptr();
                    unsafe { insert_tail_contract(base, base.add($len - 1), &mut cmp) };
                    representative_return_cover!($name);
                }
            )+
        };
    }
    typed_insert_span_cases!(Cell<u8>, CellOrder, Cell::new(kani::any()), 34;
        insert_span_cell_02: 2,
        insert_span_cell_03: 3,
        insert_span_cell_04: 4,
        insert_span_cell_05: 5,
        insert_span_cell_06: 6,
        insert_span_cell_07: 7,
        insert_span_cell_08: 8,
        insert_span_cell_09: 9,
        insert_span_cell_10: 10,
        insert_span_cell_11: 11,
        insert_span_cell_12: 12,
        insert_span_cell_13: 13,
        insert_span_cell_14: 14,
        insert_span_cell_15: 15,
        insert_span_cell_16: 16,
        insert_span_cell_17: 17,
    );
    typed_insert_span_cases!(u128, WideOrder, kani::any::<u128>(), 34;
        insert_span_wide_02: 2,
        insert_span_wide_03: 3,
        insert_span_wide_04: 4,
        insert_span_wide_05: 5,
        insert_span_wide_06: 6,
        insert_span_wide_07: 7,
        insert_span_wide_08: 8,
        insert_span_wide_09: 9,
        insert_span_wide_10: 10,
        insert_span_wide_11: 11,
        insert_span_wide_12: 12,
        insert_span_wide_13: 13,
        insert_span_wide_14: 14,
        insert_span_wide_15: 15,
        insert_span_wide_16: 16,
        insert_span_wide_17: 17,
    );
    typed_insert_span_cases!([u8; 17], BytesOrder, kani::any::<[u8; 17]>(), 34;
        insert_span_bytes_02: 2,
        insert_span_bytes_03: 3,
        insert_span_bytes_04: 4,
        insert_span_bytes_05: 5,
        insert_span_bytes_06: 6,
        insert_span_bytes_07: 7,
        insert_span_bytes_08: 8,
        insert_span_bytes_09: 9,
        insert_span_bytes_10: 10,
        insert_span_bytes_11: 11,
        insert_span_bytes_12: 12,
        insert_span_bytes_13: 13,
        insert_span_bytes_14: 14,
        insert_span_bytes_15: 15,
        insert_span_bytes_16: 16,
        insert_span_bytes_17: 17,
    );
    typed_insert_span_cases!(NonCopyU8, NonCopyOrder, NonCopyU8(kani::any()), 34;
        insert_span_noncopy_02: 2,
        insert_span_noncopy_03: 3,
        insert_span_noncopy_04: 4,
        insert_span_noncopy_05: 5,
        insert_span_noncopy_06: 6,
        insert_span_noncopy_07: 7,
        insert_span_noncopy_08: 8,
        insert_span_noncopy_09: 9,
        insert_span_noncopy_10: 10,
        insert_span_noncopy_11: 11,
        insert_span_noncopy_12: 12,
        insert_span_noncopy_13: 13,
        insert_span_noncopy_14: 14,
        insert_span_noncopy_15: 15,
        insert_span_noncopy_16: 16,
        insert_span_noncopy_17: 17,
    );

    #[kani::proof_for_contract(super::sort8_stable)]
    #[kani::stub_verified(super::sort4_stable)]
    #[kani::stub_verified(super::bidirectional_merge)]
    #[kani::unwind(50)]
    fn modular_sort8_byte() {
        let values: [u8; 8] = kani::any();
        let mut source_storage = [MaybeUninit::<u8>::uninit(); 32];
        let mut scratch = [MaybeUninit::<u8>::uninit(); 48];
        let source = kani::any::<u8>() as usize;
        let dest = kani::any::<u8>() as usize;
        let temporary = kani::any::<u8>() as usize;
        kani::assume(source <= 24 && dest <= 40 && temporary <= 40);
        kani::assume(dest + 8 <= temporary || temporary + 8 <= dest);
        let mut cmp = ByteOrder { probe: kani::any() };
        unsafe {
            let source_base = source_storage.as_mut_ptr().add(source).cast::<u8>();
            ptr::copy_nonoverlapping(values.as_ptr(), source_base, 8);
            let base = scratch.as_mut_ptr().cast::<u8>();
            super::sort8_stable(source_base, base.add(dest), base.add(temporary), &mut cmp);
        }
    }

    #[kani::proof]
    fn full_value_oracle_detects_changed_payload() {
        let before = Tagged { key: kani::any(), tag: kani::any() };
        let after = Tagged { key: before.key, tag: before.tag ^ 1 };
        assert_eq!(before.key, after.key);
        assert_eq!(count_by_key(&[before], |x| *x, &before), 1);
        assert_eq!(count_by_key(&[after], |x| *x, &before), 0);
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn count_model_matches_reference() {
        let values: [u8; 32] = kani::any();
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 32);
        let cmp = ByteOrder { probe: kani::any() };
        assert!(<ByteOrder as Comparator<u8>>::modelled());
        assert_eq!(
            count(values.as_ptr(), len, &cmp),
            count_by_key(&values[..len], |x| *x, &cmp.probe)
        );
        assert_eq!(sorted(values.as_ptr(), len, &cmp), is_sorted_by_key(&values[..len], |x| *x));
        kani::cover(len == 32, "both observations agree over the complete domain");
    }

    // Forwarding contracts execute the real trait dispatch. The current Kani
    // pin cannot attach contracts to specialization defaults (#5116) or resolve
    // their method-level comparator generics (#4908). These adapters keep the
    // complete selected length domain; their bodies do not implement sorting.
    // These entry contracts require both order and full-value tracking; the
    // one-property diagnostic comparators cannot make an entry proof vacuous.
    #[safety::ensures(|_| count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less)
        == old(count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less)))]
    #[safety::ensures(|_| sorted((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less))]
    #[safety::requires(<F as Comparator<T>>::modelled()
        && <F as Comparator<T>>::tracks_order()
        && <F as Comparator<T>>::tracks_count())]
    #[safety::requires(ptr::metadata(v as *const [T]) <= <T as StableSmallSortTypeImpl>::small_sort_threshold())]
    #[safety::requires(<T as StableSmallSortTypeImpl>::small_sort_threshold() == SMALL_SORT_FALLBACK_THRESHOLD
        || ptr::metadata(v as *const [T]) < 2 || scratch.len() >= ptr::metadata(v as *const [T]) + 16)]
    #[kani::modifies(v, scratch, comparator_frame(is_less, (v as *const [T]).cast::<T>()))]
    fn stable_entry<T, F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        scratch: &mut [MaybeUninit<T>],
        is_less: &mut F,
    ) {
        <T as StableSmallSortTypeImpl>::small_sort(v, scratch, is_less);
    }

    #[safety::ensures(|_| count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less)
        == old(count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less)))]
    #[safety::ensures(|_| sorted((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less))]
    #[safety::requires(<F as Comparator<T>>::modelled()
        && <F as Comparator<T>>::tracks_order()
        && <F as Comparator<T>>::tracks_count())]
    #[safety::requires(ptr::metadata(v as *const [T]) <= <T as UnstableSmallSortTypeImpl>::small_sort_threshold())]
    #[kani::modifies(v, comparator_frame(is_less, (v as *const [T]).cast::<T>()))]
    fn unstable_entry<T, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
        <T as UnstableSmallSortTypeImpl>::small_sort(v, is_less);
    }

    #[safety::ensures(|_| count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less)
        == old(count((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less)))]
    #[safety::ensures(|_| sorted((v as *const [T]).cast::<T>(), ptr::metadata(v as *const [T]), is_less))]
    #[safety::requires(<F as Comparator<T>>::modelled()
        && <F as Comparator<T>>::tracks_order()
        && <F as Comparator<T>>::tracks_count())]
    #[safety::requires(ptr::metadata(v as *const [T]) <= <T as UnstableSmallSortFreezeTypeImpl>::small_sort_threshold())]
    #[kani::modifies(v, comparator_frame(is_less, (v as *const [T]).cast::<T>()))]
    fn unstable_freeze_entry<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        is_less: &mut F,
    ) {
        <T as UnstableSmallSortFreezeTypeImpl>::small_sort(v, is_less);
    }

    // Only this concrete instantiation has the complete matrix of proofs below.
    // A new element or comparator type must establish its own contract proof.
    trait Network13Domain {
        fn supported() -> bool;
    }
    impl<T, F> Network13Domain for (T, F) {
        default fn supported() -> bool {
            false
        }
    }
    impl Network13Domain for (u8, ByteOrder) {
        fn supported() -> bool {
            true
        }
    }
    fn network13_domain<T, F>(_: *const T, _: *const F) -> bool {
        <(T, F) as Network13Domain>::supported()
    }

    // The network reuses this whole-prefix preservation fact. Proving it once
    // avoids asking each network proof to reconstruct a sum of 13 counters
    // after every two-element exchange.
    #[safety::ensures(|_| count(base, 13, is_less as *const F)
        == old(count(base, 13, is_less as *const F)))]
    #[safety::ensures(|_| key_at(base, a, is_less as *const F)
        == old(min_key(base, a, b, is_less as *const F)))]
    #[safety::ensures(|_| key_at(base, b, is_less as *const F)
        == old(max_key(base, a, b, is_less as *const F)))]
    #[safety::requires(network13_domain(base, is_less as *const F))]
    #[safety::requires(a < b && b < 13)]
    #[safety::requires(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(base, 13)))]
    #[safety::requires(crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(base, 13)))]
    #[kani::modifies(base.wrapping_add(a), base.wrapping_add(b))]
    unsafe fn swap13_contract<T, F: FnMut(&T, &T) -> bool>(
        base: *mut T,
        a: usize,
        b: usize,
        is_less: &mut F,
    ) {
        unsafe { super::swap_if_less(base, a, b, is_less) }
    }

    // Separate the ordinary function substitution from the verified-contract
    // substitution: the pinned Kani otherwise recursively redirects the call
    // inside the contract wrapper back to that same wrapper.
    unsafe fn use_swap13_contract<T, F: FnMut(&T, &T) -> bool>(
        base: *mut T,
        a: usize,
        b: usize,
        is_less: &mut F,
    ) {
        unsafe { swap13_contract(base, a, b, is_less) }
    }

    // All ordered position pairs are checked separately, with arbitrary values.
    // Fixed positions let the verifier cancel the untouched count terms. The
    // compile-time enumeration check makes omission of a pair a build error.
    macro_rules! swap13_cases {
        ($($name:ident: ($a:literal, $b:literal)),+ $(,)?) => {
            const _: () = {
                let pairs = [$(($a, $b)),+];
                assert!(pairs.len() == 13 * 12 / 2);
                let mut i = 0;
                let mut a = 0;
                while a < 13 {
                    let mut b = a + 1;
                    while b < 13 {
                        assert!(pairs[i].0 == a && pairs[i].1 == b);
                        i += 1;
                        b += 1;
                    }
                    a += 1;
                }
            };
            $(
                #[kani::proof_for_contract(swap13_contract)]
                #[kani::unwind(34)]
                fn $name() {
                    let mut values: [u8; 13] = kani::any();
                    let mut cmp = ByteOrder { probe: kani::any() };
                    unsafe { swap13_contract(values.as_mut_ptr(), $a, $b, &mut cmp) };
                    representative_return_cover!($name);
                }
            )+
        };
    }
    swap13_cases!(
        swap13_case_00_01: (0, 1),
        swap13_case_00_02: (0, 2),
        swap13_case_00_03: (0, 3),
        swap13_case_00_04: (0, 4),
        swap13_case_00_05: (0, 5),
        swap13_case_00_06: (0, 6),
        swap13_case_00_07: (0, 7),
        swap13_case_00_08: (0, 8),
        swap13_case_00_09: (0, 9),
        swap13_case_00_10: (0, 10),
        swap13_case_00_11: (0, 11),
        swap13_case_00_12: (0, 12),
        swap13_case_01_02: (1, 2),
        swap13_case_01_03: (1, 3),
        swap13_case_01_04: (1, 4),
        swap13_case_01_05: (1, 5),
        swap13_case_01_06: (1, 6),
        swap13_case_01_07: (1, 7),
        swap13_case_01_08: (1, 8),
        swap13_case_01_09: (1, 9),
        swap13_case_01_10: (1, 10),
        swap13_case_01_11: (1, 11),
        swap13_case_01_12: (1, 12),
        swap13_case_02_03: (2, 3),
        swap13_case_02_04: (2, 4),
        swap13_case_02_05: (2, 5),
        swap13_case_02_06: (2, 6),
        swap13_case_02_07: (2, 7),
        swap13_case_02_08: (2, 8),
        swap13_case_02_09: (2, 9),
        swap13_case_02_10: (2, 10),
        swap13_case_02_11: (2, 11),
        swap13_case_02_12: (2, 12),
        swap13_case_03_04: (3, 4),
        swap13_case_03_05: (3, 5),
        swap13_case_03_06: (3, 6),
        swap13_case_03_07: (3, 7),
        swap13_case_03_08: (3, 8),
        swap13_case_03_09: (3, 9),
        swap13_case_03_10: (3, 10),
        swap13_case_03_11: (3, 11),
        swap13_case_03_12: (3, 12),
        swap13_case_04_05: (4, 5),
        swap13_case_04_06: (4, 6),
        swap13_case_04_07: (4, 7),
        swap13_case_04_08: (4, 8),
        swap13_case_04_09: (4, 9),
        swap13_case_04_10: (4, 10),
        swap13_case_04_11: (4, 11),
        swap13_case_04_12: (4, 12),
        swap13_case_05_06: (5, 6),
        swap13_case_05_07: (5, 7),
        swap13_case_05_08: (5, 8),
        swap13_case_05_09: (5, 9),
        swap13_case_05_10: (5, 10),
        swap13_case_05_11: (5, 11),
        swap13_case_05_12: (5, 12),
        swap13_case_06_07: (6, 7),
        swap13_case_06_08: (6, 8),
        swap13_case_06_09: (6, 9),
        swap13_case_06_10: (6, 10),
        swap13_case_06_11: (6, 11),
        swap13_case_06_12: (6, 12),
        swap13_case_07_08: (7, 8),
        swap13_case_07_09: (7, 9),
        swap13_case_07_10: (7, 10),
        swap13_case_07_11: (7, 11),
        swap13_case_07_12: (7, 12),
        swap13_case_08_09: (8, 9),
        swap13_case_08_10: (8, 10),
        swap13_case_08_11: (8, 11),
        swap13_case_08_12: (8, 12),
        swap13_case_09_10: (9, 10),
        swap13_case_09_11: (9, 11),
        swap13_case_09_12: (9, 12),
        swap13_case_10_11: (10, 11),
        swap13_case_10_12: (10, 12),
        swap13_case_11_12: (11, 12),
    );

    macro_rules! swap_profile_contract {
        ($name:ident, $cmp:ident) => {
            #[kani::proof_for_contract(swap_contract)]
            fn $name() {
                let mut values: [u8; 32] = kani::any();
                let start = kani::any::<u8>() as usize;
                let a = kani::any::<u8>() as usize;
                let b = kani::any::<u8>() as usize;
                kani::assume(start < 32 && a < 32 - start && b < 32 - start);
                let mut cmp = $cmp { probe: kani::any() };
                unsafe { swap_contract(values.as_mut_ptr().add(start), a, b, &mut cmp) };
            }
        };
    }
    swap_profile_contract!(swap_sorted_profile, ByteSorted);
    swap_profile_contract!(swap_permutation_profile, BytePermutation);

    // Executable abstraction of one compare-exchange. The refinement root below
    // checks the real branchless implementation against this branch form for
    // every u8 input, decision, relative position and interior allocation base.
    // Only the u8 network consumers may select this abstraction.
    trait SwapModelElement: Sized {
        unsafe fn exchange<F: FnMut(&Self, &Self) -> bool>(
            base: *mut Self,
            a: usize,
            b: usize,
            is_less: &mut F,
        );
    }
    impl<T> SwapModelElement for T {
        default unsafe fn exchange<F: FnMut(&T, &T) -> bool>(
            _: *mut T,
            _: usize,
            _: usize,
            _: &mut F,
        ) {
            kani::safety_check(false, "the compare-exchange refinement covers only u8");
        }
    }
    impl SwapModelElement for u8 {
        unsafe fn exchange<F: FnMut(&u8, &u8) -> bool>(
            base: *mut u8,
            a: usize,
            b: usize,
            is_less: &mut F,
        ) {
            unsafe {
                let left = base.add(a);
                let right = base.add(b);
                // Match the real primitive's ordering: invoke the comparator
                // before loading the values that will be exchanged.
                let exchange = is_less(&*right, &*left);
                let x = *left;
                let y = *right;
                *left = if exchange { y } else { x };
                *right = if exchange { x } else { y };
            }
        }
    }

    // Kani requires the original generic signature. The default implementation
    // rejects every type outside the u8 refinement domain.
    unsafe fn swap_branch_model<T, F: FnMut(&T, &T) -> bool>(
        base: *mut T,
        a: usize,
        b: usize,
        is_less: &mut F,
    ) {
        unsafe { <T as SwapModelElement>::exchange(base, a, b, is_less) }
    }

    #[kani::proof]
    #[kani::unwind(34)]
    fn swap_branch_refines_real_u8() {
        let input: [u8; 32] = kani::any();
        let mut actual = input;
        let mut model = input;
        let start = kani::any::<u8>() as usize;
        let a = kani::any::<u8>() as usize;
        let b = kani::any::<u8>() as usize;
        kani::assume(start < 32 && a < 32 - start && b < 32 - start);
        let decision: bool = kani::any();
        let actual_base = actual.as_mut_ptr().wrapping_add(start);
        let model_base = model.as_mut_ptr().wrapping_add(start);
        let mut actual_calls = 0u8;
        let mut model_calls = 0u8;
        unsafe {
            super::swap_if_less(actual_base, a, b, &mut |lhs: &u8, rhs: &u8| {
                assert!(ptr::eq(lhs, actual_base.wrapping_add(b)));
                assert!(ptr::eq(rhs, actual_base.wrapping_add(a)));
                assert_eq!(*lhs, input[start + b]);
                assert_eq!(*rhs, input[start + a]);
                actual_calls += 1;
                decision
            });
            swap_branch_model::<u8, _>(model_base, a, b, &mut |lhs: &u8, rhs: &u8| {
                assert!(ptr::eq(lhs, model_base.wrapping_add(b)));
                assert!(ptr::eq(rhs, model_base.wrapping_add(a)));
                assert_eq!(*lhs, input[start + b]);
                assert_eq!(*rhs, input[start + a]);
                model_calls += 1;
                decision
            });
        }
        assert_eq!(actual, model);
        assert_eq!(actual_calls, 1);
        assert_eq!(model_calls, 1);
        kani::cover(
            start == 1 && a == 0 && b == 30 && decision,
            "the real and model exchanges return at an interior-base boundary",
        );
    }
    // Separate ordinary substitution from verified-contract substitution.
    unsafe fn use_insert_tail_contract<T, F: FnMut(&T, &T) -> bool>(
        begin: *mut T,
        tail: *mut T,
        is_less: &mut F,
    ) {
        unsafe { insert_tail_contract(begin, tail, is_less) }
    }

    // Preserve the count of the entire initialized window, even though one
    // insertion touches only its prefix. A sized frame avoids rebuilding a
    // variable-length slice and a prefix-count identity in every outer step.
    #[safety::ensures(|_| count((v as *const [T; N]).cast::<T>(), N, cmp as *const F)
        == old(count((v as *const [T; N]).cast::<T>(), N, cmp as *const F)))]
    #[safety::ensures(|_| sorted((v as *const [T; N]).cast::<T>(), last + 1, cmp as *const F))]
    #[safety::requires(N <= 17 && 1 <= last && last < N)]
    #[safety::requires(<F as Comparator<T>>::modelled())]
    #[safety::requires(sorted(v.as_ptr(), last, cmp as *const F))]
    #[kani::modifies(v)]
    fn insert_window<T, F: FnMut(&T, &T) -> bool, const N: usize>(
        v: &mut [T; N],
        last: usize,
        cmp: &mut F,
    ) {
        unsafe { super::insert_tail(v.as_mut_ptr(), v.as_mut_ptr().add(last), cmp) }
    }

    // Byte and Cell proofs share the same window/outer-loop construction.
    // Keep elementwise Cell initialization: it generates every input value.
    macro_rules! insertion_window_case {
        ($window:ident, $sort:ident, $adapter:ident, $cmp:ident,
            $ty:ty, $values:expr, $n:literal, $bound:literal) => {
            #[kani::proof_for_contract(insert_window)]
            #[kani::stub(super::insert_tail, use_insert_tail_contract)]
            #[kani::stub_verified(insert_tail_contract)]
            #[kani::unwind($bound)]
            fn $window() {
                let mut values: [$ty; $n] = $values;
                let last = kani::any::<u8>() as usize;
                kani::assume(1 <= last && last < $n);
                let mut cmp = $cmp { probe: kani::any() };
                insert_window(&mut values, last, &mut cmp);
            }

            unsafe fn $adapter<T, F: FnMut(&T, &T) -> bool>(
                begin: *mut T,
                tail: *mut T,
                cmp: &mut F,
            ) {
                let last = inclusive_len(begin, tail).wrapping_sub(1);
                unsafe { insert_window(&mut *begin.cast::<[T; $n]>(), last, cmp) }
            }

            #[kani::proof_for_contract(super::insertion_sort_shift_left)]
            #[kani::stub(super::insert_tail, $adapter)]
            #[kani::stub_verified(insert_window)]
            #[kani::unwind($bound)]
            fn $sort() {
                let mut values: [$ty; $n] = $values;
                let offset = kani::any::<u8>() as usize;
                kani::assume(1 <= offset && offset <= $n);
                let mut cmp = $cmp { probe: kani::any() };
                super::insertion_sort_shift_left(&mut values, offset, &mut cmp);
                representative_return_cover!($sort, offset);
            }
        };
    }

    // Every nonempty length in SmallSort's insertion domain is enumerated.
    // The first proof uses the smallest allocation for that span; the second lifts its prefix
    // count to the complete window; the third verifies the real outer loop for
    // every starting offset. No element values are bounded beyond their type.
    macro_rules! insertion_window_cases {
        ($($span:ident, $window:ident, $sort:ident, $adapter:ident: $n:literal, $bound:literal);+ $(;)?) => {
            const _: () = {
                let lengths = [$($n),+];
                let bounds = [$($bound),+];
                assert!(lengths.len() == 16);
                let mut i = 0;
                while i < lengths.len() {
                    assert!(lengths[i] == i + 2);
                    assert!(bounds[i] == lengths[i] + 1);
                    i += 1;
                }
            };
            $(
                #[kani::proof_for_contract(insert_tail_contract)]
                #[kani::unwind(18)]
                fn $span() {
                    let mut values: [u8; $n] = kani::any();
                    let mut cmp = ByteOrder { probe: kani::any() };
                    let _moves_to_front = values[$n - 1] < values[0];
                    unsafe {
                        insert_tail_contract(values.as_mut_ptr(), values.as_mut_ptr().add($n - 1), &mut cmp);
                    }
                    representative_return_cover!($span, _moves_to_front);
                }

                insertion_window_case!(
                    $window, $sort, $adapter, ByteOrder, u8, kani::any(), $n, $bound
                );
            )+
        };
    }
    insertion_window_cases!(
        insert_span_byte_02, insert_window_byte_02, insertion_window_byte_02, use_insert_window_02: 2, 3;
        insert_span_byte_03, insert_window_byte_03, insertion_window_byte_03, use_insert_window_03: 3, 4;
        insert_span_byte_04, insert_window_byte_04, insertion_window_byte_04, use_insert_window_04: 4, 5;
        insert_span_byte_05, insert_window_byte_05, insertion_window_byte_05, use_insert_window_05: 5, 6;
        insert_span_byte_06, insert_window_byte_06, insertion_window_byte_06, use_insert_window_06: 6, 7;
        insert_span_byte_07, insert_window_byte_07, insertion_window_byte_07, use_insert_window_07: 7, 8;
        insert_span_byte_08, insert_window_byte_08, insertion_window_byte_08, use_insert_window_08: 8, 9;
        insert_span_byte_09, insert_window_byte_09, insertion_window_byte_09, use_insert_window_09: 9, 10;
        insert_span_byte_10, insert_window_byte_10, insertion_window_byte_10, use_insert_window_10: 10, 11;
        insert_span_byte_11, insert_window_byte_11, insertion_window_byte_11, use_insert_window_11: 11, 12;
        insert_span_byte_12, insert_window_byte_12, insertion_window_byte_12, use_insert_window_12: 12, 13;
        insert_span_byte_13, insert_window_byte_13, insertion_window_byte_13, use_insert_window_13: 13, 14;
        insert_span_byte_14, insert_window_byte_14, insertion_window_byte_14, use_insert_window_14: 14, 15;
        insert_span_byte_15, insert_window_byte_15, insertion_window_byte_15, use_insert_window_15: 15, 16;
        insert_span_byte_16, insert_window_byte_16, insertion_window_byte_16, use_insert_window_16: 16, 17;
        insert_span_byte_17, insert_window_byte_17, insertion_window_byte_17, use_insert_window_17: 17, 18;
    );

    #[kani::proof_for_contract(super::insertion_sort_shift_left)]
    fn insertion_window_byte_01() {
        let mut values: [u8; 1] = kani::any();
        let mut cmp = ByteOrder { probe: kani::any() };
        super::insertion_sort_shift_left(&mut values, 1, &mut cmp);
    }

    #[kani::proof_for_contract(super::insertion_sort_shift_left)]
    fn insertion_window_cell_01() {
        let mut values = [Cell::new(kani::any())];
        let mut cmp = CellOrder { probe: kani::any() };
        super::insertion_sort_shift_left(&mut values, 1, &mut cmp);
    }

    // The non-Freeze entries use fallback insertion, whose complete domain is
    // 0..=16. Lift the independently proved Cell insert_tail spans to sized
    // windows before using their summaries in the unchanged outer loop.
    macro_rules! cell_insertion_window_cases {
        ($($window:ident, $sort:ident, $adapter:ident: $n:literal, $bound:literal);+ $(;)?) => {
            const _: () = {
                let lengths = [$($n),+];
                assert!(lengths.len() == SMALL_SORT_FALLBACK_THRESHOLD - 1);
                let mut i = 0;
                while i < lengths.len() { assert!(lengths[i] == i + 2); i += 1; }
            };
            $(
                insertion_window_case!(
                    $window, $sort, $adapter, CellOrder, Cell<u8>,
                    crate::array::from_fn(|_| Cell::new(kani::any())), $n, $bound
                );
            )+
        };
    }
    cell_insertion_window_cases!(
        insert_window_cell_02, insertion_window_cell_02, use_cell_window_02: 2, 3;
        insert_window_cell_03, insertion_window_cell_03, use_cell_window_03: 3, 4;
        insert_window_cell_04, insertion_window_cell_04, use_cell_window_04: 4, 5;
        insert_window_cell_05, insertion_window_cell_05, use_cell_window_05: 5, 6;
        insert_window_cell_06, insertion_window_cell_06, use_cell_window_06: 6, 7;
        insert_window_cell_07, insertion_window_cell_07, use_cell_window_07: 7, 8;
        insert_window_cell_08, insertion_window_cell_08, use_cell_window_08: 8, 9;
        insert_window_cell_09, insertion_window_cell_09, use_cell_window_09: 9, 10;
        insert_window_cell_10, insertion_window_cell_10, use_cell_window_10: 10, 11;
        insert_window_cell_11, insertion_window_cell_11, use_cell_window_11: 11, 12;
        insert_window_cell_12, insertion_window_cell_12, use_cell_window_12: 12, 13;
        insert_window_cell_13, insertion_window_cell_13, use_cell_window_13: 13, 14;
        insert_window_cell_14, insertion_window_cell_14, use_cell_window_14: 14, 15;
        insert_window_cell_15, insertion_window_cell_15, use_cell_window_15: 15, 16;
        insert_window_cell_16, insertion_window_cell_16, use_cell_window_16: 16, 17;
    );

    #[kani::proof_for_contract(super::small_sort_fallback)]
    #[kani::stub_verified(super::insertion_sort_shift_left)]
    #[kani::unwind(18)]
    fn fallback_cell_contract() {
        let mut values: [Cell<u8>; 16] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 16);
        let mut cmp = CellOrder { probe: kani::any() };
        super::small_sort_fallback(&mut values[..len], &mut cmp);
        kani::cover(len == 16, "non-Freeze fallback returns at its full threshold");
    }

    #[kani::proof_for_contract(stable_entry)]
    #[kani::stub_verified(super::insertion_sort_shift_left)]
    #[kani::unwind(18)]
    fn entry_cell_stable() {
        let mut values: [Cell<u8>; 16] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 16);
        let mut scratch: [MaybeUninit<Cell<u8>>; 0] = [];
        let mut cmp = CellOrder { probe: kani::any() };
        stable_entry(&mut values[..len], &mut scratch, &mut cmp);
        kani::cover(len == 16, "stable non-Freeze dispatch returns at its full threshold");
    }

    #[kani::proof_for_contract(unstable_entry)]
    #[kani::stub_verified(super::small_sort_fallback)]
    #[kani::unwind(18)]
    fn entry_cell_unstable() {
        let mut values: [Cell<u8>; 16] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 16);
        let mut cmp = CellOrder { probe: kani::any() };
        unstable_entry(&mut values[..len], &mut cmp);
        kani::cover(len == 16, "unstable non-Freeze dispatch returns at its full threshold");
    }

    // A proof-local read region distinguishes a legal initialized prefix
    // from other bytes in its larger backing allocation. Native insertion
    // contract roots activate it; other roots leave it inactive.
    static mut INSERT_READ_ACTIVE: bool = false;
    static mut INSERT_READ_BEGIN: *const u8 = ptr::null();
    static mut INSERT_READ_END: *const u8 = ptr::null();

    fn check_insertion_read<T>(src: *const T, count: usize) {
        unsafe {
            if INSERT_READ_ACTIVE
                && crate::ub_checks::same_allocation(src, INSERT_READ_BEGIN.cast::<T>())
            {
                kani::safety_check(
                    crate::ub_checks::is_valid_allocation_size(size_of::<T>(), count),
                    "insertion read length is representable",
                );
                let bytes = size_of::<T>() * count;
                let start = src.addr();
                let begin = INSERT_READ_BEGIN.addr();
                let end = INSERT_READ_END.addr();
                kani::safety_check(
                    start >= begin && start <= end && bytes <= end - start,
                    "insertion reads only its initialized prefix",
                );
            }
        }
    }

    // Checked memory primitives retain every byte-level effect of the real
    // operations, while making alignment/range/initialization obligations
    // explicit safety properties (not ordinary panic assertions).
    // No violation is assumed away. The refinement roots below have NO stubs.
    unsafe fn checked_read<T>(src: *const T) -> T {
        kani::safety_check(
            crate::ub_checks::can_dereference(src),
            "checked read requires an aligned initialized valid source",
        );
        check_insertion_read(src, 1);
        let value = unsafe { crate::intrinsics::read_via_copy(src) };
        kani::safety_check(
            crate::ub_checks::can_dereference(ptr::addr_of!(value)),
            "checked read returns an initialized valid value",
        );
        value
    }

    unsafe fn checked_copy<T>(src: *const T, dst: *mut T, count: usize) {
        // The verified non-byte routes move one T at a time. Only the byte
        // network performs a bulk copy. Reject any unproved wider call domain.
        kani::safety_check(
            count <= 32 && (size_of::<T>() <= 1 || count <= 1),
            "checked copy stays in its proved byte or single-element domain",
        );
        kani::safety_check(
            crate::ub_checks::is_valid_allocation_size(size_of::<T>(), count),
            "checked copy has a representable byte length",
        );
        kani::safety_check(
            crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(src, count)),
            "checked copy requires an aligned initialized valid source",
        );
        kani::safety_check(
            crate::ub_checks::can_write(ptr::slice_from_raw_parts_mut(dst, count)),
            "checked copy requires an aligned writable destination",
        );
        check_insertion_read(src, count);
        unsafe { crate::intrinsics::copy(src, dst, count) };
        kani::safety_check(
            crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(dst, count)),
            "checked copy preserves initialized valid values",
        );
    }

    unsafe fn checked_copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
        kani::safety_check(
            crate::ub_checks::is_valid_allocation_size(size_of::<T>(), count),
            "checked nonoverlapping copy has a representable byte length",
        );
        kani::safety_check(
            crate::ub_checks::maybe_is_nonoverlapping(
                src.cast(),
                dst.cast(),
                size_of::<T>(),
                count,
            ),
            "checked copy regions do not overlap",
        );
        // On disjoint regions memmove and memcpy have identical effects.
        // Use the supported copy intrinsic after checking non-overlap, rather
        // than suppressing valid-value instrumentation on copy_nonoverlapping.
        unsafe { checked_copy(src, dst, count) };
    }

    fn checked_nondeterministic_cmp<T>(a: &T, b: &T) -> bool {
        check_insertion_read(a as *const T, 1);
        check_insertion_read(b as *const T, 1);
        kani::safety_check(
            crate::ub_checks::can_dereference(a as *const T),
            "left comparison argument is aligned initialized and valid",
        );
        kani::safety_check(
            crate::ub_checks::can_dereference(b as *const T),
            "right comparison argument is aligned initialized and valid",
        );
        kani::any()
    }

    // Named callbacks make the scope of the bulk safety summary explicit.
    // Their decisions are arbitrary; neither callback owns mutable state.
    struct CheckedSafety<T>(crate::marker::PhantomData<T>);

    impl<'a, 'b, T> FnOnce<(&'a T, &'b T)> for CheckedSafety<T> {
        type Output = bool;
        extern "rust-call" fn call_once(mut self, args: (&'a T, &'b T)) -> bool {
            self.call_mut(args)
        }
    }
    impl<'a, 'b, T> FnMut<(&'a T, &'b T)> for CheckedSafety<T> {
        extern "rust-call" fn call_mut(&mut self, (a, b): (&'a T, &'b T)) -> bool {
            checked_nondeterministic_cmp(a, b)
        }
    }

    // Unlike a generic closure, this callback cannot hold mutable references
    // to objects outside its own state and the algorithm's argument region.
    struct LocalSafetyComparator<T> {
        calls: u8,
        decision: bool,
        random: bool,
        marker: crate::marker::PhantomData<T>,
    }
    impl<'a, 'b, T> FnOnce<(&'a T, &'b T)> for LocalSafetyComparator<T> {
        type Output = bool;
        extern "rust-call" fn call_once(mut self, args: (&'a T, &'b T)) -> bool {
            self.call_mut(args)
        }
    }
    impl<'a, 'b, T> FnMut<(&'a T, &'b T)> for LocalSafetyComparator<T> {
        extern "rust-call" fn call_mut(&mut self, _: (&'a T, &'b T)) -> bool {
            self.calls = self.calls.wrapping_add(1);
            if self.random { kani::any() } else { self.decision }
        }
    }

    struct MutatingCellSafety;

    impl<'a, 'b> FnOnce<(&'a Cell<u8>, &'b Cell<u8>)> for MutatingCellSafety {
        type Output = bool;
        extern "rust-call" fn call_once(mut self, args: (&'a Cell<u8>, &'b Cell<u8>)) -> bool {
            self.call_mut(args)
        }
    }
    impl<'a, 'b> FnMut<(&'a Cell<u8>, &'b Cell<u8>)> for MutatingCellSafety {
        extern "rust-call" fn call_mut(&mut self, (a, b): (&'a Cell<u8>, &'b Cell<u8>)) -> bool {
            arbitrary_cell_compare(a, b)
        }
    }

    // A valid Rust comparator can modify a captured Cell while leaving its
    // closure object's bytes unchanged. Execute the real sort4 body with that
    // callback, and check that the narrower reusable contract rejects its type.
    // This is deliberately a plain proof: it consumes no sorting contract.
    #[kani::proof]
    fn comparator_frame_rejects_external_writes() {
        let input: [u8; 4] = kani::any();
        let mut output = [MaybeUninit::<u8>::uninit(); 4];
        let external = Cell::new(kani::any::<u8>());
        let before = external.get();
        let mut cmp = |a: &u8, b: &u8| {
            external.set(external.get().wrapping_add(1));
            a < b
        };
        assert!(!comparator_frame_domain(input.as_ptr(), &cmp, false));
        assert!(!comparator_frame_domain(input.as_ptr(), &cmp, true));
        let byte = ByteOrder { probe: kani::any() };
        assert!(comparator_frame_domain(input.as_ptr(), &byte, false));
        let checked = CheckedSafety::<u8>(crate::marker::PhantomData);
        assert!(comparator_frame_domain(input.as_ptr(), &checked, false));
        let cells = [Cell::new(0u8)];
        let mutating = MutatingCellSafety;
        assert!(comparator_frame_domain(cells.as_ptr(), &mutating, true));
        assert!(!comparator_frame_domain(cells.as_ptr(), &mutating, false));
        unsafe { super::sort4_stable(input.as_ptr(), output.as_mut_ptr().cast(), &mut cmp) };
        assert_eq!(external.get(), before.wrapping_add(5));
        kani::cover(
            true,
            "a valid captured-write callback executes the real body outside the reusable contract",
        );
    }

    // All eight fixture types accept every initialized byte pattern and have
    // no padding. Non-byte profiles cover the checked zero/one-element domain;
    // byte profiles cover every copy count through 32. The checked call-site
    // guard above prevents extending these results to an unproved copy count.
    // Source/destination regions have minimal capacities; all values and all
    // legal positions in those regions remain symbolic.
    #[repr(C, align(16))]
    struct MemoryFixture<const N: usize>([u8; N]);

    // An independent arbitrary byte probe proves equality of the ENTIRE
    // buffer, including untouched bytes. These roots have NO stubs: real
    // ptr::read/copy/copy_nonoverlapping are compared with the checked versions.
    // One byte and one non-byte witness cover the two distinct count domains;
    // the other types use the same satisfiable bounds and initialized fixtures.
    macro_rules! checked_memory_return_cover {
        (checked_memory_byte, $count:ident, $src:ident, $dst:ident, $probe:ident) => {
            kani::cover(
                $count == 32 && $src == 0 && $dst == 16 && $probe == 47,
                "the complete overlapping byte-copy domain returns",
            );
        };
        (checked_memory_wide, $count:ident, $src:ident, $dst:ident, $probe:ident) => {
            kani::cover(
                $count == 1 && $src == 0 && $dst == 1 && $probe == 31,
                "the complete single-element wide-copy domain returns",
            );
        };
        ($name:ident, $count:ident, $src:ident, $dst:ident, $probe:ident) => {};
    }
    macro_rules! checked_memory_refinement {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            #[kani::unwind(50)]
            fn $name() {
                const CAP: usize = if size_of::<$ty>() <= 1 { 48 } else { 2 };
                const BYTES: usize = CAP * size_of::<$ty>();
                const STORAGE: usize = if BYTES == 0 { 16 } else { BYTES.div_ceil(16) * 16 };
                const _: () = {
                    assert!(align_of::<$ty>() <= 16);
                    assert!(STORAGE <= u16::MAX as usize);
                };
                let input: [u8; STORAGE] = kani::any();
                let before: [u8; STORAGE] = kani::any();
                let mut actual = MemoryFixture(input);
                let mut model = MemoryFixture(input);
                let mut actual_out = MemoryFixture(before);
                let mut model_out = MemoryFixture(before);
                let count = if size_of::<$ty>() <= 1 {
                    kani::any::<u8>() as usize
                } else {
                    kani::any::<bool>() as usize
                };
                let src = kani::any::<u8>() as usize;
                let dst = kani::any::<u8>() as usize;
                let index = kani::any::<u8>() as usize;
                let probe = kani::any::<u16>() as usize;
                kani::assume(
                    count <= 32
                        && count <= CAP
                        && src <= CAP - count
                        && dst <= CAP - count
                        && index < CAP
                        && probe < STORAGE,
                );
                let a = actual.0.as_mut_ptr().cast::<$ty>();
                let m = model.0.as_mut_ptr().cast::<$ty>();
                unsafe {
                    let actual_value = ManuallyDrop::new(ptr::read(a.add(index)));
                    let model_value = ManuallyDrop::new(checked_read(m.add(index)));
                    if size_of::<$ty>() != 0 {
                        let byte = probe % size_of::<$ty>().max(1);
                        assert_eq!(
                            ptr::read(ptr::addr_of!(actual_value).cast::<u8>().add(byte)),
                            ptr::read(ptr::addr_of!(model_value).cast::<u8>().add(byte))
                        );
                    }
                    ptr::copy(a.add(src), a.add(dst), count);
                    checked_copy(m.add(src), m.add(dst), count);
                }
                unsafe {
                    assert_eq!(
                        ptr::read(a.cast::<u8>().add(probe)),
                        ptr::read(m.cast::<u8>().add(probe))
                    );
                }
                unsafe {
                    ptr::copy_nonoverlapping(
                        a.add(src),
                        actual_out.0.as_mut_ptr().cast::<$ty>().add(dst),
                        count,
                    );
                    checked_copy_nonoverlapping(
                        m.add(src),
                        model_out.0.as_mut_ptr().cast::<$ty>().add(dst),
                        count,
                    );
                }
                unsafe {
                    assert_eq!(
                        ptr::read(a.cast::<u8>().add(probe)),
                        ptr::read(m.cast::<u8>().add(probe))
                    );
                }
                assert_eq!(actual_out.0[probe], model_out.0[probe]);
                checked_memory_return_cover!($name, count, src, dst, probe);
            }
        };
    }
    checked_memory_refinement!(checked_memory_byte, u8);
    checked_memory_refinement!(checked_memory_wide, u128);
    checked_memory_refinement!(checked_memory_bytes17, [u8; 17]);
    checked_memory_refinement!(checked_memory_noncopy, NonCopyU8);
    checked_memory_refinement!(checked_memory_largecopy, [u8; LARGE_ELEMENT_SIZE]);
    checked_memory_refinement!(checked_memory_largenoncopy, LargeNonCopy);
    checked_memory_refinement!(checked_memory_cell, Cell<u8>);
    checked_memory_refinement!(checked_memory_zst, ());

    // Cell fixtures use elementwise construction: their array generator uses
    // ptr::read, which this harness instruments for the insertion read region.
    // Safety summaries have no ordering premise for these callbacks. Every
    // legal prefix length and base offset is symbolic, while the read-region
    // check forbids relying on the initialized remainder of the backing array.
    macro_rules! safety_insert_contract_case {
        ($name:ident, $ty:ty, $values:expr, $cmp:expr $(, $extra:meta)* $(; $limit:literal)?) => {
            #[kani::proof_for_contract(insert_tail_contract)]
            $(#[$extra])*
            #[kani::stub(crate::ptr::read, checked_read)]
            #[kani::stub(crate::ptr::copy, checked_copy)]
            #[kani::stub(crate::ptr::copy_nonoverlapping, checked_copy_nonoverlapping)]
            #[kani::unwind(34)]
            fn $name() {
                const MAX_SPAN: usize = safety_insert_contract_case!(@limit $( $limit )?);
                let mut values: [$ty; 32] = $values;
                let start = kani::any::<u8>() as usize;
                let span = kani::any::<u8>() as usize;
                kani::assume(2 <= span && span <= MAX_SPAN && start <= 32 - span);
                let mut cmp = $cmp;
                unsafe {
                    let begin = values.as_mut_ptr().add(start);
                    INSERT_READ_BEGIN = begin.cast();
                    INSERT_READ_END = begin.add(span).cast();
                    INSERT_READ_ACTIVE = true;
                    insert_tail_contract(begin, begin.add(span - 1), &mut cmp);
                    INSERT_READ_ACTIVE = false;
                }
                kani::cover(span == MAX_SPAN, "the full insertion safety domain returns");
            }
        };
        (@limit) => { 17 };
        (@limit $limit:literal) => { $limit };
    }
    safety_insert_contract_case!(
        safety_insert_byte_contract,
        u8,
        kani::any(),
        CheckedSafety::<u8>(crate::marker::PhantomData)
    );
    safety_insert_contract_case!(
        safety_insert_wide_contract,
        u128,
        kani::any(),
        CheckedSafety::<u128>(crate::marker::PhantomData)
    );
    safety_insert_contract_case!(
        safety_insert_bytes17_contract,
        [u8; 17],
        kani::any(),
        CheckedSafety::<[u8; 17]>(crate::marker::PhantomData)
    );
    safety_insert_contract_case!(
        safety_insert_noncopy_contract,
        NonCopyU8,
        kani::any(),
        CheckedSafety::<NonCopyU8>(crate::marker::PhantomData)
    );
    safety_insert_contract_case!(
        safety_insert_largecopy_contract,
        [u8; LARGE_ELEMENT_SIZE],
        kani::any(),
        CheckedSafety::<[u8; LARGE_ELEMENT_SIZE]>(crate::marker::PhantomData)
    );
    safety_insert_contract_case!(
        safety_insert_largenoncopy_contract,
        LargeNonCopy,
        kani::any(),
        CheckedSafety::<LargeNonCopy>(crate::marker::PhantomData)
    );
    safety_insert_contract_case!(
        safety_insert_cell_contract,
        Cell<u8>,
        crate::array::from_fn(|_| Cell::new(kani::any())),
        MutatingCellSafety
    );

    // Check that each bulk overapproximation satisfies the same frame and
    // validity contract independently of the real-helper roots above.
    safety_insert_contract_case!(
        safety_bulk_byte_contract,
        u8,
        kani::any(),
        CheckedSafety::<u8>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, insert_tail_safety_havoc)
    );
    safety_insert_contract_case!(
        safety_bulk_wide_contract,
        u128,
        kani::any(),
        CheckedSafety::<u128>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, insert_tail_safety_havoc)
    );
    safety_insert_contract_case!(
        safety_bulk_bytes17_contract,
        [u8; 17],
        kani::any(),
        CheckedSafety::<[u8; 17]>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, insert_tail_safety_havoc)
    );
    safety_insert_contract_case!(
        safety_bulk_noncopy_contract,
        NonCopyU8,
        kani::any(),
        CheckedSafety::<NonCopyU8>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, insert_tail_safety_havoc)
    );
    safety_insert_contract_case!(
        safety_bulk_largecopy_contract,
        [u8; LARGE_ELEMENT_SIZE],
        kani::any(),
        CheckedSafety::<[u8; LARGE_ELEMENT_SIZE]>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, insert_tail_safety_havoc)
    );
    safety_insert_contract_case!(
        safety_bulk_largenoncopy_contract,
        LargeNonCopy,
        kani::any(),
        CheckedSafety::<LargeNonCopy>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, insert_tail_safety_havoc)
    );
    safety_insert_contract_case!(
        safety_bulk_cell_contract,
        Cell<u8>,
        crate::array::from_fn(|_| Cell::new(kani::any())),
        MutatingCellSafety,
        kani::stub(super::insert_tail, insert_tail_safety_havoc)
    );

    // The public insertion helper also accepts larger slices. Establish the
    // full Cell prefix domain before its outer-loop proof reuses this summary.
    safety_insert_contract_case!(
        safety_insert_cell_full_contract, Cell<u8>,
        crate::array::from_fn(|_| Cell::new(kani::any())), MutatingCellSafety ; 32
    );
    safety_insert_contract_case!(
        safety_bulk_cell_full_contract, Cell<u8>,
        crate::array::from_fn(|_| Cell::new(kani::any())), MutatingCellSafety,
        kani::stub(super::insert_tail, insert_tail_safety_havoc) ; 32
    );

    unsafe fn use_safety_insert_contract<T, F: FnMut(&T, &T) -> bool>(
        begin: *mut T,
        tail: *mut T,
        cmp: &mut F,
    ) {
        let span = inclusive_len(begin, tail);
        kani::safety_check(
            size_of::<T>() != 0 && 2 <= span && span <= 32,
            "insertion consumer stays within the proved safety domain",
        );
        // Each concrete profile checks its own proved maximum (17 or 32).
        // Contract preconditions are mandatory safety obligations here;
        // should_panic must not accept a failed contract assertion.
        kani::safety_check(
            insertion_region(begin, tail)
                && comparator_frame_domain(begin, cmp as *const F, true)
                && insertion_domain(begin, span, cmp as *const F)
                && sorted(begin, span - 1, cmp as *const F),
            "insertion safety summary preconditions hold at the real call site",
        );
        // The real helper's checked contract roots above establish the frame
        // and validity used here. Every initialized prefix is possible in the
        // bulk summary, so it overapproximates every real insertion outcome.
        // No ordering or permutation fact is assumed by these safety roots.
        unsafe { <(T, F) as SafetyInsertHavoc<T, F>>::write_prefix(begin, tail, cmp) }
    }

    // Arbitrary comparison answers may cause the real merge to panic. Only
    // the native memory-safety roots for merge routes use should_panic: Kani
    // still requires every non-panic safety property to pass. Harness checks
    // use safety_check so they cannot be accepted as an expected panic.
    // Functional contract roots use ordinary proof_for_contract and retain
    // every sorting assertion. Panic unwind recovery is not modeled by Kani.
    #[kani::proof]
    #[kani::should_panic]
    fn order_violation_panics_without_memory_errors() {
        super::panic_on_ord_violation();
    }

    fn arbitrary_cell_compare(a: &Cell<u8>, b: &Cell<u8>) -> bool {
        check_insertion_read(a as *const Cell<u8>, 1);
        check_insertion_read(b as *const Cell<u8>, 1);
        kani::safety_check(
            crate::ub_checks::can_dereference(a as *const Cell<u8>),
            "left Cell comparison argument is valid",
        );
        kani::safety_check(
            crate::ub_checks::can_dereference(b as *const Cell<u8>),
            "right Cell comparison argument is valid",
        );
        a.set(kani::any());
        b.set(kani::any());
        kani::any()
    }

    // The public helpers also accept non-Freeze elements and callbacks that
    // mutate their Cell arguments. Check the real bodies, independently of
    // the pure comparator summaries used for sorting correctness.
    #[kani::proof_for_contract(swap_contract)]
    #[kani::unwind(15)]
    #[kani::stub(crate::ptr::read, checked_read)]
    #[kani::stub(crate::ptr::copy, checked_copy)]
    #[kani::stub(crate::ptr::copy_nonoverlapping, checked_copy_nonoverlapping)]
    fn safety_swap_cell() {
        // Contract checking does not reliably preserve static initial values.
        // This proof checks the full pair, not a private insertion prefix.
        unsafe { INSERT_READ_ACTIVE = false };
        let mut values: [Cell<u8>; 13] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let a = kani::any::<u8>() as usize;
        let b = kani::any::<u8>() as usize;
        kani::assume(a < 13 && b < 13);
        let mut cmp = MutatingCellSafety;
        unsafe { swap_contract(values.as_mut_ptr(), a, b, &mut cmp) };
        kani::cover(a == b, "a mutating comparator accepts coincident swap positions");
    }

    #[kani::proof_for_contract(super::insertion_sort_shift_left)]
    #[kani::unwind(34)]
    #[kani::stub(super::insert_tail, use_safety_insert_contract)]
    #[kani::stub(crate::ptr::read, checked_read)]
    #[kani::stub(crate::ptr::copy, checked_copy)]
    #[kani::stub(crate::ptr::copy_nonoverlapping, checked_copy_nonoverlapping)]
    fn safety_insertion_cell() {
        // The independently checked leaf roots own the prefix observer.
        unsafe { INSERT_READ_ACTIVE = false };
        let mut values: [Cell<u8>; 32] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let len = kani::any::<u8>() as usize;
        let offset = kani::any::<u8>() as usize;
        kani::assume(1 <= offset && offset <= len && len <= 32);
        let mut cmp = MutatingCellSafety;
        super::insertion_sort_shift_left(&mut values[..len], offset, &mut cmp);
        kani::cover(len == 32 && offset == 1, "mutating insertion returns at its full bound");
    }

    // Source writes through Cell are permitted by the actual unsafe API.
    // This root does not substitute the narrower frame proved for the pure
    // comparators in sort4's reusable functional contract proofs.
    #[kani::proof]
    #[kani::stub(crate::ptr::read, checked_read)]
    #[kani::stub(crate::ptr::copy, checked_copy)]
    #[kani::stub(crate::ptr::copy_nonoverlapping, checked_copy_nonoverlapping)]
    fn safety_sort4_cell() {
        unsafe { INSERT_READ_ACTIVE = false };
        let values: [Cell<u8>; 4] = crate::array::from_fn(|_| Cell::new(kani::any()));
        let mut output = [const { MaybeUninit::<Cell<u8>>::uninit() }; 4];
        let mut cmp = arbitrary_cell_compare;
        unsafe { super::sort4_stable(values.as_ptr(), output.as_mut_ptr().cast(), &mut cmp) };
        assert!(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(
            output.as_ptr().cast::<Cell<u8>>(),
            4
        )));
    }

    // The general unit path still calls insert_tail. Its positions coincide,
    // every copy has zero bytes, and it invokes the comparator exactly once.
    // Check the real helper separately, then preserve that call in the model.
    // The nonzero-element insertion contract does not cover this case.
    trait ZstInsertElement: Sized {
        unsafe fn insert<F: FnMut(&Self, &Self) -> bool>(
            begin: *mut Self,
            tail: *mut Self,
            cmp: &mut F,
        );
    }
    impl<T> ZstInsertElement for T {
        default unsafe fn insert<F: FnMut(&T, &T) -> bool>(_: *mut T, _: *mut T, _: &mut F) {
            kani::safety_check(false, "the ZST insertion refinement covers only unit");
        }
    }
    impl ZstInsertElement for () {
        unsafe fn insert<F: FnMut(&(), &()) -> bool>(begin: *mut (), tail: *mut (), cmp: &mut F) {
            kani::safety_check(
                begin == tail
                    && crate::ub_checks::can_dereference(begin)
                    && crate::ub_checks::can_write(begin),
                "unit insertion has valid coincident positions",
            );
            let _ = cmp(unsafe { &*tail }, unsafe { &*begin });
        }
    }
    unsafe fn use_zst_insert_summary<T, F: FnMut(&T, &T) -> bool>(
        begin: *mut T,
        tail: *mut T,
        cmp: &mut F,
    ) {
        unsafe { <T as ZstInsertElement>::insert(begin, tail, cmp) }
    }

    #[kani::proof]
    #[kani::unwind(2)]
    #[kani::stub(crate::ptr::read, checked_read)]
    #[kani::stub(crate::ptr::copy, checked_copy)]
    #[kani::stub(crate::ptr::copy_nonoverlapping, checked_copy_nonoverlapping)]
    fn zst_insertion_refines_real() {
        let mut actual = [(); 32];
        let mut model = [(); 32];
        let start = kani::any::<u8>() as usize;
        let distance = kani::any::<u8>() as usize;
        kani::assume(start <= 32 && distance <= 32 - start);
        let decision: bool = kani::any();
        let mut actual_calls = 0u8;
        let mut model_calls = 0u8;
        unsafe {
            let actual_begin = actual.as_mut_ptr().add(start);
            let actual_tail = actual_begin.add(distance);
            let model_begin = model.as_mut_ptr().add(start);
            let model_tail = model_begin.add(distance);
            kani::safety_check(
                actual_begin == actual_tail && model_begin == model_tail,
                "all unit offsets retain their original positions",
            );
            super::insert_tail(actual_begin, actual_tail, &mut |a, b| {
                assert!(ptr::eq(a, actual_tail));
                assert!(ptr::eq(b, actual_begin));
                actual_calls += 1;
                decision
            });
            use_zst_insert_summary(model_begin, model_tail, &mut |a, b| {
                assert!(ptr::eq(a, model_tail));
                assert!(ptr::eq(b, model_begin));
                model_calls += 1;
                decision
            });
        }
        assert_eq!(actual_calls, 1);
        assert_eq!(model_calls, actual_calls);
        kani::cover(decision && distance == 32, "the real unit insertion loop returns");
    }

    macro_rules! native_dispatch_safety {
        ($name:ident, $trait_name:ident, $ty:ty, $make:expr, $max:literal, $bound:literal, $cmp:expr $(, $expected:meta)* $(; $fixed:tt)?) => {
            #[kani::proof]
            $(#[$expected])*
            #[kani::stub(crate::ptr::read, checked_read)]
            #[kani::stub(crate::ptr::copy, checked_copy)]
            #[kani::stub(crate::ptr::copy_nonoverlapping, checked_copy_nonoverlapping)]
            #[kani::unwind($bound)]
            fn $name() {
                let mut values: [$ty; $max] = kani::any();
                let len = native_dispatch_safety!(@length $( $fixed )?);
                kani::assume(len <= $max);
                kani::safety_check(<$ty as $trait_name>::small_sort_threshold() == $max, "the native dispatch uses its expected threshold");
                let mut cmp = $cmp;
                native_dispatch_safety!(@call $trait_name, $ty, values, len, cmp);
                kani::safety_check(crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(values.as_ptr(), len)), "the native dispatch preserves initialized valid elements");
                native_dispatch_safety!(@cover len, $max $(, $fixed)?);
            }
        };
        (@length) => { kani::any::<u8>() as usize };
        (@length $fixed:literal) => { $fixed };
        (@cover $len:ident, $max:literal) => {
            kani::cover($len == $max, "native dispatch returns at its full threshold");
        };
        (@cover $len:ident, $max:literal, 32) => {
            kani::cover($len == $max, "fixed-length safety matrix reaches its full threshold");
        };
        (@cover $len:ident, $max:literal, $fixed:literal) => {};
        (@call StableSmallSortTypeImpl, $ty:ty, $values:ident, $len:ident, $cmp:ident) => {
            let mut scratch = [const { MaybeUninit::<$ty>::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
            <$ty as StableSmallSortTypeImpl>::small_sort(&mut $values[..$len], &mut scratch, &mut $cmp);
        };
        (@call $trait_name:ident, $ty:ty, $values:ident, $len:ident, $cmp:ident) => {
            <$ty as $trait_name>::small_sort(&mut $values[..$len], &mut $cmp);
        };
    }

    // Primitive functional proofs cover all lengths separately. These native
    // executions cover the remaining specialization and element-size branches,
    // without inheriting summaries proved for another element or comparator.
    native_dispatch_safety!(
        safety_stable_byte,
        StableSmallSortTypeImpl,
        u8,
        kani::any(),
        32,
        34,
        CheckedSafety::<u8>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_stable_bytes17,
        StableSmallSortTypeImpl,
        [u8; 17],
        kani::any(),
        32,
        34,
        CheckedSafety::<[u8; 17]>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_stable_cell,
        StableSmallSortTypeImpl,
        Cell<u8>,
        Cell::new(kani::any()),
        16,
        18,
        MutatingCellSafety,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_stable_zst,
        StableSmallSortTypeImpl,
        (),
        (),
        32,
        34,
        checked_nondeterministic_cmp::<()>,
        kani::stub(super::insert_tail, use_zst_insert_summary)
    );
    native_dispatch_safety!(
        safety_unstable_cell,
        UnstableSmallSortTypeImpl,
        Cell<u8>,
        Cell::new(kani::any()),
        16,
        18,
        MutatingCellSafety,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );

    native_dispatch_safety!(
        safety_unstable_wide,
        UnstableSmallSortTypeImpl,
        u128,
        kani::any(),
        32,
        34,
        CheckedSafety::<u128>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_unstable_bytes17,
        UnstableSmallSortTypeImpl,
        [u8; 17],
        kani::any(),
        32,
        34,
        CheckedSafety::<[u8; 17]>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_unstable_noncopy,
        UnstableSmallSortTypeImpl,
        NonCopyU8,
        NonCopyU8(kani::any()),
        32,
        34,
        CheckedSafety::<NonCopyU8>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_unstable_largecopy,
        UnstableSmallSortTypeImpl,
        [u8; LARGE_ELEMENT_SIZE],
        kani::any(),
        16,
        18,
        CheckedSafety::<[u8; LARGE_ELEMENT_SIZE]>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_unstable_largenoncopy,
        UnstableSmallSortTypeImpl,
        LargeNonCopy,
        LargeNonCopy(kani::any()),
        16,
        18,
        CheckedSafety::<LargeNonCopy>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );

    native_dispatch_safety!(
        safety_freeze_wide,
        UnstableSmallSortFreezeTypeImpl,
        u128,
        kani::any(),
        32,
        34,
        CheckedSafety::<u128>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_freeze_bytes17,
        UnstableSmallSortFreezeTypeImpl,
        [u8; 17],
        kani::any(),
        32,
        34,
        CheckedSafety::<[u8; 17]>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_freeze_noncopy,
        UnstableSmallSortFreezeTypeImpl,
        NonCopyU8,
        NonCopyU8(kani::any()),
        32,
        34,
        CheckedSafety::<NonCopyU8>(crate::marker::PhantomData),
        kani::should_panic,
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_freeze_largecopy,
        UnstableSmallSortFreezeTypeImpl,
        [u8; LARGE_ELEMENT_SIZE],
        kani::any(),
        16,
        18,
        CheckedSafety::<[u8; LARGE_ELEMENT_SIZE]>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );
    native_dispatch_safety!(
        safety_freeze_largenoncopy,
        UnstableSmallSortFreezeTypeImpl,
        LargeNonCopy,
        LargeNonCopy(kani::any()),
        16,
        18,
        CheckedSafety::<LargeNonCopy>(crate::marker::PhantomData),
        kani::stub(super::insert_tail, use_safety_insert_contract)
    );

    // Every valid network length is a separate proof. A constant midpoint
    // lets CBMC discharge the outer loop's two-iteration bound before it
    // expands impossible repetitions. No unwinding assertion is disabled.
    macro_rules! network_safety_lengths {
        // Keep lengths as tokens so the nested cover macro can match 32.
        ($(($len:tt, $unstable:ident, $freeze:ident $(, $panic:meta)?)),+ $(,)?) => {
            const _: () = {
                let lengths = [$($len),+];
                assert!(lengths.len() == SMALL_SORT_NETWORK_THRESHOLD + 1);
                let mut i = 0;
                while i < lengths.len() {
                    assert!(lengths[i] == i);
                    i += 1;
                }
            };
            $(
                native_dispatch_safety!(
                    $unstable, UnstableSmallSortTypeImpl, u8, kani::any(), 32, 34,
                    CheckedSafety::<u8>(crate::marker::PhantomData),
                    kani::stub(super::insert_tail, use_safety_insert_contract),
                    kani::stub(super::swap_if_less, swap_branch_model)
                    $(, $panic)? ; $len
                );
                native_dispatch_safety!(
                    $freeze, UnstableSmallSortFreezeTypeImpl, u8, kani::any(), 32, 34,
                    CheckedSafety::<u8>(crate::marker::PhantomData),
                    kani::stub(super::insert_tail, use_safety_insert_contract),
                    kani::stub(super::swap_if_less, swap_branch_model)
                    $(, $panic)? ; $len
                );
            )+
        };
    }
    network_safety_lengths!(
        (0, safety_unstable_byte_len_00, safety_freeze_byte_len_00),
        (1, safety_unstable_byte_len_01, safety_freeze_byte_len_01),
        (2, safety_unstable_byte_len_02, safety_freeze_byte_len_02),
        (3, safety_unstable_byte_len_03, safety_freeze_byte_len_03),
        (4, safety_unstable_byte_len_04, safety_freeze_byte_len_04),
        (5, safety_unstable_byte_len_05, safety_freeze_byte_len_05),
        (6, safety_unstable_byte_len_06, safety_freeze_byte_len_06),
        (7, safety_unstable_byte_len_07, safety_freeze_byte_len_07),
        (8, safety_unstable_byte_len_08, safety_freeze_byte_len_08),
        (9, safety_unstable_byte_len_09, safety_freeze_byte_len_09),
        (10, safety_unstable_byte_len_10, safety_freeze_byte_len_10),
        (11, safety_unstable_byte_len_11, safety_freeze_byte_len_11),
        (12, safety_unstable_byte_len_12, safety_freeze_byte_len_12),
        (13, safety_unstable_byte_len_13, safety_freeze_byte_len_13),
        (14, safety_unstable_byte_len_14, safety_freeze_byte_len_14),
        (15, safety_unstable_byte_len_15, safety_freeze_byte_len_15),
        (16, safety_unstable_byte_len_16, safety_freeze_byte_len_16),
        (17, safety_unstable_byte_len_17, safety_freeze_byte_len_17),
        (18, safety_unstable_byte_len_18, safety_freeze_byte_len_18, kani::should_panic),
        (19, safety_unstable_byte_len_19, safety_freeze_byte_len_19, kani::should_panic),
        (20, safety_unstable_byte_len_20, safety_freeze_byte_len_20, kani::should_panic),
        (21, safety_unstable_byte_len_21, safety_freeze_byte_len_21, kani::should_panic),
        (22, safety_unstable_byte_len_22, safety_freeze_byte_len_22, kani::should_panic),
        (23, safety_unstable_byte_len_23, safety_freeze_byte_len_23, kani::should_panic),
        (24, safety_unstable_byte_len_24, safety_freeze_byte_len_24, kani::should_panic),
        (25, safety_unstable_byte_len_25, safety_freeze_byte_len_25, kani::should_panic),
        (26, safety_unstable_byte_len_26, safety_freeze_byte_len_26, kani::should_panic),
        (27, safety_unstable_byte_len_27, safety_freeze_byte_len_27, kani::should_panic),
        (28, safety_unstable_byte_len_28, safety_freeze_byte_len_28, kani::should_panic),
        (29, safety_unstable_byte_len_29, safety_freeze_byte_len_29, kani::should_panic),
        (30, safety_unstable_byte_len_30, safety_freeze_byte_len_30, kani::should_panic),
        (31, safety_unstable_byte_len_31, safety_freeze_byte_len_31, kani::should_panic),
        (32, safety_unstable_byte_len_32, safety_freeze_byte_len_32, kani::should_panic),
    );

    // Keep ordinary sorting-contract roots separate from cases that MUST
    // panic. Alternating decisions consume the same merge half at both ends,
    // regardless of the element values or the parity before the merge.
    // A normal return is a safety-property failure, never an accepted panic.
    macro_rules! expected_order_panic_cases {
        ($name:ident, $entry:ident, $len:literal) => {
            #[kani::proof]
            #[kani::should_panic]
            #[kani::unwind(34)]
            #[kani::stub(crate::ptr::read, checked_read)]
            #[kani::stub(crate::ptr::copy, checked_copy)]
            #[kani::stub(crate::ptr::copy_nonoverlapping, checked_copy_nonoverlapping)]
            fn $name() {
                let mut values: [u8; $len] = kani::any();
                let len = $len;
                let mut next = true;
                let mut cmp = |a: &u8, b: &u8| {
                    kani::safety_check(crate::ub_checks::can_dereference(a as *const u8)
                        && crate::ub_checks::can_dereference(b as *const u8), "panic comparator arguments remain valid");
                    next = !next;
                    next
                };
                native_dispatch_safety!(@call $entry, u8, values, len, cmp);
                kani::safety_check(false, "alternating merge comparator must reach the real order-violation panic");
            }
        };
    }
    expected_order_panic_cases!(panic_stable_byte_02, StableSmallSortTypeImpl, 2);
    expected_order_panic_cases!(panic_unstable_byte_32, UnstableSmallSortTypeImpl, 32);
    expected_order_panic_cases!(panic_freeze_byte_32, UnstableSmallSortFreezeTypeImpl, 32);

    // General sort initializes one new element before each insertion. Use
    // exactly that initialized prefix as the sized frame; never borrow the
    // still-uninitialized remainder of the scratch half.
    unsafe fn use_initialized_prefix_window<T, F: FnMut(&T, &T) -> bool>(
        begin: *mut T,
        tail: *mut T,
        cmp: &mut F,
    ) {
        macro_rules! prefix {
            ($n:literal) => {{
                let values = unsafe { &mut *begin.cast::<[T; $n]>() };
                assert!(ptr::eq(unsafe { values.as_mut_ptr().add($n - 1) }, tail));
                insert_window(values, $n - 1, cmp);
            }};
        }
        match inclusive_len(begin, tail) {
            2 => prefix!(2),
            3 => prefix!(3),
            4 => prefix!(4),
            5 => prefix!(5),
            6 => prefix!(6),
            7 => prefix!(7),
            8 => prefix!(8),
            9 => prefix!(9),
            10 => prefix!(10),
            11 => prefix!(11),
            12 => prefix!(12),
            13 => prefix!(13),
            14 => prefix!(14),
            15 => prefix!(15),
            16 => prefix!(16),
            17 => prefix!(17),
            _ => panic!("initialized prefix is outside the verified insertion domain"),
        }
    }

    // Each length is a separate SAT instance, with the smallest valid input
    // and scratch allocations. The compile-time enumeration covers 0..=32.
    // There are no data assumptions: each root's closed length/scratch
    // preconditions hold by construction, so one maximal return cover suffices.
    macro_rules! parent_return_cover {
        (last) => {
            kani::cover(true, "the full SmallSort threshold returns");
        };
        (skip) => {};
    }
    macro_rules! byte_parent_length_cases {
        ($($general:ident, $network:ident: $len:literal, $cover:ident);+ $(;)?) => {
            const _: () = {
                let lengths = [$($len),+];
                assert!(lengths.len() == SMALL_SORT_GENERAL_THRESHOLD + 1);
                let mut i = 0;
                while i < lengths.len() { assert!(lengths[i] == i); i += 1; }
            };
            $(
                #[kani::proof_for_contract(super::small_sort_general_with_scratch)]
                #[kani::stub_verified(super::sort4_stable)]
                #[kani::stub_verified(super::sort8_stable)]
                #[kani::stub(super::insert_tail, use_initialized_prefix_window)]
                #[kani::stub_verified(insert_window)]
                #[kani::stub_verified(super::bidirectional_merge)]
                #[kani::unwind(50)]
                fn $general() {
                    let mut values: [u8; $len] = kani::any();
                    const SCRATCH: usize = if $len < 2 { 0 } else { $len + 16 };
                    let mut scratch = [MaybeUninit::<u8>::uninit(); SCRATCH];
                    let mut cmp = ByteOrder { probe: kani::any() };
                    super::small_sort_general_with_scratch(&mut values, &mut scratch, &mut cmp);
                    parent_return_cover!($cover);
                }

                #[kani::proof_for_contract(super::small_sort_network)]
                #[kani::stub_verified(super::sort9_optimal)]
                #[kani::stub_verified(super::sort13_optimal)]
                #[kani::stub_verified(super::insertion_sort_shift_left)]
                #[kani::stub_verified(super::bidirectional_merge)]
                #[kani::unwind(34)]
                fn $network() {
                    let mut values: [u8; $len] = kani::any();
                    let mut cmp = ByteOrder { probe: kani::any() };
                    super::small_sort_network(&mut values, &mut cmp);
                    parent_return_cover!($cover);
                }
            )+
        };
    }
    byte_parent_length_cases!(
        general_scratch_byte_len_00, network_byte_len_00: 0, skip;
        general_scratch_byte_len_01, network_byte_len_01: 1, skip;
        general_scratch_byte_len_02, network_byte_len_02: 2, skip;
        general_scratch_byte_len_03, network_byte_len_03: 3, skip;
        general_scratch_byte_len_04, network_byte_len_04: 4, skip;
        general_scratch_byte_len_05, network_byte_len_05: 5, skip;
        general_scratch_byte_len_06, network_byte_len_06: 6, skip;
        general_scratch_byte_len_07, network_byte_len_07: 7, skip;
        general_scratch_byte_len_08, network_byte_len_08: 8, skip;
        general_scratch_byte_len_09, network_byte_len_09: 9, skip;
        general_scratch_byte_len_10, network_byte_len_10: 10, skip;
        general_scratch_byte_len_11, network_byte_len_11: 11, skip;
        general_scratch_byte_len_12, network_byte_len_12: 12, skip;
        general_scratch_byte_len_13, network_byte_len_13: 13, skip;
        general_scratch_byte_len_14, network_byte_len_14: 14, skip;
        general_scratch_byte_len_15, network_byte_len_15: 15, skip;
        general_scratch_byte_len_16, network_byte_len_16: 16, skip;
        general_scratch_byte_len_17, network_byte_len_17: 17, skip;
        general_scratch_byte_len_18, network_byte_len_18: 18, skip;
        general_scratch_byte_len_19, network_byte_len_19: 19, skip;
        general_scratch_byte_len_20, network_byte_len_20: 20, skip;
        general_scratch_byte_len_21, network_byte_len_21: 21, skip;
        general_scratch_byte_len_22, network_byte_len_22: 22, skip;
        general_scratch_byte_len_23, network_byte_len_23: 23, skip;
        general_scratch_byte_len_24, network_byte_len_24: 24, skip;
        general_scratch_byte_len_25, network_byte_len_25: 25, skip;
        general_scratch_byte_len_26, network_byte_len_26: 26, skip;
        general_scratch_byte_len_27, network_byte_len_27: 27, skip;
        general_scratch_byte_len_28, network_byte_len_28: 28, skip;
        general_scratch_byte_len_29, network_byte_len_29: 29, skip;
        general_scratch_byte_len_30, network_byte_len_30: 30, skip;
        general_scratch_byte_len_31, network_byte_len_31: 31, skip;
        general_scratch_byte_len_32, network_byte_len_32: 32, last;
    );

    #[kani::proof_for_contract(super::small_sort_fallback)]
    #[kani::stub_verified(super::insertion_sort_shift_left)]
    #[kani::unwind(18)]
    fn fallback_byte_contract() {
        let mut values: [u8; 16] = kani::any();
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 16);
        let mut cmp = ByteOrder { probe: kani::any() };
        super::small_sort_fallback(&mut values[..len], &mut cmp);
        kani::cover(len == 16, "fallback_byte_contract returns at its full bound");
    }

    // The stack-owning helper has its own contract: proving its scratch-slice
    // construction and the call below prevents a decorative, unproved contract.
    #[kani::proof_for_contract(super::small_sort_general)]
    #[kani::stub_verified(super::small_sort_general_with_scratch)]
    #[kani::unwind(50)]
    fn general_byte_contract() {
        let mut values: [u8; 32] = kani::any();
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 32);
        let mut cmp = ByteOrder { probe: kani::any() };
        super::small_sort_general(&mut values[..len], &mut cmp);
        kani::cover(len == 32, "general helper returns at its full threshold");
    }

    // These roots check the real specialized trait dispatch. Their verified
    // callees carry the sorting and full-value permutation postconditions.
    #[kani::proof_for_contract(stable_entry)]
    #[kani::stub_verified(super::small_sort_general_with_scratch)]
    #[kani::unwind(50)]
    fn entry_byte_stable() {
        let mut values: [u8; 32] = kani::any();
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 32);
        let mut scratch = [MaybeUninit::<u8>::uninit(); 48];
        let mut cmp = ByteOrder { probe: kani::any() };
        stable_entry(&mut values[..len], &mut scratch, &mut cmp);
        kani::cover(len == 32, "stable dispatch reaches its full threshold");
    }

    #[kani::proof_for_contract(unstable_entry)]
    #[kani::stub_verified(super::small_sort_network)]
    #[kani::unwind(34)]
    fn entry_byte_unstable() {
        let mut values: [u8; 32] = kani::any();
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 32);
        let mut cmp = ByteOrder { probe: kani::any() };
        unstable_entry(&mut values[..len], &mut cmp);
        kani::cover(len == 32, "unstable dispatch reaches its full threshold");
    }

    #[kani::proof_for_contract(unstable_freeze_entry)]
    #[kani::stub_verified(super::small_sort_network)]
    #[kani::unwind(34)]
    fn entry_byte_unstable_freeze() {
        let mut values: [u8; 32] = kani::any();
        let len = kani::any::<u8>() as usize;
        kani::assume(len <= 32);
        let mut cmp = ByteOrder { probe: kani::any() };
        unstable_freeze_entry(&mut values[..len], &mut cmp);
        kani::cover(len == 32, "freeze dispatch reaches its full threshold");
    }

    // A bulk implementation of the same nondeterministic write used by a
    // safety-only contract. Every valid i32 prefix remains possible. This is
    // an overapproximation of insert_tail, not an alternative sorting model.
    // Restrict it to the pure nondeterministic comparator used in the two roots
    // below; sorted/permutation proofs continue to use verified postconditions.
    trait SafetyInsertHavoc<T, F> {
        unsafe fn write_prefix(begin: *mut T, tail: *mut T, cmp: &mut F);
    }
    impl<T, F> SafetyInsertHavoc<T, F> for (T, F) {
        default unsafe fn write_prefix(_: *mut T, _: *mut T, _: &mut F) {
            kani::safety_check(false, "the safety havoc requires a verified concrete profile");
        }
    }

    // Each listed type has no padding, accepts every initialized byte pattern,
    // and has no destructor. This is deliberately not a generic T/F summary.
    // Slice contract replacement uses fill_with(T::any), repeatedly expanding
    // a loop at every insertion. A single arbitrary byte array supplies the
    // identical set of prefix states without that repeated initialization.
    macro_rules! bulk_safety_insert_profile {
        ($ty:ty, $cmp:ty) => {
            bulk_safety_insert_profile!($ty, $cmp, 17);
        };
        ($ty:ty, $cmp:ty, $limit:literal) => {
            impl SafetyInsertHavoc<$ty, $cmp> for ($ty, $cmp) {
                unsafe fn write_prefix(begin: *mut $ty, tail: *mut $ty, _: &mut $cmp) {
                    let span = inclusive_len(begin, tail);
                    kani::safety_check(
                        2 <= span && span <= $limit && insertion_region(begin, tail),
                        "bulk insertion writes exactly the verified initialized prefix",
                    );
                    const BYTES: usize = $limit * size_of::<$ty>();
                    let arbitrary: [u8; BYTES] = kani::any();
                    // SAFETY: the source has BYTES initialized bytes, and the
                    // checked prefix is writable, disjoint, and no larger.
                    unsafe {
                        crate::intrinsics::copy_nonoverlapping(
                            arbitrary.as_ptr(),
                            begin.cast::<u8>(),
                            span * size_of::<$ty>(),
                        );
                    }
                }
            }
        };
    }
    bulk_safety_insert_profile!(u8, CheckedSafety<u8>);
    bulk_safety_insert_profile!(u128, CheckedSafety<u128>);
    bulk_safety_insert_profile!([u8; 17], CheckedSafety<[u8; 17]>);
    bulk_safety_insert_profile!(NonCopyU8, CheckedSafety<NonCopyU8>);
    bulk_safety_insert_profile!([u8; LARGE_ELEMENT_SIZE], CheckedSafety<[u8; LARGE_ELEMENT_SIZE]>);
    bulk_safety_insert_profile!(LargeNonCopy, CheckedSafety<LargeNonCopy>);
    bulk_safety_insert_profile!(Cell<u8>, MutatingCellSafety, 32);
    impl SafetyInsertHavoc<i32, WordSafety> for (i32, WordSafety) {
        unsafe fn write_prefix(begin: *mut i32, tail: *mut i32, _: &mut WordSafety) {
            let len = inclusive_len(begin, tail);
            kani::safety_check(
                2 <= len && len <= 32 && insertion_region(begin, tail),
                "i32 insertion havoc stays within its verified writable prefix",
            );
            let arbitrary: [i32; 32] = kani::any();
            // The complete prefix is arbitrary and valid, and bytes outside
            // that prefix are untouched. The original helper's safety contract
            // is independently checked by harness_insert_tail_safety.
            unsafe { ptr::copy_nonoverlapping(arbitrary.as_ptr(), begin, len) };
        }
    }
    unsafe fn insert_tail_safety_havoc<T, F: FnMut(&T, &T) -> bool>(
        begin: *mut T,
        tail: *mut T,
        cmp: &mut F,
    ) {
        unsafe { <(T, F) as SafetyInsertHavoc<T, F>>::write_prefix(begin, tail, cmp) }
    }

    #[kani::proof_for_contract(insert_tail_contract)]
    #[kani::stub(super::insert_tail, insert_tail_safety_havoc)]
    #[kani::unwind(34)]
    fn harness_insert_tail_safety_model() {
        let mut values: [i32; 32] = kani::any();
        let last = kani::any::<u8>() as usize;
        kani::assume(1 <= last && last < 32);
        let mut cmp = WordSafety { probe: kani::any() };
        unsafe {
            insert_tail_contract(values.as_mut_ptr(), values.as_mut_ptr().add(last), &mut cmp)
        };
    }

    // Scalar read/write models for the two one-element merge operations. The
    // refinement root checks the unchanged helpers, including returned cursors,
    // comparator state, and every byte outside the destination position.
    trait MergeStepModel<T, F> {
        unsafe fn up(
            left: *const T,
            right: *const T,
            dst: *mut T,
            cmp: &mut F,
        ) -> (*const T, *const T, *mut T);
        unsafe fn down(
            left: *const T,
            right: *const T,
            dst: *mut T,
            cmp: &mut F,
        ) -> (*const T, *const T, *mut T);
    }
    impl<T, F> MergeStepModel<T, F> for (T, F) {
        default unsafe fn up(
            _: *const T,
            _: *const T,
            _: *mut T,
            _: &mut F,
        ) -> (*const T, *const T, *mut T) {
            panic!("merge-step refinement supports only (u8, ByteOrder)");
        }
        default unsafe fn down(
            _: *const T,
            _: *const T,
            _: *mut T,
            _: &mut F,
        ) -> (*const T, *const T, *mut T) {
            panic!("merge-step refinement supports only (u8, ByteOrder)");
        }
    }
    impl MergeStepModel<u8, ByteOrder> for (u8, ByteOrder) {
        unsafe fn up(
            left: *const u8,
            right: *const u8,
            dst: *mut u8,
            cmp: &mut ByteOrder,
        ) -> (*const u8, *const u8, *mut u8) {
            unsafe {
                assert!(left != dst.cast_const() && right != dst.cast_const());
                let a = *left;
                let b = *right;
                let take_left = !cmp(&*right, &*left);
                dst.write(if take_left { a } else { b });
                (left.add(take_left as usize), right.add((!take_left) as usize), dst.add(1))
            }
        }
        unsafe fn down(
            left: *const u8,
            right: *const u8,
            dst: *mut u8,
            cmp: &mut ByteOrder,
        ) -> (*const u8, *const u8, *mut u8) {
            unsafe {
                assert!(left != dst.cast_const() && right != dst.cast_const());
                let a = *left;
                let b = *right;
                let take_right = !cmp(&*right, &*left);
                dst.write(if take_right { b } else { a });
                (
                    left.wrapping_sub((!take_right) as usize),
                    right.wrapping_sub(take_right as usize),
                    dst.sub(1),
                )
            }
        }
    }
    unsafe fn merge_up_scalar<T, F: FnMut(&T, &T) -> bool>(
        left: *const T,
        right: *const T,
        dst: *mut T,
        cmp: &mut F,
    ) -> (*const T, *const T, *mut T) {
        unsafe { <(T, F) as MergeStepModel<T, F>>::up(left, right, dst, cmp) }
    }
    unsafe fn merge_down_scalar<T, F: FnMut(&T, &T) -> bool>(
        left: *const T,
        right: *const T,
        dst: *mut T,
        cmp: &mut F,
    ) -> (*const T, *const T, *mut T) {
        unsafe { <(T, F) as MergeStepModel<T, F>>::down(left, right, dst, cmp) }
    }

    #[kani::proof]
    #[kani::unwind(34)]
    fn merge_steps_refine_real_byte() {
        let source: [u8; 32] = kani::any();
        let before_source = source;
        let before: [u8; 32] = kani::any();
        let mut actual = before;
        let mut model = before;
        let a = kani::any::<u8>() as usize;
        let b = kani::any::<u8>() as usize;
        let d = kani::any::<u8>() as usize;
        let backwards: bool = kani::any();
        kani::assume(a < 32 && b < 32 && d < 32);
        kani::assume(!backwards || d > 0);
        let probe: u8 = kani::any();
        let mut actual_cmp = ByteOrder { probe };
        let mut model_cmp = ByteOrder { probe };
        let base = source.as_ptr();
        let (real_result, model_result);
        unsafe {
            if backwards {
                real_result = super::merge_down(
                    base.add(a),
                    base.add(b),
                    actual.as_mut_ptr().add(d),
                    &mut actual_cmp,
                );
                model_result = merge_down_scalar(
                    base.add(a),
                    base.add(b),
                    model.as_mut_ptr().add(d),
                    &mut model_cmp,
                );
            } else {
                real_result = super::merge_up(
                    base.add(a),
                    base.add(b),
                    actual.as_mut_ptr().add(d),
                    &mut actual_cmp,
                );
                model_result = merge_up_scalar(
                    base.add(a),
                    base.add(b),
                    model.as_mut_ptr().add(d),
                    &mut model_cmp,
                );
            }
            assert!(ptr::eq(real_result.0, model_result.0));
            assert!(ptr::eq(real_result.1, model_result.1));
            let next = if backwards { d - 1 } else { d + 1 };
            assert!(ptr::eq(real_result.2, actual.as_mut_ptr().add(next)));
            assert!(ptr::eq(model_result.2, model.as_mut_ptr().add(next)));
        }
        assert_eq!(actual, model);
        assert_eq!(source, before_source);
        assert_eq!(actual_cmp.probe, probe);
        assert_eq!(model_cmp.probe, probe);
        kani::cover(
            backwards && d == 31,
            "the backwards real merge step returns at the destination boundary",
        );
    }

    #[kani::proof]
    #[kani::unwind(50)]
    fn merge_steps_refine_real_byte_regions() {
        let before: [u8; 48] = kani::any();
        let mut actual = before;
        let mut model = before;
        let a = kani::any::<u8>() as usize;
        let b = kani::any::<u8>() as usize;
        let d = kani::any::<u8>() as usize;
        let backwards: bool = kani::any();
        kani::assume(a < 48 && b < 48 && d < 48 && d != a && d != b);
        kani::assume(!backwards || d > 0);
        let probe: u8 = kani::any();
        let mut actual_cmp = ByteOrder { probe };
        let mut model_cmp = ByteOrder { probe };
        let real_base = actual.as_mut_ptr();
        let model_base = model.as_mut_ptr();
        let left_is_min = before[a] <= before[b];
        unsafe {
            let (r, m) = if backwards {
                (
                    super::merge_down(
                        real_base.add(a),
                        real_base.add(b),
                        real_base.add(d),
                        &mut actual_cmp,
                    ),
                    merge_down_scalar(
                        model_base.add(a),
                        model_base.add(b),
                        model_base.add(d),
                        &mut model_cmp,
                    ),
                )
            } else {
                (
                    super::merge_up(
                        real_base.add(a),
                        real_base.add(b),
                        real_base.add(d),
                        &mut actual_cmp,
                    ),
                    merge_up_scalar(
                        model_base.add(a),
                        model_base.add(b),
                        model_base.add(d),
                        &mut model_cmp,
                    ),
                )
            };
            let left_step = (if backwards { !left_is_min } else { left_is_min }) as usize;
            let right_step = (if backwards { left_is_min } else { !left_is_min }) as usize;
            let left_r = if backwards {
                real_base.add(a).wrapping_sub(left_step)
            } else {
                real_base.add(a + left_step)
            };
            let left_m = if backwards {
                model_base.add(a).wrapping_sub(left_step)
            } else {
                model_base.add(a + left_step)
            };
            let right_r = if backwards {
                real_base.add(b).wrapping_sub(right_step)
            } else {
                real_base.add(b + right_step)
            };
            let right_m = if backwards {
                model_base.add(b).wrapping_sub(right_step)
            } else {
                model_base.add(b + right_step)
            };
            let next = if backwards { d - 1 } else { d + 1 };
            assert!(ptr::eq(r.0, left_r));
            assert!(ptr::eq(m.0, left_m));
            assert!(ptr::eq(r.1, right_r));
            assert!(ptr::eq(m.1, right_m));
            assert!(ptr::eq(r.2, real_base.add(next)));
            assert!(ptr::eq(m.2, model_base.add(next)));
        }
        assert_eq!(actual, model);
        assert_eq!(actual_cmp.probe, probe);
        assert_eq!(model_cmp.probe, probe);
        kani::cover(
            backwards && a == 1 && b == 47 && d == 46,
            "the disjoint same-allocation merge regions remain reachable",
        );
    }
    /// Fixed backing capacity, with a symbolic live slice of 2..=32 elements.
    /// Only the live prefix participates in the proof. Keeping its length in
    /// the immutable input prevents a contract summary from changing it.
    #[derive(kani::Arbitrary)]
    struct MergeInput {
        values: [u8; 32],
        len: u8,
    }
    impl crate::ops::Deref for MergeInput {
        type Target = [u8; 32];
        fn deref(&self) -> &Self::Target {
            &self.values
        }
    }
    impl MergeInput {
        fn len(&self) -> usize {
            self.len as usize
        }
        fn mid(&self) -> usize {
            self.len() / 2
        }
        fn valid(&self) -> bool {
            2 <= self.len && self.len <= 32
        }
    }
    fn any_merge_input() -> MergeInput {
        let source: MergeInput = kani::any();
        kani::assume(source.valid());
        source
    }

    // A step-local conservation invariant for the two-ended merge. The proof
    // counts consumed source occurrences, including overlaps. The independent
    // ordering predicate establishes non-crossing for the pure byte comparator.
    #[derive(Clone, Copy, PartialEq, Eq, kani::Arbitrary)]
    struct MergeProgress {
        left: u8,
        right: u8,
        left_end: u8,
        right_end: u8,
        front: u8,
        back: u8,
        last_front: u8,
        last_back: u8,
    }

    impl MergeProgress {
        fn valid(&self, len: usize) -> bool {
            if !(2 <= len && len <= 32) {
                return false;
            }
            let mid = len / 2;
            self.left as usize <= mid
                && mid <= self.right as usize
                && self.right as usize <= len
                && self.left_end as usize <= mid
                && mid <= self.right_end as usize
                && self.right_end as usize <= len
                && self.front as usize <= len - mid
                && self.back as usize <= mid
                && (self.front == 0 || (self.last_front as usize) < len)
                && (self.back == 0 || (self.last_back as usize) < len)
                && self.left as usize + self.right as usize == mid + self.front as usize
                && self.left_end as usize + self.right_end as usize
                    == mid + len - self.back as usize
        }
    }

    fn progress_after_up(source: &MergeInput, mut p: MergeProgress) -> MergeProgress {
        let from_left = source[p.left as usize] <= source[p.right as usize];
        p.last_front = if from_left { p.left } else { p.right };
        p.left += from_left as u8;
        p.right += (!from_left) as u8;
        p.front += 1;
        p
    }

    fn progress_after_down(source: &MergeInput, mut p: MergeProgress) -> MergeProgress {
        let from_right = source[p.left_end as usize - 1] <= source[p.right_end as usize - 1];
        p.last_back = if from_right { p.right_end - 1 } else { p.left_end - 1 };
        p.left_end -= (!from_right) as u8;
        p.right_end -= from_right as u8;
        p.back += 1;
        p
    }

    fn merge_written(output: &[MaybeUninit<u8>; 32], p: &MergeProgress, len: usize) -> bool {
        p.valid(len)
            && crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(
                output.as_ptr().cast::<u8>(),
                p.front as usize,
            ))
            && crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(
                output.as_ptr().cast::<u8>().wrapping_add(len - p.back as usize),
                p.back as usize,
            ))
    }

    #[inline(never)]
    fn source_contribution(
        source: &MergeInput,
        p: &MergeProgress,
        probe: u8,
        i: usize,
        len: usize,
    ) -> u8 {
        if i >= len {
            return 0;
        }
        let low = if i < source.mid() { p.left } else { p.right } as usize;
        let high = if i < source.mid() { p.left_end } else { p.right_end } as usize;
        if source[i] == probe { (i < low) as u8 + (i >= high) as u8 } else { 0 }
    }

    #[inline(never)]
    fn output_contribution(
        output: &[MaybeUninit<u8>; 32],
        p: &MergeProgress,
        probe: u8,
        i: usize,
        len: usize,
    ) -> u8 {
        if i < len && (i < p.front as usize || i >= len - p.back as usize) {
            (unsafe { *output[i].assume_init_ref() } == probe) as u8
        } else {
            0
        }
    }

    fn merge_conserved(
        source: &MergeInput,
        output: &[MaybeUninit<u8>; 32],
        p: &MergeProgress,
        cmp: &ByteOrder,
    ) -> bool {
        // Avoid nesting statement blocks inside every preceding sum term.
        // Separate leaf functions leave the same arithmetic with a small MIR.
        macro_rules! sum {
            ($part:ident, $values:ident; $acc:expr;) => { $acc };
            ($part:ident, $values:ident; $acc:expr; $i:literal $(, $rest:literal)*) => {
                sum!($part, $values; ($acc).wrapping_add($part($values, p, cmp.probe, $i, source.len())); $($rest),*)
            };
        }
        macro_rules! total {
            ($part:ident, $values:ident) => {
                sum!($part, $values; 0u8; 0, 1, 2, 3, 4, 5, 6, 7,
                    8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31)
            };
        }
        total!(source_contribution, source) == total!(output_contribution, output)
    }

    // The original index breaks equal-key ties exactly as the real merge does:
    // up prefers the left half and down prefers the right half. It is only
    // ghost state; the production comparator and its values are unchanged.
    fn merge_rank(source: &MergeInput, i: u8) -> u16 {
        ((source[i as usize] as u16) << 5) | i as u16
    }

    fn merge_ordered(
        source: &MergeInput,
        output: &[MaybeUninit<u8>; 32],
        p: &MergeProgress,
        cmp: &ByteOrder,
    ) -> bool {
        if p.left > p.left_end || p.right > p.right_end {
            return false;
        }
        let mid = source.mid() as u8;
        let len = source.len() as u8;
        let base = output.as_ptr().cast::<u8>();
        if !sorted(base, p.front as usize, cmp)
            || !sorted(base.wrapping_add((len - p.back) as usize), p.back as usize, cmp)
        {
            return false;
        }
        if p.front > 0 {
            let rank = merge_rank(source, p.last_front);
            if merge_value(output, p.front - 1) != source[p.last_front as usize]
                || (p.left > 0 && merge_rank(source, p.left - 1) > rank)
                || (p.right > mid && merge_rank(source, p.right - 1) > rank)
                || (p.left < mid && rank >= merge_rank(source, p.left))
                || (p.right < len && rank >= merge_rank(source, p.right))
            {
                return false;
            }
        }
        if p.back > 0 {
            let rank = merge_rank(source, p.last_back);
            if merge_value(output, len - p.back) != source[p.last_back as usize]
                || (p.left_end > 0 && merge_rank(source, p.left_end - 1) >= rank)
                || (p.right_end > mid && merge_rank(source, p.right_end - 1) >= rank)
                || (p.left_end < mid && rank > merge_rank(source, p.left_end))
                || (p.right_end < len && rank > merge_rank(source, p.right_end))
            {
                return false;
            }
        }
        p.front == 0
            || p.back == 0
            || merge_rank(source, p.last_front) < merge_rank(source, p.last_back)
    }

    fn merge_invariant(
        source: &MergeInput,
        output: &[MaybeUninit<u8>; 32],
        p: &MergeProgress,
        cmp: &ByteOrder,
    ) -> bool {
        merge_written(output, p, source.len())
            && merge_conserved(source, output, p, cmp)
            && merge_ordered(source, output, p, cmp)
    }

    fn merge_value(output: &[MaybeUninit<u8>; 32], i: u8) -> u8 {
        unsafe { *output[i as usize].assume_init_ref() }
    }
    fn up_value(source: &MergeInput, p: &MergeProgress) -> u8 {
        source[p.left as usize].min(source[p.right as usize])
    }
    fn down_value(source: &MergeInput, p: &MergeProgress) -> u8 {
        source[p.left_end as usize - 1].max(source[p.right_end as usize - 1])
    }

    #[safety::requires(p.valid(source.len()) && p.front == p.back && (p.front as usize) < source.mid())]
    #[safety::requires(merge_invariant(source, output, &p, cmp))]
    #[safety::requires(source.valid() && sorted_halves(source.as_ptr(), source.len(), cmp))]
    #[safety::ensures(|next| merge_invariant(source, output, next, cmp))]
    #[safety::ensures(|next| *next == progress_after_up(source, p))]
    #[safety::ensures(|_| merge_value(output, p.front) == up_value(source, &p))]
    #[kani::modifies(output.as_mut_ptr().wrapping_add(p.front as usize))]
    fn counted_merge_up(
        source: &MergeInput,
        output: &mut [MaybeUninit<u8>; 32],
        p: MergeProgress,
        cmp: &mut ByteOrder,
    ) -> MergeProgress {
        let next = progress_after_up(source, p);
        unsafe {
            let actual = merge_up_scalar(
                source.as_ptr().add(p.left as usize),
                source.as_ptr().add(p.right as usize),
                output.as_mut_ptr().cast::<u8>().add(p.front as usize),
                cmp,
            );
            assert!(ptr::eq(actual.0, source.as_ptr().add(next.left as usize)));
            assert!(ptr::eq(actual.1, source.as_ptr().add(next.right as usize)));
            assert!(ptr::eq(actual.2, output.as_mut_ptr().cast::<u8>().add(next.front as usize)));
        }
        next
    }

    #[safety::requires(p.valid(source.len()) && p.front == p.back + 1 && (p.back as usize) < source.mid())]
    #[safety::requires(merge_invariant(source, output, &p, cmp))]
    #[safety::requires(source.valid() && sorted_halves(source.as_ptr(), source.len(), cmp))]
    #[safety::ensures(|next| merge_invariant(source, output, next, cmp))]
    #[safety::ensures(|next| *next == progress_after_down(source, p))]
    #[safety::ensures(|_| merge_value(output, (source.len() as u8 - 1) - p.back) == down_value(source, &p))]
    #[kani::modifies(output.as_mut_ptr().wrapping_add(source.len() - 1 - p.back as usize))]
    fn counted_merge_down(
        source: &MergeInput,
        output: &mut [MaybeUninit<u8>; 32],
        p: MergeProgress,
        cmp: &mut ByteOrder,
    ) -> MergeProgress {
        let next = progress_after_down(source, p);
        unsafe {
            let actual = merge_down_scalar(
                source.as_ptr().add(p.left_end as usize - 1),
                source.as_ptr().add(p.right_end as usize - 1),
                output.as_mut_ptr().cast::<u8>().add(source.len() - 1 - p.back as usize),
                cmp,
            );
            assert!(ptr::eq(actual.0, source.as_ptr().add(next.left_end as usize).wrapping_sub(1)));
            assert!(ptr::eq(
                actual.1,
                source.as_ptr().add(next.right_end as usize).wrapping_sub(1)
            ));
            assert!(ptr::eq(
                actual.2,
                output.as_mut_ptr().cast::<u8>().add(source.len() - 1 - next.back as usize)
            ));
        }
        next
    }

    // Enumerate every iteration boundary. The data and all source cursors
    // remain symbolic; only the two output lengths are fixed in each case.
    macro_rules! counted_merge_case {
        ($name:ident, $step:ident, $front:expr, $back:expr) => {
            #[kani::proof_for_contract($step)]
            #[kani::unwind(34)]
            fn $name() {
                let source = any_merge_input();
                let initial: [u8; 32] = kani::any();
                let p = MergeProgress { front: $front, back: $back, ..kani::any() };
                kani::assume(p.valid(source.len()));
                let mut output = [MaybeUninit::<u8>::uninit(); 32];
                unsafe {
                    let dst = output.as_mut_ptr().cast::<u8>();
                    ptr::copy_nonoverlapping(initial.as_ptr(), dst, $front as usize);
                    ptr::copy_nonoverlapping(
                        initial.as_ptr().add(source.len() - $back as usize),
                        dst.add(source.len() - $back as usize),
                        $back as usize,
                    );
                }
                let mut cmp = ByteOrder { probe: kani::any() };
                $step(&source, &mut output, p, &mut cmp);
                kani::cover(true, "dynamic merge step returns");
            }
        };
    }
    macro_rules! counted_merge_cases {
        ($($up:ident, $down:ident: $k:literal);+ $(;)?) => {
            const _: () = {
                let steps = [$($k),+];
                assert!(steps.len() == 16);
                let mut i = 0;
                while i < 16 { assert!(steps[i] == i); i += 1; }
            };
            $(
                counted_merge_case!($up, counted_merge_up, $k, $k);
                counted_merge_case!($down, counted_merge_down, $k + 1, $k);
            )+
        };
    }
    counted_merge_cases!(
        merge_step_up_00, merge_step_down_00: 0;
        merge_step_up_01, merge_step_down_01: 1;
        merge_step_up_02, merge_step_down_02: 2;
        merge_step_up_03, merge_step_down_03: 3;
        merge_step_up_04, merge_step_down_04: 4;
        merge_step_up_05, merge_step_down_05: 5;
        merge_step_up_06, merge_step_down_06: 6;
        merge_step_up_07, merge_step_down_07: 7;
        merge_step_up_08, merge_step_down_08: 8;
        merge_step_up_09, merge_step_down_09: 9;
        merge_step_up_10, merge_step_down_10: 10;
        merge_step_up_11, merge_step_down_11: 11;
        merge_step_up_12, merge_step_down_12: 12;
        merge_step_up_13, merge_step_down_13: 13;
        merge_step_up_14, merge_step_down_14: 14;
        merge_step_up_15, merge_step_down_15: 15;
    );

    #[kani::proof]
    #[kani::unwind(34)]
    fn merge_initial_invariant() {
        let source = any_merge_input();
        let output = [MaybeUninit::<u8>::uninit(); 32];
        let cmp = ByteOrder { probe: kani::any() };
        let p = initial_merge_progress(&source);
        kani::assume(sorted_halves(source.as_ptr(), source.len(), &cmp));
        assert!(merge_invariant(&source, &output, &p, &cmp));
        kani::cover(source.len() == 32, "the complete initial merge invariant is reachable");
    }
    trait MergeStorage {
        fn uninit_view(&mut self) -> &mut [MaybeUninit<u8>; 32];
    }
    impl MergeStorage for [u8; 32] {
        fn uninit_view(&mut self) -> &mut [MaybeUninit<u8>; 32] {
            // MaybeUninit has the same layout and accepts every initialized u8.
            unsafe { &mut *(self as *mut [u8; 32]).cast::<[MaybeUninit<u8>; 32]>() }
        }
    }
    fn initialized_merge_invariant(
        source: &MergeInput,
        output: &[u8; 32],
        p: &MergeProgress,
        cmp: &ByteOrder,
    ) -> bool {
        let view = unsafe { &*(output as *const [u8; 32]).cast::<[MaybeUninit<u8>; 32]>() };
        p.valid(source.len())
            && merge_conserved(source, view, p, cmp)
            && merge_ordered(source, view, p, cmp)
    }

    #[safety::requires(p.valid(source.len()) && p.front == p.back && (p.front as usize) < source.mid())]
    #[safety::requires(initialized_merge_invariant(source, output, &p, cmp))]
    #[safety::requires(source.valid() && sorted_halves(source.as_ptr(), source.len(), cmp))]
    #[safety::ensures(|next| initialized_merge_invariant(source, output, next, cmp))]
    #[safety::ensures(|next| *next == progress_after_up(source, p))]
    #[safety::ensures(|_| output[p.front as usize] == up_value(source, &p))]
    #[kani::modifies(output.as_mut_ptr().wrapping_add(p.front as usize))]
    fn typed_merge_up(
        source: &MergeInput,
        output: &mut [u8; 32],
        p: MergeProgress,
        cmp: &mut ByteOrder,
    ) -> MergeProgress {
        counted_merge_up(source, MergeStorage::uninit_view(output), p, cmp)
    }

    #[safety::requires(p.valid(source.len()) && p.front == p.back + 1 && (p.back as usize) < source.mid())]
    #[safety::requires(initialized_merge_invariant(source, output, &p, cmp))]
    #[safety::requires(source.valid() && sorted_halves(source.as_ptr(), source.len(), cmp))]
    #[safety::ensures(|next| initialized_merge_invariant(source, output, next, cmp))]
    #[safety::ensures(|next| *next == progress_after_down(source, p))]
    #[safety::ensures(|_| output[source.len() - 1 - p.back as usize] == down_value(source, &p))]
    #[kani::modifies(output.as_mut_ptr().wrapping_add(source.len() - 1 - p.back as usize))]
    fn typed_merge_down(
        source: &MergeInput,
        output: &mut [u8; 32],
        p: MergeProgress,
        cmp: &mut ByteOrder,
    ) -> MergeProgress {
        counted_merge_down(source, MergeStorage::uninit_view(output), p, cmp)
    }

    #[kani::proof_for_contract(typed_merge_up)]
    #[kani::stub_verified(counted_merge_up)]
    #[kani::unwind(34)]
    fn typed_merge_up_contract() {
        let source = any_merge_input();
        let mut output: [u8; 32] = kani::any();
        let p: MergeProgress = kani::any();
        let mut cmp = ByteOrder { probe: kani::any() };
        typed_merge_up(&source, &mut output, p, &mut cmp);
        kani::cover(true, "typed_merge_up_contract returns");
    }

    #[kani::proof_for_contract(typed_merge_down)]
    #[kani::stub_verified(counted_merge_down)]
    #[kani::unwind(34)]
    fn typed_merge_down_contract() {
        let source = any_merge_input();
        let mut output: [u8; 32] = kani::any();
        let p: MergeProgress = kani::any();
        let mut cmp = ByteOrder { probe: kani::any() };
        typed_merge_down(&source, &mut output, p, &mut cmp);
        kani::cover(true, "typed_merge_down_contract returns");
    }

    fn initial_merge_progress(source: &MergeInput) -> MergeProgress {
        MergeProgress {
            left: 0,
            right: source.mid() as u8,
            left_end: source.mid() as u8,
            right_end: source.len,
            front: 0,
            back: 0,
            last_front: 0,
            last_back: 0,
        }
    }

    fn last_source_index(p: &MergeProgress) -> u8 {
        if p.left < p.left_end { p.left } else { p.right }
    }
    fn progress_after_last(mut p: MergeProgress) -> MergeProgress {
        let from_left = p.left < p.left_end;
        p.last_front = last_source_index(&p);
        p.left += from_left as u8;
        p.right += (!from_left) as u8;
        p.front += 1;
        p
    }

    // An odd-length merge has exactly one source element left after its paired
    // steps. Check its copy separately, including both choices of source half.
    #[safety::requires(source.valid() && source.len() % 2 == 1)]
    #[safety::requires(p.front as usize == source.mid() && p.back == p.front)]
    #[safety::requires(initialized_merge_invariant(source, output, &p, cmp))]
    #[safety::requires(sorted_halves(source.as_ptr(), source.len(), cmp))]
    #[safety::requires(source.valid() && trace[2 * source.mid()] == p)]
    #[safety::ensures(|next| initialized_merge_invariant(source, output, next, cmp))]
    #[safety::ensures(|next| *next == progress_after_last(p))]
    #[safety::ensures(|next| trace[source.len()] == *next)]
    #[safety::ensures(|_| merge_trace_segment(source, output, trace, 2 * source.mid(), source.len()))]
    #[kani::modifies(output.as_mut_ptr().wrapping_add(source.mid()), trace.as_mut_ptr().wrapping_add(source.len()))]
    fn merge_last_element(
        source: &MergeInput,
        output: &mut [u8; 32],
        p: MergeProgress,
        cmp: &mut ByteOrder,
        trace: &mut [MergeProgress; 33],
    ) -> MergeProgress {
        let next = progress_after_last(p);
        output[p.front as usize] = source[next.last_front as usize];
        trace[source.len()] = next;
        next
    }

    #[kani::proof_for_contract(merge_last_element)]
    #[kani::unwind(34)]
    fn merge_last_element_contract() {
        let source = any_merge_input();
        let mut output: [u8; 32] = kani::any();
        let mut trace: [MergeProgress; 33] = kani::any();
        let p: MergeProgress = kani::any();
        let mut cmp = ByteOrder { probe: kani::any() };
        merge_last_element(&source, &mut output, p, &mut cmp, &mut trace);
        kani::cover(true, "the odd-length final copy returns");
    }

    // Each certificate edge describes one actual scalar update, including its
    // source cursors and the byte stored in the destination. Consumers check
    // these facts rather than assuming an end-to-end reference result.
    #[inline(never)]
    fn merge_trace_edge(
        source: &MergeInput,
        output: &[u8; 32],
        trace: &[MergeProgress; 33],
        i: usize,
    ) -> bool {
        if !source.valid() || i >= source.len() {
            return false;
        }
        let before = trace[i];
        let after = trace[i + 1];
        if !before.valid(source.len()) || !after.valid(source.len()) {
            return false;
        }
        if i == 2 * source.mid() {
            return source.len() % 2 == 1
                && before.front as usize == source.mid()
                && before.back == before.front
                && after == progress_after_last(before)
                && output[source.mid()] == source[after.last_front as usize];
        }
        if before.front as usize != (i + 1) / 2
            || before.back as usize != i / 2
            || after.front as usize != (i + 2) / 2
            || after.back as usize != (i + 1) / 2
        {
            return false;
        }
        if i % 2 == 0 {
            after == progress_after_up(source, before)
                && output[before.front as usize] == source[after.last_front as usize]
        } else {
            after == progress_after_down(source, before)
                && output[source.len() - 1 - before.back as usize]
                    == source[after.last_back as usize]
        }
    }

    fn merge_trace_segment(
        source: &MergeInput,
        output: &[u8; 32],
        trace: &[MergeProgress; 33],
        first: usize,
        last: usize,
    ) -> bool {
        macro_rules! edge {
            (($left:tt, $right:tt)) => {
                edge!($left) && edge!($right)
            };
            ($i:literal) => {
                $i < first || $i >= last || merge_trace_edge(source, output, trace, $i)
            };
        }
        source.valid() && first <= last && last <= source.len() && fold_32!(edge)
    }

    fn traced_merge_up(
        source: &MergeInput,
        output: &mut [u8; 32],
        p: MergeProgress,
        cmp: &mut ByteOrder,
        trace: &mut [MergeProgress; 33],
    ) -> MergeProgress {
        let next = typed_merge_up(source, output, p, cmp);
        trace[p.front as usize + p.back as usize + 1] = next;
        next
    }

    fn traced_merge_down(
        source: &MergeInput,
        output: &mut [u8; 32],
        p: MergeProgress,
        cmp: &mut ByteOrder,
        trace: &mut [MergeProgress; 33],
    ) -> MergeProgress {
        let next = typed_merge_down(source, output, p, cmp);
        trace[p.front as usize + p.back as usize + 1] = next;
        next
    }

    // Re-express counters only after checking equality. This preserves the
    // complete state, but exposes constant intervals in fixed-start proofs.
    fn checked_progress(next: MergeProgress, front: u8, back: u8) -> MergeProgress {
        assert!(next.front == front && next.back == back);
        MergeProgress { front, back, ..next }
    }

    // A balanced proof tree prevents callers from expanding all 32 updates.
    // Every node is checked independently, over arbitrary valid cursors and
    // arbitrary data. Its children summarize only previously verified nodes.
    macro_rules! merge_block {
        ($name:ident, $proof:ident, $first:ident, $second:ident, $width:literal;
            $($child:ident),+ $(,)?) => {
            #[safety::requires(p.valid(source.len()) && p.front == p.back && (p.front as usize + $width) <= source.mid() && p.front % $width == 0)]
            #[safety::requires(initialized_merge_invariant(source, output, &p, cmp))]
            #[safety::requires(source.valid() && sorted_halves(source.as_ptr(), source.len(), cmp))]
            #[safety::requires(p.front <= 16 && trace[2 * p.front as usize] == p)]
            #[safety::ensures(|next| initialized_merge_invariant(source, output, next, cmp))]
            #[safety::ensures(|next| next.front == p.front + $width && next.back == p.back + $width)]
            #[safety::ensures(|next| next.front <= 16 && trace[2 * next.front as usize] == *next)]
            #[safety::ensures(|_| merge_trace_segment(source, output, trace,
                2 * p.front as usize, 2 * (p.front as usize + $width)))]
            #[kani::modifies(
                ptr::slice_from_raw_parts_mut(output.as_mut_ptr().wrapping_add(p.front as usize), $width),
                ptr::slice_from_raw_parts_mut(output.as_mut_ptr().wrapping_add(source.len() - p.back as usize - $width), $width),
                ptr::slice_from_raw_parts_mut(trace.as_mut_ptr().wrapping_add(2 * p.front as usize + 1), 2 * $width)
            )]
            fn $name(
                source: &MergeInput,
                output: &mut [u8; 32],
                p: MergeProgress,
                cmp: &mut ByteOrder,
                trace: &mut [MergeProgress; 33],
            ) -> MergeProgress {
                let start = p;
                let after_first = $first(source, output, p, cmp, trace);
                let p = checked_progress(
                    after_first,
                    start.front + if $width == 1 { 1 } else { $width / 2 },
                    start.back + if $width == 1 { 0 } else { $width / 2 },
                );
                let after_second = $second(source, output, p, cmp, trace);
                checked_progress(after_second, start.front + $width, start.back + $width)
            }

        };
    }
    merge_block!(merge_block_01, merge_block_01_contract, traced_merge_up, traced_merge_down, 1;
        typed_merge_up, typed_merge_down);
    merge_block!(merge_block_02, merge_block_02_contract, merge_block_01, merge_block_01, 2;
        merge_block_01);
    merge_block!(merge_block_04, merge_block_04_contract, merge_block_02, merge_block_02, 4;
        merge_block_02);
    merge_block!(merge_block_08, merge_block_08_contract, merge_block_04, merge_block_04, 8;
        merge_block_04);
    merge_block!(merge_block_16, merge_block_16_contract, merge_block_08, merge_block_08, 16;
        merge_block_08);

    // Fixed starts cover every aligned call in the balanced tree. Keeping
    // the trace interval constant avoids materializing all 32 edge branches.
    macro_rules! merge_block_at {
        ($block:ident, $proof:ident, $start:literal; [$($child:ident),+]) => {
            #[kani::proof_for_contract($block)]
            $(#[kani::stub_verified($child)])+
            #[kani::unwind(34)]
            fn $proof() {
                let source = any_merge_input();
                let mut output: [u8; 32] = kani::any();
                let p = MergeProgress { front: $start, back: $start, ..kani::any() };
                let mut trace: [MergeProgress; 33] = kani::any();
                let mut cmp = ByteOrder { probe: kani::any() };
                $block(&source, &mut output, p, &mut cmp, &mut trace);
                // One return witness permits --no-assertion-reach-checks without
                // relying on vacuous preconditions for this proof partition.
                kani::cover(true, "certificate block returns");
            }
        };
    }
    macro_rules! merge_block_cases {
        ($block:ident, $width:literal, $children:tt; $($proof:ident: $start:literal),+ $(,)?) => {
            const _: () = {
                let starts = [$($start),+];
                assert!(starts.len() == 16 / $width);
                let mut i = 0;
                while i < starts.len() { assert!(starts[i] == i * $width); i += 1; }
            };
            $(merge_block_at!($block, $proof, $start; $children);)+
        };
    }
    merge_block_cases!(merge_block_01, 1, [typed_merge_up, typed_merge_down];
        merge_block_01_at_00: 0,
        merge_block_01_at_01: 1,
        merge_block_01_at_02: 2,
        merge_block_01_at_03: 3,
        merge_block_01_at_04: 4,
        merge_block_01_at_05: 5,
        merge_block_01_at_06: 6,
        merge_block_01_at_07: 7,
        merge_block_01_at_08: 8,
        merge_block_01_at_09: 9,
        merge_block_01_at_10: 10,
        merge_block_01_at_11: 11,
        merge_block_01_at_12: 12,
        merge_block_01_at_13: 13,
        merge_block_01_at_14: 14,
        merge_block_01_at_15: 15
    );
    merge_block_cases!(merge_block_02, 2, [merge_block_01];
        merge_block_02_at_00: 0,
        merge_block_02_at_02: 2,
        merge_block_02_at_04: 4,
        merge_block_02_at_06: 6,
        merge_block_02_at_08: 8,
        merge_block_02_at_10: 10,
        merge_block_02_at_12: 12,
        merge_block_02_at_14: 14
    );
    merge_block_cases!(merge_block_04, 4, [merge_block_02];
        merge_block_04_at_00: 0,
        merge_block_04_at_04: 4,
        merge_block_04_at_08: 8,
        merge_block_04_at_12: 12
    );
    merge_block_cases!(merge_block_08, 8, [merge_block_04];
        merge_block_08_at_00: 0,
        merge_block_08_at_08: 8
    );
    merge_block_cases!(merge_block_16, 16, [merge_block_08];
        merge_block_16_at_00: 0
    );

    #[safety::requires(source.valid() && sorted_halves(source.as_ptr(), source.len(), cmp))]
    #[safety::ensures(|_| count((output as *const [u8; 32]).cast::<u8>(), source.len(), cmp as *const ByteOrder)
        == count(source.as_ptr(), source.len(), cmp as *const ByteOrder))]
    #[safety::ensures(|_| sorted((output as *const [u8; 32]).cast::<u8>(), source.len(), cmp as *const ByteOrder))]
    #[safety::ensures(|_| crate::ub_checks::can_dereference(ptr::slice_from_raw_parts(
        (output as *const [u8; 32]).cast::<u8>(), source.len())))]
    #[safety::ensures(|_| merge_trace_segment(source, output, trace, 0, source.len()))]
    #[safety::ensures(|_| trace[source.len()].front as usize == source.len() - source.mid()
        && trace[source.len()].back as usize == source.mid()
        && trace[source.len()].left == trace[source.len()].left_end
        && trace[source.len()].right == trace[source.len()].right_end)]
    #[safety::ensures(|_| trace[0] == initial_merge_progress(source))]
    #[kani::modifies(output, trace)]
    fn indexed_merge_contract(
        source: &MergeInput,
        output: &mut [u8; 32],
        cmp: &mut ByteOrder,
        trace: &mut [MergeProgress; 33],
    ) {
        let mut p = initial_merge_progress(source);
        trace[0] = p;
        // The binary decomposition covers every half length from 1 through 16.
        // Earlier (larger) blocks leave a start aligned for every later block.
        macro_rules! block {
            ($width:literal, $run:ident) => {
                if source.mid() - p.front as usize >= $width {
                    let start = p;
                    let next = $run(source, output, p, cmp, trace);
                    p = checked_progress(next, start.front + $width, start.back + $width);
                }
            };
        }
        block!(16, merge_block_16);
        block!(8, merge_block_08);
        block!(4, merge_block_04);
        block!(2, merge_block_02);
        block!(1, merge_block_01);
        assert!(p.front as usize == source.mid() && p.back == p.front);
        if source.len() % 2 == 1 {
            let _ = merge_last_element(source, output, p, cmp, trace);
        }
    }

    // These partitions enumerate the entire contract domain. Keeping the live
    // length constant avoids expanding every binary decomposition in one SAT
    // instance; element values, cursors returned by summaries and probes remain
    // symbolic. The compile-time check prevents a missing length.
    macro_rules! indexed_merge_length_cases {
        ($($name:ident: $len:literal),+ $(,)?) => {
            const _: () = {
                let lengths = [$($len),+];
                assert!(lengths.len() == 31);
                let mut i = 0;
                while i < lengths.len() { assert!(lengths[i] == i + 2); i += 1; }
            };
            $(
                #[kani::proof_for_contract(indexed_merge_contract)]
                #[kani::stub_verified(merge_block_01)]
                #[kani::stub_verified(merge_block_02)]
                #[kani::stub_verified(merge_block_04)]
                #[kani::stub_verified(merge_block_08)]
                #[kani::stub_verified(merge_block_16)]
                #[kani::stub_verified(merge_last_element)]
                #[kani::unwind(34)]
                fn $name() {
                    let source = MergeInput { values: kani::any(), len: $len };
                    let mut output: [u8; 32] = kani::any();
                    let mut trace: [MergeProgress; 33] = kani::any();
                    let mut cmp = ByteOrder { probe: kani::any() };
                    indexed_merge_contract(&source, &mut output, &mut cmp, &mut trace);
                    kani::cover(true, "the length partition returns");
                }
            )+
        };
    }
    indexed_merge_length_cases!(
        indexed_merge_length_02: 2,
        indexed_merge_length_03: 3,
        indexed_merge_length_04: 4,
        indexed_merge_length_05: 5,
        indexed_merge_length_06: 6,
        indexed_merge_length_07: 7,
        indexed_merge_length_08: 8,
        indexed_merge_length_09: 9,
        indexed_merge_length_10: 10,
        indexed_merge_length_11: 11,
        indexed_merge_length_12: 12,
        indexed_merge_length_13: 13,
        indexed_merge_length_14: 14,
        indexed_merge_length_15: 15,
        indexed_merge_length_16: 16,
        indexed_merge_length_17: 17,
        indexed_merge_length_18: 18,
        indexed_merge_length_19: 19,
        indexed_merge_length_20: 20,
        indexed_merge_length_21: 21,
        indexed_merge_length_22: 22,
        indexed_merge_length_23: 23,
        indexed_merge_length_24: 24,
        indexed_merge_length_25: 25,
        indexed_merge_length_26: 26,
        indexed_merge_length_27: 27,
        indexed_merge_length_28: 28,
        indexed_merge_length_29: 29,
        indexed_merge_length_30: 30,
        indexed_merge_length_31: 31,
        indexed_merge_length_32: 32,
    );

    static mut MERGE_TRACE_SOURCE: *const MergeInput = ptr::null();
    static mut MERGE_TRACE_ACTUAL_SOURCE: *const u8 = ptr::null();
    static mut MERGE_TRACE_EXPECTED: *const [MaybeUninit<u8>; 32] = ptr::null();
    static mut MERGE_TRACE_STATES: *const [MergeProgress; 33] = ptr::null();
    static mut MERGE_TRACE_OUTPUT: *mut u8 = ptr::null_mut();

    unsafe fn merge_trace_output_index(dst: *mut u8) -> usize {
        let offset = unsafe { dst.offset_from(MERGE_TRACE_OUTPUT) };
        assert!(offset >= 0 && (offset as usize) < unsafe { (*MERGE_TRACE_SOURCE).len() });
        offset as usize
    }

    trait TraceMergeStep<T, F> {
        unsafe fn up(
            left: *const T,
            right: *const T,
            dst: *mut T,
            cmp: &mut F,
        ) -> (*const T, *const T, *mut T);
        unsafe fn down(
            left: *const T,
            right: *const T,
            dst: *mut T,
            cmp: &mut F,
        ) -> (*const T, *const T, *mut T);
    }
    impl<T, F> TraceMergeStep<T, F> for (T, F) {
        default unsafe fn up(
            _: *const T,
            _: *const T,
            _: *mut T,
            _: &mut F,
        ) -> (*const T, *const T, *mut T) {
            panic!("trace refinement supports only (u8, ByteOrder)");
        }
        default unsafe fn down(
            _: *const T,
            _: *const T,
            _: *mut T,
            _: &mut F,
        ) -> (*const T, *const T, *mut T) {
            panic!("trace refinement supports only (u8, ByteOrder)");
        }
    }
    impl TraceMergeStep<u8, ByteOrder> for (u8, ByteOrder) {
        unsafe fn up(
            left: *const u8,
            right: *const u8,
            dst: *mut u8,
            cmp: &mut ByteOrder,
        ) -> (*const u8, *const u8, *mut u8) {
            unsafe {
                let i = 2 * merge_trace_output_index(dst);
                assert!(i < 2 * (*MERGE_TRACE_SOURCE).mid());
                let before = (*MERGE_TRACE_STATES)[i];
                let after = (*MERGE_TRACE_STATES)[i + 1];
                let source = MERGE_TRACE_ACTUAL_SOURCE;
                assert!(ptr::eq(left, source.add(before.left as usize)));
                assert!(ptr::eq(right, source.add(before.right as usize)));
                assert!(ptr::eq(dst, MERGE_TRACE_OUTPUT.add(before.front as usize)));
                let result = merge_up_scalar(left, right, dst, cmp);
                assert!(ptr::eq(result.0, source.add(after.left as usize)));
                assert!(ptr::eq(result.1, source.add(after.right as usize)));
                assert!(ptr::eq(result.2, MERGE_TRACE_OUTPUT.add(after.front as usize)));
                let expected = (*MERGE_TRACE_EXPECTED)[before.front as usize].assume_init();
                assert_eq!(*dst, expected);
                result
            }
        }
        unsafe fn down(
            left: *const u8,
            right: *const u8,
            dst: *mut u8,
            cmp: &mut ByteOrder,
        ) -> (*const u8, *const u8, *mut u8) {
            unsafe {
                let len = (*MERGE_TRACE_SOURCE).len();
                let i = 2 * (len - 1 - merge_trace_output_index(dst)) + 1;
                assert!(i < 2 * (*MERGE_TRACE_SOURCE).mid());
                let before = (*MERGE_TRACE_STATES)[i];
                let after = (*MERGE_TRACE_STATES)[i + 1];
                let source = MERGE_TRACE_ACTUAL_SOURCE;
                assert!(ptr::eq(left, source.add(before.left_end as usize).wrapping_sub(1)));
                assert!(ptr::eq(right, source.add(before.right_end as usize).wrapping_sub(1)));
                assert!(ptr::eq(
                    dst,
                    MERGE_TRACE_OUTPUT.add((*MERGE_TRACE_SOURCE).len() - 1 - before.back as usize)
                ));
                let result = merge_down_scalar(left, right, dst, cmp);
                assert!(ptr::eq(result.0, source.add(after.left_end as usize).wrapping_sub(1)));
                assert!(ptr::eq(result.1, source.add(after.right_end as usize).wrapping_sub(1)));
                assert!(ptr::eq(
                    result.2,
                    MERGE_TRACE_OUTPUT.add((*MERGE_TRACE_SOURCE).len() - 1 - after.back as usize)
                ));
                let expected = (*MERGE_TRACE_EXPECTED)
                    [(*MERGE_TRACE_SOURCE).len() - 1 - before.back as usize]
                    .assume_init();
                assert_eq!(*dst, expected);
                result
            }
        }
    }
    unsafe fn merge_up_trace<T, F: FnMut(&T, &T) -> bool>(
        left: *const T,
        right: *const T,
        dst: *mut T,
        cmp: &mut F,
    ) -> (*const T, *const T, *mut T) {
        unsafe { <(T, F) as TraceMergeStep<T, F>>::up(left, right, dst, cmp) }
    }
    unsafe fn merge_down_trace<T, F: FnMut(&T, &T) -> bool>(
        left: *const T,
        right: *const T,
        dst: *mut T,
        cmp: &mut F,
    ) -> (*const T, *const T, *mut T) {
        unsafe { <(T, F) as TraceMergeStep<T, F>>::down(left, right, dst, cmp) }
    }

    macro_rules! native_merge_length_cases {
        ($($name:ident: $len:literal),+ $(,)?) => {
            const _: () = {
                let lengths = [$($len),+];
                assert!(lengths.len() == 31);
                let mut i = 0;
                while i < lengths.len() { assert!(lengths[i] == i + 2); i += 1; }
            };
            $(
                #[kani::proof_for_contract(super::bidirectional_merge)]
                #[kani::stub_verified(indexed_merge_contract)]
                #[kani::stub(super::merge_up, merge_up_trace)]
                #[kani::stub(super::merge_down, merge_down_trace)]
                #[kani::unwind(34)]
                fn $name() {
                    let source = MergeInput { values: kani::any(), len: $len };
                    // Exact source and destination capacities make stray reads
                    // or writes past the live slice visible to the verifier.
                    let actual_source: [u8; $len] = crate::array::from_fn(|i| source[i]);
                    let mut actual = [MaybeUninit::<u8>::uninit(); $len];
                    let mut model: [u8; 32] = kani::any();
                    let mut trace = [initial_merge_progress(&source); 33];
                    let probe: u8 = kani::any();
                    let mut actual_cmp = ByteOrder { probe };
                    let mut model_cmp = ByteOrder { probe };
                    kani::assume(sorted_halves(source.as_ptr(), source.len(), &actual_cmp));
                    indexed_merge_contract(&source, &mut model, &mut model_cmp, &mut trace);
                    unsafe {
                        MERGE_TRACE_SOURCE = &source;
                        MERGE_TRACE_ACTUAL_SOURCE = actual_source.as_ptr();
                        MERGE_TRACE_EXPECTED = (&model as *const [u8; 32]).cast();
                        MERGE_TRACE_STATES = &trace;
                        MERGE_TRACE_OUTPUT = actual.as_mut_ptr().cast();
                        super::bidirectional_merge(
                            &actual_source,
                            actual.as_mut_ptr().cast(),
                            &mut actual_cmp,
                        );
                        let mut i = 0;
                        while i < source.len() {
                            assert_eq!(actual[i].assume_init(), model[i]);
                            i += 1;
                        }
                    }
                    assert_eq!(actual_cmp.probe, probe);
                    assert_eq!(model_cmp.probe, probe);
                    kani::cover(true, "the native length partition returns");
                }
            )+
        };
    }
    native_merge_length_cases!(
        indexed_merge_native_length_02: 2,
        indexed_merge_native_length_03: 3,
        indexed_merge_native_length_04: 4,
        indexed_merge_native_length_05: 5,
        indexed_merge_native_length_06: 6,
        indexed_merge_native_length_07: 7,
        indexed_merge_native_length_08: 8,
        indexed_merge_native_length_09: 9,
        indexed_merge_native_length_10: 10,
        indexed_merge_native_length_11: 11,
        indexed_merge_native_length_12: 12,
        indexed_merge_native_length_13: 13,
        indexed_merge_native_length_14: 14,
        indexed_merge_native_length_15: 15,
        indexed_merge_native_length_16: 16,
        indexed_merge_native_length_17: 17,
        indexed_merge_native_length_18: 18,
        indexed_merge_native_length_19: 19,
        indexed_merge_native_length_20: 20,
        indexed_merge_native_length_21: 21,
        indexed_merge_native_length_22: 22,
        indexed_merge_native_length_23: 23,
        indexed_merge_native_length_24: 24,
        indexed_merge_native_length_25: 25,
        indexed_merge_native_length_26: 26,
        indexed_merge_native_length_27: 27,
        indexed_merge_native_length_28: 28,
        indexed_merge_native_length_29: 29,
        indexed_merge_native_length_30: 30,
        indexed_merge_native_length_31: 31,
        indexed_merge_native_length_32: 32,
    );
}
