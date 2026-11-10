//! Stable scratch geometry and full-value preservation with an arbitrary reading comparator.
//! The unwind budget accommodates the selected route and its full-value count loops.

use super::super::{SMALL_SORT_GENERAL_THRESHOLD, StableSmallSortTypeImpl};
use super::merge::{probe_count_unrolled, regions_are_disjoint, set_value_probe};
use crate::mem::MaybeUninit;
use crate::slice::sort::shared::FreezeMarker;
use crate::{kani, ptr};

fn require_freeze<T: FreezeMarker>() {}

fn arbitrary_order(a: &u64, b: &u64) -> bool {
    // SAFETY: the sort must provide initialized, readable elements for both references.
    unsafe {
        ptr::read_volatile(a);
        ptr::read_volatile(b);
    }
    kani::any()
}

fn abort_on_order_violation() -> ! {
    kani::assume(false);
    unreachable!()
}

fn check_geometry<const N: usize>(
    original: &[u64; N],
    v: &mut [u64],
    scratch: &mut [MaybeUninit<u64>],
) {
    const { assert!(N >= 2 && N <= 32) };
    require_freeze::<u64>();
    let threshold = <u64 as StableSmallSortTypeImpl>::small_sort_threshold();
    assert!(threshold == SMALL_SORT_GENERAL_THRESHOLD);
    assert!(v.len() == N && N <= threshold);
    assert!(scratch.len() >= N + 16);
    assert!(regions_are_disjoint::<u64>(
        v.as_ptr(),
        N,
        scratch.as_ptr().cast::<u64>(),
        scratch.len(),
    ));
    // Stable's Freeze specialization calls small_sort_general_with_scratch unconditionally;
    // the efficient-swap predicate belongs to unstable dispatch and is not a stable selector.
    kani::cover(
        threshold == SMALL_SORT_GENERAL_THRESHOLD && v.len() >= 2,
        "Stable Freeze selects small_sort_general_with_scratch beyond its early return",
    );
    set_value_probe::<u64>();
    <u64 as StableSmallSortTypeImpl>::small_sort(v, scratch, &mut arbitrary_order);
    // u64 has no padding: the existing arbitrary byte probe observes the complete value.
    // Both regions counted here contain N initialized u64 values; scratch is never counted.
    assert!(
        probe_count_unrolled::<u64>(original.as_ptr(), N)
            == probe_count_unrolled::<u64>(v.as_ptr(), N),
        "full u64 value multiplicities are preserved on normal return"
    );
    kani::cover(true, "scratch geometry returns normally and preserves full values");
}

fn separate_allocation<const N: usize, const S: usize>() {
    const { assert!(S >= N + 16 && S != 48) };
    let original: [u64; N] = kani::any();
    let mut v = original;
    let mut scratch = [MaybeUninit::<u64>::uninit(); S];
    assert!(!kani::mem::same_allocation(v.as_ptr(), scratch.as_ptr().cast::<u64>()));
    check_geometry(&original, &mut v, &mut scratch);
}

macro_rules! geometry_harness {
    ($name:ident, $body:ident, $n:literal, $capacity:literal) => {
        #[kani::proof]
        #[kani::stub(super::super::panic_on_ord_violation, abort_on_order_violation)]
        #[kani::unwind(34)]
        fn $name() {
            $body::<$n, $capacity>();
        }
    };
}

geometry_harness!(stable_u64_min_scratch_n2, separate_allocation, 2, 18);
