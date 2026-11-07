//! Bounded permutation checks with distinct identity tags and arbitrary comparison answers.
//!
//! Each comparison reads both arguments and chooses a fresh bool. No ordering law is assumed.
//! Distinct tags track equal payloads separately, and fresh answers include every answer
//! sequence of a returning comparator. The fixed initial identity order restricts no payload
//! order; see verify.rs for the whole-element transfer assumption and its limits.
//! Tag types match the source types without wrappers; a separate root checks dispatch.
//!
//! Exactly N outputs, range checks, and an all-ones mask imply that each tag occurs once.
//! A u64 mask accommodates 32 tags without a full-width shift. The unwind budget also covers
//! the largest selected route and the tag-check loops.

use super::super::{
    MAX_STACK_ARRAY_SIZE, SMALL_SORT_FALLBACK_THRESHOLD, SMALL_SORT_GENERAL_SCRATCH_LEN,
    SMALL_SORT_GENERAL_THRESHOLD, SMALL_SORT_NETWORK_SCRATCH_LEN, SMALL_SORT_NETWORK_THRESHOLD,
    StableSmallSortTypeImpl, UnstableSmallSortFreezeTypeImpl, UnstableSmallSortTypeImpl,
    has_efficient_in_place_swap,
};
use crate::cell::Cell;
use crate::mem::size_of;
use crate::{kani, ptr};

fn arbitrary_u8_order(a: &u8, b: &u8) -> bool {
    // SAFETY: the real sort must supply initialized, readable comparator arguments.
    unsafe {
        let _ = ptr::read_volatile(a);
        let _ = ptr::read_volatile(b);
    }
    kani::any()
}

#[cfg(kani_smallsort_controls)]
fn abort_on_order_violation() -> ! {
    kani::cover(true, "order violation panic is reachable");
    kani::assume(false);
    unreachable!()
}

// The ordinary networks never reach this panic boundary. Keep the cutoff but omit its cover.
fn abort_without_panic_cover() -> ! {
    kani::assume(false);
    unreachable!()
}

fn check_tags<const N: usize>(tags: &[u64; N]) {
    assert!(N > 0 && N <= 32);
    let mut seen = 0u64;
    for &tag in tags {
        kani::assert(tag < N as u64, "output tag is in range");
        // Keep the shift defined even on a counterexample with an out-of-range tag.
        if tag < N as u64 {
            seen |= 1u64 << tag;
        }
    }
    kani::assert(seen == (1u64 << N) - 1, "every input tag occurs exactly once");
}

fn network_output<const N: usize>() -> [u8; N] {
    let mut v = crate::array::from_fn(|i| i as u8);
    <u8 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut arbitrary_u8_order);
    v
}

fn network_body<const N: usize>() {
    let v = network_output::<N>();
    check_tags(&crate::array::from_fn::<_, N, _>(|i| v[i] as u64));
    kani::cover(true, "network returns with every tag");
}

#[kani::proof]
fn tag_types_preserve_source_routes() {
    fn require_freeze_copy<T: crate::slice::sort::shared::FreezeMarker + Copy>() {}
    require_freeze_copy::<u8>();
    require_freeze_copy::<u64>();

    // Unstable u8 takes the Freeze+Copy network specialization and its size branch.
    assert!(size_of::<u8>() == 1);
    assert!(has_efficient_in_place_swap::<u8>());
    assert!(size_of::<u8>() * SMALL_SORT_NETWORK_SCRATCH_LEN <= MAX_STACK_ARRAY_SIZE);
    assert!(<u8 as UnstableSmallSortTypeImpl>::small_sort_threshold() == 32);
    assert!(
        <u8 as UnstableSmallSortFreezeTypeImpl>::small_sort_threshold()
            == SMALL_SORT_NETWORK_THRESHOLD
    );

    // Stable Freeze u64 always selects general, independently of the swap heuristic.
    assert!(size_of::<u64>() == 8);
    assert!(SMALL_SORT_GENERAL_SCRATCH_LEN == 48);
    assert!(
        <u64 as StableSmallSortTypeImpl>::small_sort_threshold() == SMALL_SORT_GENERAL_THRESHOLD
    );
    assert!(SMALL_SORT_GENERAL_THRESHOLD == 32);

    // The Freeze specialization would return 32: 16 identifies the blanket Stable entry.
    assert!(
        <Cell<u8> as StableSmallSortTypeImpl>::small_sort_threshold()
            == SMALL_SORT_FALLBACK_THRESHOLD
    );
    assert!(SMALL_SORT_FALLBACK_THRESHOLD == 16);
    kani::cover(true, "tag and source types select the required routes");
}

#[kani::proof]
#[kani::stub(
    crate::slice::sort::shared::smallsort::panic_on_ord_violation,
    abort_without_panic_cover
)]
#[kani::unwind(34)]
fn network_u8_n9() {
    network_body::<9>();
}

#[kani::proof]
#[kani::stub(
    crate::slice::sort::shared::smallsort::panic_on_ord_violation,
    abort_without_panic_cover
)]
#[kani::unwind(34)]
fn network_u8_n13() {
    network_body::<13>();
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::stub(
    crate::slice::sort::shared::smallsort::panic_on_ord_violation,
    abort_on_order_violation
)]
#[kani::unwind(34)]
fn reject_duplicate_network_u8_n9() {
    let mut v = network_output::<9>();
    kani::cover(true, "duplicate mutant reaches the corruption");
    // SAFETY: both pointers name distinct initialized elements of the same live array.
    // Deliberately lose one identity after the same real sorting call used by the positive root.
    unsafe { ptr::copy(v.as_ptr(), v.as_mut_ptr().add(1), 1) };
    check_tags(&crate::array::from_fn::<_, 9, _>(|i| v[i] as u64));
}
