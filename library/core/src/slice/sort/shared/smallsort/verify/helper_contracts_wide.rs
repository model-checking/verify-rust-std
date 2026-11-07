//! Allocation-aware contract proofs paired with network and sort8 consumers.

use super::super::{UnstableSmallSortTypeImpl, bidirectional_merge, sort8_stable, swap_if_less};
use crate::mem::{ManuallyDrop, MaybeUninit};
use crate::{kani, ptr};

fn arbitrary_less<T>(a: &T, b: &T) -> bool {
    // SAFETY: the real helper supplies readable initialized references. ManuallyDrop
    // prevents dropping the temporary volatile copies of the Copy scalar elements.
    unsafe {
        let _a = ManuallyDrop::new(ptr::read_volatile(a));
        let _b = ManuallyDrop::new(ptr::read_volatile(b));
    }
    let answer: bool = kani::any();
    kani::cover(answer, "comparator true");
    kani::cover(!answer, "comparator false");
    answer
}

fn exercise_swap<T: kani::Arbitrary + Copy + PartialEq>() {
    let mut backing: [T; 32] = kani::any();
    let before = backing;
    let start: usize = kani::any();
    let a: usize = kani::any();
    let b: usize = kani::any();
    kani::assume(start < 32);
    kani::assume(a < 32 - start && b < 32 - start);
    // SAFETY: both possibly equal relative positions are initialized writable elements
    // in this allocation, including when the base is an interior pointer.
    unsafe { swap_if_less(backing.as_mut_ptr().add(start), a, b, &mut arbitrary_less::<T>) };
    for i in 0..32 {
        kani::assert(
            i == start + a || i == start + b || backing[i] == before[i],
            "swap allocation frame",
        );
    }
    kani::cover(a == b, "swap equal positions return");
    kani::cover(a < b, "swap increasing positions return");
    kani::cover(a > b, "swap decreasing positions return");
    kani::cover(start == 0, "swap allocation base returns");
    kani::cover(start == 16, "swap second half base returns");
    kani::cover(start + b == 31, "swap last element returns");
    kani::cover(true, "swap returns");
}

fn cut_order_violation() -> ! {
    kani::cover(true, "network order violation reachable");
    kani::assume(false);
    unreachable!()
}

fn tail_less_u64(a: &u64, b: &u64) -> bool {
    // SAFETY: the helper must provide readable, initialized scalar references.
    unsafe {
        ptr::read_volatile(a);
        ptr::read_volatile(b);
    }
    let answer: bool = kani::any();
    tail_comparison_covers(answer);
    answer
}

fn tail_comparison_covers(answer: bool) {
    kani::cover(answer, "comparator true");
    kani::cover(!answer, "comparator false");
}

fn cut_merge_order_violation() -> ! {
    kani::cover(true, "merge order violation reachable");
    kani::assume(false);
    unreachable!()
}

// The unwind budget includes the 32-element frame loop and interior-base geometry checks.
#[kani::proof_for_contract(swap_if_less)]
#[kani::unwind(50)]
fn swap_safety_u8_backing32() {
    exercise_swap::<u8>();
}

#[kani::proof_for_contract(swap_if_less)]
#[kani::unwind(50)]
fn swap_safety_u64_backing32() {
    exercise_swap::<u64>();
}

// The paired swap proof includes interior bases for both halves of this network.
// Insertion and merge run their real bodies; only the order-violation abort path is cut.
#[kani::proof]
#[kani::stub_verified(swap_if_less)]
#[kani::stub(super::super::panic_on_ord_violation, cut_order_violation)]
#[kani::unwind(50)]
fn unstable_network_safety_u8_n32_stubbed() {
    let mut backing: [u8; 32] = kani::any();
    kani::cover(backing.len() == 32, "network maximum length entered");
    <u8 as UnstableSmallSortTypeImpl>::small_sort(&mut backing, &mut arbitrary_less::<u8>);
    kani::cover(true, "network maximum length returns");
}

// Match sort8's scratch geometry with only its source region initialized.
// The unwind budget also accommodates the consumer's 32-element input-frame loop.
#[kani::proof_for_contract(bidirectional_merge)]
#[kani::stub(super::super::panic_on_ord_violation, cut_merge_order_violation)]
#[kani::unwind(34)]
fn merge_safety_u64_len8_scratch48_src32_dst0() {
    let values: [u64; 8] = kani::any();
    let mut scratch = [MaybeUninit::<u64>::uninit(); 48];
    for i in 0..8 {
        scratch[32 + i].write(values[i]);
    }
    kani::cover(values.len() == 8, "merge length8 entered");
    // SAFETY: initialized source [32..40] and uninitialized destination [0..8] are
    // disjoint regions of this one aligned, writable allocation of 48 elements.
    unsafe {
        let base = scratch.as_mut_ptr().cast::<u64>();
        let source = crate::slice::from_raw_parts(base.add(32), 8);
        bidirectional_merge(source, base, &mut tail_less_u64);
    }
    for i in 0..8 {
        // SAFETY: the initialized source must be framed by the merge.
        let after = unsafe { scratch[32 + i].assume_init() };
        kani::assert(after == values[i], "merge source frame");
    }
    kani::cover(true, "merge length8 returns");
}

// Real sort4 calls initialize the source region required by the paired merge proof.
// The source-frame check includes input elements beyond the eight passed to sort8.
#[kani::proof]
#[kani::stub_verified(bidirectional_merge)]
#[kani::unwind(34)]
fn sort8_safety_u64_scratch48_src32_dst0_merge_stubbed() {
    let mut backing: [u64; 32] = kani::any();
    let before = backing;
    let mut scratch = [MaybeUninit::<u64>::uninit(); 48];
    kani::cover(scratch.len() == 48, "sort8 scratch48 entered");
    // SAFETY: the real sort4 calls initialize scratch[32..40] before the verified
    // merge stub writes the disjoint destination [0..8]. Input has eight readable elements.
    unsafe {
        let base = scratch.as_mut_ptr().cast::<u64>();
        sort8_stable(backing.as_mut_ptr(), base, base.add(32), &mut tail_less_u64);
    }
    for i in 0..32 {
        kani::assert(backing[i] == before[i], "sort8 source allocation frame");
    }
    // A stub promising only safety and a write set gives no initialization postcondition
    // for the destination.
    kani::cover(true, "sort8 merge consumer returns");
}
