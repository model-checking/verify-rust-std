//! Fixed witnesses, a mutant swap control, and stable unit-ZST checks.

use super::super::{
    StableSmallSortTypeImpl, bidirectional_merge, insert_tail, merge_up, small_sort_network,
    swap_if_less,
};
use crate::mem::MaybeUninit;
use crate::{kani, ptr};

fn strict_less(a: &u8, b: &u8) -> bool {
    // SAFETY: both arguments must be initialized and readable before comparison.
    unsafe { ptr::read_volatile(a) < ptr::read_volatile(b) }
}

fn cut_ord_violation() -> ! {
    // The panic stub cuts only the explicit order-violation path; normal returns are covered below.
    kani::assume(false);
    unreachable!()
}

fn check_swap(call: impl FnOnce(&mut [u8; 2])) {
    let mut v: [u8; 2] = kani::any();
    let before = v;
    call(&mut v);
    assert!(v[0] <= v[1]);
    assert!((v == before) || (v == [before[1], before[0]]));
    kani::cover(true, "swap returns a sorted permutation");
}

fn check_insert(call: impl FnOnce(&mut [u8; 2])) {
    let mut v: [u8; 2] = kani::any();
    let before = v;
    call(&mut v);
    assert!(v[0] <= v[1]);
    assert!((v == before) || (v == [before[1], before[0]]));
    kani::cover(true, "insertion returns a sorted permutation");
}

fn check_merge_up(
    call: impl FnOnce(*const u8, *const u8, *mut u8) -> (*const u8, *const u8, *mut u8),
) {
    let src: [u8; 2] = kani::any();
    let left = src.as_ptr();
    // SAFETY: second element in src.
    let right = unsafe { left.add(1) };
    let mut dst = MaybeUninit::<u8>::uninit();
    let out = dst.as_mut_ptr();
    let (next_left, next_right, next_dst) = call(left, right, out);
    let take_left = src[0] <= src[1];
    // SAFETY: these expected pointers are at most one-past the source and destination arrays.
    let advancement_ok = unsafe {
        next_left == left.add(take_left as usize)
            && next_right == right.add((!take_left) as usize)
            && next_dst == out.add(1)
    };
    assert!(advancement_ok);
    // SAFETY: merge_up wrote exactly one element.
    let value = unsafe { dst.assume_init() };
    assert!(value == if take_left { src[0] } else { src[1] });
    kani::cover(take_left, "forward merge consumes left");
    kani::cover(!take_left, "forward merge consumes right");
}

fn count(v: &[u8; 4], probe: u8) -> usize {
    (v[0] == probe) as usize
        + (v[1] == probe) as usize
        + (v[2] == probe) as usize
        + (v[3] == probe) as usize
}

fn arbitrary_less(a: &u8, b: &u8) -> bool {
    // SAFETY: both comparator arguments must be initialized and readable.
    unsafe {
        let _left = ptr::read_volatile(a);
        let _right = ptr::read_volatile(b);
    }
    kani::any()
}

fn check_merge_consumption(call: impl FnOnce(&[u8; 4], *mut u8)) {
    let src: [u8; 4] = kani::any();
    let probe: u8 = kani::any();
    let mut dst = MaybeUninit::<[u8; 4]>::uninit();
    call(&src, dst.as_mut_ptr().cast());
    // SAFETY: both merge directions wrote two output elements on normal return.
    let result = unsafe { dst.assume_init() };
    assert!(count(&src, probe) == count(&result, probe));
    kani::cover(true, "merge preserves the probe count on normal return");
}

fn check_presorted_len(call: impl FnOnce(&mut [u8; 10])) {
    // Sorted prefix of nine; the tenth zero must move to the front.
    let mut v = [1u8, 1, 1, 1, 1, 1, 1, 1, 1, 0];
    call(&mut v);
    assert!(v[0] == 0 && v[9] == 1);
    kani::cover(true, "network inserts the tenth element");
}

macro_rules! original_case {
    ($positive:ident, $check:ident, $original:expr) => {
        #[kani::proof]
        #[kani::unwind(17)]
        #[kani::stub(super::super::panic_on_ord_violation, cut_ord_violation)]
        fn $positive() {
            $check($original);
        }
    };
}

// The shared helpers establish each call's valid pointers, initialized values, and region lengths.
original_case!(
    sorted_permutation_swap_u8_n2,
    check_swap,
    // SAFETY: two distinct initialized elements in the same two-element array.
    |v: &mut [u8; 2]| unsafe { swap_if_less(v.as_mut_ptr(), 0, 1, &mut strict_less) }
);
original_case!(
    sorted_permutation_insert_tail_u8_n2,
    check_insert,
    // SAFETY: sorted one-element prefix and initialized tail in the same array.
    |v: &mut [u8; 2]| unsafe {
        insert_tail(v.as_mut_ptr(), v.as_mut_ptr().add(1), &mut strict_less)
    }
);
original_case!(
    advancement_merge_up_u8_n2,
    check_merge_up,
    // SAFETY: helper supplies two readable elements and a separate writable destination.
    |l, r, d| unsafe { merge_up(l, r, d, &mut strict_less) }
);
original_case!(
    permutation_merge_u8_n4,
    check_merge_consumption,
    // SAFETY: helper supplies four initialized inputs and a separate four-element destination.
    |v: &[u8; 4], d| unsafe { bidirectional_merge(v, d, &mut arbitrary_less) }
);
original_case!(
    sorted_network_prefix_u8_n10,
    check_presorted_len,
    // Safe entry: the exact ten-element array supplies the network length.
    |v: &mut [u8; 10]| small_sort_network(v, &mut strict_less)
);

// Opt-in negative control: the swap check above, run on a copy that negates the exchange decision.
#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::unwind(17)]
#[kani::stub(super::super::panic_on_ord_violation, cut_ord_violation)]
fn reject_mutant_swap_u8_n2() {
    // SAFETY: two distinct initialized elements in the same two-element array.
    check_swap(|v: &mut [u8; 2]| unsafe {
        super::mutations::mutant_swap_if_less(v.as_mut_ptr(), 0, 1, &mut strict_less)
    });
}

// The unwind budget allows the longest selected stable route despite zero-sized elements.
macro_rules! stable_unit_case {
    ($name:ident, $n:literal) => {
        #[kani::proof]
        #[kani::unwind(65)]
        #[kani::stub(super::super::panic_on_ord_violation, cut_ord_violation)]
        fn $name() {
            let mut v = [(); $n];
            let mut scratch = [MaybeUninit::<()>::uninit(); 48];
            <() as StableSmallSortTypeImpl>::small_sort(
                &mut v,
                &mut scratch,
                &mut super::comparators::zst_aware_less::<()>,
            );
            kani::cover(true, concat!("stable unit sort returns at length ", stringify!($n)));
        }
    };
}

stable_unit_case!(safety_stable_unit_n1, 1);
stable_unit_case!(safety_stable_unit_n2, 2);
stable_unit_case!(safety_stable_unit_n7, 7);
stable_unit_case!(safety_stable_unit_n8, 8);
stable_unit_case!(safety_stable_unit_n16, 16);
stable_unit_case!(safety_stable_unit_n17, 17);
stable_unit_case!(safety_stable_unit_n31, 31);
stable_unit_case!(safety_stable_unit_n32, 32);
