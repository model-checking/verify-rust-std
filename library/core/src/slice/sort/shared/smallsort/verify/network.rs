//! Exchange and insertion profiles, plus real network and dispatch checks.
//! Ordered profiles guard a canonical comparator; real helper frame proofs live in the
//! contract modules listed in verify.rs.

use super::super::UnstableSmallSortFreezeTypeImpl;
use super::merge::profiles::{
    LtI32, LtU8, LtU64, Profile, identity_profile, insert_tail_profile, swap_profile,
};
use crate::kani;
use crate::mem::size_of;

/// Real exchange with coincident positions, including an unlawful true comparison on equality.
#[kani::proof]
fn swap_same_position_u8() {
    let before: u8 = kani::any();
    let mut value = before;
    let taken: bool = kani::any();
    let mut cmp = |a: &u8, b: &u8| {
        // SAFETY: both shared references point at the same initialized byte.
        unsafe {
            let _ = crate::ptr::read_volatile(a);
            let _ = crate::ptr::read_volatile(b);
        }
        taken
    };
    // SAFETY: both positions name the single live, aligned, initialized writable byte.
    unsafe { super::super::swap_if_less(&mut value, 0, 0, &mut cmp) };
    kani::assert(value == before, "same-position exchange preserves the full byte");
    kani::cover(taken, "same-position exchange: true comparator returns");
    kani::cover(!taken, "same-position exchange: false comparator returns");
}

/// Freeze without Copy; its size exceeds the general route's stack budget.
#[repr(transparent)]
struct NonCopyBytes86([u8; 86]);

const _: () = {
    use super::super::{CopyMarker, MAX_STACK_ARRAY_SIZE, SMALL_SORT_GENERAL_SCRATCH_LEN};
    use crate::slice::sort::shared::FreezeMarker;

    fn require_freeze<T: FreezeMarker>() {}
    let _ = require_freeze::<NonCopyBytes86>;
    assert!(size_of::<NonCopyBytes86>() == 86);
    assert!(size_of::<NonCopyBytes86>() * SMALL_SORT_GENERAL_SCRATCH_LEN > MAX_STACK_ARRAY_SIZE);

    // Type inference becomes ambiguous if CopyMarker holds. Copy implies CopyMarker through
    // the runtime blanket impl, so this also statically excludes Copy and its specialization.
    trait AmbiguousIfCopy<A> {
        const CHECK: () = ();
    }
    impl<T> AmbiguousIfCopy<()> for T {}
    impl<T: CopyMarker> AmbiguousIfCopy<u8> for T {}
    let () = <NonCopyBytes86 as AmbiguousIfCopy<_>>::CHECK;
};

// The unwind budget includes all 86 bytes in the full-value comparison loops.
#[kani::proof]
#[kani::unwind(87)]
fn unstable_freeze_noncopy_bytes86_fallback_n2() {
    use super::super::{SMALL_SORT_FALLBACK_THRESHOLD, UnstableSmallSortTypeImpl};

    let [a, b]: [[u8; 86]; 2] = kani::any();
    let mut v = [NonCopyBytes86(a), NonCopyBytes86(b)];
    let taken: bool = kani::any();
    let mut cmp = |a: &NonCopyBytes86, b: &NonCopyBytes86| {
        // SAFETY: the real insertion comparator must receive initialized readable payloads.
        unsafe {
            let _ = crate::ptr::read_volatile(&a.0[0]);
            let _ = crate::ptr::read_volatile(&b.0[0]);
        }
        taken
    };
    assert!(
        <NonCopyBytes86 as UnstableSmallSortTypeImpl>::small_sort_threshold()
            == SMALL_SORT_FALLBACK_THRESHOLD
    );
    <NonCopyBytes86 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut cmp);
    for i in 0..86 {
        kani::assert(v[0].0[i] == if taken { b[i] } else { a[i] }, "fallback keeps first value");
        kani::assert(v[1].0[i] == if taken { a[i] } else { b[i] }, "fallback keeps second value");
    }
    kani::cover(taken, "Freeze non-Copy bytes86 fallback swaps at N2");
    kani::cover(!taken, "Freeze non-Copy bytes86 fallback keeps order at N2");
    kani::cover(true, "Freeze non-Copy bytes86 fallback returns at N2");
}

/// Positions anywhere in a 4-element array, in either order, distinct as the profile requires.
fn exercise_swap_contract<P: Profile>()
where
    P::Elem: kani::Arbitrary + Copy,
{
    let mut v: [P::Elem; 4] = kani::any();
    let a: usize = kani::any_where(|&a| a < 4);
    let b: usize = kani::any_where(|&b| b < 4 && b != a);
    kani::cover(a == 0 && b == 3, "swap_if_less: a < b reachable");
    kani::cover(a == 3 && b == 0, "swap_if_less: a > b reachable");
    let (old_a, old_b) = (v[a], v[b]);
    // SAFETY: `a` and `b` are distinct in-bounds positions of `v`; canonical comparator.
    unsafe { swap_profile::<P>(v.as_mut_ptr(), a, b, P::CMP) };
    kani::cover((P::CMP)(&old_b, &old_a), "swap_if_less: swap taken");
    kani::cover(!(P::CMP)(&old_b, &old_a), "swap_if_less: swap not taken");
    kani::cover(true, "swap_if_less: end reached");
}

#[kani::proof_for_contract(super::merge::profiles::swap_profile)]
fn swap_contract_four_positions_u8() {
    exercise_swap_contract::<LtU8>();
}

#[kani::proof_for_contract(super::merge::profiles::swap_profile)]
fn swap_contract_four_positions_i32() {
    exercise_swap_contract::<LtI32>();
}

#[kani::proof_for_contract(super::merge::profiles::swap_profile)]
fn swap_contract_four_positions_u64() {
    exercise_swap_contract::<LtU64>();
}

/// `a[from..] == b[from..]` element by element (slice `==` would become a byte loop of `memcmp`).
fn prefix_unchanged<T: PartialEq>(a: &[T], b: &[T], from: usize) -> bool {
    let mut i = from;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    a.len() == b.len()
}

fn volatile_reading_less_u64(a: &u64, b: &u64) -> bool {
    // SAFETY: initialized readable references; volatile reads retain both accesses.
    unsafe {
        let _ = crate::ptr::read_volatile(a);
        let _ = crate::ptr::read_volatile(b);
    }
    kani::any()
}

// The safety unwind budget leaves room for the longest selected 32-element route.
fn unstable_freeze_network_fixed<const N: usize>() {
    let mut v: [u64; N] = kani::any();
    <u64 as UnstableSmallSortFreezeTypeImpl>::small_sort(&mut v, &mut volatile_reading_less_u64);
}

macro_rules! unstable_freeze_network_cases {
    ($name:ident, [$($n:literal),+], [$($attr:meta),*]) => {
        #[kani::proof]
        $(#[$attr])*
        #[kani::unwind(35)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            match len {
                $($n => unstable_freeze_network_fixed::<$n>(),)+
                _ => {}
            }
            $(kani::cover(
                len == $n,
                concat!("unstable network normal return at ", stringify!($n))
            );)+
            kani::cover(true, "unstable network family reached the end");
        }
    };
}

unstable_freeze_network_cases!(
    network_safety_unstable_u64_n0_to17,
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
    []
);
fn count_matching_values<T: PartialEq>(s: &[T], p: &T) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < s.len() {
        if s[i] == *p {
            n += 1;
        }
        i += 1;
    }
    n
}
fn is_sorted_by<T, F: FnMut(&T, &T) -> bool>(s: &[T], cmp: &mut F) -> bool {
    let mut i = 1;
    while i < s.len() {
        if cmp(&s[i], &s[i - 1]) {
            return false;
        }
        i += 1;
    }
    true
}
#[derive(Clone, Copy)]
struct TaggedKey {
    key: u8,
    tag: u8,
}

type TaggedKeyCell = crate::cell::Cell<TaggedKey>;
// N <= 20, so a u8 probe count cannot overflow.
fn count_tagged_values<const N: usize>(v: &[TaggedKeyCell; N], probe: u8) -> u8 {
    let mut count = 0;
    let mut i = 0;
    while i < N {
        count += (v[i].get().tag == probe) as u8;
        i += 1;
    }
    count
}

fn tag_sequence<const N: usize>(v: &[TaggedKeyCell; N]) -> [u8; N] {
    let mut tags = [0; N];
    let mut i = 0;
    while i < N {
        tags[i] = v[i].get().tag;
        i += 1;
    }
    tags
}
// These route checks stub only the explicit order-violation panic. The other assertions and
// memory checks remain active, and no verified contracts replace the sort bodies.
fn cut_order_violation_panic() -> ! {
    kani::cover(true, "order-violation panic stub reached");
    assume_order_violation()
}

fn assume_order_violation() -> ! {
    kani::assume(false);
    unreachable!()
}

fn unstable_dispatch_network_fixed<const N: usize>() {
    use super::super::UnstableSmallSortTypeImpl;
    let mut v: [u64; N] = kani::any();
    <u64 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut volatile_reading_less_u64);
}

macro_rules! unstable_dispatch_network_cases {
    ($name:ident, [$($n:literal),+]) => {
        #[kani::proof]
        #[kani::stub(super::super::panic_on_ord_violation, cut_order_violation_panic)]
        #[kani::unwind(35)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            match len {
                $($n => unstable_dispatch_network_fixed::<$n>(),)+
                _ => {}
            }
            $(kani::cover(
                len == $n,
                concat!("unstable network normal return at ", stringify!($n))
            );)+
            kani::cover(true, "unstable network family reached the end");
        }
    };
}

unstable_dispatch_network_cases!(network_safety_unstable_u64_n30, [30]);
unstable_dispatch_network_cases!(network_safety_unstable_u64_n31, [31]);
unstable_dispatch_network_cases!(network_safety_unstable_u64_n32, [32]);

// Dispatch checks use a conservative unwind budget for both routes and element construction.
// Inputs use their full element domains; these checks assert safety and normal return.
trait ArbitraryValue: Sized {
    fn arbitrary_value() -> Self;
}

impl ArbitraryValue for u8 {
    fn arbitrary_value() -> Self {
        kani::any()
    }
}

fn volatile_reading_less<T>(a: &T, b: &T) -> bool {
    // SAFETY: real sort bodies must supply readable initialized values. ManuallyDrop avoids
    // running Drop on the duplicate returned by the volatile read of a non-Copy value.
    unsafe {
        let _left = crate::mem::ManuallyDrop::new(crate::ptr::read_volatile(a));
        let _right = crate::mem::ManuallyDrop::new(crate::ptr::read_volatile(b));
    }
    kani::any()
}

fn dispatch_safety_fixed<T: ArbitraryValue, const N: usize, const STABLE: bool>() {
    use super::super::{StableSmallSortTypeImpl, UnstableSmallSortTypeImpl};
    let mut v: [T; N] = crate::array::from_fn(|_| T::arbitrary_value());
    if STABLE {
        let mut scratch = [const { crate::mem::MaybeUninit::<T>::uninit() }; 48];
        <T as StableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut scratch,
            &mut volatile_reading_less::<T>,
        );
    } else {
        <T as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut volatile_reading_less::<T>);
    }
}

macro_rules! dispatch_safety_cases {
    ($name:ident, $t:ty, $stable:literal, [$($n:literal),+]) => {
        #[kani::proof]
        #[kani::stub(super::super::panic_on_ord_violation, assume_order_violation)]
        #[kani::unwind(65)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            match len {
                $($n => dispatch_safety_fixed::<$t, $n, $stable>(),)+
                _ => {}
            }
            $(kani::cover(
                len == $n,
                concat!("dispatch route returns normally at ", stringify!($n))
            );)+
            kani::cover(true, "dispatch safety family reached the end");
        }
    };
}

dispatch_safety_cases!(dispatch_safety_stable_u8_n0_1_2_7_8, u8, true, [0, 1, 2, 7, 8]);
dispatch_safety_cases!(dispatch_safety_stable_u8_n15_16_17, u8, true, [15, 16, 17]);
dispatch_safety_cases!(dispatch_safety_stable_u8_n31_32, u8, true, [31, 32]);
dispatch_safety_cases!(dispatch_safety_unstable_u8_n8_9_12_13_17, u8, false, [8, 9, 12, 13, 17]);
dispatch_safety_cases!(dispatch_safety_unstable_u8_n18_31_32, u8, false, [18, 31, 32]);

/// Selects stable or unstable dispatch for each listed fixed array length and covers both routes.
macro_rules! dispatch_pair_safety_cases {
    ($name:ident, $t:ty, [$($n:literal),+]) => {
        #[kani::proof]
        #[kani::stub(super::super::panic_on_ord_violation, assume_order_violation)]
        #[kani::unwind(65)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            let stable: bool = kani::any();
            match len {
                $($n => {
                    if stable { dispatch_safety_fixed::<$t, $n, true>(); }
                    else { dispatch_safety_fixed::<$t, $n, false>(); }
                },)+
                _ => {}
            }
            $(
                kani::cover(
                    stable && len == $n,
                    concat!("stable route normal return at ", stringify!($n))
                );
                kani::cover(
                    !stable && len == $n,
                    concat!("unstable route normal return at ", stringify!($n))
                );
            )+
            kani::cover(true, "dispatch family reached the end");
        }
    };
}

macro_rules! dispatch_reachability_case {
    ($name:ident, $t:ty, $stable:literal, $n:literal) => {
        #[kani::proof]
        #[kani::stub(super::super::panic_on_ord_violation, cut_order_violation_panic)]
        #[kani::unwind(65)]
        fn $name() {
            dispatch_safety_fixed::<$t, $n, $stable>();
            kani::cover(true, "dispatch route normal return is reachable");
        }
    };
}

dispatch_reachability_case!(dispatch_reachability_stable_u8_n17, u8, true, 17);
dispatch_reachability_case!(dispatch_reachability_general_bytes16_n17, [u8; 16], false, 17);
dispatch_reachability_case!(dispatch_reachability_network_u8_n18, u8, false, 18);

impl<const M: usize> ArbitraryValue for [u8; M] {
    fn arbitrary_value() -> Self {
        kani::any()
    }
}

dispatch_pair_safety_cases!(
    dispatch_safety_stable_unstable_bytes16_n0_1_2_7_8,
    [u8; 16],
    [0, 1, 2, 7, 8]
);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_bytes16_n15, [u8; 16], [15]);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_bytes16_n16, [u8; 16], [16]);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_bytes16_n17, [u8; 16], [17]);
// Fixed routes keep each branch's return cover reachable.
#[kani::proof]
#[kani::stub(super::super::panic_on_ord_violation, assume_order_violation)]
#[kani::unwind(65)]
fn dispatch_safety_stable_bytes16_n32() {
    dispatch_safety_fixed::<[u8; 16], 32, true>();
    kani::cover(true, "stable route normal return at 32");
    kani::cover(true, "dispatch family reached the end");
}

// The solver and unwind budget are tuned together; their separate effects are not established.
#[kani::proof]
#[kani::stub(super::super::panic_on_ord_violation, assume_order_violation)]
#[kani::solver(kissat)]
#[kani::unwind(33)]
fn dispatch_safety_unstable_bytes16_n32() {
    dispatch_safety_fixed::<[u8; 16], 32, false>();
    kani::cover(true, "unstable route normal return at 32");
    kani::cover(true, "dispatch family reached the end");
}

dispatch_pair_safety_cases!(
    dispatch_safety_stable_unstable_bytes17_n0_1_2_7_8,
    [u8; 17],
    [0, 1, 2, 7, 8]
);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_bytes17_n15, [u8; 17], [15]);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_bytes17_n16, [u8; 17], [16]);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_bytes17_n17, [u8; 17], [17]);
dispatch_safety_cases!(dispatch_safety_stable_bytes17_n32, [u8; 17], true, [32]);
dispatch_safety_cases!(dispatch_safety_unstable_bytes17_n32, [u8; 17], false, [32]);

/// Freeze but non-Copy; the real destructor observes its own initialized key. No drop-count
/// or permutation property is asserted in the safety matrix.
struct DropValue(u8);

impl Drop for DropValue {
    fn drop(&mut self) {
        // SAFETY: a live value must still contain its readable u8 key when dropped.
        unsafe {
            let _ = crate::ptr::read_volatile(&self.0);
        }
    }
}

impl ArbitraryValue for DropValue {
    fn arbitrary_value() -> Self {
        Self(kani::any())
    }
}

dispatch_pair_safety_cases!(
    dispatch_safety_stable_unstable_drop_u8_n0_1_2_7_8,
    DropValue,
    [0, 1, 2, 7, 8]
);
dispatch_pair_safety_cases!(
    dispatch_safety_stable_unstable_drop_u8_n15_16_17,
    DropValue,
    [15, 16, 17]
);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_drop_u8_n32, DropValue, [32]);

impl ArbitraryValue for crate::cell::Cell<i32> {
    fn arbitrary_value() -> Self {
        Self::new(kani::any())
    }
}

dispatch_pair_safety_cases!(
    dispatch_safety_stable_unstable_bytes85_n0_1_2_7_8,
    [u8; 85],
    [0, 1, 2, 7, 8]
);
dispatch_pair_safety_cases!(
    dispatch_safety_stable_unstable_bytes85_n15_16_17,
    [u8; 85],
    [15, 16, 17]
);
dispatch_pair_safety_cases!(dispatch_safety_stable_unstable_bytes85_n32, [u8; 85], [32]);

dispatch_safety_cases!(
    dispatch_safety_unstable_bytes86_n0_1_2_15_16,
    [u8; 86],
    false,
    [0, 1, 2, 15, 16]
);

// Exercises insertion at every valid offset in exact `[u64; N]` arrays. Each match arm makes the
// offset constant at the call site; all insertion bodies are real and no sorted prefix is assumed.
fn insertion_at<T, F: FnMut(&T, &T) -> bool, const O: usize>(v: &mut [T], cmp: &mut F) {
    super::super::insertion_sort_shift_left(v, O, cmp);
}

macro_rules! insertion_at_any_offset {
    ($v:expr, $offset:expr, $n:expr, $cmp:expr) => {
        match $offset {
            1 if $n >= 1 => insertion_at::<_, _, 1>($v, $cmp),
            2 if $n >= 2 => insertion_at::<_, _, 2>($v, $cmp),
            3 if $n >= 3 => insertion_at::<_, _, 3>($v, $cmp),
            4 if $n >= 4 => insertion_at::<_, _, 4>($v, $cmp),
            5 if $n >= 5 => insertion_at::<_, _, 5>($v, $cmp),
            6 if $n >= 6 => insertion_at::<_, _, 6>($v, $cmp),
            7 if $n >= 7 => insertion_at::<_, _, 7>($v, $cmp),
            8 if $n >= 8 => insertion_at::<_, _, 8>($v, $cmp),
            9 if $n >= 9 => insertion_at::<_, _, 9>($v, $cmp),
            10 if $n >= 10 => insertion_at::<_, _, 10>($v, $cmp),
            11 if $n >= 11 => insertion_at::<_, _, 11>($v, $cmp),
            12 if $n >= 12 => insertion_at::<_, _, 12>($v, $cmp),
            13 if $n >= 13 => insertion_at::<_, _, 13>($v, $cmp),
            14 if $n >= 14 => insertion_at::<_, _, 14>($v, $cmp),
            15 if $n >= 15 => insertion_at::<_, _, 15>($v, $cmp),
            16 if $n >= 16 => insertion_at::<_, _, 16>($v, $cmp),
            17 if $n >= 17 => insertion_at::<_, _, 17>($v, $cmp),
            18 if $n >= 18 => insertion_at::<_, _, 18>($v, $cmp),
            19 if $n >= 19 => insertion_at::<_, _, 19>($v, $cmp),
            20 if $n >= 20 => insertion_at::<_, _, 20>($v, $cmp),
            _ => {}
        }
    };
}

fn insertion_safety_fixed<const N: usize>() {
    let mut v: [u64; N] = kani::any();
    let offset: usize = kani::any_where(|&o| 1 <= o && o <= N);
    insertion_at_any_offset!(&mut v, offset, N, &mut volatile_reading_less_u64);
    kani::cover(offset == 1, "insertion at offset one returns normally");
    kani::cover(offset == N, "insertion at final offset returns normally");
}

// The unwind budget covers insertion loops at the largest selected length.
macro_rules! insertion_safety_cases {
    ($name:ident, [$($n:literal),+]) => {
        #[kani::proof]
        #[kani::unwind(25)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            match len {
                $($n => insertion_safety_fixed::<$n>(),)+
                _ => {}
            }
            $(kani::cover(
                len == $n,
                concat!("insertion returns normally at length ", stringify!($n))
            );)+
            kani::cover(true, "insertion safety family reached the end");
        }
    };
}

insertion_safety_cases!(insertion_safety_u64_n1_to5, [1, 2, 3, 4, 5]);
insertion_safety_cases!(insertion_safety_u64_n6_to10, [6, 7, 8, 9, 10]);

// Mutating comparisons overwrite both keys in tagged `Cell` values. These exact-length route and
// insertion harnesses check memory safety and normal return without assuming a sorted prefix.
fn mutating_key_order(a: &TaggedKeyCell, b: &TaggedKeyCell) -> bool {
    // SAFETY: both initialized Cell payloads must be readable before either write.
    let (left, right) =
        unsafe { (crate::ptr::read_volatile(a.as_ptr()), crate::ptr::read_volatile(b.as_ptr())) };
    let left_key: u8 = kani::any();
    let right_key: u8 = kani::any();
    a.set(TaggedKey { key: left_key, tag: left.tag });
    b.set(TaggedKey { key: right_key, tag: right.tag });
    kani::cover(
        left_key != left.key && right_key != right.key,
        "mutating comparator changes both keys",
    );
    kani::any()
}

fn tagged_values<const N: usize>() -> [TaggedKeyCell; N] {
    crate::array::from_fn(|_| TaggedKeyCell::new(TaggedKey { key: kani::any(), tag: kani::any() }))
}

fn mutating_route_fixed<const N: usize>(stable: bool) {
    use super::super::{StableSmallSortTypeImpl, UnstableSmallSortTypeImpl};
    let mut v = tagged_values::<N>();
    if stable {
        let mut scratch = [];
        <TaggedKeyCell as StableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut scratch,
            &mut mutating_key_order,
        );
    } else {
        <TaggedKeyCell as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut mutating_key_order);
    }
}

// The mutating-comparator budget includes route loops and tagged-value construction.
macro_rules! mutating_route_cases {
    ($name:ident, [$($n:literal),+]) => {
        #[kani::proof]
        #[kani::unwind(35)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            let stable: bool = kani::any();
            match len {
                $($n => mutating_route_fixed::<$n>(stable),)+
                _ => {}
            }
            $(
                kani::cover(
                    stable && len == $n,
                    concat!("stable mutating route returns normally at ", stringify!($n))
                );
                kani::cover(
                    !stable && len == $n,
                    concat!("unstable mutating route returns normally at ", stringify!($n))
                );
            )+
            kani::cover(true, "mutating route family reached the end");
        }
    };
}

fn mutating_insertion_fixed<const N: usize>() {
    let mut v = tagged_values::<N>();
    let offset: usize = kani::any_where(|&o| 1 <= o && o <= N);
    insertion_at_any_offset!(&mut v, offset, N, &mut mutating_key_order);
    kani::cover(offset == 1, "mutating insertion at offset one returns normally");
    kani::cover(offset == N, "mutating insertion at final offset returns normally");
}

macro_rules! mutating_insertion_cases {
    ($name:ident, [$($n:literal),+]) => {
        #[kani::proof]
        #[kani::unwind(35)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            match len {
                $($n => mutating_insertion_fixed::<$n>(),)+
                _ => {}
            }
            $(kani::cover(
                len == $n,
                concat!("mutating insertion returns normally at ", stringify!($n))
            );)+
            kani::cover(true, "mutating insertion family reached the end");
        }
    };
}

mutating_route_cases!(mutating_route_safety_cell_n0_to4, [0, 1, 2, 3, 4]);
mutating_route_cases!(mutating_route_safety_cell_n5_to8, [5, 6, 7, 8]);
mutating_route_cases!(mutating_route_safety_cell_n9_to12, [9, 10, 11, 12]);
mutating_route_cases!(mutating_route_safety_cell_n13_to16, [13, 14, 15, 16]);
mutating_insertion_cases!(mutating_insertion_safety_cell_n1_to5, [1, 2, 3, 4, 5]);

insertion_safety_cases!(insertion_safety_u64_n11_to12, [11, 12]);

insertion_safety_cases!(insertion_safety_u64_n13, [13]);
insertion_safety_cases!(insertion_safety_u64_n14, [14]);

// The u64 groups partition all valid offsets for each exact length 15..=20; the Cell groups do so
// for length 20. Each listed offset becomes a constant call-site value; comparisons are
// unconstrained and no sorted-prefix contract is assumed.
macro_rules! insertion_offset_group_u64_case {
    ($plain:ident, $n:literal, [$($o:literal),+]) => {
        #[kani::proof]
        #[kani::unwind(25)]
        fn $plain() {
            const { $(assert!($o >= 1 && $o <= $n);)+ };
            let mut v: [u64; $n] = kani::any();
            let offset: usize = kani::any_where(|&o| matches!(o, $($o)|+));
            match offset {
                $($o => insertion_at::<_, _, $o>(&mut v, &mut volatile_reading_less_u64),)+
                _ => unreachable!(),
            }
            $(kani::cover(offset == $o, concat!("insertion offset ", stringify!($o)));)+
            kani::cover(true, "insertion offset group returns normally");
        }
    };
}

macro_rules! insertion_offset_group_cell_case {
    ($cell:ident, $n:literal, [$($o:literal),+]) => {
        #[kani::proof]
        #[kani::unwind(35)]
        fn $cell() {
            const { $(assert!($o >= 1 && $o <= $n);)+ };
            let mut v = tagged_values::<$n>();
            let offset: usize = kani::any_where(|&o| matches!(o, $($o)|+));
            match offset {
                $($o => insertion_at::<_, _, $o>(&mut v, &mut mutating_key_order),)+
                _ => unreachable!(),
            }
            $(kani::cover(offset == $o, concat!("mutating insertion offset ", stringify!($o)));)+
            kani::cover(true, "mutating insertion offset group returns normally");
        }
    };
}

insertion_offset_group_u64_case!(insertion_safety_u64_n15_offsets1_to4, 15, [1, 2, 3, 4]);
insertion_offset_group_u64_case!(insertion_safety_u64_n15_offsets5_to8, 15, [5, 6, 7, 8]);
insertion_offset_group_u64_case!(insertion_safety_u64_n15_offsets9_to12, 15, [9, 10, 11, 12]);
insertion_offset_group_u64_case!(insertion_safety_u64_n15_offsets13_to15, 15, [13, 14, 15]);
insertion_offset_group_u64_case!(insertion_safety_u64_n16_offsets1_to4, 16, [1, 2, 3, 4]);
insertion_offset_group_u64_case!(insertion_safety_u64_n16_offsets5_to8, 16, [5, 6, 7, 8]);
insertion_offset_group_u64_case!(insertion_safety_u64_n16_offsets9_to12, 16, [9, 10, 11, 12]);
insertion_offset_group_u64_case!(insertion_safety_u64_n16_offsets13_to16, 16, [13, 14, 15, 16]);
insertion_offset_group_u64_case!(insertion_safety_u64_n17_offsets1_to4, 17, [1, 2, 3, 4]);
insertion_offset_group_u64_case!(insertion_safety_u64_n17_offsets5_to8, 17, [5, 6, 7, 8]);
insertion_offset_group_u64_case!(insertion_safety_u64_n17_offsets9_to12, 17, [9, 10, 11, 12]);
insertion_offset_group_u64_case!(insertion_safety_u64_n17_offsets13_to15, 17, [13, 14, 15]);
insertion_offset_group_u64_case!(insertion_safety_u64_n17_offsets16_to17, 17, [16, 17]);
insertion_offset_group_u64_case!(insertion_safety_u64_n18_offsets1_to4, 18, [1, 2, 3, 4]);
insertion_offset_group_u64_case!(insertion_safety_u64_n18_offsets5_to8, 18, [5, 6, 7, 8]);
insertion_offset_group_u64_case!(insertion_safety_u64_n18_offsets9_to12, 18, [9, 10, 11, 12]);
insertion_offset_group_u64_case!(insertion_safety_u64_n18_offsets13_to16, 18, [13, 14, 15, 16]);
insertion_offset_group_u64_case!(insertion_safety_u64_n18_offsets17_to18, 18, [17, 18]);
insertion_offset_group_u64_case!(insertion_safety_u64_n19_offsets1_to4, 19, [1, 2, 3, 4]);
insertion_offset_group_u64_case!(insertion_safety_u64_n19_offsets5_to8, 19, [5, 6, 7, 8]);
insertion_offset_group_u64_case!(insertion_safety_u64_n19_offsets9_to12, 19, [9, 10, 11, 12]);
insertion_offset_group_u64_case!(insertion_safety_u64_n19_offsets13_to16, 19, [13, 14, 15, 16]);
insertion_offset_group_u64_case!(insertion_safety_u64_n19_offsets17_to19, 19, [17, 18, 19]);
insertion_offset_group_u64_case!(insertion_safety_u64_n20_offsets1_to4, 20, [1, 2, 3, 4]);
insertion_offset_group_cell_case!(
    mutating_insertion_safety_cell_n20_offsets1_to4,
    20,
    [1, 2, 3, 4]
);
insertion_offset_group_u64_case!(insertion_safety_u64_n20_offsets5_to8, 20, [5, 6, 7, 8]);
insertion_offset_group_cell_case!(
    mutating_insertion_safety_cell_n20_offsets5_to8,
    20,
    [5, 6, 7, 8]
);
insertion_offset_group_u64_case!(insertion_safety_u64_n20_offsets9_to12, 20, [9, 10, 11, 12]);
insertion_offset_group_cell_case!(
    mutating_insertion_safety_cell_n20_offsets9_to12,
    20,
    [9, 10, 11, 12]
);
insertion_offset_group_u64_case!(insertion_safety_u64_n20_offsets13_to16, 20, [13, 14, 15, 16]);
insertion_offset_group_cell_case!(
    mutating_insertion_safety_cell_n20_offsets13_to16,
    20,
    [13, 14, 15, 16]
);
insertion_offset_group_u64_case!(insertion_safety_u64_n20_offsets17_to20, 20, [17, 18, 19, 20]);
insertion_offset_group_cell_case!(
    mutating_insertion_safety_cell_n20_offsets17_to20,
    20,
    [17, 18, 19, 20]
);

// Full-width `u8` and `u64` arrays enter through the unstable trait with a strict total order.
// The checks assert sortedness; only N < 9 also checks full-route probe counts.
fn strict_less<T: Ord>(a: &T, b: &T) -> bool {
    a < b
}

fn network_correctness_fixed<T: kani::Arbitrary + Copy + Ord, const N: usize>() {
    use super::super::UnstableSmallSortTypeImpl;
    let mut v: [T; N] = kani::any();
    let pre = v;
    let probe: T = kani::any();
    let mut cmp = strict_less::<T>;
    <T as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut cmp);
    assert!(is_sorted_by(&v, &mut cmp));
    // Below the network width, keep the direct full-route permutation proof.
    // At N >= 9 this harness checks only order. Separate harnesses check permutation of
    // the insertion suffix; this harness does not assert full-route permutation.
    if N < 9 {
        assert!(count_matching_values(&pre, &probe) == count_matching_values(&v, &probe));
    }
    kani::cover(N < 2 || !prefix_unchanged(&v, &pre, 0), "trivial input or sort moves elements");
}

// The unwind budget includes sortedness and full-value count loops as well as sorting.
macro_rules! network_correctness_cases {
    ($name:ident, $t:ty, [$($n:literal),+]) => {
        #[kani::proof]
        #[kani::unwind(25)]
        fn $name() {
            let len: usize = kani::any_where(|&l| matches!(l, $($n)|+));
            match len {
                $($n => network_correctness_fixed::<$t, $n>(),)+
                _ => {}
            }
            $(kani::cover(len == $n, concat!("sort returns normally at length ", stringify!($n)));)+
            kani::cover(true, "sort family reached the end");
        }
    };
}

network_correctness_cases!(network_correctness_u8_n0_to2, u8, [0, 1, 2]);
network_correctness_cases!(network_correctness_u64_n0_to2, u64, [0, 1, 2]);
network_correctness_cases!(network_correctness_u8_n3_to4, u8, [3, 4]);
network_correctness_cases!(network_correctness_u64_n3_to4, u64, [3, 4]);

network_correctness_cases!(network_correctness_u8_n5, u8, [5]);
network_correctness_cases!(network_correctness_u64_n5, u64, [5]);
network_correctness_cases!(network_correctness_u8_n6, u8, [6]);
network_correctness_cases!(network_correctness_u64_n6, u64, [6]);

network_correctness_cases!(network_correctness_u8_n7, u8, [7]);
network_correctness_cases!(network_correctness_u64_n7, u64, [7]);

impl ArbitraryValue for u64 {
    fn arbitrary_value() -> Self {
        kani::any()
    }
}

fn drop_value_less(a: &DropValue, b: &DropValue) -> bool {
    a.0 < b.0
}
fn cell_value_less(a: &crate::cell::Cell<i32>, b: &crate::cell::Cell<i32>) -> bool {
    a.get() < b.get()
}
fn array_key_less<const M: usize>(a: &[u8; M], b: &[u8; M]) -> bool {
    // All instantiated arrays have M > 0; the remaining bytes are full-width payload.
    a[0] < b[0]
}

// Profile tags for the comparators owned by this module. Each model is the full logical value:
// the whole scalar or byte array, `Cell::get()`, and the whole DropValue payload. The private
// DropValue profile stays with its owner type.
identity_profile!(
    /// `u8` with `strict_less::<u8>`, the full order.
    StrictU8,
    u8,
    PROFILE_PROBE_STRICT_U8,
    0,
    strict_less::<u8>,
    strict_less::<u8>
);
identity_profile!(
    /// `u64` with `strict_less::<u64>`, the full order.
    StrictU64,
    u64,
    PROFILE_PROBE_STRICT_U64,
    0,
    strict_less::<u64>,
    strict_less::<u64>
);
identity_profile!(
    /// `[u8; 16]` with `array_key_less::<16>`: key byte 0, the other bytes are payload.
    KeyB16,
    [u8; 16],
    PROFILE_PROBE_KEY_B16,
    [0; 16],
    array_key_less::<16>,
    array_key_less::<16>
);
identity_profile!(
    /// `[u8; 17]` with `array_key_less::<17>`: key byte 0, the other bytes are payload.
    KeyB17,
    [u8; 17],
    PROFILE_PROBE_KEY_B17,
    [0; 17],
    array_key_less::<17>,
    array_key_less::<17>
);

static mut PROFILE_PROBE_CELL_I32: i32 = 0;

/// `Cell<i32>` with `cell_value_less`; the model is `get()`, the comparator only reads.
pub(crate) struct CellI32;

impl Profile for CellI32 {
    type Elem = crate::cell::Cell<i32>;
    type Model = i32;
    const CMP: fn(&Self::Elem, &Self::Elem) -> bool = cell_value_less;
    fn model(x: &crate::cell::Cell<i32>) -> i32 {
        x.get()
    }
    fn model_less(a: &i32, b: &i32) -> bool {
        *a < *b
    }
    fn probe() -> i32 {
        // SAFETY: single-threaded harness; no reference to the static is alive.
        unsafe { *crate::ptr::addr_of!(PROFILE_PROBE_CELL_I32) }
    }
    fn set_probe(m: i32) {
        // SAFETY: single-threaded harness; no reference to the static is alive.
        unsafe { *crate::ptr::addr_of_mut!(PROFILE_PROBE_CELL_I32) = m }
    }
}

static mut PROFILE_PROBE_DROP_U8: u8 = 0;

/// `DropValue` with `drop_value_less`; the model is the whole u8 payload. Snapshots copy the
/// payload model only, so no destructor runs in a specification. Private like its element type.
struct DropU8;

impl Profile for DropU8 {
    type Elem = DropValue;
    type Model = u8;
    const CMP: fn(&DropValue, &DropValue) -> bool = drop_value_less;
    fn model(x: &DropValue) -> u8 {
        x.0
    }
    fn model_less(a: &u8, b: &u8) -> bool {
        *a < *b
    }
    fn probe() -> u8 {
        // SAFETY: single-threaded harness; no reference to the static is alive.
        unsafe { *crate::ptr::addr_of!(PROFILE_PROBE_DROP_U8) }
    }
    fn set_probe(m: u8) {
        // SAFETY: single-threaded harness; no reference to the static is alive.
        unsafe { *crate::ptr::addr_of_mut!(PROFILE_PROBE_DROP_U8) = m }
    }
}

fn swap_contract_fixed<P: Profile>()
where
    P::Elem: ArbitraryValue,
{
    let mut v: [P::Elem; 2] =
        crate::array::from_fn(|_| <P::Elem as ArbitraryValue>::arbitrary_value());
    let reverse: bool = kani::any();
    let (a, b) = if reverse { (1, 0) } else { (0, 1) };
    let taken = (P::CMP)(&v[b], &v[a]);
    // SAFETY: a and b are distinct initialized writable elements of the live exact array.
    unsafe {
        swap_profile::<P>(v.as_mut_ptr(), a, b, P::CMP);
    }
    kani::cover(reverse, "swap contract covers indices 1 and 0");
    kani::cover(!reverse, "swap contract covers indices 0 and 1");
    kani::cover(size_of::<P::Elem>() == 0 || taken, "swap branch or zero-sized value");
    kani::cover(!taken, "no-swap branch");
    kani::cover(true, "swap contract reached the end");
}

// This conservative unwind budget includes byte-array models as well as scalar elements.
// It does not express a bound on the two-element allocation.
macro_rules! swap_contract_exact_array_case {
    ($name:ident, $tag:ty) => {
        #[kani::proof_for_contract(super::merge::profiles::swap_profile)]
        #[kani::unwind(180)]
        fn $name() {
            swap_contract_fixed::<$tag>();
        }
    };
}

swap_contract_exact_array_case!(swap_contract_u8_n2, StrictU8);
swap_contract_exact_array_case!(swap_contract_u64_n2, StrictU64);
swap_contract_exact_array_case!(swap_contract_drop_u8_n2, DropU8);
swap_contract_exact_array_case!(swap_contract_cell_i32_n2, CellI32);
swap_contract_exact_array_case!(swap_contract_bytes16_n2, KeyB16);
swap_contract_exact_array_case!(swap_contract_bytes17_n2, KeyB17);

network_correctness_cases!(network_correctness_u8_n9, u8, [9]);
network_correctness_cases!(network_correctness_u64_n9, u64, [9]);
network_correctness_cases!(network_correctness_u8_n10, u8, [10]);

/// Full-value permutation of the real insertion suffix, independent of ordering. An arbitrary
/// read-only comparison result includes every sequence produced by the pure strict comparator.
/// No sorted-prefix assumption: all possible network outputs are included in this larger domain.
fn insertion_permutation_fixed<T: kani::Arbitrary + Copy + Eq, const N: usize>() {
    let mut v: [T; N] = kani::any();
    let pre = v;
    let probe: T = kani::any();
    if N >= 13 {
        super::super::insertion_sort_shift_left(&mut v, 13, &mut volatile_reading_less::<T>);
    } else {
        super::super::insertion_sort_shift_left(&mut v, 9, &mut volatile_reading_less::<T>);
    }
    assert!(count_matching_values(&pre, &probe) == count_matching_values(&v, &probe));
    kani::cover(
        !prefix_unchanged(&v, &pre, 0),
        "insertion preserves permutation and moves elements",
    );
}

// The insertion unwind budget also covers the probe-count loops over the full array.
macro_rules! insertion_permutation_case {
    ($name:ident, $t:ty, $n:literal) => {
        #[kani::proof]
        #[kani::unwind(25)]
        fn $name() {
            insertion_permutation_fixed::<$t, $n>();
            kani::cover(true, "insertion permutation check reached the end");
        }
    };
}

insertion_permutation_case!(insertion_permutation_u8_n10, u8, 10);
insertion_permutation_case!(insertion_permutation_u64_n10, u64, 10);

network_correctness_cases!(network_correctness_u8_n11, u8, [11]);
insertion_permutation_case!(insertion_permutation_u8_n11, u8, 11);

network_correctness_cases!(network_correctness_u8_n12, u8, [12]);

network_correctness_cases!(network_correctness_u8_n13, u8, [13]);

insertion_permutation_case!(insertion_permutation_u8_n14, u8, 14);
insertion_permutation_case!(insertion_permutation_u64_n14, u64, 14);

// The profile uses the network correctness order; the unwind budget includes the frame loop.
fn swap_contract_indices<P: Profile, const N: usize>()
where
    P::Elem: kani::Arbitrary + Copy + PartialEq,
{
    const { assert!(N >= 9 && N <= 17) };
    let mut v: [P::Elem; N] = kani::any();
    let pre = v;
    let a: usize = kani::any_where(|&i| i < N);
    let b: usize = kani::any_where(|&i| i < N && i != a);
    let taken = (P::CMP)(&v[b], &v[a]);
    // SAFETY: a and b are distinct in-bounds initialized writable elements of v.
    unsafe {
        swap_profile::<P>(v.as_mut_ptr(), a, b, P::CMP);
    }
    let mut i = 0;
    while i < N {
        if i != a && i != b {
            assert!(v[i] == pre[i], "swap contract covers other cells unchanged");
        }
        i += 1;
    }
    kani::cover(a == 0 && b == N - 1, "swap contract covers first to last");
    kani::cover(a == N - 1 && b == 0, "swap contract covers last to first");
    kani::cover(a > 0 && a < N - 1 && b > 0 && b < N - 1, "swap contract covers interior pair");
    let network_last = if N >= 13 { 12 } else { 8 };
    kani::cover(
        a == network_last || b == network_last,
        "swap contract covers network final position",
    );
    kani::cover(taken, "swap contract covers swap branch");
    kani::cover(!taken, "swap contract covers no-swap branch");
    kani::cover(true, "swap contract covers end reached");
}

macro_rules! swap_contract_arbitrary_indices_case {
    ($name:ident, $tag:ty, $n:literal) => {
        #[kani::proof_for_contract(super::merge::profiles::swap_profile)]
        #[kani::unwind(25)]
        fn $name() {
            swap_contract_indices::<$tag, $n>();
        }
    };
}

swap_contract_arbitrary_indices_case!(swap_contract_u8_indices_n17, StrictU8, 17);
swap_contract_arbitrary_indices_case!(swap_contract_u64_indices_n17, StrictU64, 17);
swap_contract_arbitrary_indices_case!(swap_contract_u8_n9, StrictU8, 9);
swap_contract_arbitrary_indices_case!(swap_contract_u8_n13, StrictU8, 13);
swap_contract_arbitrary_indices_case!(swap_contract_u64_n9, StrictU64, 9);

// Fix the region's start at index 1 to check both an untouched prefix and a suffix.
// The tail intervals cover indices 2 through 16; the profile supplies the sorted prefix.
fn insert_tail_start1_frame(v: &[u64; 17], pre: &[u64; 17], tail: usize) {
    assert!(v[0] == pre[0], "insert-tail contract covers prefix before begin unchanged");
    assert!(prefix_unchanged(v, pre, tail + 1), "suffix after inserted tail remains unchanged");
}

fn insert_tail_group_value<const LO: usize, const HI: usize>() -> usize {
    const {
        assert!(1 < LO && LO <= HI && HI < 17);
    };
    LtU64::set_probe(kani::any());
    let mut v: [u64; 17] = kani::any();
    let tail: usize = kani::any_where(|&t| LO <= t && t <= HI);
    let pre = v;
    let base = v.as_mut_ptr();
    // SAFETY: 1 < LO <= tail <= HI < 17; the enclosing proof_for_contract
    // assumes precisely the profile requires, including the model-sorted prefix.
    unsafe {
        insert_tail_profile::<LtU64>(base.add(1), base.add(tail), LtU64::CMP);
    }
    insert_tail_start1_frame(&v, &pre, tail);
    kani::cover(!prefix_unchanged(&v, &pre, 0), "insertion moves elements");
    kani::cover(true, "insert-tail contract covers end reached");
    tail
}

// The unwind budget accommodates the farthest tail and both frame-check loops.
macro_rules! insert_tail_start1_group_case {
    ($name:ident, $lo:literal, $hi:literal, [$($end:literal),+]) => {
        #[kani::proof_for_contract(super::merge::profiles::insert_tail_profile)]
        #[kani::unwind(25)]
        fn $name() {
            let tail = insert_tail_group_value::<$lo, $hi>();
            $(kani::cover(
                tail == $end,
                concat!(
                    "insert-tail contract covers tail ",
                    stringify!($end),
                    " with requires satisfied"
                )
            );)+
        }
    };
}

insert_tail_start1_group_case!(
    insert_tail_contract_u64_start1_tail2_to8,
    2,
    8,
    [2, 3, 4, 5, 6, 7, 8]
);

insert_tail_start1_group_case!(insert_tail_contract_u64_start1_tail9_to12, 9, 12, [9, 10, 11, 12]);

insert_tail_start1_group_case!(insert_tail_contract_u64_start1_tail13_to14, 13, 14, [13, 14]);

insert_tail_start1_group_case!(insert_tail_contract_u64_start1_tail15_to16, 15, 16, [15, 16]);

// The symbolic tail includes a full prefix; solver choice is specific to this model.
#[kani::proof_for_contract(super::merge::profiles::insert_tail_profile)]
#[kani::solver(cadical)]
#[kani::unwind(18)]
fn contract_insert_tail_u8_prefix() {
    LtU8::set_probe(kani::any());
    let mut input: [u8; 17] = kani::any();
    let tail: usize = kani::any_where(|t: &usize| 1 <= *t && *t < 17);
    let before = input;
    let base = input.as_mut_ptr();
    // SAFETY: valid same-allocation region. proof_for_contract supplies the model-sorted
    // prefix requires of the profile; the suffix is outside the modifies region.
    unsafe {
        insert_tail_profile::<LtU8>(base, base.add(tail), LtU8::CMP);
    }
    for i in tail + 1..17 {
        assert!(input[i] == before[i]);
    }
    kani::cover(tail == 1, "u8 prefix: region 2 reachable");
    kani::cover(tail == 15, "u8 prefix: proper prefix region 16 reachable");
    kani::cover(tail == 16, "u8 prefix: full region 17 reachable");
    kani::cover(true, "u8 prefix: completion");
}

// At lengths 2 through 4, checks tag multiplicities after stable, unstable, or insertion routes
// whose comparator may rewrite keys. No ordering precondition is assumed.
fn mutating_route_permutation<const N: usize>() -> (u8, usize) {
    use super::super::{StableSmallSortTypeImpl, UnstableSmallSortTypeImpl};
    let mut v = tagged_values::<N>();
    let probe: u8 = kani::any();
    let before = count_tagged_values(&v, probe);
    let tags = tag_sequence(&v);
    let mode: u8 = kani::any_where(|&m| m < 3);
    let offset: usize = kani::any_where(|&o| 1 <= o && o <= N);
    if mode == 0 {
        let mut scratch = [];
        <TaggedKeyCell as StableSmallSortTypeImpl>::small_sort(
            &mut v,
            &mut scratch,
            &mut mutating_key_order,
        );
    } else if mode == 1 {
        <TaggedKeyCell as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut mutating_key_order);
    } else {
        insertion_at_any_offset!(&mut v, offset, N, &mut mutating_key_order);
    }
    assert!(before == count_tagged_values(&v, probe), "tag multiplicity is preserved");
    let moved = tags != tag_sequence(&v);
    kani::cover(mode == 0 && moved, "stable route moves a tag");
    kani::cover(mode == 1 && moved, "unstable route moves a tag");
    kani::cover(mode == 2 && moved, "insertion route moves a tag");
    kani::cover(true, "tag permutation check reached the end");
    (mode, offset)
}

// The unwind budget includes tag extraction and counts after each selected route.
macro_rules! mutating_route_permutation_case {
    ($name:ident, $n:literal, [$($offset:literal),+]) => {
        #[kani::proof]
        #[kani::unwind(25)]
        fn $name() {
            let (mode, offset) = mutating_route_permutation::<$n>();
            $(kani::cover(
                mode == 2 && offset == $offset,
                concat!("insertion route returns normally at offset ", stringify!($offset))
            );)+
        }
    };
}

mutating_route_permutation_case!(mutating_route_permutation_cell_n2, 2, [1, 2]);
mutating_route_permutation_case!(mutating_route_permutation_cell_n3, 3, [1, 2, 3]);
mutating_route_permutation_case!(mutating_route_permutation_cell_n4, 4, [1, 2, 3, 4]);
