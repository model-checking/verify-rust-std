//! Merge, insertion-tail and stable-primitive checked-profile proofs and bounded callers.
//! Probe multiplicity represents full values only for types without padding; Drop uses tag counts.
//! Profile proofs (`profiles`) use typed full-value model counts; real-body callers use the probe.

pub(super) mod profiles;

use profiles::{LtU8, LtU64, Profile, Sort4ReadB16, Sort4ReadU64, merge_profile, sort4_profile};

use super::super::{
    SMALL_SORT_GENERAL_SCRATCH_LEN, StableSmallSortTypeImpl, UnstableSmallSortTypeImpl,
    sort4_stable,
};
use crate::mem::{MaybeUninit, size_of};
use crate::slice::sort::shared::FreezeMarker;
use crate::{kani, ptr};

const PROBE_BYTES: usize = 128;

#[repr(C, align(16))]
struct Probe([u8; PROBE_BYTES]);

static mut VALUE_PROBE_BYTES: Probe = Probe([0; PROBE_BYTES]);

pub(crate) fn set_value_probe<T>() {
    assert!(size_of::<T>() <= PROBE_BYTES);
    let bytes: [u8; PROBE_BYTES] = kani::any();
    // SAFETY: single-threaded harness; no reference to the static is alive.
    unsafe { *ptr::addr_of_mut!(VALUE_PROBE_BYTES) = Probe(bytes) };
}

/// `*p` is bytewise equal to the probe. `p` must be valid for reads of one initialized `T`.
/// Guarded word reads avoid nested specification loops during instrumentation.
/// Supported domain: `size_of::<T>() <= PROBE_BYTES`, checked here before the first read even
/// when `set_value_probe` was bypassed; a larger `T` is an explicit unsupported-domain failure.
#[inline(always)]
unsafe fn matches_value_probe<T>(p: *const T) -> bool {
    let a = p as *const u8;
    let n = size_of::<T>();
    kani::assert(n <= PROBE_BYTES, "value probe supports at most 128 bytes per value");
    if n > PROBE_BYTES {
        return false;
    }
    let w = n / 8;
    let mut eq = true;
    // SAFETY: `p` is readable for `n` bytes and `n <= PROBE_BYTES` was checked above; every read
    // below is guarded to lie in `0..n`.
    unsafe {
        let b = ptr::addr_of!(VALUE_PROBE_BYTES) as *const u8;
        macro_rules! words {
            ($($j:literal)*) => {$(
                if $j < w {
                    let x = ptr::read_unaligned(a.add(8 * $j) as *const u64);
                    let y = ptr::read_unaligned(b.add(8 * $j) as *const u64);
                    eq &= x == y;
                }
            )*};
        }
        words!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15);
        let mut i = 8 * w;
        if n - i >= 4 {
            eq &= ptr::read_unaligned(a.add(i) as *const u32)
                == ptr::read_unaligned(b.add(i) as *const u32);
            i += 4;
        }
        if n - i >= 2 {
            eq &= ptr::read_unaligned(a.add(i) as *const u16)
                == ptr::read_unaligned(b.add(i) as *const u16);
            i += 2;
        }
        if n - i >= 1 {
            eq &= *a.add(i) == *b.add(i);
        }
    }
    eq
}

pub(crate) fn probe_count<T>(base: *const T, len: usize) -> usize {
    let mut c = 0;
    let mut i = 0;
    while i < len {
        // SAFETY: callers pass a readable, initialized region of `len` elements.
        if unsafe { matches_value_probe(base.add(i)) } {
            c += 1;
        }
        i += 1;
    }
    c
}

/// Loop-free count for `len <= MAX_UNROLLED_ELEMENTS`, bounding specification instrumentation.
pub(crate) fn probe_count_unrolled<T>(base: *const T, len: usize) -> usize {
    let mut c = 0;
    macro_rules! step {
        ($($i:literal)*) => {$(
            // SAFETY: `$i < len`, callers pass a readable region of `len` elements.
            if $i < len && unsafe { matches_value_probe(base.add($i)) } {
                c += 1;
            }
        )*};
    }
    step!(
        0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
    );
    c
}

pub(crate) fn regions_are_disjoint<T>(a: *const T, n: usize, b: *const T, m: usize) -> bool {
    !kani::mem::same_allocation(a, b) || {
        // SAFETY: same allocation was checked just above.
        let d = unsafe { b.offset_from(a) };
        d >= n as isize || -d >= m as isize
    }
}
// Key orders admit equal keys with different full values; sortedness does not imply permutation.

pub(crate) fn lt_u8(a: &u8, b: &u8) -> bool {
    (*a >> 1) < (*b >> 1)
}

pub(crate) fn lt_i32(a: &i32, b: &i32) -> bool {
    (*a >> 1) < (*b >> 1)
}

pub(crate) fn lt_u64(a: &u64, b: &u64) -> bool {
    (*a >> 1) < (*b >> 1)
}

pub(crate) fn lt_b16(a: &[u8; 16], b: &[u8; 16]) -> bool {
    a[0] < b[0]
}

// Concrete lengths keep loop bounds constant; the shared unwind budget covers up to 32 elements.

/// Merge profile proof body: exact source `[P::Elem; N]`, disjoint uninitialized destination.
pub(crate) fn merge_length_body<P: Profile, const N: usize>()
where
    P::Elem: kani::Arbitrary + FreezeMarker,
    P::Model: kani::Arbitrary,
{
    P::set_probe(kani::any());
    let v: [P::Elem; N] = kani::any();
    let mut dst = MaybeUninit::<[P::Elem; N]>::uninit();
    // SAFETY: the profile contract is checked by the enclosing proof_for_contract harness.
    unsafe { merge_profile::<P>(&v, dst.as_mut_ptr() as *mut P::Elem, P::CMP) };
    kani::cover(true, "merge returns for a permitted length");
}

// Stable primitives: exact source and destination arrays, matching the composed caller types.

fn sort4_length_body<P: Profile>()
where
    P::Elem: kani::Arbitrary,
    P::Model: kani::Arbitrary,
{
    P::set_probe(kani::any());
    let v: [P::Elem; 4] = kani::any();
    let mut dst = MaybeUninit::<[P::Elem; 4]>::uninit();
    // SAFETY: the profile contract is checked by the enclosing proof_for_contract harness.
    unsafe { sort4_profile::<P>(v.as_ptr(), dst.as_mut_ptr() as *mut P::Elem, P::CMP) };
    kani::cover(true, "four-element stable sort returns");
}

// Separate sort4 checks: ordered profile contract with the reading fixture order (a checked
// profile tag), and real-body safety and permutation with arbitrary comparison results.
fn read_sort4_arguments<T: Copy>(a: &T, b: &T) {
    // SAFETY: both references must point to initialized readable elements.
    unsafe {
        ptr::read_volatile(a);
        ptr::read_volatile(b);
    }
}

fn sort4_arbitrary_comparator_body<T: kani::Arbitrary + Copy>() {
    set_value_probe::<T>();
    let v: [T; 4] = kani::any();
    let mut dst = MaybeUninit::<[T; 4]>::uninit();
    let mut cmp = |a: &T, b: &T| {
        read_sort4_arguments(a, b);
        kani::any()
    };
    // SAFETY: two disjoint exact four-element allocations, initialized source;
    // sort4_stable's SAFETY precondition does not require an ordered comparator.
    unsafe { sort4_stable(v.as_ptr(), dst.as_mut_ptr() as *mut T, &mut cmp) };
    assert!(probe_count::<T>(v.as_ptr(), 4) == probe_count::<T>(dst.as_ptr() as *const T, 4));
    kani::cover(true, "sort returns and preserves values with an arbitrary comparator");
}

macro_rules! define_sort4_contract_and_comparator_harnesses {
    ($contract:ident, $arbitrary:ident, $t:ty, $tag:ty) => {
        #[kani::proof_for_contract(profiles::sort4_profile)]
        #[kani::unwind(34)]
        fn $contract() {
            sort4_length_body::<$tag>();
        }

        #[kani::proof]
        #[kani::unwind(34)]
        fn $arbitrary() {
            sort4_arbitrary_comparator_body::<$t>();
        }
    };
}

define_sort4_contract_and_comparator_harnesses!(
    sort4_contract_u64_n4,
    sort4_arbitrary_comparator_u64_n4,
    u64,
    Sort4ReadU64
);
define_sort4_contract_and_comparator_harnesses!(
    sort4_contract_bytes16_n4,
    sort4_arbitrary_comparator_bytes16_n4,
    [u8; 16],
    Sort4ReadB16
);

// Real-body safety harnesses use no verified-contract stubs. The manual panic boundary cuts
// order-violation panic paths under abort semantics; it makes no claim about unwinding.

fn arbitrary_u64_order(a: &u64, b: &u64) -> bool {
    // SAFETY: initialized references; volatile reads retain both accesses.
    unsafe {
        ptr::read_volatile(a);
        ptr::read_volatile(b);
    }
    kani::any()
}

fn abort_on_order_violation() -> ! {
    kani::cover(true, "order violation panic path is reachable");
    kani::assume(false);
    unreachable!()
}

// u64 selects the network through the unstable trait. A transparent non-Copy wrapper also
// exercises the general trait route; stable Freeze sorting selects general directly for u64.
#[repr(transparent)]
struct WrappedU64(u64);

fn arbitrary_wrapped_u64_order(a: &WrappedU64, b: &WrappedU64) -> bool {
    // SAFETY: both initialized transparent payloads are readable; no Drop value is copied.
    unsafe {
        ptr::read_volatile(&a.0);
        ptr::read_volatile(&b.0);
    }
    kani::any()
}

fn unstable_general_u64_safety_body<const N: usize>() {
    let mut v: [u64; N] = kani::any();
    super::super::small_sort_general(&mut v, &mut arbitrary_u64_order);
    kani::cover(true, "general u64 safety: normal return reachable");
}

fn noncopy_general_u64_safety_body<const N: usize>() {
    let payload: [u64; N] = kani::any();
    let mut v = payload.map(WrappedU64);
    <WrappedU64 as UnstableSmallSortTypeImpl>::small_sort(&mut v, &mut arbitrary_wrapped_u64_order);
    kani::cover(true, "non-Copy u64 route safety: normal return reachable");
}

fn stable_general_u64_safety_body<const N: usize>() {
    let mut v: [u64; N] = kani::any();
    let mut scratch = [MaybeUninit::<u64>::uninit(); SMALL_SORT_GENERAL_SCRATCH_LEN];
    <u64 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut arbitrary_u64_order);
    kani::cover(true, "stable u64 route safety: normal return reachable");
}

// Every exact length 2..=32 selects direct general u64, non-Copy unstable general, or stable
// Freeze sorting. Each route has a normal-return cover and uses real callees with scratch 48.
fn all_upper_routes_safety_body<const N: usize>() {
    let route: u8 = kani::any();
    match route {
        0 => unstable_general_u64_safety_body::<N>(),
        1 => noncopy_general_u64_safety_body::<N>(),
        _ => stable_general_u64_safety_body::<N>(),
    }
}

macro_rules! define_route_safety_harness {
    ($name:ident, $body:ident, $n:literal) => {
        #[kani::proof]
        #[kani::stub(
            crate::slice::sort::shared::smallsort::panic_on_ord_violation,
            abort_on_order_violation
        )]
        #[kani::unwind(34)]
        fn $name() {
            $body::<$n>();
        }
    };
}

define_route_safety_harness!(route_safety_all_routes_n2, all_upper_routes_safety_body, 2);
define_route_safety_harness!(route_safety_all_routes_n3, all_upper_routes_safety_body, 3);
define_route_safety_harness!(route_safety_all_routes_n4, all_upper_routes_safety_body, 4);
define_route_safety_harness!(route_safety_all_routes_n5, all_upper_routes_safety_body, 5);
define_route_safety_harness!(route_safety_all_routes_n6, all_upper_routes_safety_body, 6);
define_route_safety_harness!(route_safety_all_routes_n7, all_upper_routes_safety_body, 7);
define_route_safety_harness!(route_safety_all_routes_n8, all_upper_routes_safety_body, 8);
define_route_safety_harness!(route_safety_all_routes_n16, all_upper_routes_safety_body, 16);

// Upper-bit key orders allow distinct full values to share a key.
macro_rules! define_small_merge_contract_harness {
    ($name:ident, $tag:ty) => {
        #[kani::proof_for_contract(profiles::merge_profile)]
        #[kani::unwind(34)]
        fn $name() {
            let len: u8 = kani::any_where(|n: &u8| *n >= 2 && *n <= 4);
            match len {
                2 => {
                    merge_length_body::<$tag, 2>();
                    kani::cover(true, "merge contract: length 2");
                }
                3 => {
                    merge_length_body::<$tag, 3>();
                    kani::cover(true, "merge contract: length 3");
                }
                4 => {
                    merge_length_body::<$tag, 4>();
                    kani::cover(true, "merge contract: length 4");
                }
                _ => {}
            }
        }
    };
}

define_small_merge_contract_harness!(merge_contract_u64_n2_to4, LtU64);
define_small_merge_contract_harness!(merge_contract_u8_n2_to4, LtU8);

macro_rules! define_merge_contract_harness {
    ($name:ident, $tag:ty, $n:literal) => {
        #[kani::proof_for_contract(profiles::merge_profile)]
        #[kani::unwind(34)]
        fn $name() {
            merge_length_body::<$tag, $n>();
        }
    };
}

fn assert_sorted_and_probe_preserved<T, F: FnMut(&T, &T) -> bool, const N: usize>(
    orig: &[T; N],
    out: &[T; N],
    cmp: &mut F,
) {
    for i in 1..N {
        assert!(!cmp(&out[i], &out[i - 1]), "output is sorted");
    }
    assert!(
        probe_count_unrolled::<T>(orig.as_ptr(), N) == probe_count_unrolled::<T>(out.as_ptr(), N),
        "input value counts are preserved"
    );
}

// General and stable routes share a full-value oracle independent of the comparison key.
fn general_route_properties<
    T: kani::Arbitrary + Copy + FreezeMarker,
    F: FnMut(&T, &T) -> bool,
    const N: usize,
>(
    mut cmp: F,
) {
    const { assert!(N <= 16) };
    set_value_probe::<T>();
    let mut v: [T; N] = kani::any();
    let orig = v;
    let stable: bool = kani::any();
    if stable {
        let mut scratch = [MaybeUninit::<T>::uninit(); SMALL_SORT_GENERAL_SCRATCH_LEN];
        <T as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut cmp);
    } else {
        super::super::small_sort_general(&mut v, &mut cmp);
    }
    assert_sorted_and_probe_preserved::<T, _, N>(&orig, &v, &mut cmp);
    kani::cover(!stable, "general route properties checked");
    kani::cover(stable, "stable route properties checked");
}

fn general_route_const_u64_properties<const N: usize>() {
    const { assert!(N <= 16) };
    set_value_probe::<u64>();
    let mut v: [u64; N] = kani::any();
    let orig = v;
    let mut cmp = lt_u64;
    let stable: bool = kani::any();
    if stable {
        let mut scratch = [const { MaybeUninit::<u64>::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        <u64 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut cmp);
    } else {
        super::super::small_sort_general(&mut v, &mut cmp);
    }
    assert_sorted_and_probe_preserved::<u64, _, N>(&orig, &v, &mut cmp);
    kani::cover(!stable, "general route properties checked");
    kani::cover(stable, "stable route properties checked");
}

// Fallback correctness uses real insertion bodies and checks both order and full values.
fn fallback_route_properties<
    T: kani::Arbitrary + Copy,
    F: FnMut(&T, &T) -> bool,
    const N: usize,
>(
    mut cmp: F,
) {
    const { assert!(N <= 16) };
    set_value_probe::<T>();
    let mut v: [T; N] = kani::any();
    let orig = v;
    super::super::small_sort_fallback(&mut v, &mut cmp);
    assert_sorted_and_probe_preserved::<T, _, N>(&orig, &v, &mut cmp);
    kani::cover(true, "fallback route properties checked");
}

// Empty and singleton inputs return before reaching a merge helper.
macro_rules! define_general_sortedness_harness {
    ($name:ident, $t:ty, $cmp:expr, $n:literal) => {
        #[kani::proof]
        #[kani::unwind(34)]
        fn $name() {
            general_route_properties::<$t, _, $n>($cmp);
        }
    };
}

macro_rules! define_direct_u64_route_harness {
    ($name:ident, $body:ident, $n:literal) => {
        #[kani::proof]
        #[kani::unwind(34)]
        fn $name() {
            $body::<$n>();
        }
    };
}

define_direct_u64_route_harness!(
    general_stable_direct_u64_n2,
    general_route_const_u64_properties,
    2
);

define_direct_u64_route_harness!(
    general_stable_direct_u64_n3,
    general_route_const_u64_properties,
    3
);

define_direct_u64_route_harness!(
    general_stable_direct_u64_n4,
    general_route_const_u64_properties,
    4
);

define_direct_u64_route_harness!(
    general_stable_direct_u64_n5,
    general_route_const_u64_properties,
    5
);

define_general_sortedness_harness!(general_stable_direct_u8_n2, u8, lt_u8, 2);
define_general_sortedness_harness!(general_stable_direct_u8_n3, u8, lt_u8, 3);
define_general_sortedness_harness!(general_stable_direct_u8_n4, u8, lt_u8, 4);
define_general_sortedness_harness!(general_stable_direct_u8_n5, u8, lt_u8, 5);
define_general_sortedness_harness!(general_stable_direct_u8_n6, u8, lt_u8, 6);
define_general_sortedness_harness!(general_stable_direct_u8_n7, u8, lt_u8, 7);
define_general_sortedness_harness!(general_stable_direct_u8_n8, u8, lt_u8, 8);

// Direct u64 routes use real merge bodies and the shared full-value oracle.
fn general_direct_u64_properties<const N: usize>() {
    const { assert!(N >= 6 && N <= 9) };
    set_value_probe::<u64>();
    let mut v: [u64; N] = kani::any();
    let orig = v;
    let mut cmp = lt_u64;
    super::super::small_sort_general(&mut v, &mut cmp);
    assert_sorted_and_probe_preserved::<u64, _, N>(&orig, &v, &mut cmp);
    kani::cover(true, "general direct split properties checked");
}

fn stable_direct_u64_properties<const N: usize>() {
    const { assert!(N >= 6 && N <= 9) };
    set_value_probe::<u64>();
    let mut v: [u64; N] = kani::any();
    let orig = v;
    let mut cmp = lt_u64;
    let mut scratch = [const { MaybeUninit::<u64>::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
    <u64 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut cmp);
    assert_sorted_and_probe_preserved::<u64, _, N>(&orig, &v, &mut cmp);
    kani::cover(true, "stable direct split properties checked");
}

define_direct_u64_route_harness!(general_direct_u64_n6, general_direct_u64_properties, 6);
define_direct_u64_route_harness!(general_direct_u64_n7, general_direct_u64_properties, 7);
define_direct_u64_route_harness!(general_direct_u64_n8, general_direct_u64_properties, 8);
define_direct_u64_route_harness!(stable_direct_u64_n6, stable_direct_u64_properties, 6);
define_direct_u64_route_harness!(stable_direct_u64_n7, stable_direct_u64_properties, 7);
define_direct_u64_route_harness!(stable_direct_u64_n8, stable_direct_u64_properties, 8);

define_direct_u64_route_harness!(general_direct_u64_n9, general_direct_u64_properties, 9);
define_direct_u64_route_harness!(stable_direct_u64_n9, stable_direct_u64_properties, 9);

// Match both callers' scratch allocations: only prefix N is initialized, dst is separate.
fn merge_scratch48_length_body<P: Profile, const N: usize>()
where
    P::Elem: kani::Arbitrary + Copy + FreezeMarker,
    P::Model: kani::Arbitrary,
{
    const { assert!(N >= 2 && N <= 32) };
    P::set_probe(kani::any());
    let input: [P::Elem; N] = kani::any();
    let mut dst: [P::Elem; N] = kani::any();
    let stable: bool = kani::any();
    let mut stable_scratch = [MaybeUninit::<P::Elem>::uninit(); SMALL_SORT_GENERAL_SCRATCH_LEN];
    let mut general_scratch = MaybeUninit::<[P::Elem; SMALL_SORT_GENERAL_SCRATCH_LEN]>::uninit();
    let src = if stable {
        stable_scratch.as_mut_ptr() as *mut P::Elem
    } else {
        general_scratch.as_mut_ptr() as *mut P::Elem
    };
    // SAFETY: prefix N fits either backing allocation; dst is initialized and disjoint; the
    // profile contract is checked by the enclosing proof_for_contract harness.
    unsafe {
        ptr::copy_nonoverlapping(input.as_ptr(), src, N);
        let v = crate::slice::from_raw_parts(src, N);
        merge_profile::<P>(v, dst.as_mut_ptr(), P::CMP);
    }
    kani::cover(!stable, "general scratch48 merge contract checked");
    kani::cover(stable, "stable scratch48 merge contract checked");
}

#[kani::proof_for_contract(profiles::merge_profile)]
#[kani::unwind(34)]
fn merge_scratch48_contract_u8_n9() {
    merge_scratch48_length_body::<LtU8, 9>();
}

macro_rules! define_fallback_property_harness {
    ($name:ident, $n:literal) => {
        #[kani::proof]
        #[kani::unwind(34)]
        fn $name() {
            if kani::any() {
                fallback_route_properties::<u64, _, $n>(lt_u64);
            } else {
                fallback_route_properties::<u8, _, $n>(lt_u8);
            }
        }
    };
}
define_merge_contract_harness!(merge_contract_u64_n5, LtU64, 5);
define_merge_contract_harness!(merge_contract_u8_n5, LtU8, 5);
define_merge_contract_harness!(merge_contract_u64_n6, LtU64, 6);
define_merge_contract_harness!(merge_contract_u8_n6, LtU8, 6);
define_merge_contract_harness!(merge_contract_u64_n7, LtU64, 7);
define_merge_contract_harness!(merge_contract_u8_n7, LtU8, 7);
define_merge_contract_harness!(merge_contract_u64_n8, LtU64, 8);
define_merge_contract_harness!(merge_contract_u8_n8, LtU8, 8);
define_merge_contract_harness!(merge_contract_u8_n9, LtU8, 9);
define_general_sortedness_harness!(general_stable_sorted_permutation_u64_n0, u64, lt_u64, 0);
define_general_sortedness_harness!(general_stable_sorted_permutation_u8_n0, u8, lt_u8, 0);
define_fallback_property_harness!(fallback_sorted_permutation_u8_u64_n0, 0);
define_general_sortedness_harness!(general_stable_sorted_permutation_u64_n1, u64, lt_u64, 1);
define_general_sortedness_harness!(general_stable_sorted_permutation_u8_n1, u8, lt_u8, 1);
define_fallback_property_harness!(fallback_sorted_permutation_u8_u64_n1, 1);
define_fallback_property_harness!(fallback_sorted_permutation_u8_u64_n2, 2);
define_fallback_property_harness!(fallback_sorted_permutation_u8_u64_n3, 3);
define_fallback_property_harness!(fallback_sorted_permutation_u8_u64_n4, 4);
define_fallback_property_harness!(fallback_sorted_permutation_u8_u64_n5, 5);
define_fallback_property_harness!(fallback_sorted_permutation_u8_u64_n6, 6);

// Drop values can have padding; test tag multiplicity rather than bytewise equality.
struct DropTaggedValue {
    key: u64,
    tag: u8,
}

static mut DROP_COUNT: usize = 0;

impl crate::ops::Drop for DropTaggedValue {
    fn drop(&mut self) {
        // SAFETY: single-threaded harness, no live references to the counter.
        unsafe {
            let count = ptr::read(ptr::addr_of!(DROP_COUNT));
            ptr::write(ptr::addr_of_mut!(DROP_COUNT), count + 1);
        }
    }
}

fn arbitrary_drop_value_order(a: &DropTaggedValue, b: &DropTaggedValue) -> bool {
    // SAFETY: both initialized fields are readable; no Drop value is copied.
    unsafe {
        ptr::read_volatile(&a.key);
        ptr::read_volatile(&a.tag);
        ptr::read_volatile(&b.key);
        ptr::read_volatile(&b.tag);
    }
    kani::any()
}

// Fallback and insertion routes do not merge, so their panic cut has no cover obligation.
// General and stable route controls use the covering panic stub above.
fn abort_without_order_cover() -> ! {
    kani::assume(false);
    unreachable!()
}

// Count destructors separately from tag multiplicities: either property alone can miss a bug.
// Normal return only; tag multiplicities and destructor counts are checked separately.
fn drop_route_properties<const N: usize, const UPPER: bool, const PERM: bool>() -> bool {
    const { assert!(N >= 2 && N <= 32) };
    // SAFETY: no prior array or counter reference survives into this harness.
    unsafe { ptr::write(ptr::addr_of_mut!(DROP_COUNT), 0) };
    let mut v: [DropTaggedValue; N] =
        crate::array::from_fn(|tag| DropTaggedValue { key: kani::any(), tag: tag as u8 });
    let probe: u8 = kani::any();
    let alternate: bool = kani::any();
    let mut cmp = arbitrary_drop_value_order;
    if UPPER {
        if alternate {
            let mut scratch = [const { MaybeUninit::<DropTaggedValue>::uninit() };
                SMALL_SORT_GENERAL_SCRATCH_LEN];
            <DropTaggedValue as StableSmallSortTypeImpl>::small_sort(
                &mut v,
                &mut scratch,
                &mut cmp,
            );
        } else {
            super::super::small_sort_general(&mut v, &mut cmp);
        }
    } else if alternate {
        super::super::insertion_sort_shift_left(&mut v, 1, &mut cmp);
    } else {
        super::super::small_sort_fallback(&mut v, &mut cmp);
    }
    if PERM {
        let mut count = 0usize;
        for value in &v {
            count += (value.tag == probe) as usize;
        }
        // Input tags are 0..N, each once; the arbitrary probe also covers absent tags.
        let expected = if (probe as usize) < N { 1 } else { 0 };
        assert!(count == expected);
    }
    crate::mem::drop(v);
    if !PERM {
        // SAFETY: single-threaded harness; the array was explicitly destroyed.
        let count = unsafe { ptr::read(ptr::addr_of!(DROP_COUNT)) };
        assert!(count == N);
    }
    alternate
}

macro_rules! define_drop_route_harness {
    ($name:ident, $n:literal, false, $perm:literal, $abort:ident) => {
        define_drop_route_harness!(@routes $name, $n, false, $perm, $abort,
            "fallback route returns with the property checked",
            "insertion route returns with the property checked");
    };
    ($name:ident, $n:literal, true, $perm:literal, $abort:ident) => {
        define_drop_route_harness!(@routes $name, $n, true, $perm, $abort,
            "general route returns with the property checked",
            "stable route returns with the property checked");
    };
    (@routes $name:ident, $n:literal, $upper:literal, $perm:literal,
        $abort:ident, $first:literal, $second:literal) => {
        #[kani::proof]
        #[kani::stub(crate::slice::sort::shared::smallsort::panic_on_ord_violation, $abort)]
        #[kani::unwind(34)]
        fn $name() {
            let alternate = drop_route_properties::<$n, $upper, $perm>();
            kani::cover(!alternate, $first);
            kani::cover(alternate, $second);
        }
    };
}

define_drop_route_harness!(drop_fallback_drop_count_n2, 2, false, false, abort_without_order_cover);
define_drop_route_harness!(
    drop_fallback_tag_permutation_n2,
    2,
    false,
    true,
    abort_without_order_cover
);
define_drop_route_harness!(drop_fallback_drop_count_n4, 4, false, false, abort_without_order_cover);
define_drop_route_harness!(
    drop_fallback_tag_permutation_n4,
    4,
    false,
    true,
    abort_without_order_cover
);
define_drop_route_harness!(drop_fallback_drop_count_n8, 8, false, false, abort_without_order_cover);
define_drop_route_harness!(
    drop_fallback_tag_permutation_n8,
    8,
    false,
    true,
    abort_without_order_cover
);
define_drop_route_harness!(drop_general_drop_count_n2, 2, true, false, abort_on_order_violation);
define_drop_route_harness!(
    drop_general_tag_permutation_n2,
    2,
    true,
    true,
    abort_on_order_violation
);
define_drop_route_harness!(drop_general_drop_count_n4, 4, true, false, abort_on_order_violation);
define_drop_route_harness!(
    drop_general_tag_permutation_n4,
    4,
    true,
    true,
    abort_on_order_violation
);
define_drop_route_harness!(drop_general_drop_count_n8, 8, true, false, abort_on_order_violation);
define_drop_route_harness!(
    drop_general_tag_permutation_n8,
    8,
    true,
    true,
    abort_on_order_violation
);
define_drop_route_harness!(drop_general_drop_count_n16, 16, true, false, abort_on_order_violation);

// Direct u8 N9 routes retain nonconst scratch and the shared full-value oracle.
fn general_direct_u8_n9_properties() {
    set_value_probe::<u8>();
    let mut v: [u8; 9] = kani::any();
    let orig = v;
    let mut cmp = lt_u8;
    super::super::small_sort_general(&mut v, &mut cmp);
    assert_sorted_and_probe_preserved::<u8, _, 9>(&orig, &v, &mut cmp);
    kani::cover(true, "general route properties checked");
}

fn stable_direct_nonconst_u8_n9_properties() {
    set_value_probe::<u8>();
    let mut v: [u8; 9] = kani::any();
    let orig = v;
    let mut cmp = lt_u8;
    let mut scratch = [MaybeUninit::<u8>::uninit(); SMALL_SORT_GENERAL_SCRATCH_LEN];
    <u8 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut cmp);
    assert_sorted_and_probe_preserved::<u8, _, 9>(&orig, &v, &mut cmp);
    kani::cover(true, "stable route properties checked");
}

macro_rules! define_direct_u8_n9_route_harness {
    ($name:ident, $body:ident) => {
        #[kani::proof]
        #[kani::unwind(34)]
        fn $name() {
            $body();
        }
    };
}

define_direct_u8_n9_route_harness!(general_direct_u8_n9, general_direct_u8_n9_properties);

define_direct_u8_n9_route_harness!(
    stable_direct_nonconst_u8_n9,
    stable_direct_nonconst_u8_n9_properties
);
