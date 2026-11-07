//! Ordered profiles for the real swap, sort4, tail-insertion, and merge helpers.
//! Each tag fixes an element type, a canonical comparator, and a pure full-value model.
//! Specifications use that model without calling the comparator. Forwarders reject any other
//! comparator value before assuming an ordered summary; the helpers' frame contracts alone
//! do not promise an order. Equal keys may have different full values.
//!
//! `kani::assert` preserves literal descriptions here; core `assert!` reports a shared
//! placeholder on the pinned Kani.

use super::{lt_u8, lt_u64, regions_are_disjoint};
#[cfg(kani_smallsort_controls)]
use crate::mem::MaybeUninit;
use crate::mem::size_of;
use crate::slice::sort::shared::FreezeMarker;
use crate::slice::sort::shared::smallsort::{
    bidirectional_merge, insert_tail, sort4_stable, swap_if_less,
};
use crate::ub_checks::{can_dereference, can_write, same_allocation};
use crate::{kani, ptr};

/// Closed verification profile. Each implementation is audited: `CMP(a, b)` computes
/// `model_less(&model(a), &model(b))`, at most with additional volatile reads of both arguments;
/// `model` is the full logical value and has no side effects; the probe is one model value shared
/// by a composition. This is not a blanket lawful-order or purity claim about any other `FnMut`.
pub(crate) trait Profile {
    type Elem;
    type Model: Copy + PartialEq;
    const CMP: fn(&Self::Elem, &Self::Elem) -> bool;
    fn model(x: &Self::Elem) -> Self::Model;
    fn model_less(a: &Self::Model, b: &Self::Model) -> bool;
    fn probe() -> Self::Model;
    fn set_probe(m: Self::Model);
}

/// Tag whose model is the whole value; `$less` is the pure order and `$cmp` is `$less`, possibly
/// with volatile reads. Callers import `Profile`.
macro_rules! identity_profile {
    ($(#[$doc:meta])* $tag:ident, $t:ty, $probe:ident, $zero:expr, $cmp:expr, $less:expr) => {
        $(#[$doc])*
        pub(crate) struct $tag;

        static mut $probe: $t = $zero;

        impl Profile for $tag {
            type Elem = $t;
            type Model = $t;
            const CMP: fn(&$t, &$t) -> bool = $cmp;
            fn model(x: &$t) -> $t {
                *x
            }
            fn model_less(a: &$t, b: &$t) -> bool {
                $less(a, b)
            }
            fn probe() -> $t {
                // SAFETY: single-threaded harness; no reference to the static is alive.
                unsafe { *$crate::ptr::addr_of!($probe) }
            }
            fn set_probe(m: $t) {
                // SAFETY: single-threaded harness; no reference to the static is alive.
                unsafe { *$crate::ptr::addr_of_mut!($probe) = m }
            }
        }
    };
}
pub(crate) use identity_profile;

/// The sort4 fixture order: both arguments are read volatile, then `lt_u64`.
pub(crate) fn sort4_read_lt_u64(a: &u64, b: &u64) -> bool {
    super::read_sort4_arguments(a, b);
    lt_u64(a, b)
}

/// The sort4 fixture order on 16-byte arrays: volatile reads, then `lt_b16` (first byte).
pub(crate) fn sort4_read_lt_b16(a: &[u8; 16], b: &[u8; 16]) -> bool {
    super::read_sort4_arguments(a, b);
    super::lt_b16(a, b)
}

identity_profile!(
    /// `u8` with `lt_u8`, key `x >> 1`.
    LtU8,
    u8,
    PROFILE_PROBE_LT_U8,
    0,
    lt_u8,
    lt_u8
);
identity_profile!(
    /// `i32` with `lt_i32`, key `x >> 1`.
    LtI32,
    i32,
    PROFILE_PROBE_LT_I32,
    0,
    super::lt_i32,
    super::lt_i32
);
identity_profile!(
    /// `u64` with `lt_u64`, key `x >> 1`.
    LtU64,
    u64,
    PROFILE_PROBE_LT_U64,
    0,
    lt_u64,
    lt_u64
);
identity_profile!(
    /// `u64` with the reading sort4 fixture over `lt_u64`.
    Sort4ReadU64,
    u64,
    PROFILE_PROBE_SORT4_U64,
    0,
    sort4_read_lt_u64,
    lt_u64
);
identity_profile!(
    /// `[u8; 16]` with the reading sort4 fixture over `lt_b16`.
    Sort4ReadB16,
    [u8; 16],
    PROFILE_PROBE_SORT4_B16,
    [0; 16],
    sort4_read_lt_b16,
    super::lt_b16
);

/// The canonical guard: only the profile's audited function value is accepted. This is the
/// address comparison `ptr::fn_addr_eq` performs, written as a direct cast for the pinned model.
pub(crate) fn profile_canonical_comparator<P: Profile>(
    cmp: fn(&P::Elem, &P::Elem) -> bool,
) -> bool {
    cmp as *const () == P::CMP as *const ()
}

/// No adjacent strict model inversion in `base[..len]`; loop-free for `len <= 32`.
pub(crate) fn model_sorted<P: Profile>(base: *const P::Elem, len: usize) -> bool {
    let mut ok = true;
    macro_rules! step {
        ($($i:literal)*) => {$(
            // SAFETY: `$i < len`; callers pass a readable initialized region of `len` elements.
            if $i < len
                && unsafe {
                    P::model_less(&P::model(&*base.add($i)), &P::model(&*base.add($i - 1)))
                }
            {
                ok = false;
            }
        )*};
    }
    step!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);
    ok
}

/// Number of full models equal to the shared probe in `base[..len]`; loop-free for `len <= 32`.
pub(crate) fn model_count<P: Profile>(base: *const P::Elem, len: usize) -> usize {
    let mut c = 0;
    let probe = P::probe();
    macro_rules! step {
        ($($i:literal)*) => {$(
            // SAFETY: `$i < len`; callers pass a readable initialized region of `len` elements.
            if $i < len && unsafe { P::model(&*base.add($i)) } == probe {
                c += 1;
            }
        )*};
    }
    step!(
        0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
    );
    c
}

// swap_if_less profile: one comparator decision, made from pure pre-state models.

pub(crate) fn swap_geometry<T>(v: *mut T, a: usize, b: usize) -> bool {
    a != b
        && same_allocation(v as *const T, v.wrapping_add(a) as *const T)
        && same_allocation(v as *const T, v.wrapping_add(b) as *const T)
        && can_dereference(v.wrapping_add(a) as *const T)
        && can_dereference(v.wrapping_add(b) as *const T)
        && can_write(v.wrapping_add(a))
        && can_write(v.wrapping_add(b))
}

pub(crate) fn pair_models<P: Profile>(
    v: *const P::Elem,
    a: usize,
    b: usize,
) -> (P::Model, P::Model) {
    // SAFETY: fixture values are initialized; the requires check both positions' geometry.
    unsafe { (P::model(&*v.add(a)), P::model(&*v.add(b))) }
}

/// Conditional transfer by the pure pre-key comparison; the other branch keeps both values.
pub(crate) fn swap_transfer<P: Profile>(
    pre: (P::Model, P::Model),
    v: *const P::Elem,
    a: usize,
    b: usize,
) -> bool {
    let (now_a, now_b) = pair_models::<P>(v, a, b);
    if P::model_less(&pre.1, &pre.0) {
        now_a == pre.1 && now_b == pre.0
    } else {
        now_a == pre.0 && now_b == pre.1
    }
}

pub(crate) fn swap_ordered<P: Profile>(v: *const P::Elem, a: usize, b: usize) -> bool {
    let (now_a, now_b) = pair_models::<P>(v, a, b);
    !P::model_less(&now_b, &now_a)
}

#[kani::requires(swap_geometry::<P::Elem>(v, a, b))]
#[kani::requires(profile_canonical_comparator::<P>(cmp))]
#[kani::modifies(v.wrapping_add(a), v.wrapping_add(b))]
#[kani::ensures(|_| swap_transfer::<P>(old(pair_models::<P>(v, a, b)), v, a, b))]
#[kani::ensures(|_| swap_ordered::<P>(v, a, b))]
pub(crate) unsafe fn swap_profile<P: Profile>(
    v: *mut P::Elem,
    a: usize,
    b: usize,
    cmp: fn(&P::Elem, &P::Elem) -> bool,
) {
    let mut is_less = cmp;
    // SAFETY: initialized exclusive fixture storage; requires check geometry and `P::CMP`.
    unsafe { swap_if_less(v, a, b, &mut is_less) }
}

// sort4_stable profile: source and destination geometry; fixtures initialize the source.

pub(crate) fn sort4_regions<T>(src: *const T, dst: *mut T) -> bool {
    size_of::<T>() > 0
        && can_dereference(ptr::slice_from_raw_parts(src, 4))
        && can_write(ptr::slice_from_raw_parts_mut(dst, 4))
        && regions_are_disjoint::<T>(src, 4, dst as *const T, 4)
}

#[kani::requires(sort4_regions::<P::Elem>(src, dst))]
#[kani::requires(profile_canonical_comparator::<P>(cmp))]
#[kani::modifies(ptr::slice_from_raw_parts_mut(dst, 4))]
#[kani::ensures(|_| model_sorted::<P>(dst, 4))]
#[kani::ensures(|_| model_count::<P>(src, 4) == model_count::<P>(dst, 4))]
pub(crate) unsafe fn sort4_profile<P: Profile>(
    src: *const P::Elem,
    dst: *mut P::Elem,
    cmp: fn(&P::Elem, &P::Elem) -> bool,
) {
    let mut is_less = cmp;
    // SAFETY: fixtures initialize src and own dst; requires check both spans and disjointness.
    unsafe { sort4_stable(src, dst, &mut is_less) }
}

// insert_tail profile: full-span geometry and bounds before the distance or typed reads;
// fixtures initialize the elements; the sorted prefix is a pure model premise.

pub(crate) fn tail_len<T>(begin: *const T, tail: *const T) -> usize {
    // SAFETY: evaluated only after `tail_region` established one allocation and both bounds.
    (unsafe { tail.offset_from(begin) }) as usize + 1
}

pub(crate) fn tail_region<T>(begin: *mut T, tail: *mut T) -> bool {
    size_of::<T>() > 0
        && same_allocation(begin as *const T, tail as *const T)
        && can_dereference(begin as *const T)
        && can_dereference(tail as *const T)
        && {
            // SAFETY: nonzero size, one allocation, both pointers in bounds (checked above).
            let d = unsafe { tail.offset_from(begin) };
            1 <= d && d < 32
        }
        && can_dereference(ptr::slice_from_raw_parts(begin as *const T, tail_len::<T>(begin, tail)))
        && can_write(ptr::slice_from_raw_parts_mut(begin, tail_len::<T>(begin, tail)))
}

#[kani::requires(profile_canonical_comparator::<P>(cmp))]
#[kani::requires(
    tail_region::<P::Elem>(begin, tail)
        && model_sorted::<P>(begin, tail_len::<P::Elem>(begin, tail) - 1)
)]
#[kani::modifies(ptr::slice_from_raw_parts_mut(begin, tail_len::<P::Elem>(begin, tail)))]
#[kani::ensures(|_| model_sorted::<P>(begin, tail_len::<P::Elem>(begin, tail)))]
#[kani::ensures(|_|
    old(model_count::<P>(begin, tail_len::<P::Elem>(begin, tail)))
        == model_count::<P>(begin, tail_len::<P::Elem>(begin, tail))
)]
pub(crate) unsafe fn insert_tail_profile<P: Profile>(
    begin: *mut P::Elem,
    tail: *mut P::Elem,
    cmp: fn(&P::Elem, &P::Elem) -> bool,
) {
    let mut is_less = cmp;
    // SAFETY: initialized exclusive fixture storage; requires check geometry and sorted prefix.
    unsafe { insert_tail(begin, tail, &mut is_less) }
}

// bidirectional_merge profile: N in 2..=32 before any half or pointer computation.

pub(crate) fn merge_regions<T>(v: &[T], dst: *mut T) -> bool {
    size_of::<T>() > 0
        && v.len() >= 2
        && v.len() <= 32
        && can_dereference(v as *const [T])
        && can_write(ptr::slice_from_raw_parts_mut(dst, v.len()))
        && regions_are_disjoint::<T>(v.as_ptr(), v.len(), dst as *const T, v.len())
}

pub(crate) fn merge_halves_sorted<P: Profile>(v: &[P::Elem]) -> bool {
    let half = v.len() / 2;
    model_sorted::<P>(v.as_ptr(), half)
        && model_sorted::<P>(v.as_ptr().wrapping_add(half), v.len() - half)
}

#[kani::requires(profile_canonical_comparator::<P>(cmp))]
#[kani::requires(merge_regions::<P::Elem>(v, dst) && merge_halves_sorted::<P>(v))]
#[kani::modifies(ptr::slice_from_raw_parts_mut(dst, v.len()))]
#[kani::ensures(|_| model_sorted::<P>(dst, v.len()))]
#[kani::ensures(|_| model_count::<P>(v.as_ptr(), v.len()) == model_count::<P>(dst, v.len()))]
pub(crate) unsafe fn merge_profile<P: Profile>(
    v: &[P::Elem],
    dst: *mut P::Elem,
    cmp: fn(&P::Elem, &P::Elem) -> bool,
) where
    P::Elem: FreezeMarker,
{
    let mut is_less = cmp;
    // SAFETY: fixtures initialize v and own dst; requires check destination geometry and lengths.
    unsafe { bidirectional_merge(v, dst, &mut is_less) }
}

// Opt-in negative controls; the profile contract proofs are in `network` and `merge`. Each control
// expects exactly the named check to fail.

/// Real sort4 with the canonical comparator, then one payload bit flip that keeps the key.
#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::unwind(6)]
fn profile_full_value_checker_rejects_payload_change_u8() {
    LtU8::set_probe(kani::any());
    let src: [u8; 4] = kani::any();
    let mut dst = [0u8; 4];
    let mut cmp = LtU8::CMP;
    // SAFETY: separate initialized four-element arrays.
    unsafe { sort4_stable(src.as_ptr(), dst.as_mut_ptr(), &mut cmp) };
    kani::cover(true, "payload corruption reached");
    dst[1] ^= 1;
    let keys = model_sorted::<LtU8>(dst.as_ptr(), 4);
    kani::assert(keys, "corrupted payload keeps key order");
    let same = model_count::<LtU8>(src.as_ptr(), 4) == model_count::<LtU8>(dst.as_ptr(), 4);
    kani::assert(same, "full-value checker detects payload corruption");
}

// Wrong-F controls, one per profile family: a consumer of the verified profile summary passes an
// always-true function value. Every other requires holds, so exactly the canonical guard must
// fail at the call, before the ordered ensures are assumed.

#[cfg(kani_smallsort_controls)]
fn always_true_u8(_: &u8, _: &u8) -> bool {
    true
}

#[cfg(kani_smallsort_controls)]
fn always_true_u64(_: &u64, _: &u64) -> bool {
    true
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::stub_verified(swap_profile)]
fn profile_wrong_f_swap_rejected_u8() {
    let mut v: [u8; 2] = kani::any();
    kani::cover(true, "wrong-F swap call reached");
    // SAFETY: distinct in-bounds initialized positions; only the comparator guard is violated.
    unsafe { swap_profile::<LtU8>(v.as_mut_ptr(), 0, 1, always_true_u8) };
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::stub_verified(sort4_profile)]
fn profile_wrong_f_sort4_rejected_u64() {
    let src: [u64; 4] = kani::any();
    let mut dst = MaybeUninit::<[u64; 4]>::uninit();
    kani::cover(true, "wrong-F sort4 call reached");
    // SAFETY: initialized source, separate destination of four; only the guard is violated.
    unsafe {
        sort4_profile::<Sort4ReadU64>(src.as_ptr(), dst.as_mut_ptr() as *mut u64, always_true_u64)
    };
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::stub_verified(insert_tail_profile)]
fn profile_wrong_f_insert_rejected_u8() {
    // Keys under `lt_u8` are [0, 2, 1]: the prefix [0, 2] is model-sorted.
    let mut v = [0u8, 4, 2];
    let base = v.as_mut_ptr();
    kani::cover(true, "wrong-F insert call reached");
    // SAFETY: one initialized writable array, begin < tail; only the guard is violated.
    unsafe { insert_tail_profile::<LtU8>(base, base.add(2), always_true_u8) };
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::stub_verified(merge_profile)]
fn profile_wrong_f_merge_rejected_u8() {
    // Keys under `lt_u8` are [0, 1 | 0, 1]: both halves are model-sorted.
    let v = [0u8, 2, 1, 3];
    let mut dst = MaybeUninit::<[u8; 4]>::uninit();
    kani::cover(true, "wrong-F merge call reached");
    // SAFETY: initialized source, separate destination of four; only the guard is violated.
    unsafe { merge_profile::<LtU8>(&v, dst.as_mut_ptr() as *mut u8, always_true_u8) };
}
