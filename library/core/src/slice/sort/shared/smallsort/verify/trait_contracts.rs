//! Checks the `small_sort` postconditions for `u64` at lengths 2 and 3, `Cell<u8>` at length 2,
//! and `NonCopyKey` at length 2. Negative controls are opt-in.

use super::super::{
    StableSmallSortTypeImpl, UnstableSmallSortFreezeTypeImpl, UnstableSmallSortTypeImpl,
};
use super::trait_model::{
    CellCmp, NonCopyCmp, NonCopyKey, SortEntry, SortModel, U64Cmp, canonical_less_cell,
    canonical_less_noncopy, canonical_less_u64,
};
use crate::cell::Cell;
use crate::kani;
use crate::mem::MaybeUninit;

fn sort_input_covers(ascending: bool, descending: bool, duplicate: bool) {
    kani::cover(ascending, "ascending input returns");
    kani::cover(descending, "descending input returns");
    kani::cover(duplicate, "duplicate input returns");
    kani::cover(true, "trait small_sort returns");
}

#[kani::proof_for_contract(<u64 as StableSmallSortTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn stable_sorts_permutation_u64_len2() {
    let mut v: [u64; 2] = kani::any();
    let ascending = v[0] < v[1];
    let descending = v[1] < v[0];
    let duplicate = v[0] == v[1];
    let mut cmp: U64Cmp = canonical_less_u64;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Stable, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    let mut scratch = [MaybeUninit::<u64>::uninit(); 18];
    <u64 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut cmp);
    sort_input_covers(ascending, descending, duplicate);
}

#[kani::proof_for_contract(<u64 as StableSmallSortTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn stable_sorts_permutation_u64_len3() {
    let mut v: [u64; 3] = kani::any();
    let ascending = v[0] < v[1] && v[1] < v[2];
    let descending = v[1] < v[0] && v[2] < v[1];
    let duplicate = v[0] == v[1] || v[0] == v[2] || v[1] == v[2];
    let mut cmp: U64Cmp = canonical_less_u64;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Stable, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    let mut scratch = [MaybeUninit::<u64>::uninit(); 19];
    <u64 as StableSmallSortTypeImpl>::small_sort(&mut v, &mut scratch, &mut cmp);
    sort_input_covers(ascending, descending, duplicate);
}

#[kani::proof_for_contract(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn freeze_sorts_permutation_u64_backing4() {
    let mut backing: [u64; 4] = kani::any();
    let outside = [backing[0], backing[3]];
    let v = &mut backing[1..3];
    let ascending = v[0] < v[1];
    let descending = v[1] < v[0];
    let duplicate = v[0] == v[1];
    let mut cmp: U64Cmp = canonical_less_u64;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Freeze, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    <u64 as UnstableSmallSortFreezeTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(backing[0] == outside[0] && backing[3] == outside[1], "outside slice unchanged");
    sort_input_covers(ascending, descending, duplicate);
}

#[kani::proof_for_contract(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn freeze_sorts_permutation_u64_backing5() {
    let mut backing: [u64; 5] = kani::any();
    let outside = [backing[0], backing[4]];
    let v = &mut backing[1..4];
    let ascending = v[0] < v[1] && v[1] < v[2];
    let descending = v[1] < v[0] && v[2] < v[1];
    let duplicate = v[0] == v[1] || v[0] == v[2] || v[1] == v[2];
    let mut cmp: U64Cmp = canonical_less_u64;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Freeze, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    <u64 as UnstableSmallSortFreezeTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(backing[0] == outside[0] && backing[4] == outside[1], "outside slice unchanged");
    sort_input_covers(ascending, descending, duplicate);
}

#[kani::proof_for_contract(<u64 as UnstableSmallSortTypeImpl>::small_sort)]
#[kani::stub_verified(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn unstable_sorts_permutation_u64_backing4() {
    let mut backing: [u64; 4] = kani::any();
    let outside = [backing[0], backing[3]];
    let v = &mut backing[1..3];
    let ascending = v[0] < v[1];
    let descending = v[1] < v[0];
    let duplicate = v[0] == v[1];
    let mut cmp: U64Cmp = canonical_less_u64;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Unstable, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    <u64 as UnstableSmallSortTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(backing[0] == outside[0] && backing[3] == outside[1], "outside slice unchanged");
    sort_input_covers(ascending, descending, duplicate);
}

#[kani::proof_for_contract(<u64 as UnstableSmallSortTypeImpl>::small_sort)]
#[kani::stub_verified(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn unstable_sorts_permutation_u64_backing5() {
    let mut backing: [u64; 5] = kani::any();
    let outside = [backing[0], backing[4]];
    let v = &mut backing[1..4];
    let ascending = v[0] < v[1] && v[1] < v[2];
    let descending = v[1] < v[0] && v[2] < v[1];
    let duplicate = v[0] == v[1] || v[0] == v[2] || v[1] == v[2];
    let mut cmp: U64Cmp = canonical_less_u64;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Unstable, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    <u64 as UnstableSmallSortTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(backing[0] == outside[0] && backing[4] == outside[1], "outside slice unchanged");
    sort_input_covers(ascending, descending, duplicate);
}

#[kani::proof]
#[kani::stub_verified(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn verified_forwarding_sorts_permutation_u64_backing5() {
    let mut backing: [u64; 5] = kani::any();
    let outside = [backing[0], backing[4]];
    let v = &mut backing[1..4];
    let pre = [v[0], v[1], v[2]];
    let ascending = v[0] < v[1] && v[1] < v[2];
    let descending = v[1] < v[0] && v[2] < v[1];
    let duplicate = v[0] == v[1] || v[0] == v[2] || v[1] == v[2];
    let mut cmp: U64Cmp = canonical_less_u64;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Unstable, &cmp, v.len())
        && <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Freeze, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    <u64 as UnstableSmallSortTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(v[0] <= v[1] && v[1] <= v[2], "forwarded output is sorted");
    let post = [v[0], v[1], v[2]];
    let mut i = 0;
    while i < 3 {
        let mut pre_count = 0;
        let mut post_count = 0;
        let mut j = 0;
        while j < 3 {
            pre_count += usize::from(pre[j] == pre[i]);
            post_count += usize::from(post[j] == pre[i]);
            j += 1;
        }
        kani::assert(pre_count == post_count, "forwarded output preserves full multiplicities");
        i += 1;
    }
    kani::assert(backing[0] == outside[0] && backing[4] == outside[1], "outside slice unchanged");
    sort_input_covers(ascending, descending, duplicate);
}

#[kani::proof_for_contract(<Cell<u8> as StableSmallSortTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn stable_default_sorts_permutation_cell_u8_backing4() {
    let [left, a, b, right]: [u8; 4] = kani::any();
    let mut backing = [Cell::new(left), Cell::new(a), Cell::new(b), Cell::new(right)];
    let sentinel: u8 = kani::any();
    let mut scratch = [MaybeUninit::new(Cell::new(sentinel)), MaybeUninit::uninit()];
    let mut cmp: CellCmp = canonical_less_cell;
    let v = &mut backing[1..3];
    let enabled = <() as SortModel<Cell<u8>, CellCmp>>::enabled(SortEntry::Stable, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    // Cell is !Freeze. The default Stable entry uses insertion and ignores caller scratch.
    <Cell<u8> as StableSmallSortTypeImpl>::small_sort(v, &mut scratch, &mut cmp);
    kani::assert(backing[0].get() == left && backing[3].get() == right, "outside slice unchanged");
    // SAFETY: only slot 0 was initialized and the default entry leaves scratch untouched.
    let after = unsafe { scratch[0].assume_init_ref() }.get();
    kani::assert(after == sentinel, "stable scratch sentinel unchanged");
    sort_input_covers(a < b, b < a, a == b);
}

#[kani::proof_for_contract(<Cell<u8> as UnstableSmallSortTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn unstable_default_sorts_permutation_cell_u8_backing4() {
    let [left, a, b, right]: [u8; 4] = kani::any();
    let mut backing = [Cell::new(left), Cell::new(a), Cell::new(b), Cell::new(right)];
    let mut cmp: CellCmp = canonical_less_cell;
    let v = &mut backing[1..3];
    let enabled = <() as SortModel<Cell<u8>, CellCmp>>::enabled(SortEntry::Unstable, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    // Cell is !Freeze. The default Unstable entry uses the insertion fallback.
    <Cell<u8> as UnstableSmallSortTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(backing[0].get() == left && backing[3].get() == right, "outside slice unchanged");
    sort_input_covers(a < b, b < a, a == b);
}

#[kani::proof_for_contract(<NonCopyKey as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn freeze_default_sorts_permutation_noncopy_u8_backing4() {
    let [left, a, b, right]: [u8; 4] = kani::any();
    let mut backing = [NonCopyKey(left), NonCopyKey(a), NonCopyKey(b), NonCopyKey(right)];
    let mut cmp: NonCopyCmp = canonical_less_noncopy;
    let v = &mut backing[1..3];
    let enabled =
        <() as SortModel<NonCopyKey, NonCopyCmp>>::enabled(SortEntry::Freeze, &cmp, v.len());
    kani::assert(enabled, "sort model enabled before call");
    kani::cover(enabled, "sort model enabled before call");
    // `NonCopyKey` is `Freeze` but not `Copy`, so this checks the default general sort with its
    // private 48-element scratch array.
    <NonCopyKey as UnstableSmallSortFreezeTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(backing[0].0 == left && backing[3].0 == right, "outside slice unchanged");
    sort_input_covers(a < b, b < a, a == b);
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::unwind(32)]
fn rejects_high_bit_corruption_u64_len3() {
    let mut v = [0u64, 1, 2];
    let pre = <() as SortModel<u64, U64Cmp>>::snapshot(v.as_ptr(), v.len());
    kani::assert(
        <() as SortModel<u64, U64Cmp>>::sort_postcondition(pre, v.as_ptr(), v.len()),
        "unchanged sorted snapshot passes checker",
    );
    v[2] |= 1u64 << 63;
    kani::cover(
        v[0] <= v[1] && v[1] <= v[2] && v[2] == (2 | (1u64 << 63)),
        "sorted high-bit corruption reached",
    );
    kani::assert(
        <() as SortModel<u64, U64Cmp>>::sort_postcondition(pre, v.as_ptr(), v.len()),
        "high-bit corruption preserves sorted full values",
    );
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::unwind(32)]
fn rejects_changed_multiplicities_u64_len3() {
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    kani::assume(a < b);
    let pre_values = [a, a, b];
    let pre = <() as SortModel<u64, U64Cmp>>::snapshot(pre_values.as_ptr(), 3);
    let post = [a, b, b];
    kani::cover(
        post[0] < post[1] && post[1] == post[2] && pre_values[1] != post[1],
        "sorted multiplicity corruption reached",
    );
    kani::assert(
        <() as SortModel<u64, U64Cmp>>::sort_postcondition(pre, post.as_ptr(), 3),
        "same set preserves full multiplicities",
    );
}

#[cfg(kani_smallsort_controls)]
fn reverse_less(a: &u64, b: &u64) -> bool {
    a > b
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::stub_verified(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn rejects_reverse_pointer_sorted_u64_backing5() {
    let mut backing: [u64; 5] = kani::any();
    let outside = [backing[0], backing[4]];
    let v = &mut backing[1..4];
    let mut cmp: U64Cmp = reverse_less;
    let enabled = <() as SortModel<u64, U64Cmp>>::enabled(SortEntry::Freeze, &cmp, v.len());
    kani::assert(!enabled, "reverse pointer disables sort model");
    <u64 as UnstableSmallSortTypeImpl>::small_sort(v, &mut cmp);
    let sorted = v[0] <= v[1] && v[1] <= v[2];
    kani::assert(backing[0] == outside[0] && backing[4] == outside[1], "outside slice unchanged");
    kani::cover(!enabled && !sorted, "guard-disabled reverse pointer can return unsorted");
    kani::assert(sorted, "reverse pointer output is sorted");
}

#[cfg(kani_smallsort_controls)]
fn trait_less_u64(a: &u64, b: &u64) -> bool {
    a < b
}

#[cfg(kani_smallsort_controls)]
fn trait_input_covers(input_descending: bool) {
    kani::cover(input_descending, "descending input returns");
    kani::cover(!input_descending, "non-descending input returns");
    kani::cover(true, "trait small_sort returns");
}

#[cfg(kani_smallsort_controls)]
fn function_item_model_enabled<F>(cmp: &F, len: usize) -> bool {
    <() as SortModel<u64, F>>::enabled(SortEntry::Freeze, cmp, len)
}

#[cfg(kani_smallsort_controls)]
#[kani::proof]
#[kani::stub_verified(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn rejects_function_item_sorted_u64_backing5() {
    let mut backing: [u64; 5] = kani::any();
    let outside = [backing[0], backing[4]];
    let v = &mut backing[1..4];
    let mut cmp = trait_less_u64;
    let enabled = function_item_model_enabled(&cmp, v.len());
    kani::assert(!enabled, "function item disables sort model");
    <u64 as UnstableSmallSortTypeImpl>::small_sort(v, &mut cmp);
    let sorted = v[0] <= v[1] && v[1] <= v[2];
    kani::assert(backing[0] == outside[0] && backing[4] == outside[1], "outside slice unchanged");
    kani::cover(!enabled && !sorted, "guard-disabled function item can return unsorted");
    kani::assert(sorted, "function item output is sorted");
}

#[cfg(kani_smallsort_controls)]
#[kani::proof_for_contract(<u64 as UnstableSmallSortFreezeTypeImpl>::small_sort)]
#[kani::unwind(32)]
fn freeze_frame_function_item_u64_backing5() {
    let mut backing: [u64; 5] = kani::any();
    let outside = [backing[0], backing[4]];
    let v = &mut backing[1..4];
    let input_descending = v[1] < v[0];
    let mut cmp = trait_less_u64;
    let enabled = function_item_model_enabled(&cmp, v.len());
    kani::assert(!enabled, "function item disables sort model");
    <u64 as UnstableSmallSortFreezeTypeImpl>::small_sort(v, &mut cmp);
    kani::assert(backing[0] == outside[0] && backing[4] == outside[1], "outside slice unchanged");
    trait_input_covers(input_descending);
}
