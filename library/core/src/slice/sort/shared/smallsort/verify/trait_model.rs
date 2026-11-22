//! Verification-only sort model, specialized by element and comparator type.
//! Snapshot callers supply an initialized readable slice region, never scratch storage.

use crate::cell::Cell;

pub(super) type U64Cmp = fn(&u64, &u64) -> bool;
pub(super) type CellCmp = fn(&Cell<u8>, &Cell<u8>) -> bool;
pub(super) type NonCopyCmp = fn(&NonCopyKey, &NonCopyKey) -> bool;

/// A one-byte Freeze key with neither Copy nor a custom Drop.
#[repr(transparent)]
pub(super) struct NonCopyKey(pub(super) u8);

pub(super) fn canonical_less_u64(a: &u64, b: &u64) -> bool {
    a < b
}

pub(super) fn canonical_less_cell(a: &Cell<u8>, b: &Cell<u8>) -> bool {
    a.get() < b.get()
}

pub(super) fn canonical_less_noncopy(a: &NonCopyKey, b: &NonCopyKey) -> bool {
    a.0 < b.0
}

#[derive(Clone, Copy)]
pub(in super::super) enum SortEntry {
    Stable,
    Unstable,
    Freeze,
}

#[derive(Clone, Copy)]
pub(in super::super) struct SortSnapshot {
    len: usize,
    valid: bool,
    vals: [u64; 3],
}

impl SortSnapshot {
    fn invalid(len: usize) -> Self {
        Self { len, valid: false, vals: [0; 3] }
    }

    fn byte_pair(a: u8, b: u8) -> Self {
        Self { len: 2, valid: true, vals: [u64::from(a), u64::from(b), 0] }
    }
}

pub(in super::super) trait SortModel<T, F> {
    fn enabled(entry: SortEntry, cmp: &F, len: usize) -> bool;
    fn snapshot(base: *const T, len: usize) -> SortSnapshot;
    fn sort_postcondition(pre: SortSnapshot, base: *const T, len: usize) -> bool;
}

impl<T, F> SortModel<T, F> for () {
    default fn enabled(_entry: SortEntry, _cmp: &F, _len: usize) -> bool {
        false
    }

    default fn snapshot(_base: *const T, _len: usize) -> SortSnapshot {
        SortSnapshot::invalid(0)
    }

    default fn sort_postcondition(_pre: SortSnapshot, _base: *const T, _len: usize) -> bool {
        true
    }
}

fn snapshot_count(snapshot: SortSnapshot, value: u64) -> usize {
    let mut result = 0;
    let mut i = 0;
    while i < snapshot.len {
        result += usize::from(snapshot.vals[i] == value);
        i += 1;
    }
    result
}

fn sorted_permutation(pre: SortSnapshot, post: SortSnapshot) -> bool {
    if !pre.valid || !post.valid || pre.len != post.len || pre.len > 3 || pre.len < 2 {
        return false;
    }
    if !(post.vals[0] <= post.vals[1] && (post.len == 2 || post.vals[1] <= post.vals[2])) {
        return false;
    }
    if pre.len == 2 {
        return (post.vals[0] == pre.vals[0] && post.vals[1] == pre.vals[1])
            || (post.vals[0] == pre.vals[1] && post.vals[1] == pre.vals[0]);
    }
    let mut i = 0;
    while i < pre.len {
        if snapshot_count(pre, pre.vals[i]) != snapshot_count(post, pre.vals[i]) {
            return false;
        }
        i += 1;
    }
    true
}

impl SortModel<u64, U64Cmp> for () {
    fn enabled(entry: SortEntry, cmp: &U64Cmp, len: usize) -> bool {
        let supported = match entry {
            SortEntry::Stable => len == 2 || len == 3,
            SortEntry::Unstable => len == 2 || len == 3,
            SortEntry::Freeze => len == 2 || len == 3,
        };
        supported && *cmp as *const () == canonical_less_u64 as *const ()
    }

    fn snapshot(base: *const u64, len: usize) -> SortSnapshot {
        let mut result = SortSnapshot::invalid(len);
        if len != 2 && len != 3 {
            return result;
        }
        result.valid = true;
        let mut i = 0;
        while i < len {
            // SAFETY: callers provide len initialized readable u64s in the active slice.
            result.vals[i] = unsafe { *base.add(i) };
            i += 1;
        }
        result
    }

    fn sort_postcondition(pre: SortSnapshot, base: *const u64, len: usize) -> bool {
        sorted_permutation(pre, <() as SortModel<u64, U64Cmp>>::snapshot(base, len))
    }
}

impl SortModel<Cell<u8>, CellCmp> for () {
    fn enabled(entry: SortEntry, cmp: &CellCmp, len: usize) -> bool {
        matches!(entry, SortEntry::Stable | SortEntry::Unstable)
            && len == 2
            && *cmp as *const () == canonical_less_cell as *const ()
    }

    fn snapshot(base: *const Cell<u8>, len: usize) -> SortSnapshot {
        if len != 2 {
            return SortSnapshot::invalid(len);
        }
        // SAFETY: the active slice contains two initialized cells. get reads their values.
        let (a, b) = unsafe { ((*base).get(), (*base.add(1)).get()) };
        SortSnapshot::byte_pair(a, b)
    }

    fn sort_postcondition(pre: SortSnapshot, base: *const Cell<u8>, len: usize) -> bool {
        sorted_permutation(pre, <() as SortModel<Cell<u8>, CellCmp>>::snapshot(base, len))
    }
}

impl SortModel<NonCopyKey, NonCopyCmp> for () {
    fn enabled(entry: SortEntry, cmp: &NonCopyCmp, len: usize) -> bool {
        matches!(entry, SortEntry::Freeze)
            && len == 2
            && *cmp as *const () == canonical_less_noncopy as *const ()
    }

    fn snapshot(base: *const NonCopyKey, len: usize) -> SortSnapshot {
        if len != 2 {
            return SortSnapshot::invalid(len);
        }
        // SAFETY: the active slice contains two initialized keys. Read only the byte fields.
        let (a, b) = unsafe { ((*base).0, (*base.add(1)).0) };
        SortSnapshot::byte_pair(a, b)
    }

    fn sort_postcondition(pre: SortSnapshot, base: *const NonCopyKey, len: usize) -> bool {
        sorted_permutation(pre, <() as SortModel<NonCopyKey, NonCopyCmp>>::snapshot(base, len))
    }
}
