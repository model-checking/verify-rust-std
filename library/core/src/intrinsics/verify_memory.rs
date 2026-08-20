//! Challenge 2: safety contracts for raw-pointer `core::intrinsics`.
//!
//! Bodyless `#[rustc_intrinsic]` declarations cannot carry Kani contracts
//! (kani#3325 / kani#3345). Contracts therefore sit on thin wrappers that
//! immediately call the intrinsic — the same pattern as
//! `transmute_unchecked_wrapper` in `mod.rs`.
//!
//! Tractability bounds (buffer caps, representative overlap shifts) live in
//! harnesses via `kani::assume` / fixed constants, never in `#[requires]`.
//! `#[requires]` is only the documented safety condition.
//!
//! `kani::cover` after each successful call witnesses that the precondition
//! was satisfiable (an unreached harness is otherwise reported SUCCESSFUL).

use safety::{ensures, requires};

use super::*;
use crate::mem::{self, MaybeUninit, SizedTypeProperties};
use crate::ptr::{self, DynMetadata};
use crate::{kani, ub_checks};

/// Object-safe probe so vtable tests are not tied to `fmt::Debug` (or to one
/// erased type). An empty trait still has a vtable with drop/size/align.
trait Probe {}
impl<T> Probe for T {}

fn vtable_ptr(obj: *const dyn Probe) -> *const () {
    let meta = ptr::metadata(obj);
    // `DynMetadata` is ABI-equivalent to the vtable pointer
    // (`DynMetadata::vtable_ptr` is private and uses the same transmute).
    unsafe { mem::transmute::<DynMetadata<dyn Probe>, *const ()>(meta) }
}

fn copy_len_ok<T>(count: usize) -> bool {
    count.checked_mul(size_of::<T>()).is_some()
}

fn aligned_for_copy<T>(p: *const (), count: usize) -> bool {
    ub_checks::maybe_is_aligned_and_not_null(p, align_of::<T>(), T::IS_ZST || count == 0)
}

/// Untyped source: bytes may be uninitialized, so the region is `MaybeUninit<T>`.
fn src_readable<T>(src: *const T, count: usize) -> bool {
    copy_len_ok::<T>(count)
        && aligned_for_copy::<T>(src as *const (), count)
        && (count == 0
            || ub_checks::can_dereference(ptr::slice_from_raw_parts(
                src as *const MaybeUninit<T>,
                count,
            )))
}

fn dst_writable<T>(dst: *mut T, count: usize) -> bool {
    copy_len_ok::<T>(count)
        && aligned_for_copy::<T>(dst as *const (), count)
        && (count == 0 || ub_checks::can_write(ptr::slice_from_raw_parts_mut(dst, count)))
}

fn compare_bytes_ord(left: *const u8, right: *const u8, bytes: usize) -> crate::cmp::Ordering {
    let mut i = 0;
    while i < bytes {
        let a = unsafe { *left.add(i) };
        let b = unsafe { *right.add(i) };
        if a != b {
            return a.cmp(&b);
        }
        i += 1;
    }
    crate::cmp::Ordering::Equal
}

// ---------------------------------------------------------------------------
// typed_swap_nonoverlapping — already contracted on the intrinsic (has a body).
// Criterion 2: the fallback body is `ptr::swap_nonoverlapping(x, y, 1)`.
// ---------------------------------------------------------------------------

/// Verifies the fallback body of `typed_swap_nonoverlapping` against the same
/// documented safety condition. The intrinsic itself is already contracted in
/// `mod.rs`; this wrapper exists so the fallback is not only trusted via Kani's
/// built-in model of the intrinsic.
#[requires(ub_checks::can_dereference(x) && ub_checks::can_write(x))]
#[requires(ub_checks::can_dereference(y) && ub_checks::can_write(y))]
#[requires(x.addr() != y.addr() || size_of::<T>() == 0)]
#[requires(ub_checks::maybe_is_nonoverlapping(x as *const (), y as *const (), size_of::<T>(), 1))]
#[ensures(|_| ub_checks::can_dereference(x) && ub_checks::can_dereference(y))]
#[kani::modifies(x)]
#[kani::modifies(y)]
unsafe fn typed_swap_fallback_wrapper<T>(x: *mut T, y: *mut T) {
    // Same body as `typed_swap_nonoverlapping`'s fallback.
    unsafe { ptr::swap_nonoverlapping(x, y, 1) };
}

// ---------------------------------------------------------------------------
// vtable_size / vtable_align
//
// Documented safety: `ptr` must point to a vtable. Kani has no vtable
// predicate; dereferenceability of the first three `usize` words (drop, size,
// align — rustc `COMMON_VTABLE_ENTRIES`) is the necessary approximation.
// Sufficiency is assumed from compiler-produced vtables. Functional checks in
// the harnesses use `size_of::<T>()` / `align_of::<T>()` of the *erased* type,
// not a fixture hard-coded into `#[ensures]`.
// ---------------------------------------------------------------------------

#[requires(ub_checks::can_dereference(ptr as *const [usize; 3]))]
unsafe fn vtable_size_wrapper(ptr: *const ()) -> usize {
    unsafe { vtable_size(ptr) }
}

#[requires(ub_checks::can_dereference(ptr as *const [usize; 3]))]
unsafe fn vtable_align_wrapper(ptr: *const ()) -> usize {
    unsafe { vtable_align(ptr) }
}

// ---------------------------------------------------------------------------
// copy / copy_nonoverlapping / write_bytes
// ---------------------------------------------------------------------------

#[requires(src_readable(src, count) && dst_writable(dst, count))]
#[kani::modifies(ptr::slice_from_raw_parts(dst, count))]
unsafe fn copy_wrapper<T>(src: *const T, dst: *mut T, count: usize) {
    unsafe { copy(src, dst, count) }
}

#[requires(
    src_readable(src, count)
        && dst_writable(dst, count)
        && ub_checks::maybe_is_nonoverlapping(src as *const (), dst as *const (), size_of::<T>(), count)
)]
#[ensures(|_| check_copy_untyped(src, dst, count))]
#[kani::modifies(ptr::slice_from_raw_parts(dst, count))]
unsafe fn copy_nonoverlapping_wrapper<T>(src: *const T, dst: *mut T, count: usize) {
    unsafe { copy_nonoverlapping(src, dst, count) }
}

#[requires(dst_writable(dst, count))]
#[ensures(|_| {
    count == 0
        || ub_checks::can_dereference(ptr::slice_from_raw_parts(
            dst as *const u8,
            count * size_of::<T>(),
        ))
})]
#[kani::modifies(ptr::slice_from_raw_parts(dst, count))]
unsafe fn write_bytes_wrapper<T>(dst: *mut T, val: u8, count: usize) {
    unsafe { write_bytes(dst, val, count) }
}

// ---------------------------------------------------------------------------
// size_of_val / align_of_val  (min_align_of_val is the mem wrapper)
//
// Documented (`size_of_val_raw` / `align_of_val_raw`):
// - Sized: always safe, including null/dangling.
// - slice tail: length initialized, total size fits in `isize` (len 0 always ok).
// - trait object: vtable valid, total size fits in `isize`.
// `can_dereference` is stronger than the Sized case and is not used there.
// ---------------------------------------------------------------------------

#[ensures(|result| *result == size_of::<T>())]
unsafe fn size_of_val_sized_wrapper<T>(ptr: *const T) -> usize {
    unsafe { size_of_val(ptr) }
}

#[requires({
    let len = ptr.len();
    len == 0
        || size_of::<T>().checked_mul(len).is_some_and(|bytes| bytes <= isize::MAX as usize)
})]
#[ensures(|result| *result == ptr.len() * size_of::<T>())]
unsafe fn size_of_val_slice_wrapper<T>(ptr: *const [T]) -> usize {
    unsafe { size_of_val(ptr) }
}

#[requires(ub_checks::can_dereference(vtable_ptr(ptr) as *const [usize; 3]))]
unsafe fn size_of_val_dyn_wrapper(ptr: *const dyn Probe) -> usize {
    unsafe { size_of_val(ptr) }
}

#[ensures(|result| *result == align_of::<T>())]
unsafe fn align_of_val_sized_wrapper<T>(ptr: *const T) -> usize {
    unsafe { align_of_val(ptr) }
}

#[requires({
    let len = ptr.len();
    len == 0
        || size_of::<T>().checked_mul(len).is_some_and(|bytes| bytes <= isize::MAX as usize)
})]
#[ensures(|result| *result == align_of::<T>())]
unsafe fn align_of_val_slice_wrapper<T>(ptr: *const [T]) -> usize {
    unsafe { align_of_val(ptr) }
}

#[requires(ub_checks::can_dereference(vtable_ptr(ptr) as *const [usize; 3]))]
unsafe fn align_of_val_dyn_wrapper(ptr: *const dyn Probe) -> usize {
    unsafe { align_of_val(ptr) }
}

// ---------------------------------------------------------------------------
// arith_offset
//
// Documented: always safe; the result need not be dereferenceable and wraps
// in two's complement. There is no language offset bound.
//
// The wrapping-address `#[ensures]` is only CBMC-faithful while the result
// stays in a small in-object window (`offset ∈ [0, 8]` on a `[u8; 8]`).
// That window is a Kani/CBMC pointer-model bound, not a safety precondition
// (out-of-object `ptr as usize` is not integer wrapping in CBMC). Unbounded
// safety is the separate `#[kani::proof]` that calls `arith_offset` itself.
// ---------------------------------------------------------------------------

#[requires(offset >= 0 && offset <= 8)]
#[ensures(|result| {
    (*result as usize)
        == (dst as usize).wrapping_add((offset as usize).wrapping_mul(size_of::<T>()))
})]
unsafe fn arith_offset_wrapper<T>(dst: *const T, offset: isize) -> *const T {
    unsafe { arith_offset(dst, offset) }
}

// ---------------------------------------------------------------------------
// Volatile family
//
// `volatile_load` / `volatile_store` are modelled by pinned Kani. Their
// contracts cover the documented *Rust-allocation* case (`read_volatile` /
// `write_volatile`: valid, aligned, initialized). The documented MMIO case
// (aligned non-trapping access outside any Rust allocation) is an unverified
// residual: Kani has no model of I/O memory.
//
// `volatile_copy_*`, `volatile_set_memory`, `unaligned_volatile_{load,store}`
// are not codegen'd by pinned Kani (`d4df833`) — it emits "not currently
// supported". Volatility is a reordering/observability property; the
// memory-safety contract matches `copy` / `copy_nonoverlapping` /
// `write_bytes` / `read_unaligned` / `write_unaligned`. Wrappers implement
// those stores/loads so the safety contract is machine-checked. See the PR
// for the correspondence.
// ---------------------------------------------------------------------------

#[requires(ub_checks::can_dereference(src))]
unsafe fn volatile_load_wrapper<T>(src: *const T) -> T {
    unsafe { volatile_load(src) }
}

#[requires(ub_checks::can_write(dst))]
#[ensures(|_| ub_checks::can_dereference(dst))]
#[kani::modifies(dst)]
unsafe fn volatile_store_wrapper<T>(dst: *mut T, val: T) {
    unsafe { volatile_store(dst, val) }
}

#[requires(
    src_readable(src, count)
        && dst_writable(dst, count)
        && ub_checks::maybe_is_nonoverlapping(src as *const (), dst as *const (), size_of::<T>(), count)
)]
#[ensures(|_| check_copy_untyped(src, dst, count))]
#[kani::modifies(ptr::slice_from_raw_parts(dst, count))]
unsafe fn volatile_copy_nonoverlapping_memory_wrapper<T>(dst: *mut T, src: *const T, count: usize) {
    // Safety-equivalent model (see module comment).
    unsafe { copy_nonoverlapping(src, dst, count) }
}

#[requires(src_readable(src, count) && dst_writable(dst, count))]
#[kani::modifies(ptr::slice_from_raw_parts(dst, count))]
unsafe fn volatile_copy_memory_wrapper<T>(dst: *mut T, src: *const T, count: usize) {
    unsafe { copy(src, dst, count) }
}

#[requires(dst_writable(dst, count))]
#[kani::modifies(ptr::slice_from_raw_parts(dst, count))]
unsafe fn volatile_set_memory_wrapper<T>(dst: *mut T, val: u8, count: usize) {
    unsafe { write_bytes(dst, val, count) }
}

#[requires(ub_checks::can_read_unaligned(src))]
unsafe fn unaligned_volatile_load_wrapper<T>(src: *const T) -> T {
    unsafe { ptr::read_unaligned(src) }
}

#[requires(ub_checks::can_write_unaligned(dst))]
#[kani::modifies(dst)]
unsafe fn unaligned_volatile_store_wrapper<T>(dst: *mut T, val: T) {
    unsafe { ptr::write_unaligned(dst, val) }
}

// ---------------------------------------------------------------------------
// compare_bytes
//
// Documented: `left` and `right` valid for reads of `bytes` bytes (the whole
// range, not only until the first difference). The return sign is the
// lexicographic unsigned-byte order; the magnitude is unspecified.
// ---------------------------------------------------------------------------

#[requires(
    ub_checks::can_dereference(ptr::slice_from_raw_parts(left, bytes))
        && ub_checks::can_dereference(ptr::slice_from_raw_parts(right, bytes))
)]
#[ensures(|result| match compare_bytes_ord(left, right, bytes) {
    crate::cmp::Ordering::Equal => *result == 0,
    crate::cmp::Ordering::Less => *result < 0,
    crate::cmp::Ordering::Greater => *result > 0,
})]
unsafe fn compare_bytes_wrapper(left: *const u8, right: *const u8, bytes: usize) -> i32 {
    unsafe { compare_bytes(left, right, bytes) }
}

// ---------------------------------------------------------------------------
// ptr_offset_from / ptr_offset_from_unsigned
//
// Documented (`<*const T>::offset_from`): same allocation, distance a multiple
// of `size_of::<T>()`, no `isize` overflow; unsigned form also requires
// `ptr >= base`. Fixtures below derive both pointers from one array so the
// same-allocation conjunct is true; a cross-allocation call is language UB
// and is not executed here (it would be a failing harness).
// ---------------------------------------------------------------------------

#[requires(
    size_of::<T>() > 0
        && (ptr as isize).checked_sub(base as isize).is_some()
        && (ptr as isize - base as isize) % (size_of::<T>() as isize) == 0
        && (ptr as isize == base as isize || ub_checks::same_allocation(ptr, base))
)]
#[ensures(|result| {
    *result == (ptr as isize - base as isize) / (size_of::<T>() as isize)
})]
unsafe fn ptr_offset_from_wrapper<T>(ptr: *const T, base: *const T) -> isize {
    unsafe { ptr_offset_from(ptr, base) }
}

#[requires(
    size_of::<T>() > 0
        && (ptr as usize) >= (base as usize)
        && (ptr as usize - base as usize) % size_of::<T>() == 0
        && (ptr as usize == base as usize || ub_checks::same_allocation(ptr, base))
)]
#[ensures(|result| *result == (ptr as usize - base as usize) / size_of::<T>())]
unsafe fn ptr_offset_from_unsigned_wrapper<T>(ptr: *const T, base: *const T) -> usize {
    unsafe { ptr_offset_from_unsigned(ptr, base) }
}

// ---------------------------------------------------------------------------
// read_via_copy / write_via_move  (used by ptr::read / ptr::write)
// ---------------------------------------------------------------------------

#[requires(ub_checks::can_dereference(ptr))]
unsafe fn read_via_copy_wrapper<T>(ptr: *const T) -> T {
    unsafe { read_via_copy(ptr) }
}

#[requires(ub_checks::can_write(ptr))]
#[ensures(|_| ub_checks::can_dereference(ptr))]
#[kani::modifies(ptr)]
unsafe fn write_via_move_wrapper<T>(ptr: *mut T, value: T) {
    unsafe { write_via_move(ptr, value) }
}

// ===========================================================================
// Harnesses
// ===========================================================================

#[kani::proof_for_contract(typed_swap_fallback_wrapper)]
fn check_typed_swap_fallback_u8() {
    let mut x: u8 = kani::any();
    let mut y: u8 = kani::any();
    unsafe { typed_swap_fallback_wrapper(&mut x, &mut y) }
    kani::cover(true, "typed_swap fallback reached");
}

#[kani::proof_for_contract(vtable_size_wrapper)]
fn check_vtable_size_u32() {
    let x: u32 = kani::any();
    let fat: &dyn Probe = &x;
    let size = unsafe { vtable_size_wrapper(vtable_ptr(fat)) };
    assert_eq!(size, size_of::<u32>());
    kani::cover(size == 4, "u32 vtable size");
}

#[kani::proof_for_contract(vtable_size_wrapper)]
fn check_vtable_size_u8_array() {
    let x: [u8; 8] = kani::any();
    let fat: &dyn Probe = &x;
    let size = unsafe { vtable_size_wrapper(vtable_ptr(fat)) };
    assert_eq!(size, 8);
    kani::cover(size == 8, "[u8; 8] vtable size is not size_of::<u32>()");
}

#[kani::proof_for_contract(vtable_size_wrapper)]
fn check_vtable_size_zst() {
    let x = ();
    let fat: &dyn Probe = &x;
    let size = unsafe { vtable_size_wrapper(vtable_ptr(fat)) };
    assert_eq!(size, 0);
    kani::cover(size == 0, "ZST vtable size");
}

#[kani::proof_for_contract(vtable_align_wrapper)]
fn check_vtable_align_u32() {
    let x: u32 = kani::any();
    let fat: &dyn Probe = &x;
    let align = unsafe { vtable_align_wrapper(vtable_ptr(fat)) };
    assert_eq!(align, align_of::<u32>());
    kani::cover(align == 4, "u32 vtable align");
}

#[kani::proof_for_contract(vtable_align_wrapper)]
fn check_vtable_align_u8() {
    let x: u8 = kani::any();
    let fat: &dyn Probe = &x;
    let align = unsafe { vtable_align_wrapper(vtable_ptr(fat)) };
    assert_eq!(align, 1);
    kani::cover(align == 1, "u8 vtable align is not 4");
}

#[kani::proof_for_contract(copy_wrapper)]
fn check_copy_nonoverlapping_regions_u8() {
    let src: [u8; 4] = kani::any();
    let mut dst: [u8; 4] = kani::any();
    let count = kani::any_where(|c: &usize| *c <= 4);
    unsafe { copy_wrapper(src.as_ptr(), dst.as_mut_ptr(), count) }
    kani::cover(count > 0, "copy count > 0");
}

#[kani::proof_for_contract(copy_wrapper)]
fn check_copy_overlapping_shift_u8() {
    // Representative overlap (not all shifts). Symbolic `count` with a
    // symbolic shift does not converge; this is the same bound used for
    // `copy` overlap in the challenge write-up.
    const SHIFT: usize = 2;
    let mut buf: [u8; 8] = kani::any();
    let count = 4;
    unsafe { copy_wrapper(buf.as_ptr(), buf.as_mut_ptr().add(SHIFT), count) }
    kani::cover(true, "overlapping copy");
}

#[kani::proof_for_contract(copy_nonoverlapping_wrapper)]
fn check_copy_nonoverlapping_u8() {
    let src: [u8; 4] = kani::any();
    let mut dst: [u8; 4] = kani::any();
    let count = kani::any_where(|c: &usize| *c <= 4);
    unsafe { copy_nonoverlapping_wrapper(src.as_ptr(), dst.as_mut_ptr(), count) }
    if count > 0 {
        let i = kani::any_where(|i: &usize| *i < count);
        assert_eq!(dst[i], src[i]);
    }
    kani::cover(count > 0, "copy_nonoverlapping count > 0");
}

#[kani::proof_for_contract(copy_nonoverlapping_wrapper)]
fn check_copy_nonoverlapping_zero_count() {
    // `count == 0` is a no-op. Language-safe dangling dst is rejected by
    // CBMC `modifies` (kani#90); use a live allocation.
    let src: [u8; 1] = kani::any();
    let mut dst: [u8; 1] = kani::any();
    unsafe { copy_nonoverlapping_wrapper(src.as_ptr(), dst.as_mut_ptr(), 0) }
    kani::cover(true, "zero-count copy_nonoverlapping");
}

#[kani::proof_for_contract(write_bytes_wrapper)]
fn check_write_bytes_u8() {
    let mut dst: [u8; 4] = kani::any();
    let val: u8 = kani::any();
    let count = kani::any_where(|c: &usize| *c <= 4);
    unsafe { write_bytes_wrapper(dst.as_mut_ptr(), val, count) }
    if count > 0 {
        let i = kani::any_where(|i: &usize| *i < count);
        assert_eq!(dst[i], val);
    }
    kani::cover(count > 0, "write_bytes count > 0");
}

#[kani::proof_for_contract(write_bytes_wrapper)]
fn check_write_bytes_zero_count() {
    // `count == 0` is a no-op. Language-safe dangling dst is rejected by
    // CBMC `modifies` (kani#90); use a live allocation.
    let mut dst: [u8; 1] = kani::any();
    unsafe { write_bytes_wrapper(dst.as_mut_ptr(), kani::any(), 0) }
    kani::cover(true, "zero-count write_bytes");
}

#[kani::proof_for_contract(size_of_val_sized_wrapper)]
fn check_size_of_val_sized_u32() {
    let x: u32 = kani::any();
    // Documented: always safe for Sized, including null.
    let ptr = if kani::any() {
        &x as *const u32
    } else {
        ptr::null()
    };
    let size = unsafe { size_of_val_sized_wrapper(ptr) };
    assert_eq!(size, 4);
    kani::cover(ptr.is_null(), "size_of_val on null Sized pointer");
}

#[kani::proof_for_contract(size_of_val_slice_wrapper)]
fn check_size_of_val_slice_u8() {
    let buf: [u8; 4] = kani::any();
    let len = kani::any_where(|l: &usize| *l <= 4);
    let ptr = ptr::slice_from_raw_parts(buf.as_ptr(), len);
    let size = unsafe { size_of_val_slice_wrapper::<u8>(ptr) };
    assert_eq!(size, len);
    kani::cover(len == 0, "empty slice size_of_val");
}

#[kani::proof_for_contract(size_of_val_slice_wrapper)]
fn check_size_of_val_slice_len_zero_dangling() {
    let ptr = ptr::slice_from_raw_parts(ptr::NonNull::<u8>::dangling().as_ptr(), 0);
    let size = unsafe { size_of_val_slice_wrapper::<u8>(ptr) };
    assert_eq!(size, 0);
    kani::cover(true, "dangling empty slice");
}

#[kani::proof_for_contract(size_of_val_dyn_wrapper)]
fn check_size_of_val_dyn_u32() {
    let x: u32 = kani::any();
    let fat: &dyn Probe = &x;
    let size = unsafe { size_of_val_dyn_wrapper(fat) };
    assert_eq!(size, size_of::<u32>());
    kani::cover(true, "dyn size_of_val");
}

#[kani::proof_for_contract(size_of_val_dyn_wrapper)]
fn check_size_of_val_dyn_array() {
    let x: [u8; 8] = kani::any();
    let fat: &dyn Probe = &x;
    let size = unsafe { size_of_val_dyn_wrapper(fat) };
    assert_eq!(size, 8);
    kani::cover(true, "dyn size_of_val of [u8; 8]");
}

#[kani::proof_for_contract(align_of_val_sized_wrapper)]
fn check_align_of_val_sized_u32() {
    let ptr = ptr::null::<u32>();
    let align = unsafe { align_of_val_sized_wrapper(ptr) };
    assert_eq!(align, 4);
    kani::cover(true, "align_of_val Sized null");
}

#[kani::proof_for_contract(align_of_val_slice_wrapper)]
fn check_align_of_val_slice_u32() {
    let buf: [u32; 2] = kani::any();
    let len = kani::any_where(|l: &usize| *l <= 2);
    let ptr = ptr::slice_from_raw_parts(buf.as_ptr(), len);
    let align = unsafe { align_of_val_slice_wrapper::<u32>(ptr) };
    assert_eq!(align, 4);
    kani::cover(true, "align_of_val slice");
}

#[kani::proof_for_contract(align_of_val_dyn_wrapper)]
fn check_align_of_val_dyn_u8() {
    let x: u8 = kani::any();
    let fat: &dyn Probe = &x;
    let align = unsafe { align_of_val_dyn_wrapper(fat) };
    assert_eq!(align, 1);
    kani::cover(align == 1, "dyn align of u8");
}

#[kani::proof_for_contract(arith_offset_wrapper)]
fn check_arith_offset_in_object_u8() {
    let buf: [u8; 8] = kani::any();
    let offset: isize = kani::any();
    let dst = buf.as_ptr();
    let result = unsafe { arith_offset_wrapper(dst, offset) };
    kani::cover(true, "in-object arith_offset");
    let _ = (result, dst);
}

/// Criterion-5 safety is unconditional: `arith_offset` has an empty documented
/// precondition. This is not `proof_for_contract` — the wrapping-address
/// `#[ensures]` is only CBMC-faithful in-object (see wrapper comment).
#[kani::proof]
fn check_arith_offset_unbounded_no_ub() {
    let x: u32 = kani::any();
    let offset: isize = kani::any();
    let dst = &x as *const u32;
    let result = unsafe { arith_offset(dst, offset) };
    kani::cover(offset < 0, "negative unbounded arith_offset");
    let _ = result;
}

#[kani::proof_for_contract(volatile_load_wrapper)]
fn check_volatile_load_u32() {
    let x: u32 = kani::any();
    let y = unsafe { volatile_load_wrapper(&x as *const u32) };
    assert_eq!(x, y);
    kani::cover(true, "volatile_load");
}

#[kani::proof_for_contract(volatile_store_wrapper)]
fn check_volatile_store_u32() {
    let mut dst: u32 = kani::any();
    let val: u32 = kani::any();
    unsafe { volatile_store_wrapper(&mut dst, val) }
    assert_eq!(dst, val);
    kani::cover(true, "volatile_store");
}

#[kani::proof_for_contract(volatile_copy_nonoverlapping_memory_wrapper)]
fn check_volatile_copy_nonoverlapping_u8() {
    let src: [u8; 4] = kani::any();
    let mut dst: [u8; 4] = kani::any();
    let count = kani::any_where(|c: &usize| *c <= 4);
    unsafe { volatile_copy_nonoverlapping_memory_wrapper(dst.as_mut_ptr(), src.as_ptr(), count) }
    if count > 0 {
        let i = kani::any_where(|i: &usize| *i < count);
        assert_eq!(dst[i], src[i]);
    }
    kani::cover(count > 0, "volatile_copy_nonoverlapping");
}

#[kani::proof_for_contract(volatile_copy_memory_wrapper)]
fn check_volatile_copy_memory_shift_u8() {
    const SHIFT: usize = 2;
    let mut buf: [u8; 8] = kani::any();
    unsafe { volatile_copy_memory_wrapper(buf.as_mut_ptr().add(SHIFT), buf.as_ptr(), 4) }
    kani::cover(true, "volatile_copy_memory representative overlap");
}

#[kani::proof_for_contract(volatile_set_memory_wrapper)]
fn check_volatile_set_memory_u8() {
    let mut dst: [u8; 4] = kani::any();
    let val: u8 = kani::any();
    let count = kani::any_where(|c: &usize| *c <= 4);
    unsafe { volatile_set_memory_wrapper(dst.as_mut_ptr(), val, count) }
    if count > 0 {
        let i = kani::any_where(|i: &usize| *i < count);
        assert_eq!(dst[i], val);
    }
    kani::cover(count > 0, "volatile_set_memory");
}

#[kani::proof_for_contract(unaligned_volatile_load_wrapper)]
fn check_unaligned_volatile_load_u32() {
    let bytes: [u8; 8] = kani::any();
    let offset = kani::any_where(|o: &usize| *o <= 4);
    let ptr = unsafe { bytes.as_ptr().add(offset) as *const u32 };
    let _v = unsafe { unaligned_volatile_load_wrapper(ptr) };
    kani::cover(offset % 4 != 0, "unaligned volatile load");
}

#[kani::proof_for_contract(unaligned_volatile_store_wrapper)]
fn check_unaligned_volatile_store_u32() {
    let mut bytes: [u8; 8] = kani::any();
    let offset = kani::any_where(|o: &usize| *o <= 4);
    let ptr = unsafe { bytes.as_mut_ptr().add(offset) as *mut u32 };
    let val: u32 = kani::any();
    unsafe { unaligned_volatile_store_wrapper(ptr, val) }
    kani::cover(offset % 4 != 0, "unaligned volatile store");
}

#[kani::proof_for_contract(compare_bytes_wrapper)]
#[kani::unwind(5)]
fn check_compare_bytes() {
    let left: [u8; 4] = kani::any();
    let right: [u8; 4] = kani::any();
    // Cap is a harness bound, not a contract precondition.
    let bytes = kani::any_where(|b: &usize| *b <= 4);
    let cmp = unsafe { compare_bytes_wrapper(left.as_ptr(), right.as_ptr(), bytes) };
    match compare_bytes_ord(left.as_ptr(), right.as_ptr(), bytes) {
        crate::cmp::Ordering::Equal => assert_eq!(cmp, 0),
        crate::cmp::Ordering::Less => assert!(cmp < 0),
        crate::cmp::Ordering::Greater => assert!(cmp > 0),
    }
    kani::cover(bytes > 0 && cmp != 0, "compare_bytes unequal");
}

#[kani::proof_for_contract(ptr_offset_from_wrapper)]
fn check_ptr_offset_from_same_alloc() {
    let buf: [u8; 8] = kani::any();
    let i = kani::any_where(|i: &usize| *i <= 8);
    let j = kani::any_where(|j: &usize| *j <= 8);
    let ptr = unsafe { buf.as_ptr().add(i) };
    let base = unsafe { buf.as_ptr().add(j) };
    let off = unsafe { ptr_offset_from_wrapper(ptr, base) };
    assert_eq!(off, i as isize - j as isize);
    kani::cover(i < j, "negative ptr_offset_from");
}

#[kani::proof_for_contract(ptr_offset_from_unsigned_wrapper)]
fn check_ptr_offset_from_unsigned_same_alloc() {
    let buf: [u8; 8] = kani::any();
    let i = kani::any_where(|i: &usize| *i <= 8);
    let j = kani::any_where(|j: &usize| *j <= i);
    let ptr = unsafe { buf.as_ptr().add(i) };
    let base = unsafe { buf.as_ptr().add(j) };
    let off = unsafe { ptr_offset_from_unsigned_wrapper(ptr, base) };
    assert_eq!(off, i - j);
    kani::cover(i > j, "strictly positive unsigned offset");
}

#[kani::proof_for_contract(read_via_copy_wrapper)]
fn check_read_via_copy_u32() {
    let x: u32 = kani::any();
    let y = unsafe { read_via_copy_wrapper(&x as *const u32) };
    assert_eq!(x, y);
    kani::cover(true, "read_via_copy");
}

#[kani::proof_for_contract(write_via_move_wrapper)]
fn check_write_via_move_u32() {
    let mut dst: u32 = kani::any();
    let val: u32 = kani::any();
    unsafe { write_via_move_wrapper(&mut dst, val) }
    assert_eq!(dst, val);
    kani::cover(true, "write_via_move");
}
