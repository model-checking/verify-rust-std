// ===== BEGIN TRUSTED STD WRAPPERS =====
//
// Trusted part of the specifications, following the verify-rust-std LinkedList proof. VeriFast 26.10
// cannot attach a spec to these std calls (see README.md), so each call site in this file calls a
// wrapper instead. Each wrapper's body is exactly the original call, and refinement-checker checks
// that the code with wrappers refines the original code. Each spec is assumed (`assume_correct`),
// not proven, and follows the function's documentation in core.
// Every target crate contains this block verbatim (checked by verify.sh).

/*@

// The elements an array iterator has yet to yield.
fix array_IntoIter_remaining<T, N>(it: core::array::IntoIter<T, N>) -> list<T>;

// An address computed with wrapping `usize` arithmetic, for offsets of magnitude at most `usize::MAX + 1`.
fix wrap_usize(a: i32) -> i32 {
    if a < 0 { a + usize::MAX + 1 } else if a > usize::MAX { a - usize::MAX - 1 } else { a }
}

// `p.wrapping_offset(n)`: the same provenance and metadata, address `p + n * size_of::<T>()` modulo
// `usize::MAX + 1`.
fix ptr_wrapping_offset<T>(p: *T, n: i32) -> *T {
    pointer_ctor((p as pointer).provenance, wrap_usize((p as pointer).address + n * std::mem::size_of::<T>()), (p as pointer).metadata) as *T
}

@*/

// `v.as_mut_ptr()`: the slice's data pointer, as for `<[T]>::as_ptr`.
fn slice_as_mut_ptr__VeriFast_wrapper<T>(v: &mut [T]) -> *mut T
//@ req true;
//@ ens result == v as *T;
//@ on_unwind_ens false;
//@ assume_correct
{
    v.as_mut_ptr()
}

// `m.as_mut_ptr()`: a pointer to the contained value; `MaybeUninit<U>` is `repr(transparent)`.
fn maybe_uninit_as_mut_ptr__VeriFast_wrapper<U>(m: &mut MaybeUninit<U>) -> *mut U
//@ req true;
//@ ens result == m as *U;
//@ on_unwind_ens false;
//@ assume_correct
{
    m.as_mut_ptr()
}

// `p.wrapping_sub(count)`: `count` elements down with wrapping address arithmetic, the same provenance,
// no in-bounds requirement (core: "the resulting pointer ... has the same provenance"). Specified for
// `count * size_of::<T>() <= isize::MAX` (one wrap-around at most).
fn const_ptr_wrapping_sub__VeriFast_wrapper<T>(p: *const T, count: usize) -> *const T
//@ req true;
//@ ens if count * std::mem::size_of::<T>() <= isize::MAX { result == ptr_wrapping_offset(p, -count) } else { true };
//@ on_unwind_ens false;
//@ assume_correct
{
    p.wrapping_sub(count)
}

// `p.wrapping_add(1)`: one element up with wrapping address arithmetic, the same provenance
// (refinement-checker does not accept constants as arguments of wrapper calls, so the constant is
// inside the wrapper). Specified for `size_of::<T>() <= isize::MAX` (true of every Rust type).
fn const_ptr_wrapping_add_1__VeriFast_wrapper<T>(p: *const T) -> *const T
//@ req true;
//@ ens if std::mem::size_of::<T>() <= isize::MAX { result == ptr_wrapping_offset(p, 1) } else { true };
//@ on_unwind_ens false;
//@ assume_correct
{
    p.wrapping_add(1)
}

// `IntoIterator::into_iter([0, b])`, the head of `for offset in [0, len_div_2]`. This and the next
// wrapper are `unsafe` only so that VeriFast does not also require the specs VeriFast generates for
// safe functions (it cannot express ownership of their array and `Option` values); the call site is
// inside an `unsafe` block, and refinement-checker checks it against the original `for` loop.
unsafe fn array_0_and_into_iter__VeriFast_wrapper(b: usize) -> core::array::IntoIter<usize, 2>
//@ req thread_token(?t);
//@ ens thread_token(t) &*& <core::array::IntoIter<usize, 2>>.own(t, result) &*& array_IntoIter_remaining(result) == [0, b];
//@ on_unwind_ens false;
//@ assume_correct
{
    IntoIterator::into_iter([0, b])
}

// `iter.next()` for the iterator above: yields the remaining elements in order.
unsafe fn array_usize_2_into_iter_next__VeriFast_wrapper(iter: &mut core::array::IntoIter<usize, 2>) -> Option<usize>
//@ req thread_token(?t) &*& *iter |-> ?it0 &*& <core::array::IntoIter<usize, 2>>.own(t, it0);
/*@
ens thread_token(t) &*& *iter |-> ?it1 &*& <core::array::IntoIter<usize, 2>>.own(t, it1) &*&
    match array_IntoIter_remaining(it0) {
        nil => result == std::option::Option::None && array_IntoIter_remaining(it1) == nil,
        cons(x, xs) => result == std::option::Option::Some(x) && array_IntoIter_remaining(it1) == xs
    };
@*/
//@ on_unwind_ens false;
//@ assume_correct
{
    Iterator::next(iter)
}

// `ptr::copy(src, dst, 1)`: memmove of one element (refinement-checker does not accept constants as
// arguments of wrapper calls, so the count is inside the wrapper). VeriFast 26.10's prelude spec of
// `std::ptr::copy` does not bound `offset` in its `some(offset)` branch: at a call whose regions are
// disjoint and farther apart than `count` elements, choosing that branch yields a chunk whose byte list
// is shorter than the chunk, from which `false` follows. This spec is that prelude spec at `count = 1`
// with `-1 <= offset <= 1` added to the `some(offset)` branch; regions farther apart use `none`.
unsafe fn ptr_copy_1__VeriFast_wrapper<T>(src: *const T, dst: *mut T)
/*@
req exists::<option<isize>>(?offset_opt) &*&
    match offset_opt {
        none => // No overlap
            [?f](src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& (dst as *u8)[..1 * std::mem::size_of::<T>()] |-> _ &*&
            ens [f](src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs &*& (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs,
        some(offset) =>
            dst == src + offset &*& -1 <= offset &*& offset <= 1 &*&
            if offset == 0 {
                (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*&
                ens (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            } else if offset > 0 {
                (src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& ((src + 1) as *u8)[..offset * std::mem::size_of::<T>()] |-> _ &*&
                ens (src as *u8)[..offset * std::mem::size_of::<T>()] |-?-> take(offset * std::mem::size_of::<T>(), bs) &*&
                    (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            } else {
                (src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& (dst as *u8)[..-offset * std::mem::size_of::<T>()] |-> _ &*&
                ens ((dst + 1) as *u8)[..-offset * std::mem::size_of::<T>()] |-?-> drop((1 + offset) * std::mem::size_of::<T>(), bs) &*&
                    (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            }
    };
@*/
//@ ens true;
//@ on_unwind_ens false;
//@ terminates;
//@ assume_correct
{
    ptr::copy(src, dst, 1)
}

// `a + 16` on `usize` (refinement-checker does not accept constants as arguments of wrapper calls, so
// the constant is inside the wrapper). Rust's checked semantics (a build with overflow checks): the
// result is `a + 16`, and the addition panics if that exceeds `usize::MAX`. (In a build without overflow
// checks it wraps instead; it can overflow only for zero-sized `T`, see README.md.)
fn usize_add_16__VeriFast_wrapper(a: usize) -> usize
//@ req true;
//@ ens a + 16 <= usize::MAX &*& result == a + 16;
//@ on_unwind_ens true;
//@ assume_correct
{
    a + 16
}

// `MaybeUninit::<U>::uninit()`: an uninitialized `MaybeUninit<U>` (VeriFast 26.10 has no spec for it).
// `unsafe` only so that VeriFast does not also require the spec it generates for safe functions; the call
// sites are rewritten (see rewrites/LOG.md) and refinement-checker checks them.
unsafe fn maybe_uninit_uninit__VeriFast_wrapper<U>() -> MaybeUninit<U>
//@ req true;
//@ ens result == std::mem::MaybeUninit::uninit::<U>();
//@ on_unwind_ens false;
//@ assume_correct
{
    MaybeUninit::uninit()
}

// ===== END TRUSTED STD WRAPPERS =====
