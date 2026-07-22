#[cfg(kani)]
use core::kani;
use core::ptr;

use super::{IsZero, Vec};
use crate::alloc::Allocator;
use crate::raw_vec::RawVec;

// Specialization trait used for Vec::from_elem
pub(super) trait SpecFromElem: Sized {
    fn from_elem<A: Allocator>(elem: Self, n: usize, alloc: A) -> Vec<Self, A>;
}

impl<T: Clone> SpecFromElem for T {
    default fn from_elem<A: Allocator>(elem: Self, n: usize, alloc: A) -> Vec<Self, A> {
        let mut v = Vec::with_capacity_in(n, alloc);
        v.extend_with(n, elem);
        v
    }
}

impl<T: Clone + IsZero> SpecFromElem for T {
    #[inline]
    default fn from_elem<A: Allocator>(elem: T, n: usize, alloc: A) -> Vec<T, A> {
        if elem.is_zero() {
            return Vec { buf: RawVec::with_capacity_zeroed_in(n, alloc), len: n };
        }
        let mut v = Vec::with_capacity_in(n, alloc);
        v.extend_with(n, elem);
        v
    }
}

impl SpecFromElem for i8 {
    #[inline]
    fn from_elem<A: Allocator>(elem: i8, n: usize, alloc: A) -> Vec<i8, A> {
        if elem == 0 {
            return Vec { buf: RawVec::with_capacity_zeroed_in(n, alloc), len: n };
        }
        let mut v = Vec::with_capacity_in(n, alloc);
        unsafe {
            ptr::write_bytes(v.as_mut_ptr(), elem as u8, n);
            v.set_len(n);
        }
        v
    }
}

impl SpecFromElem for u8 {
    #[inline]
    fn from_elem<A: Allocator>(elem: u8, n: usize, alloc: A) -> Vec<u8, A> {
        if elem == 0 {
            return Vec { buf: RawVec::with_capacity_zeroed_in(n, alloc), len: n };
        }
        let mut v = Vec::with_capacity_in(n, alloc);
        unsafe {
            ptr::write_bytes(v.as_mut_ptr(), elem, n);
            v.set_len(n);
        }
        v
    }
}

// A better way would be to implement this for all ZSTs which are `Copy` and have trivial `Clone`
// but the latter cannot be detected currently
impl SpecFromElem for () {
    #[inline]
    fn from_elem<A: Allocator>(_elem: (), n: usize, alloc: A) -> Vec<(), A> {
        let mut v = Vec::with_capacity_in(n, alloc);
        // SAFETY: the capacity has just been set to `n`
        // and `()` is a ZST with trivial `Clone` implementation
        unsafe {
            v.set_len(n);
        }
        v
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;
    use crate::alloc::Global;

    // Harness for `SpecFromElem::from_elem` for `i8`
    #[kani::proof]
    pub fn harness_from_elem_for_i8() {
        // Create a non-deterministic element to repeat
        let elem: i8 = kani::any();
        // Choose a non-deterministic output length
        let n: usize = kani::any();
        // Require the requested allocation layout to be representable
        kani::assume(core::alloc::Layout::array::<i8>(n).is_ok());
        // Build a Vec by repeating the selected element
        let _ = <i8 as SpecFromElem>::from_elem(elem, n, Global);
    }

    // Harness for `SpecFromElem::from_elem` for `u8`
    #[kani::proof]
    pub fn harness_from_elem_for_u8() {
        // Create a non-deterministic element to repeat
        let elem: u8 = kani::any();
        // Choose a non-deterministic output length
        let n: usize = kani::any();
        // Require the requested allocation layout to be representable
        kani::assume(core::alloc::Layout::array::<u8>(n).is_ok());
        // Build a Vec by repeating the selected element
        let _ = <u8 as SpecFromElem>::from_elem(elem, n, Global);
    }

    // Harness for `SpecFromElem::from_elem` for `()`
    #[kani::proof]
    pub fn harness_from_elem_for_unit() {
        // Choose a non-deterministic output length for the zero-sized element type
        let n: usize = kani::any();
        // Build a Vec by repeating the unit element
        let _ = <() as SpecFromElem>::from_elem((), n, Global);
    }
}
