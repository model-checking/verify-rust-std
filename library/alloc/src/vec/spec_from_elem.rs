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
mod verify {
    use core::kani;

    use super::SpecFromElem;
    use crate::alloc::Global;

    // from_elem (i8/u8/()): with_capacity + write_bytes/zeroed (memset intrinsic,
    // no element loop) — object-light, real body, symbolic length and element.
    // The symbolic `elem` exercises both the zeroed and the write_bytes branches;
    // the postcondition checks length and element value at a symbolic index.
    #[kani::proof]
    #[kani::unwind(8)]
    fn check_from_elem_i8() {
        let n: usize = kani::any();
        kani::assume(n <= 64);
        kani::cover(n == 64, "non-vacuity: the full-length case is reachable");
        let elem: i8 = kani::any();
        let v = <i8 as SpecFromElem>::from_elem(elem, n, Global);
        assert!(v.len() == n);
        if n > 0 {
            let j: usize = kani::any();
            kani::assume(j < n);
            assert!(v[j] == elem);
        }
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_from_elem_u8() {
        let n: usize = kani::any();
        kani::assume(n <= 64);
        kani::cover(n == 64, "non-vacuity: the full-length case is reachable");
        let elem: u8 = kani::any();
        let v = <u8 as SpecFromElem>::from_elem(elem, n, Global);
        assert!(v.len() == n);
        if n > 0 {
            let j: usize = kani::any();
            kani::assume(j < n);
            assert!(v[j] == elem);
        }
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_from_elem_unit() {
        let n: usize = kani::any();
        kani::assume(n <= 64);
        kani::cover(n == 64, "non-vacuity: the full-length case is reachable");
        let v = <() as SpecFromElem>::from_elem((), n, Global);
        assert!(v.len() == n);
    }
}
