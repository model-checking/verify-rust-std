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
            return Vec {
                buf: RawVec::with_capacity_zeroed_in(n, alloc),
                len: n,
            };
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
            return Vec {
                buf: RawVec::with_capacity_zeroed_in(n, alloc),
                len: n,
            };
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
            return Vec {
                buf: RawVec::with_capacity_zeroed_in(n, alloc),
                len: n,
            };
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
    use core::kani;

    use super::*;

    #[kani::proof]
    fn check_from_elem_i8() {
        let elem: i8 = kani::any();
        let n: usize = kani::any();
        kani::assume(n <= 3);
        let v = <i8 as SpecFromElem>::from_elem(elem, n, crate::alloc::Global);
        assert!(v.len() == n);
        let k: usize = kani::any();
        kani::assume(k < n);
        assert!(v[k] == elem);
    }

    #[kani::proof]
    fn check_from_elem_u8() {
        let elem: u8 = kani::any();
        let n: usize = kani::any();
        kani::assume(n <= 3);
        let v = <u8 as SpecFromElem>::from_elem(elem, n, crate::alloc::Global);
        assert!(v.len() == n);
        let k: usize = kani::any();
        kani::assume(k < n);
        assert!(v[k] == elem);
    }

    #[kani::proof]
    fn check_from_elem_unit() {
        let n: usize = kani::any();
        kani::assume(n <= 3);
        let v = <() as SpecFromElem>::from_elem((), n, crate::alloc::Global);
        assert!(v.len() == n);
    }
}
