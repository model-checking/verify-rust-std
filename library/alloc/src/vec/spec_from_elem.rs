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
    use super::super::kani_vec_harness_helpers::*;
    use super::*;
    use crate::alloc::Global;

    // Harness for `SpecFromElem::from_elem` for `i8` and `u8`
    macro_rules! gen_from_elem_byte_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let elem: $ty = kani::any();
                let n: usize = kani::any();
                kani::cover(elem == 0, "from_elem: zero element");
                kani::cover(elem != 0, "from_elem: non-zero element");
                kani::cover(n == 0, "from_elem: empty Vec");
                kani::cover(n > 0, "from_elem: non-empty Vec");
                // Restrict only allocations that cannot be represented by the
                // target layout or CBMC object model.
                let layout_ok = core::alloc::Layout::array::<$ty>(n).is_ok();
                kani::cover(layout_ok, "from_elem: allocation layout is representable");
                kani::assume(layout_ok);
                let object_model_ok = n
                    .checked_mul(core::mem::size_of::<$ty>())
                    .is_some_and(|bytes| bytes <= MAX_ALLOCATION_BYTES);
                kani::cover(object_model_ok, "from_elem: allocation fits the CBMC object model");
                kani::assume(object_model_ok);
                let vec = <$ty as SpecFromElem>::from_elem(elem, n, Global);
                assert!(vec.len() == n, "from_elem: resulting Vec has the wrong length");
                assert!(vec.capacity() >= n, "from_elem: resulting Vec has insufficient capacity");
                if n > 0 {
                    let i = kani::any_where(|i: &usize| *i < n);
                    assert!(
                        vec[i] == elem,
                        "from_elem: an initialized element differs from the requested value"
                    );
                    kani::cover(i == 0, "from_elem: first element");
                    kani::cover(i == n - 1, "from_elem: last element");
                    kani::cover(n > 2 && i > 0 && i < n - 1, "from_elem: interior element");
                }
            }
        };
    }

    gen_from_elem_byte_harness!(harness_from_elem_for_i8, i8);
    gen_from_elem_byte_harness!(harness_from_elem_for_u8, u8);

    // Harness for `SpecFromElem::from_elem` for `()`
    #[kani::proof]
    pub fn harness_from_elem_for_unit() {
        let n: usize = kani::any();
        kani::cover(n == 0, "from_elem<()>: empty Vec");
        kani::cover(n > 0, "from_elem<()>: non-empty Vec");
        kani::cover(n == usize::MAX, "from_elem<()>: maximum logical length");
        let vec = <() as SpecFromElem>::from_elem((), n, Global);
        assert!(vec.len() == n, "from_elem<()>: resulting Vec has the wrong length");
        assert!(
            vec.capacity() >= vec.len(),
            "from_elem<()>: resulting Vec has insufficient capacity"
        );
    }
}
