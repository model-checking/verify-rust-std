use core::clone::TrivialClone;
use core::iter::TrustedLen;
use core::slice::{self};

use super::{IntoIter, Vec};
use crate::alloc::Allocator;

// Specialization trait used for Vec::extend
pub(super) trait SpecExtend<T, I> {
    fn spec_extend(&mut self, iter: I);
}

impl<T, I, A: Allocator> SpecExtend<T, I> for Vec<T, A>
where
    I: Iterator<Item = T>,
{
    default fn spec_extend(&mut self, iter: I) {
        self.extend_desugared(iter)
    }
}

impl<T, I, A: Allocator> SpecExtend<T, I> for Vec<T, A>
where
    I: TrustedLen<Item = T>,
{
    default fn spec_extend(&mut self, iterator: I) {
        self.extend_trusted(iterator)
    }
}

impl<T, A1: Allocator, A2: Allocator> SpecExtend<T, IntoIter<T, A2>> for Vec<T, A1> {
    fn spec_extend(&mut self, mut iterator: IntoIter<T, A2>) {
        unsafe {
            self.append_elements(iterator.as_slice() as _);
        }
        iterator.forget_remaining_elements();
    }
}

impl<'a, T: 'a, I, A: Allocator> SpecExtend<&'a T, I> for Vec<T, A>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    default fn spec_extend(&mut self, iterator: I) {
        self.spec_extend(iterator.cloned())
    }
}

impl<'a, T: 'a, A: Allocator> SpecExtend<&'a T, slice::Iter<'a, T>> for Vec<T, A>
where
    T: TrivialClone,
{
    fn spec_extend(&mut self, iterator: slice::Iter<'a, T>) {
        let slice = iterator.as_slice();
        unsafe { self.append_elements(slice) };
    }
}

#[cfg(kani)]
mod verify {
    use core::kani;

    use super::SpecExtend;
    use crate::vec::{IntoIter, Vec};

    // spec_extend (IntoIter): routes to append_elements (bulk memcpy). Self is
    // pre-sized so reserve() is a no-op — this is the copy path, not the
    // element-by-element grow. Real body, symbolic-length source; postcondition
    // checks length and element value at a symbolic index.
    #[kani::proof]
    #[kani::unwind(8)]
    fn check_spec_extend_intoiter_u8() {
        let mut v: Vec<u8> = Vec::with_capacity(128);
        let arr: [u8; 64] = kani::any();
        let s = kani::slice::any_slice_of_array(&arr);
        let m = s.len();
        let src: IntoIter<u8> = s.to_vec().into_iter();
        v.spec_extend(src);
        assert!(v.len() == m);
        if m > 0 {
            let j: usize = kani::any();
            kani::assume(j < m);
            assert!(v[j] == s[j]);
        }
    }

    // spec_extend (slice::Iter, TrivialClone specialization): same append_elements path.
    #[kani::proof]
    #[kani::unwind(8)]
    fn check_spec_extend_sliceiter_u8() {
        let mut v: Vec<u8> = Vec::with_capacity(128);
        let arr: [u8; 64] = kani::any();
        let s = kani::slice::any_slice_of_array(&arr);
        let m = s.len();
        v.spec_extend(s.iter());
        assert!(v.len() == m);
        if m > 0 {
            let j: usize = kani::any();
            kani::assume(j < m);
            assert!(v[j] == s[j]);
        }
    }

    use crate::vec::kani_shapes::DropToken;

    // spec_extend (IntoIter) over a Drop-carrying T: append_elements bulk-move +
    // forget_remaining_elements is the move-without-double-drop obligation.
    // Mirrors check_spec_extend_intoiter_u8.
    fn check_spec_extend_intoiter_shape<T: kani::Arbitrary + Clone + PartialEq, const N: usize>() {
        let mut v: Vec<T> = Vec::with_capacity(2 * N);
        let arr: [T; N] = kani::any();
        let s = kani::slice::any_slice_of_array(&arr);
        let m = s.len();
        let src: IntoIter<T> = s.to_vec().into_iter();
        v.spec_extend(src);
        assert!(v.len() == m);
        if m > 0 {
            let j: usize = kani::any();
            kani::assume(j < m);
            assert!(v[j] == s[j]);
        }
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn check_spec_extend_intoiter_droptoken() {
        check_spec_extend_intoiter_shape::<DropToken, 8>();
    }
}
