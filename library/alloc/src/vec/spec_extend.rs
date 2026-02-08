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

impl<T, A: Allocator> SpecExtend<T, IntoIter<T>> for Vec<T, A> {
    fn spec_extend(&mut self, mut iterator: IntoIter<T>) {
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
    T: Copy,
{
    fn spec_extend(&mut self, iterator: slice::Iter<'a, T>) {
        let slice = iterator.as_slice();
        unsafe { self.append_elements(slice) };
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::kani;

    use super::*;

    const MAX_LEN: usize = 3;

    fn any_vec<T: kani::Arbitrary, const N: usize>() -> Vec<T> {
        let arr: [T; N] = kani::Arbitrary::any_array();
        let mut v = Vec::from(arr);
        let new_len: usize = kani::any();
        kani::assume(new_len <= v.len());
        v.truncate(new_len);
        v
    }

    macro_rules! check_spec_extend_with_ty {
        ($mod_name:ident, $ty:ty) => {
            mod $mod_name {
                use super::*;

                #[kani::proof]
                #[kani::unwind(8)]
                fn check_spec_extend_into_iter() {
                    let mut dest: Vec<$ty> = any_vec::<$ty, MAX_LEN>();
                    let src: Vec<$ty> = any_vec::<$ty, MAX_LEN>();
                    let dest_len = dest.len();
                    let src_len = src.len();
                    let src_iter = src.into_iter();
                    <Vec<$ty> as SpecExtend<$ty, IntoIter<$ty>>>::spec_extend(&mut dest, src_iter);
                    assert!(dest.len() == dest_len + src_len);
                }
            }
        };
    }

    // spec_extend for slice::Iter requires T: Copy, so only verify for Copy types
    macro_rules! check_spec_extend_slice_iter_with_ty {
        ($mod_name:ident, $ty:ty) => {
            mod $mod_name {
                use super::*;

                #[kani::proof]
                #[kani::unwind(8)]
                fn check_spec_extend_slice_iter() {
                    let mut dest: Vec<$ty> = any_vec::<$ty, MAX_LEN>();
                    let src: Vec<$ty> = any_vec::<$ty, MAX_LEN>();
                    let dest_len = dest.len();
                    let src_len = src.len();
                    let src_slice = src.as_slice();
                    <Vec<$ty> as SpecExtend<&$ty, slice::Iter<'_, $ty>>>::spec_extend(
                        &mut dest,
                        src_slice.iter(),
                    );
                    assert!(dest.len() == dest_len + src_len);
                }
            }
        };
    }

    check_spec_extend_with_ty!(verify_spec_extend_u8, u8);
    check_spec_extend_with_ty!(verify_spec_extend_unit, ());
    check_spec_extend_with_ty!(verify_spec_extend_char, char);
    check_spec_extend_with_ty!(verify_spec_extend_tup, (char, u8));

    // slice::Iter specialization requires T: Copy
    check_spec_extend_slice_iter_with_ty!(verify_spec_extend_slice_u8, u8);
    check_spec_extend_slice_iter_with_ty!(verify_spec_extend_slice_unit, ());
    check_spec_extend_slice_iter_with_ty!(verify_spec_extend_slice_char, char);
    check_spec_extend_slice_iter_with_ty!(verify_spec_extend_slice_tup, (char, u8));
}
