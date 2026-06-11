use core::iter::TrustedLen;
#[cfg(kani)]
use core::kani;
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
    use super::super::kani_vec_harness_helpers::*;
    use super::*;

    // Harnesses for `Vec::spec_extend` with `IntoIter`
    macro_rules! gen_spec_extend_into_iter_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create the destination Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Create the source Vec whose elements will be moved by IntoIter
                let source = verifier_nondet_vec::<$ty>();
                // Convert the source Vec into its owning iterator
                let iter = source.into_iter();
                // Require enough capacity for all remaining source elements
                assume_reserve_no_capacity_overflow::<$ty>(
                    vec.len(),
                    vec.capacity(),
                    iter.as_slice().len(),
                );
                // Extend the destination Vec from the owning iterator specialization
                vec.spec_extend(iter);
            }
        };
    }

    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_u8, u8);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_u16, u16);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_u32, u32);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_u64, u64);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_u128, u128);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_usize, usize);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_i8, i8);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_i16, i16);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_i32, i32);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_i64, i64);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_i128, i128);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_isize, isize);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_unit, ());
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_array, [u8; 4]);

    // Harnesses for `Vec::spec_extend` with `slice::Iter`
    macro_rules! gen_spec_extend_slice_iter_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create the destination Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Create the source Vec whose elements will be cloned from a slice iterator
                let source = verifier_nondet_vec::<$ty>();
                // Borrow the source Vec through its slice iterator
                let iter = source.iter();
                // Require enough capacity for all remaining source elements
                assume_reserve_no_capacity_overflow::<$ty>(
                    vec.len(),
                    vec.capacity(),
                    iter.as_slice().len(),
                );
                // Extend the destination Vec from the slice iterator specialization
                vec.spec_extend(iter);
            }
        };
    }

    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_u8, u8);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_u16, u16);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_u32, u32);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_u64, u64);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_u128, u128);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_usize, usize);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_i8, i8);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_i16, i16);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_i32, i32);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_i64, i64);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_i128, i128);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_isize, isize);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_unit, ());
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_array, [u8; 4]);
}
