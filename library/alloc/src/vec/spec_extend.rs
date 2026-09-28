use core::clone::TrivialClone;
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
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::super::kani_vec_harness_helpers::*;
    use super::*;

    // Harnesses for `Vec::spec_extend` with `IntoIter`
    macro_rules! gen_spec_extend_into_iter_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut vec = verifier_nondet_vec::<$ty>();
                let before_len = vec.len();
                let before_cap = vec.capacity();
                // Construct an arbitrary reachable IntoIter state directly instead
                // of consuming elements through another iterator target.
                let mut iter = verifier_nondet_into_iter::<$ty>();
                position_into_iter(&mut iter);
                let additional = iter.len();
                // Restrict only capacity-overflow and verifier-representation
                // failures. Both no-growth and real growth remain reachable.
                assume_reserve_no_capacity_overflow::<$ty>(before_len, before_cap, additional);
                let expected_len = before_len + additional;
                vec.spec_extend(iter);
                assert!(
                    vec.len() == expected_len,
                    "spec_extend<IntoIter>: destination length is incorrect"
                );
                assert!(
                    vec.capacity() >= vec.len(),
                    "spec_extend<IntoIter>: destination length exceeds capacity"
                );
                kani::cover(additional == 0, "spec_extend<IntoIter>: empty source");
                kani::cover(additional > 0, "spec_extend<IntoIter>: non-empty source");
                if core::mem::size_of::<$ty>() != 0 {
                    let spare = before_cap - before_len;
                    kani::cover(
                        additional > 0 && additional <= spare,
                        "spec_extend<IntoIter>: append without growth",
                    );
                    kani::cover(additional > spare, "spec_extend<IntoIter>: append with growth");
                }
            }
        };
    }

    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_u8, u8);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_u64, u64);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_unit, ());
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_array, [u8; 4]);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_bool, bool);
    gen_spec_extend_into_iter_harness!(harness_spec_extend_into_iter_al16, Al16);

    // Harnesses for `Vec::spec_extend` with `slice::Iter`
    macro_rules! gen_spec_extend_slice_iter_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                let mut vec = verifier_nondet_vec::<$ty>();
                let before_len = vec.len();
                let before_cap = vec.capacity();
                let source = verifier_nondet_vec::<$ty>();
                let source_len = source.len();
                // Any remaining state of slice::Iter is represented directly as
                // an arbitrary subslice, without advancing through another target.
                let start = kani::any_where(|start: &usize| *start <= source_len);
                let end = kani::any_where(|end: &usize| start <= *end && *end <= source_len);
                let iter = source[start..end].iter();
                let additional = end - start;
                // Restrict only capacity-overflow and verifier-representation
                // failures. Both no-growth and real growth remain reachable.
                assume_reserve_no_capacity_overflow::<$ty>(before_len, before_cap, additional);
                let expected_len = before_len + additional;
                vec.spec_extend(iter);
                assert!(
                    vec.len() == expected_len,
                    "spec_extend<slice::Iter>: destination length is incorrect"
                );
                assert!(
                    vec.capacity() >= vec.len(),
                    "spec_extend<slice::Iter>: destination length exceeds capacity"
                );
                assert!(
                    source.len() == source_len,
                    "spec_extend<slice::Iter>: source Vec was modified"
                );
                kani::cover(additional == 0, "spec_extend<slice::Iter>: empty source range");
                kani::cover(additional > 0, "spec_extend<slice::Iter>: non-empty source range");
                kani::cover(start > 0, "spec_extend<slice::Iter>: front-consumed state");
                kani::cover(end < source_len, "spec_extend<slice::Iter>: back-consumed state");
                kani::cover(
                    start > 0 && end < source_len,
                    "spec_extend<slice::Iter>: both ends consumed",
                );
                if core::mem::size_of::<$ty>() != 0 {
                    let spare = before_cap - before_len;
                    kani::cover(
                        additional > 0 && additional <= spare,
                        "spec_extend<slice::Iter>: append without growth",
                    );
                    kani::cover(additional > spare, "spec_extend<slice::Iter>: append with growth");
                }
            }
        };
    }

    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_u8, u8);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_u64, u64);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_unit, ());
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_array, [u8; 4]);
    gen_spec_extend_slice_iter_harness!(harness_spec_extend_slice_iter_bool, bool);
}
