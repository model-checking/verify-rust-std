//! Logical-value correctness through real trait entries; no contracts or panic paths are stubbed.

use super::super::{
    SMALL_SORT_GENERAL_SCRATCH_LEN, StableSmallSortTypeImpl, UnstableSmallSortTypeImpl,
};
use crate::cell::Cell;
use crate::kani;
use crate::mem::MaybeUninit;

trait LogicalByte {
    fn new(value: u8) -> Self;
    fn value(&self) -> u8;
}

impl LogicalByte for Cell<u8> {
    fn new(value: u8) -> Self {
        Cell::new(value)
    }

    fn value(&self) -> u8 {
        self.get()
    }
}

#[repr(transparent)]
struct DropKey(u8);

impl crate::ops::Drop for DropKey {
    fn drop(&mut self) {}
}

impl LogicalByte for DropKey {
    fn new(value: u8) -> Self {
        Self(value)
    }

    fn value(&self) -> u8 {
        self.0
    }
}

fn logical_less<T: LogicalByte>(a: &T, b: &T) -> bool {
    a.value() < b.value()
}

fn count(values: &[u8], probe: u8) -> usize {
    let mut count = 0;
    for value in values {
        count += (*value == probe) as usize;
    }
    count
}

fn check_output<const N: usize>(input: &[u8; N], output: &[u8; N], probe: u8) {
    for i in 1..N {
        assert!(output[i - 1] <= output[i]);
    }
    assert!(count(input, probe) == count(output, probe));
    kani::cover(true, "logical sort returns after both assertions");
}

fn cover_nontrivial_input<const N: usize>(input: &[u8; N]) {
    kani::cover(input[0] > input[1], "logical sort returns from an unsorted input");
    kani::cover(input[0] == input[1], "logical sort returns with duplicate keys");
}

// Cell is !Freeze: both trait defaults use insertion or fallback, with threshold 16.
// DropKey is Freeze and non-Copy: stable and unstable dispatch select general, threshold 32.
fn trait_properties<T: LogicalByte, const N: usize>() -> [u8; N] {
    let input: [u8; N] = kani::any();
    let probe: u8 = kani::any();
    let mut values: [T; N] = crate::array::from_fn(|i| T::new(input[i]));
    let stable: bool = kani::any();
    if stable {
        let mut scratch = [const { MaybeUninit::<T>::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        <T as StableSmallSortTypeImpl>::small_sort(
            &mut values,
            &mut scratch,
            &mut logical_less::<T>,
        );
    } else {
        <T as UnstableSmallSortTypeImpl>::small_sort(&mut values, &mut logical_less::<T>);
    }
    let output = crate::array::from_fn(|i| values[i].value());
    check_output(&input, &output, probe);
    kani::cover(stable, "logical stable trait entry returns");
    kani::cover(!stable, "logical unstable trait entry returns");
    input
}

fn trivial_trait_properties<T: LogicalByte>() {
    let selector: u8 = kani::any();
    match selector {
        0 => {
            trait_properties::<T, 0>();
        }
        1 => {
            trait_properties::<T, 1>();
        }
        _ => cover_nontrivial_input(&trait_properties::<T, 2>()),
    }
    kani::cover(selector == 0, "logical length zero");
    kani::cover(selector == 1, "logical length one");
    kani::cover(selector == 2, "logical length two");
}

// The unwind budget covers element construction, sorting, and logical-value count loops.
// Solver choice is specific to these logical-value models.
macro_rules! trait_cases {
    ($name:ident, $t:ty, [0, 1, 2]) => {
        #[kani::proof]
        #[kani::solver(cadical)]
        #[kani::unwind(50)]
        fn $name() {
            trivial_trait_properties::<$t>();
        }
    };
}

trait_cases!(sorted_permutation_traits_fallback_cell_u8_n0_to2, Cell<u8>, [0, 1, 2]);
trait_cases!(sorted_permutation_traits_general_drop_u8_n0_to2, DropKey, [0, 1, 2]);

macro_rules! fixed_trait_case {
    ($name:ident, $t:ty, $n:literal) => {
        #[kani::proof]
        #[kani::solver(cadical)]
        #[kani::unwind(50)]
        fn $name() {
            cover_nontrivial_input(&trait_properties::<$t, $n>());
        }
    };
}

// A single length keeps solver time within the ordinary budget.
fixed_trait_case!(sorted_permutation_traits_fallback_cell_u8_n7, Cell<u8>, 7);

fixed_trait_case!(sorted_permutation_traits_general_drop_u8_n8, DropKey, 8);

// Fixed routes check each Cell branch independently.
// The two const values cover both dispatch choices without restricting keys.
fn fixed_route_trait_properties<T: LogicalByte, const N: usize, const STABLE: bool>() {
    let input: [u8; N] = kani::any();
    let probe: u8 = kani::any();
    let mut values: [T; N] = crate::array::from_fn(|i| T::new(input[i]));
    if STABLE {
        let mut scratch = [const { MaybeUninit::<T>::uninit() }; SMALL_SORT_GENERAL_SCRATCH_LEN];
        <T as StableSmallSortTypeImpl>::small_sort(
            &mut values,
            &mut scratch,
            &mut logical_less::<T>,
        );
    } else {
        <T as UnstableSmallSortTypeImpl>::small_sort(&mut values, &mut logical_less::<T>);
    }
    let output = crate::array::from_fn(|i| values[i].value());
    check_output(&input, &output, probe);
    cover_nontrivial_input(&input);
}

macro_rules! fixed_route_trait_case {
    ($name:ident, $t:ty, $n:literal, $stable:literal) => {
        #[kani::proof]
        #[kani::solver(cadical)]
        #[kani::unwind(50)]
        fn $name() {
            fixed_route_trait_properties::<$t, $n, $stable>();
            // Emit only the selected route's cover; the opposite const branch cannot return.
            kani::cover(true, concat!("logical fixed trait entry returns: stable=", $stable));
        }
    };
}

fixed_route_trait_case!(sorted_permutation_traits_stable_fallback_cell_u8_n8, Cell<u8>, 8, true);
fixed_route_trait_case!(sorted_permutation_traits_unstable_fallback_cell_u8_n8, Cell<u8>, 8, false);
