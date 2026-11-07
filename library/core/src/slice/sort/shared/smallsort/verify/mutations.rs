//! Deliberately changed copy for the opt-in swap control.

use super::super::*;

// Negates the exchange decision.
pub(super) unsafe fn mutant_swap_if_less<T, F>(
    v_base: *mut T,
    a_pos: usize,
    b_pos: usize,
    is_less: &mut F,
) where
    F: FnMut(&T, &T) -> bool,
{
    unsafe {
        let v_a = v_base.add(a_pos);
        let v_b = v_base.add(b_pos);

        let should_swap = !is_less(&*v_b, &*v_a);

        let v_a_swap = hint::select_unpredictable(should_swap, v_b, v_a);
        let v_b_swap = hint::select_unpredictable(should_swap, v_a, v_b);

        let v_b_swap_tmp = ManuallyDrop::new(ptr::read(v_b_swap));
        ptr::copy(v_a_swap, v_a, 1);
        ptr::copy_nonoverlapping(&*v_b_swap_tmp, v_b, 1);
    }
}
