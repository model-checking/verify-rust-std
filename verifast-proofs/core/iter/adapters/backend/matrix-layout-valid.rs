#![crate_type = "lib"]
#![crate_name = "matrix_layout_valid"]

#[path = "../array_layout.rs"]
mod array_layout;
//@ use array_layout::{collapse_window, expand_window, matrix_elems, pack_array, pack_matrix, unpack_matrix};

unsafe fn round_trip<T, const N: usize>(p: *mut [[T; N]; 2])
//@ req *p |-> ?matrix;
//@ ens *p |-> ?after &*& matrix_elems(after) == matrix_elems(matrix);
//@ on_unwind_ens false;
{
    //@ unpack_matrix(p);
    //@ pack_matrix(p);
}

unsafe fn writable_window<T, const N: usize>(p: *mut [std::mem::MaybeUninit<T>; N])
//@ req *p |-> _;
//@ ens *p |-> _;
//@ on_unwind_ens false;
{
    //@ Array_to_array(p);
    //@ collapse_window::<T, N>(p as *std::mem::MaybeUninit<T>);
    //@ expand_window(p as *std::mem::MaybeUninit<[T; N]>);
    //@ pack_array(p);
}
