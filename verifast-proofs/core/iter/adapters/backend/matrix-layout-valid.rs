#![crate_type = "lib"]
#![crate_name = "matrix_layout_valid"]

#[path = "../array_layout.rs"]
mod array_layout;
//@ use array_layout::{matrix_elems, pack_matrix, unpack_matrix};

unsafe fn round_trip<T, const N: usize>(p: *mut [[T; N]; 2])
//@ req *p |-> ?matrix;
//@ ens *p |-> ?after &*& matrix_elems(after) == matrix_elems(matrix);
//@ on_unwind_ens false;
{
    //@ unpack_matrix(p);
    //@ pack_matrix(p);
}
