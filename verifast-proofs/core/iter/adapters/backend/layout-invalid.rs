#![allow(dead_code)]

unsafe fn incorrect_stride<T, const N: usize>()
//@ req true;
//@ ens std::mem::size_of(typeid([T; N])) == std::mem::size_of::<T>() * usize_of_const(typeid(N)) + 1;
{
    //@ std::mem::array_layout::<T, N>();
}
