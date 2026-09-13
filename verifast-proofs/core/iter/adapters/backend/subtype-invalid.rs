#![allow(dead_code)]

unsafe fn missing_subtype<T0, T1, const N: usize>()
//@ req true;
//@ ens true;
{
    //@ std::mem::array_subtype::<T0, T1, N>();
}
