#![no_std]

use core::mem::{MaybeUninit, size_of};

pub fn wrapper_size<T>() -> usize
//@ req true;
//@ ens result == std::mem::size_of::<T>();
//@ on_unwind_ens false;
{
    if size_of::<T>() == 0 {
        let n = size_of::<MaybeUninit<T>>();
        //@ assert n == 0;
        return n;
    }
    size_of::<MaybeUninit<T>>()
}
