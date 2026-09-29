#![crate_type = "lib"]
#![crate_name = "cast_init_valid"]
#![feature(cast_maybe_uninit)]

unsafe fn cast_pointer<T>(p: *mut std::mem::MaybeUninit<T>) -> *mut T
//@ req true;
//@ ens result == p as *T;
//@ on_unwind_ens false;
{
    p.cast_init()
}
