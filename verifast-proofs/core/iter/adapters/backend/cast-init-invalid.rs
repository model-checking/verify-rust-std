#![crate_type = "lib"]
#![crate_name = "cast_init_invalid"]
#![feature(cast_maybe_uninit)]

unsafe fn read_without_storage<T>(p: *mut std::mem::MaybeUninit<T>) -> T
//@ req true;
//@ ens true;
//@ on_unwind_ens false;
{
    unsafe { p.cast_init().read() }
}
