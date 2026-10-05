#![crate_type = "lib"]
#![crate_name = "add_overflow"]
#![feature(core_intrinsics)]

unsafe fn successor(value: usize) -> usize
//@ req true;
//@ ens true;
//@ on_unwind_ens false;
{
    unsafe { std::intrinsics::unchecked_add(value, 1) }
}
