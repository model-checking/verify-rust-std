#![crate_type = "lib"]
#![crate_name = "add_valid"]
#![feature(core_intrinsics)]

unsafe fn successor(value: usize) -> usize
//@ req value < usize::MAX;
//@ ens result == value + 1;
//@ on_unwind_ens false;
{
    unsafe { std::intrinsics::unchecked_add(value, 1) }
}
