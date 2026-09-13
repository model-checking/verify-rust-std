#![crate_type = "lib"]
#![crate_name = "array_mut_invalid"]

unsafe fn exclusive<T, const N: usize>(p: *mut [T; N]) -> *mut [T; N]
//@ req true;
//@ ens true;
//@ on_unwind_ens false;
{
    unsafe { &mut *p as *mut [T; N] }
}
