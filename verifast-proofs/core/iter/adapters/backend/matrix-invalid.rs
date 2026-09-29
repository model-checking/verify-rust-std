#![crate_type = "lib"]
#![crate_name = "matrix_invalid"]

unsafe fn matrix_ptr<T, const N: usize>(
    p: *const [[std::mem::MaybeUninit<T>; N]; 2],
) -> *const std::mem::MaybeUninit<T>
//@ req pointer_within_limits(p) == true;
//@ ens result == p as *std::mem::MaybeUninit<T>;
//@ on_unwind_ens false;
{
    unsafe { (*p).as_ptr().cast() }
}
