#![crate_type = "lib"]
#![crate_name = "nonzero_invalid"]

unsafe fn construct(value: usize) -> std::num::NonZero<usize>
//@ req true;
//@ ens result.get() == value;
//@ on_unwind_ens false;
{
    unsafe { std::num::NonZero::new_unchecked(value) }
}
