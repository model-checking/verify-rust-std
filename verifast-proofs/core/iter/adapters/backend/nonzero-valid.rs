#![crate_type = "lib"]
#![crate_name = "nonzero_valid"]

unsafe fn construct(value: usize) -> std::num::NonZero<usize>
//@ req 0 < value;
//@ ens result.get() == value;
//@ on_unwind_ens false;
{
    unsafe { std::num::NonZero::new_unchecked(value) }
}
