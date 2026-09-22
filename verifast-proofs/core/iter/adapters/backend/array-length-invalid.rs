#![crate_type = "lib"]
#![crate_name = "array_length_invalid"]

unsafe fn array_len<T, const N: usize>(p: *const [T; N]) -> usize
//@ req [?f]ref_initialized(p);
//@ ens [f]ref_initialized(p) &*& result == usize_of_const(typeid(N)) + 1;
//@ on_unwind_ens false;
{
    //@ reborrow_ref_(p);
    let slice: &[T] = unsafe { &*p };
    slice.len()
}
