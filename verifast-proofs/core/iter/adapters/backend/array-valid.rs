#![crate_type = "lib"]
#![crate_name = "array_valid"]

unsafe fn shared<'a, T, const N: usize>(p: *const [T; N]) -> &'a [T; N]
//@ req thread_token(?t) &*& [?q]lifetime_token('a) &*& [_](<[T; N]>.share)('a, t, p) &*& [?r]ref_initialized(p);
//@ ens thread_token(t) &*& [q]lifetime_token('a) &*& result == p &*& [_](<[T; N]>.share)('a, t, result) &*& [r]ref_initialized(p);
//@ on_unwind_ens false;
{
    //@ reborrow_ref_(p);
    unsafe { &*p }
}

// Keep one reference-creation expression without an unsafe-block coercion.
#[allow(unsafe_op_in_unsafe_fn)]
unsafe fn exclusive<'a, T, const N: usize>(p: *mut [T; N]) -> &'a mut [T; N]
//@ req *p |-> ?values;
//@ ens *result |-> values &*& ref_mut_end_token(result, p);
//@ on_unwind_ens false;
{
    &mut *p
}
