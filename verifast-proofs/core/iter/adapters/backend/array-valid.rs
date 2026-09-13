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

// Return the new reference as a raw pointer to test creation independently
// of the extra lifetime reborrow inserted when returning a mutable reference.
unsafe fn exclusive<T, const N: usize>(p: *mut [T; N]) -> *mut [T; N]
//@ req *p |-> ?values;
//@ ens *result |-> values &*& ref_mut_end_token(result, p);
//@ on_unwind_ens false;
{
    unsafe { &mut *p as *mut [T; N] }
}

unsafe fn matrix_ptr<T, const N: usize>(
    p: *const [[std::mem::MaybeUninit<T>; N]; 2],
) -> *const std::mem::MaybeUninit<T>
//@ req pointer_within_limits(p) == true &*& [?f]ref_initialized(p);
//@ ens [f]ref_initialized(p) &*& result == p as *std::mem::MaybeUninit<T>;
//@ on_unwind_ens false;
{
    //@ reborrow_ref_(p);
    unsafe { (*p).as_ptr().cast() }
}
