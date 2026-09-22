#![crate_type = "lib"]
#![crate_name = "array_invalid"]

unsafe fn shared<'a, T, const N: usize>(p: *const [T; N]) -> &'a [T; N]
//@ req thread_token(?t) &*& [?q]lifetime_token('a) &*& [?r]ref_initialized(p);
//@ ens thread_token(t) &*& [q]lifetime_token('a) &*& result == p &*& [_](<[T; N]>.share)('a, t, result) &*& [r]ref_initialized(p);
//@ on_unwind_ens false;
{
    //@ reborrow_ref_(p);
    unsafe { &*p }
}
