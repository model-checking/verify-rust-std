#![crate_type = "lib"]
#![crate_name = "array_valid"]

unsafe fn shared<'a, T, const N: usize>(p: *const [T; N]) -> &'a [T; N]
//@ req thread_token(?t) &*& [?q]lifetime_token('a) &*& [_](<[T; N]>.share)('a, t, p);
//@ ens thread_token(t) &*& [q]lifetime_token('a) &*& result == p &*& [_](<[T; N]>.share)('a, t, result);
//@ on_unwind_ens false;
{
    unsafe { &*p }
}

unsafe fn exclusive<'a, T, const N: usize>(p: *mut [T; N]) -> &'a mut [T; N]
//@ req thread_token(?t) &*& [?q]lifetime_token('a) &*& full_borrow('a, <[T; N]>.full_borrow_content(t, p));
//@ ens thread_token(t) &*& [q]lifetime_token('a) &*& result == p &*& full_borrow('a, <[T; N]>.full_borrow_content(t, result));
//@ on_unwind_ens false;
{
    unsafe { &mut *p }
}
