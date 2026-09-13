#![crate_type = "lib"]
#![crate_name = "array_invalid"]

unsafe fn shared<'a, T, const N: usize>(p: *const [T; N]) -> &'a [T; N]
//@ req thread_token(?t) &*& [?q]lifetime_token('a);
//@ ens thread_token(t) &*& [q]lifetime_token('a) &*& result == p;
//@ on_unwind_ens false;
{
    unsafe { &*p }
}
