#![crate_type = "lib"]
#![crate_name = "array_mut_invalid"]

unsafe fn exclusive<'a, T, const N: usize>(p: *mut [T; N]) -> &'a mut [T; N]
//@ req thread_token(?t) &*& [?q]lifetime_token('a);
//@ ens thread_token(t) &*& [q]lifetime_token('a);
//@ on_unwind_ens false;
{
    unsafe { &mut *p }
}
