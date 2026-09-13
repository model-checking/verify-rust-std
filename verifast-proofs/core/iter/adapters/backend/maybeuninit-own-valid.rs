#![crate_type = "lib"]
#![crate_name = "maybeuninit_own_valid"]

unsafe fn wrapper_ownership<T>(p: *mut std::mem::MaybeUninit<T>)
//@ req thread_token(?t) &*& *p |-> ?value;
//@ ens thread_token(t) &*& *p |-> value &*& <std::mem::MaybeUninit<T>>.own(t, value);
//@ on_unwind_ens false;
{
    //@ std::mem::MaybeUninit_own_init(t, value);
}
