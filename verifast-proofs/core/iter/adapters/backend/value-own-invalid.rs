#![crate_type = "lib"]
#![crate_name = "value_own_invalid"]

unsafe fn missing_value_ownership<T>(p: *mut T)
//@ req thread_token(?t) &*& *p |-> ?value;
//@ ens thread_token(t) &*& *p |-> value &*& <T>.own(t, value);
//@ on_unwind_ens false;
{
}
