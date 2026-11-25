//! Ownership transfer inside the guarded root replacement in `btree::mem`.

#![allow(dead_code)]

use std::ptr;

struct PanicGuard;

//@ pred <PanicGuard>.own(t, guard) = true;

impl Drop for PanicGuard {
    fn drop(&mut self)
    //@ req true;
    //@ ens false;
    //@ on_unwind_ens false;
    {
        // The source intrinsic and the pinned toolchain's process abort
        // both terminate without unwinding.
        std::process::abort()
    }
}

// Verify the replacement transfer with the callback's ownership contract.
// The MIR comparison wraps this core with the checked aborting destructor
// and checks the guard's lifetime against btree::mem::replace.
unsafe fn replace_core<T, R, F: FnOnce(T) -> (T, R)>(v: &mut T, change: F) -> R
/*@
req thread_token(?t) &*& type_interp::<T>() &*& type_interp::<R>() &*& type_interp::<F>() &*&
    *v |-> ?old &*& <T>.own(t,old) &*& <F>.own(t,change);
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*& type_interp::<R>() &*& type_interp::<F>() &*&
    *v |-> ?new &*& <T>.own(t,new) &*& <R>.own(t,result);
@*/
//@ on_unwind_ens thread_token(t) &*& type_interp::<T>() &*& type_interp::<R>() &*& type_interp::<F>() &*& *v |-> old;
{
    let value = unsafe { ptr::read(v) };
    //@ close_tuple_1_own(t, std_tuple_1_::<T> { 0: old });
    let (new_value, ret) = change(value);
    //@ assert <(T,R)>.own(t,?replacement);
    //@ open_tuple_2_own(t,replacement);
    unsafe {
        ptr::write(v, new_value);
    }
    ret
}

fn main() {}
