#![no_std]

fn disjoint_types<'a>(select_static: bool, _borrowed: &'a u8)
//@ req thread_token(?t);
//@ ens thread_token(t);
//@ on_unwind_ens false;
{
    // A None value can inhabit the slot at either lifetime. The address is
    // allocated before the branch, when the slot's MIR lifetime is erased.
    let mut value: Option<&u8>;
    if select_static {
        value = None;
        //@ assert [1/2]points_to::<std::option::Option<&'static u8>>(&value, _);
    } else {
        value = None;
        //@ assert [1/2]points_to::<std::option::Option<&'a u8>>(&value, _);
    }
}
