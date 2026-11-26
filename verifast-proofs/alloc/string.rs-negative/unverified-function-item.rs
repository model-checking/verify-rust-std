#![no_std]

fn unchecked_by_verifast(x: u8) -> u8 {
    x
}

fn take_callback<F: FnMut(u8) -> u8>(_callback: F)
//@ req thread_token(?t) &*& <F>.own(t, _callback);
//@ ens thread_token(t);
//@ on_unwind_ens thread_token(t);
{
}

fn forward_unchecked()
//@ req thread_token(?t);
//@ ens thread_token(t);
//@ on_unwind_ens thread_token(t);
{
    //@ close <VfFunctionItem$unchecked_5fby_5fverifast>.own(t, VfFunctionItem$unchecked_5fby_5fverifast {});
    take_callback(unchecked_by_verifast);
}
