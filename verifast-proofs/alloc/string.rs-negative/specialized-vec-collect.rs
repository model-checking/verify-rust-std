#![no_std]

extern crate alloc;

use alloc::vec::{IntoIter, Vec};

pub fn collect_owned(iter: IntoIter<u8>) -> Vec<u8>
//@ req thread_token(?t) &*& <std::vec::IntoIter<u8, std::alloc::Global>>.own(t, iter);
//@ ens thread_token(t) &*& <std::vec::Vec<u8, std::alloc::Global>>.own(t, result);
//@ on_unwind_ens thread_token(t);
{
    iter.collect/*@~verify_vec_collect@*/()
}
