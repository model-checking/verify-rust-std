#![feature(adt_const_params)]
#![allow(incomplete_features, non_snake_case)]
use std::marker::ConstParamTy;

#[derive(ConstParamTy, PartialEq, Eq)]
enum AtomicOrdering { Relaxed, Release, Acquire, AcqRel, SeqCst }

fn marker<const ORDER: AtomicOrdering>() {}

mod bridge {
}

pub fn call_marker() {
    marker::<{ AtomicOrdering::Relaxed }>();
}
