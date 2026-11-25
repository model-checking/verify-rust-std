#![feature(allocator_ext, maybe_uninit_slice, slice_ptr_get, box_as_ptr)]
#![allow(dead_code, unused_imports, unexpected_cfgs)]
mod alloc { pub use std::alloc::*; }
mod boxed { pub use std::boxed::Box; }
mod node;
mod mem;
mod borrow;
fn main() {}
