#![no_std]
#![crate_type = "lib"]
#![allow(dead_code, unused_imports, internal_features)]
#![feature(cast_maybe_uninit, core_intrinsics, staged_api, stmt_expr_attributes)]
#![stable(feature = "rust1", since = "1.0.0")]

extern crate core as std;

#[stable(feature = "rust1", since = "1.0.0")]
pub use std::{fmt, intrinsics, mem, num, ptr};

#[path = "../array_layout.rs"]
mod array_layout;
mod map_windows;
mod step_by;
