#![feature(core_intrinsics, staged_api, rustc_attrs, cfg_target_has_atomic, cfg_target_has_atomic_equal_alignment, decl_macro, const_trait_impl, const_convert, deprecated_suggestion)]
#![allow(internal_features)]
#![stable(feature = "atomic_source_proof", since = "1.0.0")]
use core::{cell, fmt, hint, intrinsics, ptr};
pub mod atomic;
