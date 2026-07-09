// verifast_options{skip_specless_fns ignore_unwind_paths}

#![no_std]
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![feature(staged_api)]
#![feature(rustc_attrs)]
#![feature(slice_swap_unchecked)]
#![feature(slice_partition_dedup)]
#![feature(sized_type_properties)]
#![feature(core_intrinsics)]
#![feature(ub_checks)]
#![feature(const_trait_impl)]
#![feature(ptr_metadata)]
#![feature(panic_internals)]
#![feature(fmt_arguments_from_str)]

#![stable(feature = "rust1", since = "1.0.0")]

#[path = "mod.rs"]
pub mod slice;
