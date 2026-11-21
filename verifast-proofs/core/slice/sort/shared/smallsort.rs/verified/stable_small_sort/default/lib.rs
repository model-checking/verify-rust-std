// verifast_options{skip_specless_fns}

// Standalone crate wrapping core's `slice::sort::shared::smallsort` module
// (library/core/src/slice/sort/shared/smallsort.rs) so that VeriFast can verify it.
// The module refers to `crate::mem`, `crate::{hint, intrinsics, ptr, slice}` and
// `crate::slice::sort::shared::FreezeMarker`; this crate root provides exactly those paths.

#![no_std]
#![allow(dead_code)]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![allow(unexpected_cfgs)]
#![feature(core_intrinsics)]
#![feature(freeze)]
#![feature(rustc_attrs)]
#![feature(specialization)]

pub use core::{hint, mem, ptr};

pub mod intrinsics {
    pub use core::intrinsics::*;

    // `core::intrinsics::abort_immediate` is newer than the nightly VeriFast 26.10 is built on
    // (nightly-2026-09-25), whose `core` only has `abort`. Both abort the process immediately.
    // This is a re-export only; no code is added.
    pub use core::intrinsics::abort as abort_immediate;
}

pub mod slice {
    pub use core::slice::*;

    pub mod sort {
        pub mod shared {
            use core::marker::Freeze;

            // Copied from library/core/src/slice/sort/shared/mod.rs.
            /// SAFETY: this is safety relevant, how does this interact with the soundness holes in
            /// specialization?
            #[unsafe(rustc_allow_lifetime_dependent_specialization)]
            pub(crate) trait FreezeMarker {}

            impl<T: Freeze> FreezeMarker for T {}
        }
    }
}

// The module only refers to other items through absolute `crate::` paths, so it can live at the
// crate root.
pub mod smallsort;
