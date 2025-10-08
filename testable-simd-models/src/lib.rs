//! `testable-simd-models`: A Rust Model for the `core` Library
//!
//! `testable-simd-models` is a simplified, self-contained model of Rust’s `core` library. It aims to provide
//! a purely Rust-based specification of `core`'s fundamental operations, making them easier to
//! understand, analyze, and formally verify. Unlike `core`, which may rely on platform-specific
//! intrinsics and compiler magic, `core-models` expresses everything in plain Rust, prioritizing
//! clarity and explicitness over efficiency.
//!
//! ## Key Features
//!
//! - **Partial Modeling**: `core-models` includes only a subset of `core`, focusing on modeling
//!   fundamental operations rather than providing a complete replacement.
//! - **Exact Signatures**: Any item that exists in both `core-models` and `core` has the same type signature,
//!   ensuring compatibility with formal verification efforts.
//! - **Purely Functional Approach**: Where possible, `core-models` favors functional programming principles,
//!   avoiding unnecessary mutation and side effects to facilitate formal reasoning.
//! - **Explicit Implementations**: Even low-level operations, such as SIMD, are modeled explicitly using
//!   Rust constructs like bit arrays and partial maps.
//! - **Extra Abstractions**: `core-models` includes additional helper types and functions to support
//!   modeling. These extra items are marked appropriately to distinguish them from `core` definitions.
//!
//! ## Intended Use
//!
//! `testable-simd-models` is designed as a reference model for formal verification and reasoning about Rust programs.
//! By providing a readable, testable, well-specified version of `core`'s behavior, it serves as a foundation for
//! proof assistants and other verification tools.

// This recursion limit is necessary for mk! macro used for tests.
// We test functions with const generics, the macro generate a test per possible (const generic) control value.
#![recursion_limit = "4096"]
pub mod abstractions;
pub mod core_arch;

pub use core_arch as arch;
pub mod helpers;
