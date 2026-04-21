//! This module provides abstractions that are useful for writing
//! specifications for the intrinsics. Currently it provides two abstractions: bits and
//! bit vectors.
//!
//! # Examples
//!
//! Converting an integer to a bit vector and back:
//!
//! ```rust
//! use testable_simd_models::abstractions::{bit::{Bit, MachineInteger}, bitvec::BitVec};
//!
//! // Create a BitVec from a machine integer (using the integer's bit-width)
//! let bv = BitVec::<16>::from_int(42u16);
//! println!("BitVec: {:?}", bv);
//!
//! // Convert the BitVec back into a machine integer
//! let n: u16 = bv.to_int();
//! println!("Integer: {}", n);
//!
//! assert!(n == 42);
//! ```

pub mod bit;
pub mod bitvec;
pub mod funarr;
pub mod simd;
pub mod utilities;
