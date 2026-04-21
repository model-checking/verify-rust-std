//! Rust models for ARM intrinsics.
//!
//! This module contains models for the intrinsics as they are defined in the Rust core.
//! Since this is supposed to model the Rust core, the implemented functions must
//! mirror the Rust implementations as closely as they can.
//!
//! For example, calls to simd functions like simd_add and simd_sub are left as is,
//! with their implementations defined in `crate::abstractions::simd`. Some other
//! operations like simd_cast or simd_shuffle might need a little modification
//! for correct compilation.
//!
//! Calls to transmute are replaced with either an explicit call to a `BitVec::from_ function`,
//! or with `.into()`.
//!
//! Sometimes, an intrinsic in Rust is implemented by directly using the corresponding
//! LLVM instruction via an `unsafe extern "C"` module. In those cases, the corresponding
//! function is defined in the `c_extern` module in each file, which contain manually
//! written implementations made by consulting the appropriate Intel documentation.
//!
//! In general, it is best to gain an idea of how an implementation should be written by looking
//! at how other functions are implemented. Also see `core::arch::arm` for [reference](https://github.com/rust-lang/stdarch/tree/master/crates/core_arch).
#![allow(unused)]
#[allow(non_camel_case_types)]
mod types {
    use crate::abstractions::simd::*;
    pub type int32x4_t = i32x4;
    pub type int64x1_t = i64x1;
    pub type int64x2_t = i64x2;
    pub type int16x8_t = i16x8;
    pub type int8x16_t = i8x16;
    pub type uint32x4_t = u32x4;
    pub type uint64x1_t = u64x1;
    pub type uint64x2_t = u64x2;
    pub type uint16x8_t = u16x8;
    pub type uint8x16_t = u8x16;
    pub type int32x2_t = i32x2;
    pub type int16x4_t = i16x4;
    pub type int8x8_t = i8x8;
    pub type uint32x2_t = u32x2;
    pub type uint16x4_t = u16x4;
    pub type uint8x8_t = u8x8;
}

pub mod neon;
