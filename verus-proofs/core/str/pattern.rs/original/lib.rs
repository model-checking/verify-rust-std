// Standalone crate root added for a copy of `library/core/src/str/pattern.rs`.
// It supplies the file's `core` imports through `crate::` and `super::`, and holds
// copies of three `core` functions that `StrSearcher` calls (`char_boundary.rs`).
// `../check.sh` compiles `pattern.rs` with `../standalone.patch` applied.
#![feature(staged_api, portable_simd, stmt_expr_attributes, proc_macro_hygiene, slice_internals)]
#![unstable(feature = "extracted_pattern", issue = "none")]
#![allow(dead_code, internal_features)]

pub use core::{cmp, convert, fmt, ops, simd, slice};
// `pattern.rs` refers to `super::CharIndices`.
use core::str::CharIndices;

// Copies of `str::floor_char_boundary`, `str::ceil_char_boundary` and
// `u8::is_utf8_char_boundary`. Only `core` may add methods to `str` and `u8`,
// so the copies implement these traits instead.
mod char_boundary {
    use core::hint::assert_unchecked;

    trait StrCharBoundary {
        fn floor_char_boundary(&self, index: usize) -> usize;
        fn ceil_char_boundary(&self, index: usize) -> usize;
    }

    trait U8CharBoundary {
        fn is_utf8_char_boundary(self) -> bool;
    }

    include!("char_boundary.rs");
}

pub mod pattern;
