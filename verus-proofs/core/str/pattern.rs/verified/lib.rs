// Standalone wrapper for a copy of `library/core/src/str/pattern.rs`.
// `../check.sh` compares its executable code with `../original/lib.rs`.
// See `../../../../README.md` for an overview and `pattern/trusted.rs` for assumptions.
#![feature(staged_api, portable_simd, proc_macro_hygiene, slice_internals)]
#![unstable(feature = "extracted_pattern", issue = "none")]
#![allow(dead_code, internal_features)]
#![verifier::allow(autoderive_clone_without_spec)]

#[macro_use]
extern crate verus_builtin_macros;

pub use core::{cmp, convert, fmt, ops, simd, slice};
// `pattern.rs` refers to `super::CharIndices`.
use core::str::CharIndices;

// Verify copies of `str::{floor_char_boundary, ceil_char_boundary}` and
// `u8::is_utf8_char_boundary`. `pattern/trusted.rs` attaches the `str` contracts
// to std. Traits are needed because only `core` may add methods to `str` and `u8`.
mod char_boundary {
    #[cfg(verus_keep_ghost)]
    use vstd::{math::min, prelude::*, string::*, utf8::*};
    #[cfg(verus_keep_ghost)]
    use crate::pattern::proof::axiom_str_len_le_isize_max;
    use core::hint::assert_unchecked;

    #[verus_verify]
    trait StrCharBoundary {
        verus! {
        spec fn bytes(&self) -> Seq<u8>;
        }
        #[verus_spec(result => ensures floor_char_boundary_post(self.bytes(), index, result))]
        fn floor_char_boundary(&self, index: usize) -> usize;
        #[verus_spec(result => ensures ceil_char_boundary_post(self.bytes(), index, result))]
        fn ceil_char_boundary(&self, index: usize) -> usize;
    }

    #[verus_verify]
    trait U8CharBoundary {
        verus! {
        spec fn byte(&self) -> u8;
        }
        #[verus_spec(result => ensures result == !is_continuation_byte(self.byte()))]
        fn is_utf8_char_boundary(self) -> bool;
    }

    include!("char_boundary.rs");

    verus! {

    /// Least char boundary at or above `min(index, bytes.len())`.
    pub open spec fn ceil_char_boundary_post(bytes: Seq<u8>, index: usize, result: usize) -> bool {
        let limit = min(index as int, bytes.len() as int);
        &&& limit <= result <= bytes.len()
        &&& is_char_boundary(bytes, result as int)
        &&& forall|candidate_index: int|
            limit <= candidate_index < result
                ==> !#[trigger] is_char_boundary(bytes, candidate_index)
    }

    /// Greatest char boundary at or below `min(index, bytes.len())`.
    pub open spec fn floor_char_boundary_post(bytes: Seq<u8>, index: usize, result: usize) -> bool {
        let limit = min(index as int, bytes.len() as int);
        &&& result <= limit
        &&& is_char_boundary(bytes, result as int)
        &&& forall|candidate_index: int|
            result < candidate_index <= limit
                ==> !#[trigger] is_char_boundary(bytes, candidate_index)
    }

    /// Relate vstd's character sequence to UTF-8 byte boundaries.
    proof fn lemma_str_char_boundaries(text: &str)
        ensures
            valid_utf8(text.spec_bytes()),
            is_char_boundary(text.spec_bytes(), 0),
            is_char_boundary(text.spec_bytes(), text.spec_bytes().len() as int),
            forall|byte_index: int|
                0 <= byte_index < text.spec_bytes().len()
                    ==> (#[trigger] is_char_boundary(text.spec_bytes(), byte_index)
                        <==> !is_continuation_byte(text.spec_bytes()[byte_index])),
    {
        let bytes = text.spec_bytes();
        encode_utf8_valid_utf8(text@);
        is_char_boundary_start_end_of_seq(bytes);
        assert forall|byte_index: int| 0 <= byte_index < bytes.len()
            implies (#[trigger] is_char_boundary(bytes, byte_index)
                <==> !is_continuation_byte(bytes[byte_index])) by {
            is_char_boundary_iff_not_is_continuation_byte(bytes, byte_index);
        }
    }

    /// UTF-8 scalars use at most four bytes, so an interior index is within three
    /// bytes of both boundaries.
    proof fn lemma_enclosing_char_boundaries(bytes: Seq<u8>, index: int) -> (bounds: (int, int))
        requires
            valid_utf8(bytes),
            0 <= index <= bytes.len(),
        ensures
            0 <= bounds.0 <= index <= bounds.1 <= bytes.len(),
            is_char_boundary(bytes, bounds.0),
            is_char_boundary(bytes, bounds.1),
            bounds.1 - bounds.0 <= 4,
            if is_char_boundary(bytes, index) {
                bounds == (index, index)
            } else {
                bounds.0 < index < bounds.1
            },
        decreases bytes.len(),
    {
        reveal_with_fuel(is_char_boundary, 2);
        if index == 0 {
            (0, 0)
        } else {
            let scalar_width = length_of_first_scalar(bytes);
            let remaining_bytes = pop_first_scalar(bytes);
            if index < scalar_width {
                is_char_boundary_start_end_of_seq(remaining_bytes);
                (0, scalar_width)
            } else {
                // Translate the suffix's boundaries back to the original byte indices.
                let (lower_boundary, upper_boundary) = lemma_enclosing_char_boundaries(
                    remaining_bytes, index - scalar_width,
                );
                (lower_boundary + scalar_width, upper_boundary + scalar_width)
            }
        }
    }

    } // verus!
}

pub mod pattern;
