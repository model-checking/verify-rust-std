// Trusted items added by this proof. Verus and vstd are also trusted.

verus! {

// ---------------------------------------------------------------------------
// 1. Challenge assumptions: `slice` functions are correct.
// ---------------------------------------------------------------------------

// Safety needs only bounds and byte equality for a returned index.
pub assume_specification[ core::slice::memchr::memchr ](byte: u8, text: &[u8]) -> (result: Option<usize>)
    ensures
        match result {
            Some(index) => {
                &&& index < text@.len()
                &&& text@[index as int] == byte
            },
            None => true,
        },
;

pub assume_specification[ core::slice::memchr::memrchr ](byte: u8, text: &[u8]) -> (result: Option<usize>)
    ensures
        match result {
            Some(index) => {
                &&& index < text@.len()
                &&& text@[index as int] == byte
            },
            None => true,
        },
;

// ---------------------------------------------------------------------------
// 2. Missing vstd specs and facts.
// ---------------------------------------------------------------------------

// A false condition makes `assert_unchecked` undefined behavior.
pub assume_specification[ core::hint::assert_unchecked ](condition: bool)
    requires
        condition,
;

// str indexing delegates to `SliceIndex::index`, as slice indexing does.
// vstd has the precondition; this forwards the missing postcondition.
pub assume_specification<I: core::slice::SliceIndex<str>>[ <str as core::ops::Index<I>>::index ](
    text: &str,
    index: I,
) -> (result: &<I as core::slice::SliceIndex<str>>::Output)
    ensures
        call_ensures(<I as core::slice::SliceIndex<str>>::index, (index, text), result),
;

/// A Rust string reference spans at most `isize::MAX` bytes.
pub(crate) axiom fn axiom_str_len_le_isize_max(text: &str)
    ensures
        text.spec_bytes().len() <= isize::MAX,
;

// ---------------------------------------------------------------------------
// 3. Contracts proved for library copies.
// ---------------------------------------------------------------------------

// Verus checks library copies because these core methods are outside the crate.
// `../../check.sh` compares the copies with `library/`; they must stay in sync.
// We trust the linked core to satisfy the copies' proved contracts.
pub assume_specification[ str::ceil_char_boundary ](text: &str, index: usize) -> (result: usize)
    ensures
        ceil_char_boundary_post(text.spec_bytes(), index, result),
;

pub assume_specification[ str::floor_char_boundary ](text: &str, index: usize) -> (result: usize)
    ensures
        floor_char_boundary_post(text.spec_bytes(), index, result),
;

// ---------------------------------------------------------------------------
// 4. Verus cannot verify empty enums as datatypes.
//    The strategy markers are opaque, with no added facts.
// ---------------------------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
pub(super) struct ExMatchOnly(MatchOnly);

#[verifier::external_type_specification]
#[verifier::external_body]
pub(super) struct ExRejectAndMatch(RejectAndMatch);

} // verus!
