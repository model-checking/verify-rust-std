// Ghost specs and proofs for `StrSearcher`.
// As a child of `pattern`, this module can read private searcher fields.
use super::*;
use crate::char_boundary::{ceil_char_boundary_post, floor_char_boundary_post};
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;
use vstd::slice::SliceIndexSpec;
use vstd::std_specs::cmp::OrdSpec;
use vstd::string::*;
use vstd::utf8::*;

include!("trusted.rs");
include!("max_suffix.rs");

verus! {

// ---------------------------------------------------------------------------
// `byteset_create`.
// ---------------------------------------------------------------------------

// The mask keeps `byteset_create`'s shift below 64.
pub broadcast proof fn lemma_u8_low_six_bits(byte: u8)
    ensures
        #[trigger] (byte & 0x3f) < 64,
{
    assert((byte & 0x3f) < 64) by (bit_vector);
}

// ---------------------------------------------------------------------------
// Searcher contracts: returned ranges are safe to slice.
// ---------------------------------------------------------------------------

/// Conditions for slicing `haystack[start..end]`.
pub open spec fn on_char_boundaries(haystack: &str, start: usize, end: usize) -> bool {
    &&& start <= end <= haystack.spec_bytes().len()
    &&& is_char_boundary(haystack.spec_bytes(), start as int)
    &&& is_char_boundary(haystack.spec_bytes(), end as int)
}

pub open spec fn step_on_char_boundaries(step: SearchStep, haystack: &str) -> bool {
    match step {
        SearchStep::Match(start, end) | SearchStep::Reject(start, end) =>
            on_char_boundaries(haystack, start, end),
        SearchStep::Done => true,
    }
}

pub open spec fn range_on_char_boundaries(range: Option<(usize, usize)>, haystack: &str) -> bool {
    match range {
        Some((start, end)) => on_char_boundaries(haystack, start, end),
        None => true,
    }
}

// ---------------------------------------------------------------------------
// The `StrSearcher` invariant `C`.
// ---------------------------------------------------------------------------

pub(super) open spec fn cursor_ok(haystack: Seq<u8>, position: usize) -> bool {
    position <= haystack.len() && is_char_boundary(haystack, position as int)
}

impl<'a, 'b> StrSearcher<'a, 'b> {
    /// Range safety leaves cursor ordering, empty-needle flags and byteset
    /// completeness unrestricted.
    pub(super) open spec fn inv(&self) -> bool {
        let haystack = self.haystack.spec_bytes();
        let needle = self.needle.spec_bytes();
        &&& haystack.len() <= isize::MAX
        &&& needle.len() <= isize::MAX
        &&& match self.searcher {
            StrSearcherImpl::Empty(searcher) => needle.len() == 0 && searcher.inv(haystack),
            StrSearcherImpl::Byte(searcher) => needle.len() == 1 && searcher.inv(haystack, needle),
            StrSearcherImpl::TwoWay(searcher) =>
                needle.len() >= 2 && searcher.str_inv(haystack, needle),
        }
    }
}

impl EmptyNeedle {
    pub(super) open spec fn inv(&self, haystack: Seq<u8>) -> bool {
        cursor_ok(haystack, self.position) && cursor_ok(haystack, self.end)
    }
}

impl ByteNeedle {
    pub(super) open spec fn inv(&self, haystack: Seq<u8>, needle: Seq<u8>) -> bool {
        &&& self.b == needle[0]
        &&& cursor_ok(haystack, self.position)
        &&& cursor_ok(haystack, self.end)
    }
}

// ---------------------------------------------------------------------------
// TwoWaySearcher state and output contracts.
// ---------------------------------------------------------------------------

impl TwoWaySearcher {
    pub(super) open spec fn bounds_ok(&self, haystack_length: nat, needle_length: nat) -> bool {
        &&& self.crit_pos <= needle_length
        &&& self.crit_pos_back <= needle_length
        &&& 1 <= self.period <= needle_length
        &&& self.position <= haystack_length
        &&& self.end <= haystack_length
    }

    /// Periodicity and these bounds justify cache shifts.
    /// In short-period mode, the reverse cache is empty or starts at `needle[period]`.
    pub(super) open spec fn short_period_facts(&self, needle: Seq<u8>) -> bool {
        self.memory != usize::MAX ==> {
            &&& is_period(needle, self.period as int)
            &&& self.crit_pos <= self.period
            &&& needle.len() - self.crit_pos_back <= self.period
            &&& (self.memory_back == needle.len() || self.memory_back == self.period)
        }
    }

    /// Cached needle prefix at `position`, clipped to the haystack.
    pub(super) open spec fn memory_fw_ok(&self, haystack: Seq<u8>, needle: Seq<u8>) -> bool {
        self.memory != usize::MAX ==> forall|needle_index: int|
            0 <= needle_index < self.memory && self.position + needle_index < haystack.len()
                ==> #[trigger] haystack[self.position + needle_index] == needle[needle_index]
    }

    /// Cached needle suffix ending at `end`, clipped to the haystack.
    pub(super) open spec fn memory_bw_ok(&self, haystack: Seq<u8>, needle: Seq<u8>) -> bool {
        self.memory != usize::MAX ==> forall|needle_index: int|
            self.memory_back <= needle_index < needle.len()
                && 0 <= self.end - needle.len() + needle_index
                ==> #[trigger] haystack[self.end - needle.len() + needle_index]
                    == needle[needle_index]
    }

    pub(super) open spec fn str_inv(&self, haystack: Seq<u8>, needle: Seq<u8>) -> bool {
        &&& self.bounds_ok(haystack.len(), needle.len())
        &&& self.short_period_facts(needle)
        &&& self.memory_fw_ok(haystack, needle)
        &&& self.memory_bw_ok(haystack, needle)
        &&& cursor_ok(haystack, self.position)
        &&& cursor_ok(haystack, self.end)
    }

    pub(super) open spec fn same_factorization(&self, other: &Self) -> bool {
        &&& self.crit_pos == other.crit_pos
        &&& self.crit_pos_back == other.crit_pos_back
        &&& self.period == other.period
    }

    // Keep the other direction's state unchanged so calls can be mixed.
    pub(super) open spec fn unchanged_by_next(&self, other: &Self) -> bool {
        &&& self.same_factorization(other)
        &&& self.end == other.end
        &&& self.memory_back == other.memory_back
        &&& (self.memory == usize::MAX <==> other.memory == usize::MAX)
    }

    pub(super) open spec fn unchanged_by_next_back(&self, other: &Self) -> bool {
        &&& self.same_factorization(other)
        &&& self.position == other.position
        &&& self.memory == other.memory
    }
}

/// Byte matches; UTF-8 boundaries are proved separately.
pub(super) open spec fn is_byte_match(
    haystack: Seq<u8>, needle: Seq<u8>, start: int, end: int,
) -> bool {
    &&& 0 <= start <= end <= haystack.len()
    &&& end == start + needle.len()
    &&& haystack.subrange(start, end) == needle
}

// Rejections cover cursor movement. MatchOnly rejects only at exhaustion.
pub(super) open spec fn fw_output_ok<S: TwoWayStrategy>(
    result: S::Output,
    old_position: usize,
    new_position: usize,
    haystack: Seq<u8>,
    needle: Seq<u8>,
) -> bool {
    let start = new_position as int - needle.len();
    ||| {
        &&& S::is_reject(result, old_position, new_position)
        &&& old_position <= new_position
        &&& (!S::early_reject() ==> new_position == haystack.len())
    }
    ||| {
        &&& needle.len() <= new_position
        &&& S::is_match(result, start as usize, new_position)
        &&& is_byte_match(haystack, needle, start, new_position as int)
    }
}

pub(super) open spec fn bw_output_ok<S: TwoWayStrategy>(
    result: S::Output,
    old_end: usize,
    new_end: usize,
    haystack: Seq<u8>,
    needle: Seq<u8>,
) -> bool {
    let end = new_end as int + needle.len();
    ||| {
        &&& S::is_reject(result, new_end, old_end)
        &&& new_end <= old_end
        &&& (!S::early_reject() ==> new_end == 0)
    }
    ||| {
        &&& S::is_match(result, new_end, end as usize)
        &&& is_byte_match(haystack, needle, new_end as int, end)
    }
}

// ---------------------------------------------------------------------------
// Byte comparison and periods.
// ---------------------------------------------------------------------------

/// Scan both comparison directions to choose the critical factorization.
/// `descending` compares byte values with `>` when true and `<` when false.
pub(super) open spec fn byte_before(
    first_byte: u8, second_byte: u8, descending: bool,
) -> bool {
    if descending {
        first_byte > second_byte
    } else {
        first_byte < second_byte
    }
}

/// A period can exceed the sequence length; it need not be the smallest one.
pub(super) open spec fn is_period(bytes: Seq<u8>, period: int) -> bool {
    &&& 0 < period
    &&& forall|index: int|
        0 <= index < bytes.len() - period ==> #[trigger] bytes[index] == bytes[index + period]
}

/// The constructor's prefix check extends the suffix period to the whole needle.
pub(super) proof fn lemma_period_from_factorization(
    bytes: Seq<u8>, critical_position: int, period: int,
)
    requires
        0 <= critical_position,
        critical_position + period <= bytes.len(),
        is_period(bytes.subrange(critical_position, bytes.len() as int), period),
        bytes.subrange(0, critical_position) == bytes.subrange(period, period + critical_position),
    ensures
        is_period(bytes, period),
{
    // Translate prefix and suffix indices back to the original bytes.
    broadcast use vstd::seq::lemma_seq_subrange_index_alt;
}

// ---------------------------------------------------------------------------
// UTF-8 boundaries for matches and cached bytes.
// ---------------------------------------------------------------------------

/// Skipping one UTF-8 character reaches the next boundary.
pub(super) proof fn lemma_next_char_boundary(haystack: Seq<u8>, start: int)
    requires
        valid_utf8(haystack),
        is_char_boundary(haystack, start),
        0 <= start < haystack.len(),
    ensures
        is_char_boundary(
            haystack,
            start + length_of_first_scalar(haystack.subrange(start, haystack.len() as int)),
        ),
{
    valid_utf8_split(haystack, start);
    reveal_with_fuel(valid_utf8, 2);
    let scalar_width = length_of_first_scalar(haystack.subrange(start, haystack.len() as int));
    lemma_occurrence_end_is_char_boundary(
        haystack, haystack.subrange(start, start + scalar_width), start,
    );
}

/// A valid UTF-8 match cannot end inside a character.
pub(super) proof fn lemma_occurrence_end_is_char_boundary(
    haystack: Seq<u8>, matched_bytes: Seq<u8>, start: int,
)
    requires
        valid_utf8(haystack),
        valid_utf8(matched_bytes),
        is_char_boundary(haystack, start),
        start + matched_bytes.len() <= haystack.len(),
        haystack.subrange(start, start + matched_bytes.len()) == matched_bytes,
    ensures
        is_char_boundary(haystack, start + matched_bytes.len()),
{
    valid_utf8_split(haystack, start);
    let suffix = haystack.subrange(start, haystack.len() as int);
    assert(suffix.subrange(0, matched_bytes.len() as int) =~= matched_bytes);
    is_char_boundary_start_end_of_seq(haystack);
    let end = start + matched_bytes.len();
    if !is_char_boundary(haystack, end) {
        is_char_boundary_iff_not_is_continuation_byte(haystack, end);
        // An interior endpoint would leave an invalid UTF-8 suffix.
        partial_valid_partial_invalid_utf8(suffix, matched_bytes.len() as int);
    }
}

/// A non-empty UTF-8 match starts with a leading byte and ends on a boundary.
pub(super) proof fn lemma_match_on_char_boundaries(haystack: Seq<u8>, needle: Seq<u8>, start: int)
    requires
        valid_utf8(haystack),
        valid_utf8(needle),
        needle.len() >= 1,
        is_byte_match(haystack, needle, start, start + needle.len()),
    ensures
        is_char_boundary(haystack, start),
        is_char_boundary(haystack, start + needle.len()),
{
    is_char_boundary_iff_not_is_continuation_byte(haystack, start);
    lemma_occurrence_end_is_char_boundary(haystack, needle, start);
}

// Empty needles match inside characters too, so this needs a non-empty needle.
pub(super) open spec fn occurrences_on_char_boundaries(haystack: Seq<u8>, needle: Seq<u8>) -> bool {
    needle.len() > 0 ==> forall|start: int, end: int|
        #![trigger haystack.subrange(start, end)]
        is_byte_match(haystack, needle, start, end) ==> {
            &&& is_char_boundary(haystack, start)
            &&& is_char_boundary(haystack, end)
        }
}

/// The subrange trigger lets search results use the UTF-8 boundary fact.
pub(super) proof fn lemma_str_searcher_utf8(haystack: &str, needle: &str)
    ensures
        valid_utf8(haystack.spec_bytes()),
        valid_utf8(needle.spec_bytes()),
        is_char_boundary(haystack.spec_bytes(), 0),
        is_char_boundary(haystack.spec_bytes(), haystack.spec_bytes().len() as int),
        occurrences_on_char_boundaries(haystack.spec_bytes(), needle.spec_bytes()),
{
    let haystack_bytes = haystack.spec_bytes();
    let needle_bytes = needle.spec_bytes();
    broadcast use encode_utf8_valid_utf8;
    is_char_boundary_start_end_of_seq(haystack_bytes);
    if needle_bytes.len() >= 1 {
        assert forall|start: int, end: int|
            #![trigger haystack_bytes.subrange(start, end)]
            is_byte_match(haystack_bytes, needle_bytes, start, end) implies {
                &&& is_char_boundary(haystack_bytes, start)
                &&& is_char_boundary(haystack_bytes, end)
            } by {
            lemma_match_on_char_boundaries(haystack_bytes, needle_bytes, start);
        }
    }
}

/// The encoding trigger connects `Chars`' first character to the next boundary.
pub(super) proof fn lemma_first_char_ends_on_boundary(haystack: Seq<u8>, position: int)
    requires
        valid_utf8(haystack),
        is_char_boundary(haystack, position),
    ensures
        forall|characters: Seq<char>|
            #[trigger] encode_utf8(characters) == haystack.subrange(position, haystack.len() as int)
                && characters.len() > 0
                ==> is_char_boundary(
                    haystack, position + encode_scalar(characters[0] as u32).len(),
                ),
{
    assert forall|characters: Seq<char>|
        #[trigger] encode_utf8(characters) == haystack.subrange(position, haystack.len() as int)
            && characters.len() > 0
            implies is_char_boundary(
                haystack, position + encode_scalar(characters[0] as u32).len(),
            ) by {
        encode_utf8_first_scalar(characters);
        lemma_next_char_boundary(haystack, position);
    }
}

/// The encoding trigger connects `Chars`' last character to its start boundary.
pub(super) proof fn lemma_last_char_starts_on_boundary(haystack: Seq<u8>, end: int)
    requires
        valid_utf8(haystack),
        0 <= end <= haystack.len(),
    ensures
        forall|characters: Seq<char>|
            #[trigger] encode_utf8(characters) == haystack.subrange(0, end) && characters.len() > 0
                ==> is_char_boundary(haystack, end - encode_scalar(characters.last() as u32).len()),
{
    assert forall|characters: Seq<char>|
        #[trigger] encode_utf8(characters) == haystack.subrange(0, end) && characters.len() > 0
            implies is_char_boundary(
                haystack, end - encode_scalar(characters.last() as u32).len(),
            ) by {
        let preceding_characters = characters.drop_last();
        let preceding_bytes = encode_utf8(preceding_characters);
        assert(preceding_characters.push(characters.last()) =~= characters);
        encode_utf8_push(preceding_characters, characters.last());
        assert(encode_utf8(characters) == preceding_bytes + encode_scalar(characters.last() as u32));
        assert(encode_utf8(characters).len() == end);
        encode_utf8_valid_utf8(preceding_characters);
        assert(haystack.subrange(0, preceding_bytes.len() as int) =~= preceding_bytes);
        lemma_occurrence_end_is_char_boundary(haystack, preceding_bytes, 0);
    }
}

/// The cursor is already a boundary at the haystack end.
/// Otherwise, the non-empty forward cache puts `needle[0]`, a leading byte, there.
pub(super) proof fn lemma_fw_cursor_on_boundary(
    searcher: TwoWaySearcher, haystack: Seq<u8>, needle: Seq<u8>,
)
    requires
        valid_utf8(haystack),
        valid_utf8(needle),
        needle.len() >= 1,
        searcher.position <= haystack.len(),
        searcher.memory_fw_ok(haystack, needle),
        searcher.memory != usize::MAX,
        searcher.memory > 0,
    ensures
        is_char_boundary(haystack, searcher.position as int),
{
    is_char_boundary_start_end_of_seq(haystack);
    if searcher.position < haystack.len() {
        assert(haystack[searcher.position + 0] == needle[0]);
        is_char_boundary_iff_not_is_continuation_byte(haystack, searcher.position as int);
    }
}

/// Clipping starts the known suffix at the haystack start; otherwise it needs a leading byte.
pub(super) proof fn lemma_known_suffix_ends_on_boundary(
    haystack: Seq<u8>, needle: Seq<u8>, end: int, cached_start: int,
)
    requires
        valid_utf8(haystack),
        valid_utf8(needle),
        0 <= cached_start < needle.len(),
        0 <= end - needle.len() + cached_start,
        end <= haystack.len(),
        forall|needle_index: int|
            cached_start <= needle_index < needle.len()
                ==> #[trigger] haystack[end - needle.len() + needle_index] == needle[needle_index],
        !is_continuation_byte(needle[cached_start]) || end - needle.len() + cached_start == 0,
    ensures
        is_char_boundary(haystack, end),
{
    let match_start = end - needle.len() + cached_start;
    let matched_suffix = needle.subrange(cached_start, needle.len() as int);
    is_char_boundary_iff_not_is_continuation_byte(haystack, match_start);
    is_char_boundary_iff_not_is_continuation_byte(needle, cached_start);
    valid_utf8_split(needle, cached_start);
    vstd::seq_lib::assert_seqs_equal!(
        haystack.subrange(match_start, end) == matched_suffix,
        offset => {
            assert(
                haystack[end - needle.len() + (cached_start + offset)]
                    == needle[cached_start + offset]
            );
        }
    );
    lemma_occurrence_end_is_char_boundary(haystack, matched_suffix, match_start);
}

/// The reverse cache starts at `needle[period] == needle[0]`, a leading byte,
/// or at the haystack start after clipping. Its end is therefore a boundary.
pub(super) proof fn lemma_bw_cursor_on_boundary(
    searcher: TwoWaySearcher, haystack: Seq<u8>, needle: Seq<u8>,
)
    requires
        valid_utf8(haystack),
        valid_utf8(needle),
        searcher.bounds_ok(haystack.len(), needle.len()),
        searcher.short_period_facts(needle),
        searcher.memory_bw_ok(haystack, needle),
        searcher.memory != usize::MAX,
        searcher.memory_back != needle.len(),
    ensures
        is_char_boundary(haystack, searcher.end as int),
{
    if searcher.end != 0 {
        // Start at the first cached byte that is inside the haystack.
        let cached_start = vstd::math::max(searcher.period as int, needle.len() - searcher.end);
        lemma_known_suffix_ends_on_boundary(haystack, needle, searcher.end as int, cached_start);
    }
}

} // verus!
