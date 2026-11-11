// `maximal_suffix` finds the forward split and suffix period.
// `reverse_maximal_suffix` finds the backward split, stopping at the known
// period. Each runs with ascending and descending byte comparisons.
//
// Reversed bytes let the reverse scan share the forward scan's proof.
// We prove the bounds needed for search safety. Included from `proof.rs`.

verus! {

// ---------------------------------------------------------------------------
// Suffix comparisons.
// ---------------------------------------------------------------------------

/// Matching prefixes of two suffixes.
pub(super) open spec fn agree(
    bytes: Seq<u8>, candidate_start: int, reference_start: int, prefix_length: int,
) -> bool {
    forall|byte_offset: int| 0 <= byte_offset < prefix_length ==>
        #[trigger] bytes[candidate_start + byte_offset] == bytes[reference_start + byte_offset]
}

/// The first differing byte puts the candidate before the reference.
pub(super) open spec fn below_at(
    bytes: Seq<u8>, candidate_start: int, reference_start: int,
    mismatch_offset: int, descending: bool,
) -> bool {
    &&& agree(bytes, candidate_start, reference_start, mismatch_offset)
    &&& byte_before(
        bytes[candidate_start + mismatch_offset], bytes[reference_start + mismatch_offset],
        descending,
    )
}

/// The candidate loses at a byte already scanned.
pub(super) open spec fn below_within(
    bytes: Seq<u8>, candidate_start: int, reference_start: int,
    scanned_end: int, descending: bool,
) -> bool {
    exists|mismatch_offset: int|
        0 <= mismatch_offset < scanned_end - candidate_start
            && #[trigger] below_at(bytes, candidate_start, reference_start, mismatch_offset, descending)
}

/// Earlier suffixes are longer, so a losing comparison needs a mismatch.
/// The mismatch must be inside both suffixes.
pub(super) open spec fn suffix_less(
    bytes: Seq<u8>, candidate_start: int, reference_start: int, descending: bool,
) -> bool {
    exists|mismatch_offset: int|
        0 <= mismatch_offset
            && candidate_start + mismatch_offset < bytes.len()
            && reference_start + mismatch_offset < bytes.len()
            && #[trigger] below_at(bytes, candidate_start, reference_start, mismatch_offset, descending)
}

/// Suffix order is transitive; use the earlier mismatch.
pub(super) proof fn lemma_suffix_less_trans(
    bytes: Seq<u8>, first_start: int, middle_start: int, last_start: int, descending: bool,
)
    requires
        0 <= first_start < middle_start < last_start < bytes.len(),
        suffix_less(bytes, first_start, middle_start, descending),
        suffix_less(bytes, middle_start, last_start, descending),
    ensures
        suffix_less(bytes, first_start, last_start, descending),
{
    let first_mismatch = choose|mismatch: int|
        0 <= mismatch
            && middle_start + mismatch < bytes.len()
            && #[trigger] below_at(bytes, first_start, middle_start, mismatch, descending);
    let second_mismatch = choose|mismatch: int|
        0 <= mismatch
            && last_start + mismatch < bytes.len()
            && #[trigger] below_at(bytes, middle_start, last_start, mismatch, descending);
    let earliest_mismatch = vstd::math::min(first_mismatch, second_mismatch);
    assert(below_at(bytes, first_start, last_start, earliest_mismatch, descending));
}

// ---------------------------------------------------------------------------
// The scan invariant.
// ---------------------------------------------------------------------------

/// A byte equals its representative in the first period block.
pub(super) open spec fn in_phase(bytes: Seq<u8>, left: int, period: int, byte_index: int) -> bool {
    bytes[byte_index] == bytes[left + (byte_index - left) % period]
}

pub(super) open spec fn periodic_prefix(bytes: Seq<u8>, left: int, period: int, scanned_end: int) -> bool {
    forall|byte_index: int|
        left <= byte_index < scanned_end ==> #[trigger] in_phase(bytes, left, period, byte_index)
}

/// Let `scanned_end = right + offset`.
/// - `bytes[left..scanned_end]` repeats the first period block.
/// - Other starts in that block lose within the scanned prefix.
/// - Starts before `left` lose to its complete suffix.
///
/// Example: `bytes = b"ababab"`, `left = 0`, `right = 4`, `offset = 1`, `period = 2`
/// scans `b"ababa"`: two `b"ab"` blocks and `b"a"`. With descending comparisons,
/// the start at 1 loses at `b'b'` versus `b'a'`.
pub(super) open spec fn suffix_scan_inv(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool,
) -> bool {
    &&& 0 <= left
    &&& 0 <= offset < period
    &&& left + period <= right
    &&& right + offset <= bytes.len()
    &&& (right - left) % period == 0
    &&& periodic_prefix(bytes, left, period, right + offset)
    &&& forall|candidate_start: int| left < candidate_start < left + period ==>
        #[trigger] below_within(bytes, candidate_start, left, right + offset, descending)
    &&& forall|candidate_start: int| 0 <= candidate_start < left ==>
        #[trigger] suffix_less(bytes, candidate_start, left, descending)
}

/// Starts at the same phase have equal bytes at the same offset.
pub(super) proof fn lemma_same_phase(
    bytes: Seq<u8>, left: int, period: int, scanned_end: int,
    first_start: int, second_start: int, byte_offset: int,
)
    requires
        0 < period,
        periodic_prefix(bytes, left, period, scanned_end),
        left <= first_start,
        left <= second_start,
        0 <= byte_offset,
        first_start + byte_offset < scanned_end,
        second_start + byte_offset < scanned_end,
        (first_start - left) % period == (second_start - left) % period,
    ensures
        bytes[first_start + byte_offset] == bytes[second_start + byte_offset],
{
    assert(in_phase(bytes, left, period, first_start + byte_offset));
    assert(in_phase(bytes, left, period, second_start + byte_offset));
    lemma_add_mod_noop(first_start - left, byte_offset, period);
    lemma_add_mod_noop(second_start - left, byte_offset, period);
}

/// Copy the representative's known prefix and next byte to this start.
pub(super) proof fn lemma_transfer_phase_prefix(
    bytes: Seq<u8>, left: int, period: int, scanned_end: int,
    candidate_start: int, prefix_length: int,
)
    requires
        0 < period,
        periodic_prefix(bytes, left, period, scanned_end),
        0 <= left <= candidate_start,
        scanned_end <= bytes.len(),
        0 <= prefix_length <= scanned_end - candidate_start,
        agree(bytes, left + (candidate_start - left) % period, left, prefix_length),
    ensures
        agree(bytes, candidate_start, left, prefix_length),
        candidate_start + prefix_length < scanned_end ==> bytes[candidate_start + prefix_length]
            == bytes[left + (candidate_start - left) % period + prefix_length],
{
    let representative_start = left + (candidate_start - left) % period;
    if candidate_start - left < period {
        lemma_small_mod((candidate_start - left) as nat, period as nat);
    }
    lemma_mod_twice(candidate_start - left, period);
    assert forall|byte_offset: int| 0 <= byte_offset < prefix_length
        implies #[trigger] bytes[candidate_start + byte_offset] == bytes[left + byte_offset] by {
        lemma_same_phase(bytes, left, period, scanned_end, candidate_start, representative_start, byte_offset);
    }
    if candidate_start + prefix_length < scanned_end {
        lemma_same_phase(bytes, left, period, scanned_end, candidate_start, representative_start, prefix_length);
    }
}

/// Moving from a candidate start to the scan end reaches phase `offset`.
pub(super) proof fn lemma_phase_of_offset(
    left: int, right: int, offset: int, period: int,
    candidate_start: int, phase: int,
)
    requires
        0 <= offset < period,
        (right - left) % period == 0,
        (candidate_start - left) % period == phase,
    ensures
        (phase + (right + offset - candidate_start)) % period == offset,
{
    lemma_add_mod_noop_right(right + offset - candidate_start, candidate_start - left, period);
    lemma_add_mod_noop(right - left, offset, period);
    lemma_small_mod(offset as nat, period as nat);
}

// ---------------------------------------------------------------------------
// Preserve the invariant in each comparison branch.
// ---------------------------------------------------------------------------

/// In the smaller branch, every scanned start after `left` loses.
pub(super) proof fn lemma_ms_smaller_at(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool, candidate_start: int,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        right + offset < bytes.len(),
        byte_before(bytes[right + offset], bytes[left + offset], descending),
        left < candidate_start <= right + offset,
    ensures
        below_within(bytes, candidate_start, left, right + offset + 1, descending),
{
    let scanned_end = right + offset;
    let phase = (candidate_start - left) % period;
    let representative_start = left + phase;
    let representative_mismatch_offset = if phase == 0 {
        scanned_end - candidate_start
    } else {
        assert(below_within(bytes, representative_start, left, scanned_end, descending));
        choose|representative_mismatch_offset: int|
            0 <= representative_mismatch_offset < scanned_end - representative_start
                && #[trigger] below_at(
                    bytes, representative_start, left, representative_mismatch_offset, descending,
                )
    };
    let mismatch_offset = vstd::math::min(representative_mismatch_offset, scanned_end - candidate_start);
    lemma_transfer_phase_prefix(bytes, left, period, scanned_end, candidate_start, mismatch_offset);
    if mismatch_offset == scanned_end - candidate_start {
        // At the old scan end, the new byte decides the comparison.
        lemma_phase_of_offset(left, right, offset, period, candidate_start, phase);
        assert(in_phase(bytes, left, period, representative_start + mismatch_offset));
    }
    assert(below_at(bytes, candidate_start, left, mismatch_offset, descending));
}

/// Reset the period to the whole scanned suffix.
pub(super) proof fn lemma_ms_smaller(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        right + offset < bytes.len(),
        byte_before(bytes[right + offset], bytes[left + offset], descending),
    ensures
        suffix_scan_inv(bytes, left, right + offset + 1, 0, right + offset + 1 - left, descending),
{
    let scanned_end = right + offset;
    let next_period = scanned_end + 1 - left;
    assert(periodic_prefix(bytes, left, next_period, scanned_end + 1)) by {
        assert forall|byte_index: int| left <= byte_index < scanned_end + 1
            implies #[trigger] in_phase(bytes, left, next_period, byte_index) by {
            lemma_small_mod((byte_index - left) as nat, next_period as nat);
        }
    }
    assert forall|candidate_start: int| left < candidate_start < left + next_period
        implies #[trigger] below_within(bytes, candidate_start, left, scanned_end + 1, descending) by {
        lemma_ms_smaller_at(bytes, left, right, offset, period, descending, candidate_start);
    }
}

/// Keep the period and advance to the next byte or block.
pub(super) proof fn lemma_ms_equal(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        right + offset < bytes.len(),
        bytes[right + offset] == bytes[left + offset],
    ensures
        offset + 1 == period ==> suffix_scan_inv(bytes, left, right + period, 0, period, descending),
        offset + 1 < period ==> suffix_scan_inv(bytes, left, right, offset + 1, period, descending),
{
    let scanned_end = right + offset;
    // The new byte is at phase `offset`.
    lemma_add_mod_noop(right - left, offset, period);
    lemma_small_mod(offset as nat, period as nat);
    assert(periodic_prefix(bytes, left, period, scanned_end + 1));
    assert forall|candidate_start: int| left < candidate_start < left + period
        implies #[trigger] below_within(bytes, candidate_start, left, scanned_end + 1, descending) by {
        // Old mismatches remain valid after extending the prefix.
        assert(below_within(bytes, candidate_start, left, scanned_end, descending));
    }
    if offset + 1 == period {
        lemma_mod_add_multiples_vanish(right - left, period);
    }
}

/// The suffix at `right` beats every start from `left` up to `right`.
pub(super) proof fn lemma_ms_beats(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool, candidate_start: int,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        right + offset < bytes.len(),
        byte_before(bytes[left + offset], bytes[right + offset], descending),
        left <= candidate_start < right,
    ensures
        suffix_less(bytes, candidate_start, right, descending),
{
    let scanned_end = right + offset;
    let phase = (candidate_start - left) % period;
    let representative_start = left + phase;
    let representative_mismatch_offset = if phase == 0 {
        offset
    } else {
        assert(below_within(bytes, representative_start, left, scanned_end, descending));
        choose|representative_mismatch_offset: int|
            0 <= representative_mismatch_offset < scanned_end - representative_start
                && #[trigger] below_at(
                    bytes, representative_start, left, representative_mismatch_offset, descending,
                )
    };
    let mismatch_offset = vstd::math::min(representative_mismatch_offset, offset);
    lemma_transfer_phase_prefix(bytes, left, period, scanned_end, right, mismatch_offset);
    lemma_transfer_phase_prefix(bytes, left, period, scanned_end, candidate_start, mismatch_offset);
    assert(below_at(bytes, candidate_start, right, mismatch_offset, descending));
}

/// Restart at `right` and discard earlier starts by transitivity.
pub(super) proof fn lemma_ms_larger(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        right + offset < bytes.len(),
        byte_before(bytes[left + offset], bytes[right + offset], descending),
    ensures
        suffix_scan_inv(bytes, right, right + 1, 0, 1, descending),
{
    lemma_ms_beats(bytes, left, right, offset, period, descending, left);
    assert forall|candidate_start: int| 0 <= candidate_start < right
        implies #[trigger] suffix_less(bytes, candidate_start, right, descending) by {
        if candidate_start < left {
            lemma_suffix_less_trans(bytes, candidate_start, left, right, descending);
        } else {
            lemma_ms_beats(bytes, left, right, offset, period, descending, candidate_start);
        }
    }
}

// ---------------------------------------------------------------------------
// Facts used by the constructor.
// ---------------------------------------------------------------------------

/// At the scan end, the repeated blocks give a period of the suffix.
pub(super) proof fn lemma_ms_exit(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        right + offset == bytes.len(),
    ensures
        is_period(bytes.subrange(left, bytes.len() as int), period),
{
    let word_length = bytes.len() as int;
    let suffix = bytes.subrange(left, word_length);
    assert forall|byte_offset: int| 0 <= byte_offset < suffix.len() - period
        implies #[trigger] suffix[byte_offset] == suffix[byte_offset + period] by {
        lemma_mod_add_multiples_vanish(byte_offset, period);
        lemma_same_phase(bytes, left, period, word_length, left + byte_offset, left + byte_offset + period, 0);
    }
}

/// A period of the whole needle forces equal bytes one period apart, contradicting
/// the earlier suffix's mismatch if `left` reaches that period.
pub(super) proof fn lemma_ms_left_before_period(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool, comparison_period: int,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        is_period(bytes, comparison_period),
    ensures
        left < comparison_period,
{
    if comparison_period <= left {
        let earlier_start = left - comparison_period;
        assert(suffix_less(bytes, earlier_start, left, descending));
        let mismatch_offset = choose|mismatch: int|
            0 <= mismatch
                && left + mismatch < bytes.len()
                && #[trigger] below_at(bytes, earlier_start, left, mismatch, descending);
        assert(bytes[earlier_start + mismatch_offset] == bytes[left + mismatch_offset]);
    }
}

/// A smaller period would force the losing rotation's mismatch bytes to agree.
pub(super) proof fn lemma_ms_period_le(
    bytes: Seq<u8>, left: int, right: int, offset: int, period: int,
    descending: bool, comparison_period: int,
)
    requires
        suffix_scan_inv(bytes, left, right, offset, period, descending),
        is_period(bytes, comparison_period),
    ensures
        period <= comparison_period,
{
    if comparison_period < period {
        let rotation_start = left + comparison_period;
        assert(below_within(bytes, rotation_start, left, right + offset, descending));
    }
}

} // verus!
