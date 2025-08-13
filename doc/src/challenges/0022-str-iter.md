# Challenge 22: Verify the safety of `str` iter functions

- **Status:** Open
- **Tracking Issue:** [#279](https://github.com/model-checking/verify-rust-std/issues/279)
- **Start date:** *2025-03-07*
- **End date:** *2025-10-17*
- **Reward:** *10000 USD*

-------------------


## Goal

Verify the safety of [`std::str`] functions that are defined in (library/core/src/str/iter.rs):

## Motivation

String and `str` types are widely used in Rust programs, so it is important that their associated functions do not cause undefined behavior.
## Description

**Important note:** for this challenge, you can assume: 
1. The safety and functional correctness of all functions in `slice` module. 
2. The safety and functional correctness of all functions in (library/core/src/str/pattern.rs).
3. That all functions in (library/core/src/str/validations.rs) are functionally correct (consistent with the UTF-8 encoding description in https://en.wikipedia.org/wiki/UTF-8). 
4. That all the Iterators in (library/core/src/str/iter.rs) are derived from a valid UTF-8 string (str) (You can assume any property of valid UTF-8 encoded string).


### Success Criteria

Prove the safety of the following safe functions that contain unsafe code:


| Function | Impl for |
|---------| ---------|
|next| Chars|
|advance_by| Chars|
|next_back| Chars|
|as_str| Chars|
|get_end| SplitInternal|
|next| SplitInternal|
|next_inclusive| SplitInternal|
|next_match_back| SplitInternal|
|next_back_inclusive| SplitInternal|
|remainder| SplitInternal|
|next| MatchIndicesInternal|
|next_back| MatchIndicesInternal|
|next| MatchesInternal|
|next_back| MatchesInternal|
|remainder| SplitAsciiWhitespace|

Write and prove the safety contract for this unsafe function `__iterator_get_unchecked`

The verification must be unbounded---it must hold for str of arbitrary length.


### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory except for padding or unions.
* Mutating immutable bytes.
* Producing an invalid value


Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
