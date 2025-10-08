# Challenge 21: Verify the safety of substring-related functions in str::pattern

- **Status:** Open
- **Tracking Issue:** [#278](https://github.com/model-checking/verify-rust-std/issues/278)
- **Start date:** *2025-03-07*
- **End date:** *2025-10-17*
- **Reward:** *25000 USD*

-------------------
## Goal
Verify the safety of `StrSearcher` implementation in `str::pattern`.

## Motivation

String and `str` types are widely used in Rust programs, so it is important that their associated functions do not cause undefined behavior.

## Description

The following str library functions are generic over the `Pattern` trait (https://doc.rust-lang.org/std/str/pattern/trait.Pattern.html): 
- `contains`
- `starts_with`
- `ends_with`
- `find` 
- `rfind`
- `split`
- `split_inclusive`
- `rsplit`
- `split_terminator`
- `rsplit_terminator`
- `splitn`
- `rsplitn`
- `split_once`
- `rsplit_once`
- `rmatches`
- `match_indices`
- `rmatch_indices`
- `trim_matches`
- `trim_start_matches`
- `strip_prefix`
- `strip_suffix`
- `trim_end_matches`
These functions accept a pattern as input, then call [into_searcher](https://doc.rust-lang.org/std/str/pattern/trait.Pattern.html#tymethod.into_searcher) to create a [Searcher](https://doc.rust-lang.org/std/str/pattern/trait.Pattern.html#associatedtype.Searcher) for the pattern. They use this `Searcher` to perform their desired operations (split, find, etc.).
Those functions are implemented in (library/core/src/str/mod.rs), but the core of them are the searching algorithms which are implemented in (library/core/src/str/pattern.rs).

### Assumptions

**Important note:** for this challenge, you can assume: 
1. The safety and functional correctness of all functions in `slice` module. 
2. That all functions in (library/core/src/str/validations.rs) are functionally correct (consistent with the UTF8 encoding description in https://en.wikipedia.org/wiki/UTF-8). 
3. That all the Searchers in (library/core/src/str/iter.rs) are created by the into_searcher(_, haystack) with haystack is a valid utf8 string (str). You can assume any utf8 string property of haystack.

Verify the safety of the functions in (library/core/src/str/pattern.rs) listed in the next section.

The safety properties we are targeting are: 
1. There is no UB happens when calling the functions after the Searcher is created.
2. The impls of unsafe traits `Searcher` and `ReverseSearcher` satisfies the SAFETY condition stated in the file: 
```
/// The trait is marked unsafe because the indices returned by the
/// [`next()`][Searcher::next] methods are required to lie on valid utf8
/// boundaries in the haystack. This enables consumers of this trait to
/// slice the haystack without additional runtime checks.
```
This property should hold for next_back() of `ReverseSearcher` too.



### Success Criteria

Verify the safety of the following `StrSearcher` functions in (library/core/src/str/pattern.rs): 
- `next`
- `next_match`
- `next_back`
- `next_match_back`
- `next_reject`
- `next_back_reject`

The verification is considered successful if you can specify a condition (a "type invariant") `C` and prove that:
1. If the `StrSearcher` is created from any valid UTF-8 haystack, it satisfies `C`.
2. If the `StrSearcher` satisfies `C`, it ensures the two safety properties mentioned in the previous section.
3. If the `StrSearcher` satisfies `C`, after it calls any function above and gets modified, it still satisfies `C`.

Furthermore, you must prove the absence of undefined behaviors listed in the next section.

The verification must be unbounded---it must hold for inputs of arbitrary size.

### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory except for padding or unions.
* Mutating immutable bytes.
* Producing an invalid value


Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
