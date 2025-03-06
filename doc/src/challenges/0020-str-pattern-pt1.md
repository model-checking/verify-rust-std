# Challenge 20: Verify the safety of char-related functions in str::pattern

- **Status:** Open
- **Tracking Issue:** [#29](https://github.com/model-checking/verify-rust-std/issues/29)
- **Start date:** *2025/03/07*
- **End date:** *2025/10/17*
- **Reward:** *5,000 USD*

-------------------


### Context

A majority portion in str library functions take a Pattern (https://doc.rust-lang.org/std/str/pattern/trait.Pattern.html) as input. 
The functions which take Pattern as input turn the input str into a kind of Searcher which iterates over positions where the Pattern match, then perform their desired operations (split, find, ...).
Those functions is implemented in (library/core/src/str/mod.rs), but the core of them is the searching algorithms which are implemented in (library/core/src/str/pattern.rs).

# Details

IMPORTANT NOTE: for this challenge, you can assume: 
1. The safety and functional correctness of all functions in `slice` module 
2. That all functions in (library/core/src/str/validations.rs) are functionally correct (consistent with the UTF8 encoding description in https://en.wikipedia.org/wiki/UTF-8) . 
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

Verify the safety of the following functions in (library/core/src/str/pattern.rs) : `next`, `next_match`, `next_back`, `next_match_back`, `next_reject`, `next_back_reject`
which are implemented for the following `Searcher`s:  `CharSearcher`, `MultiCharEqSearcher`, `CharArraySearcher` , `CharArrayRefSearcher`, `CharSliceSearcher`, `CharPredicateSearcher`.

The verification is consider successful if for each `Searcher` above, you can specify a condition (a "type invariant") C and prove that:
1. If the `Searcher` is created from any valid utf8 haystack, it satisfies C.
2. If the `Searcher` satisfies C, it ensures the two safety properties mentioned in the previous section.
3. If the `Searcher` satisfies C, after it calls any function above and gets modified, it still statisfies C.


The verification must be unbounded---it must hold for inputs of arbitrary size.

### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory except for padding or unions.
* Mutating immutable bytes.
* Producing an invalid value


Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
