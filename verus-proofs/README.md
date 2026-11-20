# Challenge 21 in Verus

A [Verus](https://github.com/verus-lang/verus) proof of the safety of
`StrSearcher` in `library/core/src/str/pattern.rs`, for
[Challenge 21](../doc/src/challenges/0021-str-pattern-pt2.md).

## Layout

The proof runs in a standalone crate containing a copy of the library
sources. This harness uses Verus's prebuilt vstd and the pinned toolchain's
core library.

```text
core/str/pattern.rs/
  original/          unannotated crate and copied library code
  verified/          the same crate, with Verus annotations
    pattern/         proof.rs, max_suffix.rs, trusted.rs
  standalone.patch   compatibility changes for compilation outside core
```

The library's `pattern.rs` expects to live inside `core`, with access to its
modules and private iterator fields.
Both `lib.rs` files are our standalone crate roots. They re-export the pinned
toolchain's `core` modules, including `memchr`/`memrchr` through `slice_internals`.
`original/pattern.rs` is unchanged from the library. The char-boundary copies
use traits for `str` and `u8`, with unchanged bodies.

`CharSearcher` and `MultiCharEqSearcher` are outside the challenge's scope.
[standalone.patch](core/str/pattern.rs/standalone.patch) adapts their private
iterator-field accesses solely for compatibility with compilation outside `core`.

## Formalization

The invariant `C` is [StrSearcher::inv()](core/str/pattern.rs/verified/pattern/proof.rs#L66),
exposed as `searcher_inv()`. It bounds lengths and cursors, keeps cursors on
UTF-8 boundaries, and tracks the search variant, period and remembered byte matches.

| Challenge obligation | Contract and proof |
| --- | --- |
| Construction establishes `C`. | [StrSearcher::new](core/str/pattern.rs/verified/pattern.rs#L1201) ensures `C` for any valid `&str` haystack and needle. |
| Calls under `C` are safe. | All six search methods require `C`. State and loop invariants prove arithmetic and index bounds and unchecked-operation preconditions. |
| Calls preserve `C`. | Each method ensures `C` and preserves the haystack in the string model, allowing subsequent calls in either direction. |

`next` and `next_back` ensure `step_on_char_boundaries`; the four match/reject
methods ensure `range_on_char_boundaries`. Every returned range satisfies
`start <= end <= haystack.spec_bytes().len()`, with both endpoints on UTF-8
boundaries, so consumers can slice safely.

The supporting proofs cover [UTF-8 boundaries and remembered matches](core/str/pattern.rs/verified/pattern/proof.rs),
[maximal-suffix scans](core/str/pattern.rs/verified/pattern/max_suffix.rs), and
[floor/ceil char boundaries](core/str/pattern.rs/verified/char_boundary.rs).
TwoWay remembers which haystack bytes match a needle prefix or suffix,
so it can skip those comparisons after shifting.
Reference validity and ownership rely on the Rust/Verus memory model and
the trusted specifications below.

## Trusted pieces

Explicit trusted specifications are in
[verified/pattern/trusted.rs](core/str/pattern.rs/verified/pattern/trusted.rs).
No proof body uses `assume` or `admit`. The trusted items are:

1. **Challenge assumptions:** `core::slice::memchr::{memchr, memrchr}`.
   Only bounds and byte equality for `Some(i)` are assumed;
   first/last occurrence and absence for `None` are unnecessary.
2. **Missing vstd specs and facts:** `assert_unchecked` requires its condition
   to hold; `<str as Index<I>>::index` forwards its postcondition to vstd's
   `SliceIndex<str>::index` specification; `axiom_str_len_le_isize_max` supplies
   the language's `isize::MAX` bound on the length of a string reference.
3. **Contracts proved for library copies:** std's `ceil_char_boundary` and
   `floor_char_boundary` receive the contracts proved for their copies.
   The remaining trust is that std runs those bodies.
4. **Verus workaround:** the empty strategy enums `MatchOnly` and
   `RejectAndMatch` are opaque types, with no added logical facts.

The proof also trusts Verus and vstd contracts, including:

- `str::{len, is_empty, as_bytes, chars}` and `char::len_utf8`.
- str/slice indexing, `<[T]>::{len, get, get_unchecked, iter}` and slice equality.
- `Chars`, `Range` and `Rev` iteration, and `Iterator::fold`.
- `cmp::{max, min}` and `Ord` on `usize`.

vstd's UTF-8 lemmas have verified proof bodies.

## Audit scripts

We wrote a few scripts to help audit the proof:

- [check.sh](core/str/pattern.rs/check.sh) checks the source copies, compiles
  the standalone crate, runs the two checks below, and verifies the proof.
- [compare_erased.py](compare_erased.py) compares HIR after Verus erases
  annotations against the original with `standalone.patch` applied.
- [check_trusted.py](check_trusted.py) scans for trust constructs outside
  `trusted.rs`.

The token scan excludes inactive `#[cfg(kani)]` items and does not expand
macros or resolve external source. It complements review of the assumptions.

Run from the repository root:

```sh
verus-proofs/core/str/pattern.rs/check.sh
```

Verified on Verus `28029ac` (0.2026.11.11, rustc 1.99.1).
The scripts need its rustup toolchain, Python 3 and `patch`.
Set `VERUS=/path/to/verus` to override the binary.
Verification reports `69 verified, 0 errors`.
