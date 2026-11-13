# Challenge 32: Verify the safety of `str` slicing

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** *Link to issue*
- **Start date:** *YYYY/MM/DD*
- **Reward:** *TBD*

-------------------


## Goal

Verify the safety of byte-range slicing of `str`: the eleven `SliceIndex<str>` implementations in
[str/traits.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/str/traits.rs),
and the char-boundary, `get`, unchecked-slicing and `split_at` functions and the slicing panic helper in
[str/mod.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/str/mod.rs).

## Motivation

Every `&s[a..b]`, `s.get(a..b)` and `s.split_at(n)` on a string runs this code. It keeps a `str` valid
UTF-8: the safe functions test that both ends of the range are character boundaries and then call unchecked
pointer arithmetic. A wrong boundary test lets safe code build a `str` that is not UTF-8, and other parts
of the library trust that invariant when they read the bytes.

The code has changed recently, and some of its unsafe code sits inside safe functions:

- [rust-lang/rust#157224](https://github.com/rust-lang/rust/pull/157224) (merged 2026-06-08) unrolled the
  loop of the safe, stable, `const` function `str::floor_char_boundary` by hand. It now contains two
  `unsafe { assert_unchecked(..) }` calls that hold only because the first byte of a valid `str` is a
  character boundary.
- The panic helper behind every failed index, `slice_error_fail_rt`, calls `floor_char_boundary` and
  `ceil_char_boundary`, slices the string a second time and decodes one `char` to build its message. The
  path to the panic therefore contains unsafe operations.
- [rust-lang/rust#165295](https://github.com/rust-lang/rust/issues/165295) (open) reports that the
  documentation of `floor_char_boundary` and `ceil_char_boundary` does not say clearly what they return for an
  index beyond the length. A checked statement of their results settles it.

With the `core::range` index types there are now eleven implementations of the unsafe trait
`SliceIndex<str>`, and several of them forward to one another.

## Description

[Challenge 17](0017-slice.md) covers indexing of `[T]`. [Challenge 22](0022-str-iter.md) covers the
iterators of `str`. Challenges [20](0020-str-pattern-pt1.md) and [21](0021-str-pattern-pt2.md) cover the
searchers. None of them lists the functions below.

This challenge covers:

- In `core::str::traits`: the implementations of the unsafe trait `SliceIndex<str>` for `ops::RangeFull`,
  `ops::Range<usize>`, `range::Range<usize>`, `(ops::Bound<usize>, ops::Bound<usize>)`,
  `ops::RangeTo<usize>`, `ops::RangeFrom<usize>`, `range::RangeFrom<usize>`, `ops::RangeInclusive<usize>`,
  `range::RangeInclusive<usize>`, `ops::RangeToInclusive<usize>` and `range::RangeToInclusive<usize>`; the
  helper `check_range`; and `Index<I>` and `IndexMut<I>` for `str`.
- In `impl str`: `is_char_boundary`, `floor_char_boundary`, `ceil_char_boundary`, `get`, `get_mut`,
  `get_unchecked`, `get_unchecked_mut`, `slice_unchecked`, `slice_mut_unchecked`, `split_at`,
  `split_at_mut`, `split_at_checked`, `split_at_mut_checked`, `split_at_unchecked`,
  `split_at_mut_unchecked`.
- In `core::str`: the panic helper `slice_error_fail_rt`.

The following code of `str/mod.rs` is not in scope:

- `slice_error_fail` itself contains no unsafe code: it only selects, with `const_eval_select`, between
  `slice_error_fail_rt` (in scope) and `slice_error_fail_ct`, which only panics, as does the
  `panic = "immediate-abort"` variant of `slice_error_fail`.
- The conversions between bytes and `str` (`str::from_utf8_unchecked`, `str::from_utf8_unchecked_mut`,
  `as_bytes`, `as_bytes_mut`) take no index; their safety rests on the caller's bytes, not on slicing.
- The ASCII functions (`as_ascii`, `as_ascii_unchecked`, `make_ascii_uppercase`, `make_ascii_lowercase`)
  take no index and do not change the length or the character boundaries.
- `copy_from_str`, `trim_ascii_start`, `trim_ascii_end` and `trim_ascii` take no index; their unsafe step
  follows a method of `[u8]`, which is slice code (Challenge 17).
- `impl Default for &mut str` builds the empty string and takes no index.
- The functions that take a `Pattern` (`split_once`, `rsplit_once`, `trim_matches`, `trim_start_matches`,
  `trim_end_matches`) depend on the searchers of Challenges 20 and 21 and on
  [issue #753](https://github.com/model-checking/verify-rust-std/issues/753).
- `UnsafeBytesToStr` is used only by the iterators of Challenge 22.

Also out of scope: `str/iter.rs`, `str/pattern.rs`, `str/validations.rs`, `alloc::str`, `String` and
`ByteStr`.

Pull request [#621](https://github.com/model-checking/verify-rust-std/pull/621) (a Challenge 21 solution,
open at the time of writing) adds contracts to `floor_char_boundary` and `ceil_char_boundary` as helpers.
If it is merged first, those contracts may be reused, subject to the success criteria below.

### Assumptions

* The input `str` is valid UTF-8, and its length is at most `isize::MAX`. A solution may use any property
  that follows from this. A solution that does not state validity of the whole string must list the
  properties it assumes instead, and each of them must hold for every valid UTF-8 string.
* For the unsafe functions, the arguments satisfy the function's contract. For the safe functions, the index
  and range values are arbitrary, including values greater than the length, `usize::MAX`, ranges whose start
  is greater than their end, and `ops::RangeInclusive<usize>` values in the exhausted state.
* Functions outside the tables that the target code calls may be trusted through their documented behavior
  or their existing verified contracts. The solution must name each one it trusts. This includes pointer
  arithmetic and slice construction in `core::ptr` and `core::slice`; the bound conversions
  `into_slice_range`, `try_into_slice_range`, `into_range_unchecked` and the panic `slice_index_fail` in
  `slice/index.rs`; `Chars::next` on a valid `str` (Challenge 22), provided the solution shows that the bytes
  it decodes are valid; and the panic and formatting machinery after the call to `panic!`. Tools that verify
  compositionally (see [issue #755](https://github.com/model-checking/verify-rust-std/issues/755)) may trust
  the rest of the standard library through specifications of its documented behavior, listed in the solution.
* Proofs need only run on the 64-bit configuration that the repository's CI builds.
* If the verification tool limits the size of one memory object, a solution may assume that the string is
  no longer than that limit. It must state the limit and show that it comes from the tool. For example, with
  the `--object-bits 12` that CI passes to CBMC, Kani's pointer model keeps 52 bits for the offset inside an
  object, so a Kani solution may limit strings to 2^51 - 1 bytes. A length bound chosen in a harness for any
  other reason is not acceptable.

### Success Criteria

Write and prove the safety contract of the following unsafe functions:

| Function | Location |
|---------|---------|
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `ops::RangeFull` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `ops::Range<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `range::Range<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `(ops::Bound<usize>, ops::Bound<usize>)` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `ops::RangeTo<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `ops::RangeFrom<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `range::RangeFrom<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `ops::RangeInclusive<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `range::RangeInclusive<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `ops::RangeToInclusive<usize>` | `core::str::traits` |
| `get_unchecked`, `get_unchecked_mut` of `SliceIndex<str>` for `range::RangeToInclusive<usize>` | `core::str::traits` |
| `str::get_unchecked`, `str::get_unchecked_mut` | `core::str` |
| `str::slice_unchecked`, `str::slice_mut_unchecked` | `core::str` |
| `str::split_at_unchecked`, `str::split_at_mut_unchecked` | `core::str` |

Each contract must require what the function's own `# Safety` text requires, and no more:

* For the 22 methods of the `SliceIndex<str>` implementations, the trait's text: the index value denotes a
  byte range that is in bounds of the string (its start does not exceed its end, and its end does not exceed
  the length), and the `slice` pointer is not dangling. This text says nothing about character boundaries,
  and these methods compute only a pointer and a length.
* For `str::get_unchecked`, `str::get_unchecked_mut`, `str::slice_unchecked` and
  `str::slice_mut_unchecked`: in addition, both ends of the range lie on character boundaries. For
  `str::split_at_unchecked` and `str::split_at_mut_unchecked`: `mid` is not beyond the length and lies on a
  character boundary.

Each contract must ensure that the result has exactly the address and the length of the byte range that the
index value denotes (for the `split_at` functions: of both halves). The byte range must be stated directly
from the index value (its fields and the meaning of its type), not as the result of another function in the
tables. `str::get_unchecked`
and `str::get_unchecked_mut` are generic over the index type: one contract on the generic function, proved for
each of the eleven index types, meets the criterion. The trait is declared `pub impl(crate)`, so these eleven
are the only implementations.

Prove the absence of undefined behavior for the following safe abstractions, for every string and every index
or range value:

| Function | Location |
|---------|---------|
| `get`, `get_mut`, `index`, `index_mut` of each of the eleven `SliceIndex<str>` implementations listed above | `core::str::traits` |
| `check_range` | `core::str::traits` |
| `Index<I> for str`, `IndexMut<I> for str` | `core::str::traits` |
| `str::is_char_boundary` | `core::str` |
| `str::floor_char_boundary` | `core::str` |
| `str::ceil_char_boundary` | `core::str` |
| `str::get`, `str::get_mut` | `core::str` |
| `str::split_at`, `str::split_at_mut` | `core::str` |
| `str::split_at_checked`, `str::split_at_mut_checked` | `core::str` |
| `slice_error_fail_rt` | `core::str` |

In addition, prove the following properties, which are what make the unsafe calls inside the safe functions
correct:

* `is_char_boundary(i)` returns `true` exactly when `i == 0`, or `i == len`, or `i < len` and byte `i` is
  not a UTF-8 continuation byte (a byte of the form `0b10xxxxxx`).
* `get` and `get_mut` return `Some` exactly when the byte range that the index value denotes lies within the
  string, its start does not exceed its end, and both ends are character boundaries; the returned slice then
  starts at byte `start` of the input and has length `end - start`. The same holds for the two halves
  returned by `split_at_checked` and `split_at_mut_checked`.
* `index`, `index_mut`, `split_at` and `split_at_mut` return the same slice as the corresponding checked
  function when that returns `Some`, and panic otherwise, with no undefined behavior before the panic.
* `floor_char_boundary(i)` returns the greatest `x <= min(i, len)` such that `is_char_boundary(x)`, and
  `ceil_char_boundary(i)` returns the least `x >= min(i, len)` such that `is_char_boundary(x)`.
* For every valid string and every pair of arguments that a call of `slice_error_fail` in the functions above
  can pass, `slice_error_fail_rt` panics with no undefined behavior before the panic. This includes its calls
  of `floor_char_boundary` and `ceil_char_boundary`, its second slicing of the string, and the decoding of
  one `char` from that slice. The second slicing must be shown to succeed, so that the helper does not call
  `slice_error_fail` again.

The panic helper and Kani: the version of Kani pinned in CI compiles every call of `slice_error_fail` as a
plain panic, so no Kani harness reaches `slice_error_fail_rt` through one of its call sites. A Kani solution
must therefore verify `slice_error_fail_rt` by calling it directly, under a precondition that it states, and
must show for each call site that the arguments the site passes satisfy that precondition for every valid
string and every index value. Because the call itself cannot be instrumented, this may be shown by a checked
statement on the arguments as the call site computes them; the solution must say how. Tools that execute
`slice_error_fail` meet this criterion at the call sites directly.

The verification must be unbounded: it must hold for strings of every length, and for every index value.
A bound on the iterations of a loop is acceptable only where the tool proves, for every input, that the bound
is never exceeded (for example a bounded model checker whose unwinding assertions are checked and pass). This
does not bound the input: the loop of `ceil_char_boundary` stops at the next character boundary, which in a
valid string is at most three bytes on, so the code bounds the loop itself, and a bound that some input would
exceed makes the proof fail.

### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling: the raw reads in `check_range`, and the
  dereferences of the pointers that the unchecked methods return.
* Invoking undefined behavior via compiler intrinsics: pointer `add` and `unchecked_sub` in the unchecked
  methods, `assert_unchecked` in `floor_char_boundary`, and `unwrap_unchecked` in the decoding on the panic
  path.
* Producing an invalid value: the `char` that the panic path decodes with `char::from_u32_unchecked`. (The
  references built from the returned pointers are covered by the address and length criteria above.) Where
  the tool's CI configuration does not check value validity (see
  [issue #733](https://github.com/model-checking/verify-rust-std/issues/733)), the solution must establish
  that this value is a valid `char` by a checked statement, for every string and index that reach the
  decoding.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
