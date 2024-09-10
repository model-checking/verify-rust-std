# Challenge 1: Verify `core` transmuting methods

- **Status:** Open
- **Tracking Issue:** [#19](https://github.com/model-checking/verify-rust-std/issues/19)
- **Start date:** 2024-06-12
- **End date:** 2024-12-10

-------------------

## Goal

Confirm the soundness of value transmutations performed by libcore, including those transmutations exposed as public methods provided by libcore. A value-to-value transmutation is sound if:
1. the source value is a bit-valid instance of the destination type;
2. violations of library safety invariants (e.g., invariants on a field's value) of the destination type are not violated by subsequent use of the transmuted value.

If the context of the transmute is safe, these conditions should be proven with local reasoning. If the context of the transmute is unsafe, they may be discharged with a safety obligation on the caller.

To keep the goal somewhat manageable, it excludes some classes of code (e.g., UTF8-validation, async tasks, and others); see the assumptions listed below for the full list of excluded categories.

## Details

### Motivating Example

There are several calls to unsafe methods using transmute within the code of safe methods exported by libcore itself, so having clear and verifiable safety contracts is critical for verifying the safety of the safe methods that invoke them.

For example, `std::slice::align_to` (which unsafely converts any slice `&[T]` into a tuple `(&[T], &[U], &[T])` composed of a prefix, a maximal sequence of values of type `U`, and a suffix) just says for its safety that “all the usual caveats pertaining to `transmute::<T, U>` also apply here”, which might be an under specification. For more details, see the [documentation](https://doc.rust-lang.org/std/mem/fn.transmute.html) for `transmute`.


### Breaking-down the verification

We lay out the verification challenge from the bottom up. Starting with the core implementation of `transmute` moving up to all unsafe and safe APIs that rely on it.

#### Part I - The Two Intrinsics

The public unsafe intrinsic [`transmute<T, U>`](https://doc.rust-lang.org/std/mem/fn.transmute.html) takes a value of type `T` and reinterprets it to have type `U`, with the sole (statically-enforced) restriction being that the types `T` and `U` must have the same size. The unstable intrinsic [`transmute_unchecked<T, U>`](https://doc.rust-lang.org/core/intrinsics/fn.transmute_unchecked.html) is similar, except that it removes the static size restriction, treating violations of it as undefined behavior.

_What is the right way to encode the preconditions of the two transmutation intrinsics?_

If one is solely concerned about safety: The [Rustonomicon](https://doc.rust-lang.org/nomicon/transmutes.html) lists several ways that transmutation can yield undefined behavior. Encoding a safety contract for transmute that captures all the relevant criteria laid out in the documentation is crucial.

If one is concerned about proving functional correctness, then reasoning about transmutation will require reasoning about the byte representation of values to justify that the reinterpretation of the value’s bytes for satisfying the pending proof obligation associated with the output value.


#### Part II - `unsafe` APIs with Validity Constraints

There are unsafe methods (which are defined by libcore and reexported by libstd) that have the effect of a transmutation between a (sequence of) `T` and a (sequence of) `U`. Come up with an appropriate safety contract for each of them.


#### Part III - `unsafe` APIs with Richer Constraints

Similar to part 2, there are also unsafe methods, but now the safety condition is more complicated, such as “is valid ascii character” or "is valid unicode scalar value."

#### Part IV - `safe` APIs

These are safe APIs that call into the unsafe API's from parts 1 through 3 above. Now our final goal is to prove that they actually are safe, despite calling transmute or transmute-related methods in their implementations.

### Assumptions

For this challenge, the following assumptions are acceptable:

We are not attempting to validate all details of the memory model for this challenge; for example, you do not need to worry about whether we are using the Stacked Borrows or Tree Borrows aliasing models. Likewise, you do not need to validate the provenance-related API in `std::ptr`.

You are allowed, but not required, to leverage the unstable `Transmutability` trait under development as part of your solution. This is a libstd-internal feature for auditing whether a given transmutation is safe. (It seems like something tools should try to leverage in some way; but it is also experimental.) Note that if you need to add new impls of `Transmutability`, then those new impl’s need to be accepted by (and landed in) the upstream Rust project before your solution can be considered completed. See also https://github.com/rust-lang/rust/issues/99571

You do not need to verify the correctness of the transmute calls in the unit tests embedded in libcore, though it would be great to do so!

To keep the goal somewhat manageable, we are omitting the following classes of code from the acceptance criteria for this challenge:
 * utf8-validation (such as `str::from_utf8_unchecked`)
 * the provenance-related API in `std::ptr` (such as `addr`, or `without_provenance`)
 * the num methods (from modules like `core::num::f64`, `core::num::i32`, etc)
 * pointer-metadata and vtable APIs (from modules like `core::ptr::metadata`)
 * async rust runtime/task API (from `core::task`)
 * core-internal specialization methods (such as traits like `RangeIteratorImpl` with methods prefixed with "spec_")
 * core-internal `__iterator_get_unchecked` calls
 * value output formatting machinery (from `std::fmt::rt`)
 You do not need to verify those (potentially indirect) uses of transmute,  unless you need to establish the safety/correctness of some of those methods in order to verify some other type in this list. (That is, you cannot assume them to be safe nor correct in your verification of other methods listed here.) We expect to issue future challenges tailored to each of the categories of transmutation uses listed above.


## Success Criteria

A new entry to the specification book is created explaining the relevant patterns for verifying code that calls transmute.

At least 35 of the following 47 intrinsics and functions (i.e. approximately 75%) have been annotated with contracts, and, for non-intrinsics, had their bodies verified.

For the safe functions, you do not need to provide a full-functional correctness specification; it will suffice to add pre- and post-conditions (i.e. assumptions and assertions) around the relevant part of the code that calls the transmutation-related unsafe function or intrinsic.


| Function              | Location          |
|-----------------------|-------------------|
| `transmute_unchecked` | `core::intrinsics` |
| `transmute`           | `core::intrinsics` |
| `MaybeUninit<T>::array_assume_init`    | `core::mem` |
| `MaybeUninit<[T; N]>::transpose`       | `core::mem` |
| `<[MaybeUninit<T>; N]>::transpose`     | `core::mem` |
| `<[T; N] as IntoIterator>::into_iter`  | `core::array::iter` |
| `BorrowedBuf::unfilled`    | `core::io::borrowed_buf` |
| `BorrowedCursor::reborrow` | `core::io::borrowed_buf` |
| `str::as_bytes`            | `core::str` |
| `from_u32_unchecked`       | `core::char::convert` |
| `char_try_from_u32`        | `core::char::convert` |
| `Ipv6Addr::new`       | `core::net::ip_addr` |
| `Ipv6Addr::segments`  | `core::net::ip_addr` |
| `align_offset`        | `core::ptr`        |
| `Alignment::new_unchecked` | `core::ptr::alignment` |
| `MaybeUninit<T>::copy_from_slice` | `core::mem` |
| `str::as_bytes_mut`        | `core::str` |
| `<Filter<I,P> as Iterator>::next_chunk` | `core::iter::adapters` |
| `<FilterMap<I,F> as Iterator>::next_chunk` | `core::iter::adapters` |
| `try_from_fn` | `core::array` |
| `iter_next_chunk` | `core::array` |
| `from_u32_unchecked`            | `core::char`       |
| `AsciiChar::from_u8_unchecked`  | `core::ascii_char` |
| `memchr_aligned`  | `core::slice::memchr` |
| `<[T]>::align_to_mut` | `core::slice`     |
| `run_utf8_validation` | `core::str::validations` |
| `<[T]>::align_to`     | `core::slice` |
| `is_aligned_to`       | `core::const_ptr` |
| `is_aligned_to`       | `core::mut_ptr`   |
| `Alignment::new`      | `core::ptr::alignment` |
| `Layout::from_size_align`           | `core::alloc::layout` |
| `Layout::from_size_align_unchecked` | `core::alloc::layout` |
| `make_ascii_lowercase` | `core::str` |
| `make_ascii_uppercase` | `core::str` |
| `<char as Step>::forward_checked` | `core::iter::range` |
| `<Chars as Iterator>::next`                 | `core::str::iter` |
| `<Chars as DoubleEndedIterator>::next_back` | `core::str::iter` |
| `char::encode_utf16_raw` | `core::char` |
| `<char as Step>::backward_unchecked` | `core::iter::range` |
| `<char as Step>::forward_unchecked`  | `core::iter::range` |
| `AsciiChar::from_u8` | `core::ascii_char` |
| `char::as_ascii` | `core::char` |
| `<[T]>::as_simd_mut` | `core::slice` |
| `<[T]>::as_simd`     | `core::slice` |
| `memrchr` | `core::slice::memchr` |
| `do_count_chars` | `str::count` |


* All solutions to verification challenges need to satisfy the criteria established in the [challenge book](https://model-checking.github.io/verify-rust-std/general-rules.html) in addition to the ones listed below

## Appendix A: The list construction

The list of methods and intrinsics was gathered by surveying the call-graph (solely within the libcore source) of function bodies that could eventually invoke `transmute` or `transmute_unchecked`. For each caller: if the caller was itself `unsafe`, then its callers were then surveyed; if the caller was not `unsafe`, then it was treated as an end point for the survey.

As mentioned in the assumptions, some (large) classes of methods were omitted from the challenge, either because 1. they encompassed a large API surface (e.g. `core::num`) that deserved separate treatment, 2. they had an enormous number of callers that would deserve separate treatment (e.g. `core::str::from_utf8_unchecked`), or 3. they interact with aspects of the Rust memory model that still need to be better understood by reasoning tools (e.g. the provenance APIs).

You can see the [call graph produced by the survey here](https://hackmd.io/PYQNIL_aTxK0N6-AltxfbQ).
