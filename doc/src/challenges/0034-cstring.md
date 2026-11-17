# Challenge 34: Safety of `CString`, the owned C string

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** [#NNN](https://github.com/model-checking/verify-rust-std/issues/NNN)
- **Start date:** *YYYY/MM/DD*
- **Reward:** *TBD*

-------------------

## Goal

Verify the safety of `CString` and its related types in
[c_str.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/alloc/src/ffi/c_str.rs)
(`alloc::ffi::c_str`): every constructor, conversion and view must establish and preserve the
representation invariant of an owned C string — the buffer is at least one byte long, its last byte
is `0`, and it contains no other `0` byte — for byte vectors of arbitrary length.

## Motivation

`CString` is the owned counterpart of `CStr`: it is how safe Rust code manufactures a C string to
hand to foreign code, and its whole contract is the invariant above. Safe code that later calls
`as_ptr`, `CStr::from_ptr` or any C function trusts that the buffer really holds exactly one nul
byte and that it sits at the end. The file enforces that invariant with unchecked code in several
places:

- The safe constructors `CString::new` and `CString::from_vec_with_nul` scan with `core::slice::memchr`
  and then build the value through the private unchecked constructors; a wrong scan result, or a
  wrong branch on it, lets safe code create a `CString` with an interior nul or without a terminator.
- `as_bytes` and the `Drop` implementation index the buffer with `get_unchecked`, justified only by
  the invariant (`len >= 1`).
- Ownership crosses raw pointers: `into_raw` / `from_raw` hand the `Box<[u8]>` to C and take it back,
  recomputing the length with the C library's `strlen`; `into_boxed_c_str`, `From<Box<CStr>>` and the
  `Arc<CStr>` / `Rc<CStr>` conversions cast between `Box<[u8]>`, `Box<CStr>` and the reference-counted
  types with `Box::from_raw` / `Arc::from_raw` / `Rc::from_raw`.
- `From<Vec<NonZero<u8>>>` reinterprets the vector's allocation through `Vec::into_raw_parts` and
  `Vec::from_raw_parts`, relying on `NonZero<u8>` and `u8` having the same layout.

[Challenge 13](0013-cstr.md) covers the borrowed half, `core::ffi::CStr`, and its in-tree proofs are
bounded. No challenge lists a function of `alloc::ffi::c_str`, so none of the code above is covered.

## Description

`CString` is a single-field struct wrapping `Box<[u8]>`. The file also defines the error types
`NulError`, `FromVecWithNulError` and `IntoStringError`, the `ToOwned` implementation for `CStr`,
two inherent methods on `CStr` that need allocation (`to_string_lossy`, `into_c_string`), and the
conversions between `CString`, `Box<CStr>`, `Cow<CStr>`, `Arc<CStr>`, `Rc<CStr>`, `Vec<u8>`,
`Vec<NonZero<u8>>` and `String`. There are no loops in the file: the nul scan is delegated to
`core::slice::memchr`, and copying is delegated to `Vec` and `Box`. The unsafe functions are
`from_vec_unchecked`, `from_vec_with_nul_unchecked` and `from_raw` (plus the two private helpers
they share with the safe constructors). `CString::new` is generic over `Into<Vec<u8>>` and is
specialized for byte and string slices.

The following are out of scope:

- Methods of `core::ffi::CStr` itself (Challenge 13), including what a caller can do with the
  `&CStr` views this file returns. What this challenge must show is that the calls this file makes
  into `core` (for example `CStr::from_bytes_with_nul_unchecked` in `as_c_str`) satisfy their
  preconditions, and that the views have the stated bytes.
- The internals of `Vec`, `Box`, `String`, `Arc` and `Rc` (their own challenges), beyond the calls
  this file makes with raw pointers.
- Formatting: `Debug` for `CString` and the `Display` implementations of the error types only
  forward to `core::fmt` and to `CStr`'s formatting and contain no unsafe code of their own beyond
  the views covered below.
- What foreign code does with a pointer from `into_raw` while it owns it. The contract of
  `from_raw` states what the caller must guarantee when the pointer comes back.

### Assumptions

- `core::slice::memchr` does the nul scan, and its first-occurrence semantics is what the
  constructors' `Ok`/`Err` decisions rest on. A solution may treat that semantics in either of two
  ways, and must say which: prove a first-index contract for the implementation its tool executes
  (with `cfg(kani)`, the byte-by-byte loop), or state it as an assumption, name the model or bound
  that replaces the scan in its unbounded proofs, and prove the scan decisions exactly against the
  real function on bounded inputs whose bound exceeds every behavior class the decision
  distinguishes. The first way needs a quantified postcondition, which at the time of writing Kani
  can state (`-Z quantifiers` is already a CI flag) but its default SAT backend ignores for
  symbolic bounds; that tooling gap is why the second way is offered, and it must still not leave
  any `Ok`/`Err` branch, error position, or invariant clause unproved. Re-verifying the
  word-at-a-time implementation is not required either way.
- `CString::from_raw` recomputes the length with the C `strlen`. A solution may assume that, for a
  pointer satisfying the `from_raw` contract, `strlen` returns the index of the first nul byte, and
  must state how its tool models the extern function and why that model is sound for such pointers.
- Two functions evaluate C string literals in their own bodies (`Default for Box<CStr>` and
  `Default for Rc<CStr>` return `Box::from(c"")` / `Rc::from(c"")`), and one through a callee
  (`Default for CString` calls `Default` for `&CStr`, which returns `c""` in `core`). At the time
  of writing Kani cannot evaluate C string literals
  ([kani#2549](https://github.com/model-checking/kani/issues/2549)). A Kani solution may stub that
  one constant in `core` with the identical value built from a byte string, and may cover the two
  impls whose bodies hold the literal by proving the constructions they perform on the empty
  `CStr`, provided it says so. A tool that evaluates the literals needs neither allowance.
- `Vec`, `Box`, `String`, `Arc`, `Rc` and the UTF-8 validation in `core::str` may be trusted
  through their documented behavior or existing verified contracts, listed in the solution.
  Allocation failure is out of scope, as in the general rules; a capacity-overflow panic on an
  input whose length is within the limits below is not acceptable, because no valid slice or
  vector has length above `isize::MAX`.
- Proofs need only run on the 64-bit configuration that the repository's CI builds.
- If the verification tool limits the size of one memory object, a solution may assume that the
  byte vector is no longer than that limit. It must state the limit and show that it comes from
  the tool. For example, with the `--object-bits 12` that CI passes to CBMC, Kani's pointer model
  keeps 52 bits for the offset inside an object, so a Kani solution may limit vectors to
  2^51 - 1 bytes. A length bound chosen in a harness for any other reason is not acceptable.

### Success Criteria

The verification must be unbounded where it states the absence of undefined behavior, byte
preservation, lengths, and the invariant of values the harnesses generate: it must hold for byte
vectors and slices of every length (up to the stated tool limit), including the empty input
wherever the function accepts one, with no fixed-size input arrays and no unwinding bound on any
input-length scan. The exceptions are the places whose exact behavior runs a whole-buffer scan or conversion whose
symbolic-length cost at the current tool pins exceeds the CI verifier budgets, each of which a
solution may instead prove on bounded inputs against the real code, with unwinding assertions
checked and the bound exceeding every behavior class distinguished: the scan decisions (which
branch `new` and `from_vec_with_nul` take, the exact error position, the fidelity of the
invariant predicate, and the contract proofs whose `ensures` evaluates that predicate, under the
second `memchr` route above); the UTF-8 functions `into_string`, `TryFrom<CString> for String`
and `CStr::to_string_lossy` (empty, ASCII, multi-byte, invalid and truncated sequences are the
classes); and byte-exactness plus drops for the copying shared-ownership conversions
(`Arc`/`Rc`/`Box` from `CString`/`&CStr`/`&mut CStr`/`Cow`), whose in-file unsafe step is a raw
pointer cast. For each exception the same functions must still be shown memory-safe at every
length — for the conversions, the lengths they return and the terminator must also be pinned at
every length — and the solution must list what it bounded and why. A solution whose tool proves
any of these at every length within budget needs no bound there. There are no loops in this file
itself.

1. State the representation invariant of `CString` (length at least 1, last byte `0`, no other
   `0` byte) as a checked predicate — for a Kani solution, by implementing the `Invariant` trait
   for `CString`, mirroring the existing implementation for `&CStr` — and show that the predicate
   accepts exactly the byte sequences that end with a single nul byte and contain no other.

2. Write and prove the safety contracts of the following unsafe functions. Each `requires` must be
   what the function's `# Safety` text requires, and each `ensures` must pin the result's bytes,
   not merely restate the invariant:

| Function | Location |
|---------|---------|
| `CString::from_vec_unchecked` | `alloc::ffi::c_str` |
| `CString::from_vec_with_nul_unchecked` | `alloc::ffi::c_str` |
| `CString::from_raw` | `alloc::ffi::c_str` |

   Specifically: `from_vec_unchecked(v)` requires that `v` contains no `0` byte and ensures a
   valid `CString` whose bytes are `v` followed by one `0`; `from_vec_with_nul_unchecked(v)`
   requires `v.len() >= 1`, last byte `0` and no other `0`, and ensures a valid `CString` whose
   bytes are exactly `v`; `from_raw(ptr)` requires the documented conditions (the pointer came
   from `CString::into_raw`, the length was not modified, it is not dangling and is exclusively
   owned again) and ensures the reconstructed `CString` has the bytes the pointer denoted, so
   that `from_raw(into_raw(cs))` has the same bytes as `cs`. The contract annotations state the
   contract at every length; under the second `memchr` route their proofs may be among the
   bounded scan-decision proofs, and the `into_raw`/`from_raw` round trip must then additionally
   be shown memory-safe and byte-preserving at every length.

3. Prove the absence of undefined behavior, and the exact byte-level behavior stated below, for
   the following safe functions, for inputs of arbitrary length and content:

| Function | Location |
|---------|---------|
| `CString::new` (for `Vec<u8>`, `&[u8]`, `&mut [u8]` and `&str` inputs) | `alloc::ffi::c_str` |
| `CString::from_vec_with_nul` | `alloc::ffi::c_str` |
| `CString::into_raw` | `alloc::ffi::c_str` |
| `CString::into_string` | `alloc::ffi::c_str` |
| `CString::into_bytes`, `CString::into_bytes_with_nul` | `alloc::ffi::c_str` |
| `CString::as_bytes`, `CString::as_bytes_with_nul`, `CString::as_c_str` | `alloc::ffi::c_str` |
| `CString::into_boxed_c_str` | `alloc::ffi::c_str` |
| `NulError::nul_position`, `NulError::into_vec` | `alloc::ffi::c_str` |
| `FromVecWithNulError::as_bytes`, `FromVecWithNulError::into_bytes` | `alloc::ffi::c_str` |
| `IntoStringError::into_cstring`, `IntoStringError::utf8_error` | `alloc::ffi::c_str` |
| `CStr::to_string_lossy`, `CStr::into_c_string` | `alloc::ffi::c_str` |
| `Drop for CString` | `alloc::ffi::c_str` |

4. Prove the same for the following trait implementations:

| Trait implementation | Location |
|---------|---------|
| `Deref for CString`, `Borrow<CStr> for CString`, `AsRef<CStr> for CString`, `Index<RangeFull> for CString` | `alloc::ffi::c_str` |
| `Default for CString`, `Clone for CString`, `Default for Box<CStr>`, `Clone for Box<CStr>`, `Default for Rc<CStr>` | `alloc::ffi::c_str` |
| `From<&CStr> for CString`, `ToOwned for CStr` (both `to_owned` and both branches of `clone_into`) | `alloc::ffi::c_str` |
| `From<Box<CStr>> for CString`, `From<CString> for Box<CStr>` | `alloc::ffi::c_str` |
| `From<Cow<CStr>> for CString`, `From<CString> for Cow<CStr>`, `From<&CString> for Cow<CStr>`, `From<&CStr> for Cow<CStr>` | `alloc::ffi::c_str` |
| `From<Vec<NonZero<u8>>> for CString` | `alloc::ffi::c_str` |
| `FromStr for CString`, `TryFrom<CString> for String` | `alloc::ffi::c_str` |
| `From<CString> for Vec<u8>` | `alloc::ffi::c_str` |
| `From<CString> for Arc<CStr>`, `From<&CStr> for Arc<CStr>`, `From<&mut CStr> for Arc<CStr>` | `alloc::ffi::c_str` |
| `From<CString> for Rc<CStr>`, `From<&CStr> for Rc<CStr>`, `From<&mut CStr> for Rc<CStr>` | `alloc::ffi::c_str` |
| `From<&CStr> for Box<CStr>`, `From<&mut CStr> for Box<CStr>`, `From<Cow<CStr>> for Box<CStr>` | `alloc::ffi::c_str` |
| The `PartialEq` implementations between `CString`, `CStr` and `Cow<CStr>` | `alloc::ffi::c_str` |

In addition, prove the following properties, which are what make the unchecked operations inside
the safe functions correct. The `Ok`/`Err` decisions and the returned bytes must be pinned exactly,
against the input bytes and not merely against the invariant predicate:

* `CString::new(t)` returns `Ok` exactly when the input bytes contain no `0`; the result's bytes
  are then the input bytes followed by one `0`. On `Err(e)`, `e.nul_position()` is the index of
  the first `0` byte and `e.into_vec()` returns the input bytes.
* `CString::from_vec_with_nul(v)` returns `Ok` exactly when `v` has exactly one `0` byte and it is
  the last byte; the result's bytes are then `v`. On `Err(e)`, `e.as_bytes()` and `e.into_bytes()`
  return `v`. The empty vector is an `Err`.
* `as_bytes()` returns the buffer without its last byte and `as_bytes_with_nul()` the whole
  buffer; `into_bytes()` and `into_bytes_with_nul()` return the same two byte sequences as owned
  vectors. `as_c_str()`, and the `Deref`, `Borrow`, `AsRef` and `Index` views, have the
  nul-terminated bytes of the buffer.
* `into_boxed_c_str()` preserves the bytes, and `CString::from(boxed)` and `boxed.into_c_string()`
  are its inverse: the round trip in either direction preserves the bytes exactly.
* `into_string()` returns `Ok(s)` exactly when the bytes without the terminator are valid UTF-8,
  and then `s` holds those bytes; on `Err(e)`, `e.into_cstring()` returns a `CString` with the
  original bytes and `e.utf8_error()` is the UTF-8 error of those bytes.
* `CString::from(v)` for `v: Vec<NonZero<u8>>` has the bytes of `v` followed by one `0`, including
  for the empty vector.
* `to_owned()` and `clone_into` produce a `CString` with the source `CStr`'s nul-terminated
  bytes, in both branches of `clone_into` (equal length and different length), and `Default`
  produces the empty `CString`, a single `0` byte.
* `CStr::to_string_lossy` on a `CStr` equals `String::from_utf8_lossy` of its bytes without the
  terminator (borrowed exactly when they are valid UTF-8).
* The `Arc<CStr>`, `Rc<CStr>`, `Box<CStr>` and `Cow<CStr>` conversions preserve the nul-terminated
  bytes, and the `PartialEq` implementations agree with equality of those bytes.
* Dropping any `CString`, including the empty one, is free of undefined behavior.

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned
  pointer: the `get_unchecked` in `as_bytes` and in `Drop`, the `ptr::read` in the private
  `into_inner`, and the `Box::from_raw`, `Arc::from_raw`, `Rc::from_raw` and
  `Vec::from_raw_parts` calls, including freeing an allocation with a layout different from the
  one it was created with.
* Producing an invalid value: a `CString` or `&CStr` whose bytes do not end with exactly one
  nul byte, or a `Vec<u8>` reinterpreted from a `Vec<NonZero<u8>>` allocation with the wrong
  length or capacity.
* Invoking undefined behavior via compiler intrinsics.

Note: All solutions to verification challenges need to satisfy the criteria established in the
[challenge book](../general-rules.md) in addition to the ones listed above.
