# Challenge 34: Verify the safety of `core::io::BorrowedBuf` and `BorrowedCursor`

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** [#769](https://github.com/model-checking/verify-rust-std/issues/769)
- **Start date:** *2026/11/17*
- **Reward:** *TBD*

-------------------

## Goal

Verify the safety of `BorrowedBuf` and `BorrowedCursor` in
[borrowed_buf.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/io/borrowed_buf.rs)
(`core::io`), for buffers of arbitrary capacity and generic element type `T`, and prove that the
representation invariant the unsafe code relies on — `filled <= capacity`, plus the meaning of the
`init` flag — is established by every constructor and preserved by every operation, including the
operations a `BorrowedCursor` performs on its parent buffer through a raw pointer.

## Motivation

`BorrowedBuf`/`BorrowedCursor` are the types behind the `read_buf` API (`core_io_borrowed_buf`,
rust-lang/rust#117693; the `init`-tracking methods are `borrowed_buf_init`, rust-lang/rust#160476):
a caller lends possibly-uninitialized spare capacity, and a cursor fills it incrementally. The
filled region is handed back as `&[T]`/`&mut [T]` by `assume_init_ref`/`assume_init_mut` over a
`get_unchecked(..filled)` slice, so the whole API is sound exactly if `filled` never exceeds the
buffer length and never covers elements that were not initialized. Neither fact is stated anywhere
as a machine-checked invariant.

The state is shared in a fragile way. A `BorrowedCursor` does not own the counters: it holds
`NonNull<BorrowedBuf>` plus a raw element pointer, and reads and writes the parent's `filled` and
`init` fields through that pointer while the parent is mutably borrowed. `with_unfilled_buf` runs
an arbitrary caller closure on a temporary `BorrowedBuf` over the unfilled region and then trusts
its `filled`/`init` fields, guarded only by a pointer-equality assertion that the closure did not
swap the buffer. An off-by-one in `advance`, `append` or the `From<BorrowedCursor>` offset, or a
missing replacement check, turns safe code into a read or write past the end of a caller-supplied
buffer, or exposes uninitialized elements as initialized `T`.

We know of no soundness bug reported against this file. The case for the challenge is that the
invariant is subtle, split across two types and a raw-pointer back-channel, and currently rests
only on the `SAFETY:` comments. No existing challenge lists a function of `core::io`.

## Description

`BorrowedBuf<'data, T>` wraps `&'data mut [MaybeUninit<T>]` with `filled: usize` and `init: bool`.
`buf[..filled]` is always initialized; if `init` is true, `buf[filled..]` is initialized too.
`BorrowedCursor<'a, T>` is created by `BorrowedBuf::unfilled` and is the only way to write: it
tracks no counters of its own, but reads `filled`/`init`/buffer length from the parent through
`NonNull` field accesses that deliberately avoid retagging the parent's slice reference
(`buf_len`, `filled`, `is_buf_init`, `set_buf_init`, `add_filled`), and reconstructs the element
slice from its own `NonNull<MaybeUninit<T>>` (`buf_mut`, `unfilled_slice`). The file has 472 lines,
34 functions, 29 `unsafe` occurrences (blocks, `unsafe fn`s and two `unsafe impl` `Send`/`Sync`),
and no loops of its own.

Note on trait bounds: every public constructor (`From<&mut [T]>`, `From<&mut [MaybeUninit<T>]>`,
`From<BorrowedCursor>`) and every cursor operation except the private helpers requires `T: Copy`,
and `ensure_init` additionally requires `T: Default`. The surface that exists for arbitrary `T` is
`capacity`, `len`, `is_init`, the `Debug` impls and the private cursor helpers. Generic-`T`
coverage below is stated per trait bound accordingly; solutions must not silently shrink the
`Copy` surface to `u8`.

The following are out of scope:

- `std::io` (`Read::read_buf` implementors, adapters) and any other caller of this API.
- The `MaybeUninit` slice writers this file calls (`write_copy_of_slice`, `write_default`,
  `assume_init_ref`/`assume_init_mut` in `core::mem`); see Assumptions.
- The formatting machinery behind the three `Debug::fmt` bodies. They only read the three scalar
  fields (`init`, `filled`, `capacity`, the latter via the covered accessors) and delegate to
  `core::fmt`; criteria for them are stated in the Success Criteria.

### Assumptions

- `core::ptr`, `core::slice` and `core::mem` may be assumed correct, including
  `<[MaybeUninit<T>]>::write_copy_of_slice` (a sized copy), `write_default` (every element becomes
  `T::default()`) and `assume_init_ref`/`assume_init_mut`. Existing verified contracts for them may
  be reused; a solution that stubs `write_default` must use an over-approximating stub (after the
  call, each element holds *some* valid `T`) and must say so.
- **Uninitialized memory ([issue #733](https://github.com/model-checking/verify-rust-std/issues/733)).**
  The repository CI does not run with uninitialized-memory checks, so a harness does **not** get
  credit for "the tool would flag an uninitialized read". The initialization half of the invariant
  must be encoded explicitly: contracts and postconditions must state the `filled <= capacity`
  bound and the exact effect of every operation on `filled` and on the `init` flag, and harnesses
  may only call `set_init`/`advance` (and the private helpers) on buffers whose relevant region the
  harness itself initialized. What no current CI tool checks must be listed as a limit.
- **Generic `T` ([issue #734](https://github.com/model-checking/verify-rust-std/issues/734)).**
  What satisfies the generic-`T` clause is decided there; until then this challenge accepts either
  a proof polymorphic in `T`, or (for monomorphizing tools) one generic harness body instantiated
  over shapes covering every layout/validity/drop distinction the code can branch on: a zero-sized
  type, a 1-byte type, a non-power-of-two size, an 8-byte-aligned type, a validity/niche type such
  as `NonZero<u8>`, an over-aligned type (`#[repr(align(16))]`), a large element (> 1 KiB), and —
  for the surface not bounded by `Copy` — a non-`Copy` type with a destructor.
- The `unsafe impl<T: Send> Send` / `unsafe impl<T: Sync> Sync` for `BorrowedCursor` cannot be
  discharged by a harness. A solution must argue them in text from the unique-borrow structure
  (and say that this part is an argument, not a proof), and must not weaken the bounds.

### Success Criteria

The verification must be unbounded: it must hold for buffers of arbitrary capacity (including 0,
and including more than `isize::MAX` elements for zero-sized `T`, subject only to the tool's
pointer model), and from any state satisfying the invariant — in particular any
`filled <= capacity` and either value of `init` that earlier calls could have produced. Proofs
that fix or bound the capacity, or that start only from a freshly constructed buffer, do not meet
this criterion. The file contains no loops, so no unwinding bound is expected anywhere; loops
inside assumed-correct callees are covered by the Assumptions, not by bounding the capacity.

State the invariant of `BorrowedBuf` (and the corresponding cursor invariant: the element pointer
is the start of the parent's buffer, and the parent state read through it satisfies the buffer
invariant). Prove every way of creating a buffer or cursor establishes it:

| Function | Location |
|---------|---------|
| `From<&'data mut [T]> for BorrowedBuf<'data, T>` (`filled = 0`, `init = true`) | `core::io::borrowed_buf` |
| `From<&'data mut [MaybeUninit<T>]> for BorrowedBuf<'data, T>` (`filled = 0`, `init = false`) | `core::io::borrowed_buf` |
| `From<BorrowedCursor<'data, T>> for BorrowedBuf<'data, T>` (buffer is the parent's storage offset by `filled`, length `capacity - filled`, `filled = 0`, `init` carried over) | `core::io::borrowed_buf` |
| `BorrowedBuf::unfilled` | `core::io::borrowed_buf` |
| `BorrowedCursor::reborrow` | `core::io::borrowed_buf` |

Write and prove a contract for each `unsafe fn`. Each contract must state the checkable safety
precondition and the exact effect on `filled`/`init`; the part of the documented precondition that
concerns memory being initialized must be discharged as described under Assumptions (#733) and
named as a limit where the tool cannot check it:

| Function | Contract must state |
|---------|---------|
| `BorrowedBuf::set_init` | post: `is_init()`, and `len`/`capacity` unchanged |
| `BorrowedCursor::set_buf_init` (private) | post: parent `init` flag equals the argument |
| `BorrowedCursor::add_filled` (private) | pre: `n <= capacity() - written()`; post: `written()` grows by exactly `n` |
| `BorrowedCursor::set_init` | post: `is_init()` |
| `BorrowedCursor::as_mut` | post: result is the unfilled region — length `capacity()`, starting at element `written()` of the parent buffer |
| `BorrowedCursor::advance` | pre: `n <= capacity()`; post: `written()` grows by exactly `n` |

Prove the absence of undefined behavior for the following safe abstractions, from any state
satisfying the invariant, and prove each preserves the invariant. For the operations marked
"exact", the stated length/flag arithmetic is part of the criterion, not only memory safety:

| Function | Location |
|---------|---------|
| `BorrowedBuf::{capacity, len, is_init}` | `core::io::borrowed_buf` |
| `BorrowedBuf::{filled, filled_mut, into_filled, into_filled_mut}` (exact: the returned slice has length `len()` and starts at the buffer's first element) | `core::io::borrowed_buf` |
| `BorrowedBuf::clear` (exact: `len()` becomes 0; `capacity`/`init` unchanged) | `core::io::borrowed_buf` |
| `BorrowedCursor::{buf_mut, buf_len, unfilled_slice, filled, is_buf_init}` (private helpers; exact: `unfilled_slice` is `buf[filled..]`) | `core::io::borrowed_buf` |
| `BorrowedCursor::{capacity, written, is_init}` (exact: `capacity() + written()` is the parent capacity) | `core::io::borrowed_buf` |
| `BorrowedCursor::advance_checked` (exact: succeeds and grows `written()` by `n` when the next `n` elements are initialized per the `init` flag; panics when `init` is false and `n > 0`, and when `n` exceeds the initialized unfilled length) | `core::io::borrowed_buf` |
| `BorrowedCursor::append` (exact: grows `written()` by the source length and copies the source elements into the filled region; panics if the source is longer than `capacity()`) | `core::io::borrowed_buf` |
| `BorrowedCursor::with_unfilled_buf` (the closure receives a buffer over exactly the unfilled region with the cursor's `init` flag; on return, the cursor's `written()`/`init` reflect the closure's buffer; panics if the closure replaced the buffer — for arbitrary closure behavior expressible through the covered `BorrowedBuf` API) | `core::io::borrowed_buf` |
| `BorrowedCursor::ensure_init` (both branches: no-op returning the unfilled region as `&mut [T]` when already initialized; otherwise initializes every unfilled element, sets `init`, and returns the same region) | `core::io::borrowed_buf` |

For the three `Debug::fmt` bodies (`BorrowedBuf`, `BorrowedBufDebug`, `BorrowedCursor`), a
solution must either exercise them in a harness for at least one element type, or state explicitly
that they are argued from the covered accessors and assumed-correct `core::fmt`, listing them as
not machine-checked.

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Invoking undefined behavior via compiler intrinsics.
* Reading from uninitialized memory except for padding or unions — subject to the explicit
  encoding required under Assumptions (#733): what the tool configuration cannot check must be
  pinned by the flag/length postconditions above and listed as a limit.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
