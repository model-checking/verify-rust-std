# Challenge 36: Verify the safety of `core::slice::rotate`

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** *Link to issue*
- **Start date:** *2026/11/17*
- **Reward:** *TBD*

-------------------

## Goal

Verify the safety of the in-place slice rotation implementation in
[rotate.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/slice/rotate.rs),
which backs `<[T]>::rotate_left` and `<[T]>::rotate_right`, for arbitrary rotation sizes and for generic
`T`, and verify that it actually rotates.

## Motivation

`rotate_left` and `rotate_right` are safe, stable (and now `const`) slice methods used throughout the
standard library and by user code. All of their work is done by one private unsafe function,
`ptr_rotate`, which picks one of three raw-pointer algorithms at run time according to the size of `T`
and the split point:

- `ptr_rotate_memmove`, which parks the smaller half in a 256-byte `MaybeUninit` stack buffer and uses
  `ptr::copy` / `ptr::copy_nonoverlapping`;
- `ptr_rotate_gcd`, the juggling algorithm, which walks the cycles of the permutation
  `i -> i + right (mod left + right)` with `read` / `replace` / `write`, computing the number of cycles
  (the gcd) as a side effect of the first cycle;
- `ptr_rotate_swap`, the Gries--Mills block-swap algorithm, which repeatedly applies
  `ptr::swap_nonoverlapping` to adjacent blocks whose sizes are the residues of a Euclidean algorithm.

The safety argument at each pointer operation rests on arithmetic facts that are written only in prose:
that the gcd walk never leaves `[0, left + right)` (the `[long-safety-expl]` comments), that the value
computed as a side effect really is the cycle count and so bounds the starting offsets of the remaining
cycles, and that the block swaps stay inside the range while `mid` walks back and forth. A mistake of one
in any of these reads or writes an element outside the slice that safe code handed to `rotate_left`, or
duplicates or loses an element of a type with a destructor. We know of no soundness bug reported against
this file; the case for the challenge is that the argument is subtle, serves a safe API, and has no
machine-checked statement.

## Description

`ptr_rotate(left, mid, right)` rotates the range `[mid - left, mid + right)` so that the element at
`mid` becomes the first. It returns at once for zero-sized `T` and for a zero split. Otherwise, unless
the crate is built with `optimize_for_size`, it uses the memmove strategy when the smaller side fits in
the stack buffer (`min(left, right) <= size_of::<[usize; 32]>() / size_of::<T>()`), else the gcd strategy
when `left + right < 24` or `size_of::<T>() > size_of::<[usize; 4]>()`, else the block-swap strategy.
Its only callers are `rotate_left` and `rotate_right` in `core::slice`, which pass the length checks of
the safe API. The file also contains a `const`-compatible `const_min`.

The following are out of scope:

- The rotation-like block moves inside `core::slice::sort` (they do not call this file).
- `rotate_left` / `rotate_right` panic behavior for a split larger than the length (it is a plain
  `assert!` before any unsafe code; a proof of `ptr_rotate` under its precondition covers the unsafe
  part of both methods).
- Performance of the strategy choice.

No existing challenge lists a function of `core::slice::rotate`. The primitives it uses
(`ptr::copy_nonoverlapping`, `ptr::swap_nonoverlapping`, `<*mut T>::replace`) are targets of
[Challenge 2](0002-intrinsics-memory.md) and [Challenge 3](0003-pointer-arithmentic.md); their
verification is not repeated here.

### Assumptions

- `core::ptr` intrinsics and `core::mem::MaybeUninit` may be assumed correct, and their existing
  verified contracts may be reused. Deductive tools may rely on their own specifications of these.
- The safety precondition of each function is the one in its `# Safety` documentation: the range
  `[mid - left, mid + right)` is valid for reading and writing elements of `T`. For non-zero-sized `T`
  this includes the usual requirement that the byte size of the range does not exceed `isize::MAX`.
  A contract may add a side condition only where the function is in fact never called without it and
  the condition is recorded next to the contract; in particular the gcd and block-swap strategies are
  only ever called with `left > 0`, `right > 0` and non-zero-sized `T`, and the memmove strategy only
  when the smaller side fits in its buffer.
- Proofs must cover every strategy, including the branches taken when the crate is built with
  `optimize_for_size` (in that configuration only the block-swap strategy runs, so proving each
  strategy under its own precondition covers both configurations).
- No user code runs during a rotation (`T` is moved, never dropped or cloned by the rotation itself),
  so unwinding need not be modeled. Dropping the rotated elements afterwards must still be safe: no
  element may be duplicated or lost.

### Success Criteria

Write and prove a safety contract for each of the following unsafe functions, with the precondition
above (restricted as recorded for the three strategies), stating that the range is still valid for
reading and writing afterwards:

| Function | Location |
|---------|---------|
| `ptr_rotate` | `core::slice::rotate` |
| `ptr_rotate_memmove` | `core::slice::rotate` |
| `ptr_rotate_gcd` | `core::slice::rotate` |
| `ptr_rotate_swap` | `core::slice::rotate` |

Prove the absence of undefined behavior in these functions, including the early returns for
zero-sized `T` and for `left == 0` or `right == 0`, and all three dispatch branches of
`ptr_rotate`. For `ptr_rotate` on inputs that take the memmove branch, and for
`ptr_rotate_memmove` itself, this must hold for arbitrary `left` and `right` (unbounded: no fixed
bound on `left + right` other than the one in the precondition). For the gcd and block-swap
strategies it must hold for every split with `left + right <= B`, with `B >= 24` stated in the
solution (the dispatcher's whole small-total region for the gcd strategy), for the reason given
under functional correctness below; a proof for arbitrary `left` and `right` exceeds this
criterion and is welcome. `const_min` is safe code with no unsafe operations; its result is the
smaller of its arguments, which the dispatch proof may rely on.

The verification must hold for generic `T` (what satisfies this clause is to be decided in
[issue #734](https://github.com/model-checking/verify-rust-std/issues/734)). In particular it must
cover zero-sized `T`, sizes that do and do not divide the memmove buffer, alignments above `usize`,
elements larger than the buffer, types with a validity invariant (such as `NonZero`), and types with a
destructor, for each of which the safety argument takes a different branch somewhere in the file.

Prove functional correctness of the rotation: after `ptr_rotate(left, mid, right)`, the element at
each position `j` of `[mid - left, mid + right)` is the element previously at position
`(j + left) mod (left + right)` of that range. This must be proved for each of the three strategies.
For the memmove strategy it must be proved for arbitrary `left` and `right`. For the gcd and
block-swap strategies, whose loop invariants in a bounded model checker cannot name the input
arrangement of a generic `T`, it is enough to prove it for every `left` and `right` with
`left + right <= B`, where `B` is stated in the solution and `B >= 24` (so the whole input range in
which the dispatcher prefers the gcd strategy for small totals is included), for element types whose
values can be told apart. Solutions that prove the rotation postcondition for arbitrary `left` and
`right` for all three strategies (for example with ghost state in a deductive tool) are welcome and
exceed this criterion. The same bound `B` may be used for the safety proof of those two strategies, as stated above.

### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Invoking undefined behavior via compiler intrinsics.
* Reading from uninitialized memory except for padding or unions.
* Producing an invalid value

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
