# Challenge 31: Verify the safety of `BinaryHeap` functions

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** [#746](https://github.com/model-checking/verify-rust-std/issues/746)
- **Start date:** *2026/11/03*
- **Reward:** *TBD*

-------------------


## Goal

Verify the safety of `BinaryHeap` functions in (library/alloc/src/collections/binary_heap/mod.rs).

## Motivation

`BinaryHeap` is the priority queue of the standard library. To keep its elements in heap order, it moves them with raw pointer reads and copies, at positions chosen by comparing elements with `Ord`. `Ord` is safe code written by users and can return any result, so these moves must be safe even when the comparisons are inconsistent.

### Success Criteria

Verify the safety of the following functions in (library/alloc/src/collections/binary_heap/mod.rs):

Write and prove the contract for the safety of the following unsafe functions:

| Function |
|---------|
|Hole::new|
|Hole::get|
|Hole::move_to|
|sift_up|
|sift_down_range|
|sift_down|
|sift_down_to_bottom|

Prove that the following implementations of the unsafe trait `TrustedLen` are correct, that is, that `size_hint` returns the exact number of remaining elements:

| Implementation |
|---------|
|TrustedLen for IntoIterSorted|
|TrustedLen for DrainSorted|

Prove the absence of undefined behavior for following safe abstractions:

| Function |
|---------|
|push|
|pop|
|peek_mut|
|PeekMut::deref|
|PeekMut::deref_mut|
|PeekMut::pop|
|PeekMut::refresh|
|Drop for PeekMut|
|rebuild|
|rebuild_tail|
|append|
|into_sorted_vec|
|From<Vec<T>>|
|IntoIterSorted::next|
|DrainSorted::next|
|Drop for Hole|

The unsafe functions `from_raw_vec` and `as_mut_slice` require callers to keep the contents a max-heap. This is a correctness requirement, not a safety one, so the functions above must be safe even when the contents are not a max-heap.

The verification must be unbounded---it must hold for heaps of arbitrary length.

The verification must hold for generic type `T` (what satisfies this clause is to be decided in [issue #734](https://github.com/model-checking/verify-rust-std/issues/734)).

The verification must hold for any implementation of `Ord` for `T`, including ones that return inconsistent results.

### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory except for padding or unions.
* Producing an invalid value


Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
