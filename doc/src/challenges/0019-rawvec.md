# Challenge 19: Verify the safety of `RawVec` functions

- **Status:** Resolved
- **Tracking Issue:** [#283](https://github.com/model-checking/verify-rust-std/issues/283)
- **Start date:** *2025-03-07*
- **End date:** *2025-08-12*
- **Reward:** *10000 USD*
- **Contributors:** [Bart Jacobs](https://github.com/btj)

-------------------


## Goal

Verify the safety of `RawVec` functions in (library/alloc/src/raw_vec/mod.rs).

## Motivation 

`RawVec` is the type of the main component of both `Vec` and `VecDeque`: the buffer. Therefore, the safety of the functions of `Vec` and `VecDeque` depend on the safety of `RawVec`.

### Success Criteria

Verify the safety of the following functions in (library/alloc/src/raw_vec/mod.rs):

Write and prove the contract for the safety of the following unsafe functions:

| Function |
|---------|
|new_cap|
|into_box|
|from_raw_parts_in|
|from_nonnull_in|
|set_ptr_and_cap|
|shrink_unchecked|
|deallocate|

Prove the absence of undefined behavior for following safe abstractions:

| Function |
|---------|
|drop|
|new_in|
|with_capacity_in|
|try_allocate_in|
|current_memory|
|try_reserve|
|try_reserve_exact|
|grow_amortized|
|grow_exact|
|shrink|
|finish_grow|

The verification must be unbounded---it must hold for slices of arbitrary length.

The verification must hold for generic type `T` (no monomorphization).

### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory except for padding or unions.
* Mutating immutable bytes.
* Producing an invalid value


Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
