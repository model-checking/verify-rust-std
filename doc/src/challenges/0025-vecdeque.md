# Challenge 25: Verify the safety of `VecDeque` functions

- **Status:** Open
- **Tracking Issue:** [#286](https://github.com/model-checking/verify-rust-std/issues/286)
- **Start date:** *2025-03-07*
- **End date:** *2025-10-17*
- **Reward:** *10000 USD*

-------------------


## Goal

Verify the safety of `VecDeque` functions in (library/alloc/src/collections/vec_deque/mod.rs).


### Success Criteria

Verify the safety of the following functions in (library/alloc/src/collections/vec_deque/mod.rs):

Write and prove the contract for the safety of the following unsafe functions:

| Function |
|---------|
|push_unchecked|
|buffer_read|
|buffer_write|
|buffer_range|
|copy|
|copy_nonoverlapping|
|wrap_copy|
|copy_slice|
|write_iter|
|write_iter_wrapping|
|handle_capacity_increase|
|from_contiguous_raw_parts_in|
|abort_shrink|

Prove the absence of undefined behavior for following safe abstractions:

| Function |
|---------|
|get|
|get_mut|
|swap|
|reserve_exact|
|reserve|
|try_reserve_exact|
|try_reserve|
|shrink_to|
|truncate|
|as_slices|
|as_mut_slices|
|range|
|range_mut|
|drain|
|pop_front|
|pop_back|
|push_front|
|push_back|
|insert|
|remove|
|split_off|
|append|
|retain_mut|
|grow|
|resize_with|
|make_contiguous|
|rotate_left|
|rotate_right|
|rotate_left_inner|
|rotate_right_inner|

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
