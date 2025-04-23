# Challenge 17: Verify the safety of `slice` functions

- **Status:** Open
- **Tracking Issue:** [#281](https://github.com/model-checking/verify-rust-std/issues/281)
- **Start date:** *2025-03-07*
- **End date:** *2025-10-17*
- **Reward:** *10000 USD*

-------------------


## Goal

Verify the safety of `std::slice` functions in (library/core/src/slice/mod.rs).


### Success Criteria

For the following unsafe functions (in library/core/src/slice/mod.rs):
- Write contracts specifying the safety precondition(s) that the caller must uphold, then
- Verify that if the caller respects those preconditions, the function does not cause undefined behavior.

| Function |
|---------|
|get_unchecked| 
|get_unchecked_mut| 
|swap_unchecked| 
|as_chunks_unchecked| 
|as_chunks_unchecked_mut| 
|split_at_unchecked| 
|split_at_mut_unchecked| 
|align_to|
|align_to_mut|
|get_disjoint_unchecked_mut|

Prove that the following safe abstractions (in library/core/src/slice/mod.rs) do not cause undefined behavior:

| Function |
|---------|
|first_chunk| 
|first_chunk_mut| 
|split_first_chunk|
|split_first_chunk_mut| 
|split_last_chunk|
|split_last_chunk_mut| 
|last_chunk| 
|last_chunk_mut| 
|reverse| 
|as_chunks| 
|as_chunks_mut| 
|as_rchunks| 
|split_at_checked| 
|split_at_mut_checked| 
|binary_search_by| 
|partition_dedup_by|
|rotate_left|
|rotate_right|
|copy_from_slice|
|copy_within|
|swap_with_slice|
|as_simd|
|as_simd_mut|
|get_disjoint_mut|
|get_disjoint_check_valid|
|as_flattened|
|as_flattened_mut|

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
