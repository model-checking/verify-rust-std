# Challenge 19: Verify the safety of `slice` iter functions - part 2

- **Status:** Open
- **Tracking Issue:** [#29](https://github.com/model-checking/verify-rust-std/issues/29)
- **Start date:** *2025/03/07*
- **End date:** *2025/10/17*
- **Reward:** *?*

-------------------


## Goal

Verify the safety of Iterator functions of [`std::slice`] that are defined in (library/core/src/slice/iter.rs):



### Success Criteria

Write and prove the contract for the safety of the following functions:

| Function | Impl for |
|---------| ---------|
|new| Iter|
|new| IterMut|
|into_slice| IterMut|
|as_mut_slice| IterMut|
|next| Split|
|next_back| Split|
|__iterator_get_unchecked| Windows|
|__iterator_get_unchecked| Chunks|
|next_back| Chunks|
|next| ChunksMut|
|nth| ChunksMut|
|__iterator_get_unchecked| ChunksMut|
|next_back| ChunksMut|
|nth_back| ChunksMut|
|new| ChunksExact|
|__iterator_get_unchecked| ChunksExact|
|new| ChunksExactMut|
|next| ChunksExactMut|
|nth| ChunksExactMut|
|__iterator_get_unchecked| ChunksExact|
|next_back| ChunksExactMut|
|nth_back| ChunksExactMut|
|next| ArrayWindows|
|nth| ArrayWindows|
|next_back| ArrayWindows|
|nth_back| ArrayWindows|
|__iterator_get_unchecked| ArrayChunks|
|__iterator_get_unchecked| ArrayChunksMut|
|next| RChunks|
|__iterator_get_unchecked| RChunks|
|next_back| RChunks|
|next| RChunksMut|
|nth| RChunksMut|
|last| RChunksMut|
|__iterator_get_unchecked| RChunksMut|
|next_back| RChunksMut|
|nth_back| RChunksMut|
|new| RChunksExact|
|__iterator_get_unchecked| RChunksExact|
|new| RChunksExactMut|
|next| RChunksExactMut|
|nth| RChunksExactMut|
|__iterator_get_unchecked| RChunksExactMut|
|next_back| RChunksExactMut|
|nth_back| RChunksExactMut|

The verification must be unbounded---it must hold for slices of arbitrary length.

The verification must be hold for generic type `T` (no monomorphization).

### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory except for padding or unions.
* Mutating immutable bytes.
* Producing an invalid value


Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
