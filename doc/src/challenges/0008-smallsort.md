# Challenge 8: Contracts for SmallSort

- **Status:** Open
- **Tracking Issue:** [#56](https://github.com/model-checking/verify-rust-std/issues/56)
- **Start date:** *2024/08/17*
- **End date:** *2025/04/10*
- **Reward:** *10,000 USD*

-------------------


## Goal

The implementations of the traits `StableSmallSortTypeImpl`, `UnstableSmallSortTypeImpl`, and `UnstableSmallSortFreezeTypeImpl` in the `smallsort` [module](https://github.com/rust-lang/rust/blob/master/library/core/src/slice/sort/shared/smallsort.rs) of the Rust standard library are the sorting
algorithms optimized for slices with small lengths.
In this challenge, the goal is to, first prove the memory safety of the public functions in the `smallsort` module, and, second, write contracts for them to
show that the sorting algorithms actually sort the slices.

### Success Criteria

Prove absence of undefined behavior of the following public functions.

1. `<T as slice::sort::shared::smallsort::StableSmallSortTypeImpl>::small_sort`
2. `<T as slice::sort::shared::smallsort::UnstableSmallSortTypeImpl>::small_sort`
3. `<T as slice::sort::shared::smallsort::UnstableSmallSortFreezeTypeImpl>::small_sort`
4. `slice::sort::shared::smallsort::swap_if_less`
5. `slice::sort::shared::smallsort::insertion_sort_shift_left`
6. `slice::sort::shared::smallsort::sort4_stable`
7. `slice::sort::shared::smallsort::has_efficient_in_place_swap`

Write contracts for the following public functions that show that they actually sort the slices.

1. `<T as slice::sort::shared::smallsort::StableSmallSortTypeImpl>::small_sort`
2. `<T as slice::sort::shared::smallsort::UnstableSmallSortTypeImpl>::small_sort`
3. `<T as slice::sort::shared::smallsort::UnstableSmallSortFreezeTypeImpl>::small_sort`

The memory safety and the contracts of the above listed functions must be verified
for all possible slices with arbitrary valid length.

Note that most of the functions listed above call functions that contain loops.
Function contracts and loop contracts of those callee functions may be required.

### List of UBs

In addition to any properties called out as `SAFETY` comments in the source
code,
all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory.
* Mutating immutable bytes.
* Producing an invalid value

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
