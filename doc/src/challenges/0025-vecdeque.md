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

## Verification Summary

All 13 Part A unsafe functions and all 30 Part B safe abstractions have been verified using Kani.

### Part A: Safety Contracts (`#[requires]`/`#[ensures]` with `#[kani::proof_for_contract]`)

All unsafe functions have `#[requires]` contracts formalizing their safety preconditions, verified by `#[kani::proof_for_contract]` harnesses:

| Function | Contract | Harness |
|----------|----------|---------|
| `push_unchecked` | `self.len < self.capacity()` | `check_push_unchecked` |
| `buffer_read` | `off < self.capacity()` | `check_buffer_read` |
| `buffer_write` | `off < self.capacity()` | `check_buffer_write` |
| `buffer_range` | `range.start <= range.end && range.end <= self.capacity()` | `check_buffer_range` |
| `copy` | `len <= cap && src <= cap - len && dst <= cap - len` | `check_copy` |
| `copy_nonoverlapping` | Same as `copy` + non-overlap | `check_copy_nonoverlapping` |
| `wrap_copy` | `min(diff, cap - diff) + len <= cap` | `check_wrap_copy` |
| `copy_slice` | `src.len() <= cap && dst < cap` | `check_copy_slice` |
| `write_iter` | `dst < self.capacity()` | `check_write_iter` |
| `write_iter_wrapping` | `dst < cap && len <= cap` | `check_write_iter_wrapping` |
| `handle_capacity_increase` | `old_cap <= cap && len <= old_cap` | `check_handle_capacity_increase` |
| `from_contiguous_raw_parts_in` | `init.start <= init.end <= capacity` | `check_from_contiguous_raw_parts_in` |
| `abort_shrink` | `target_cap <= cap && len <= target_cap && old_head < cap` | `check_abort_shrink` |
| `rotate_left_inner` | `mid <= self.len() / 2` | `check_rotate_left_inner` |
| `rotate_right_inner` | `k <= self.len() / 2` | `check_rotate_right_inner` |

### Part B: UB Absence Proofs (`#[kani::proof]`)

All safe abstractions verified with `#[kani::proof]` harnesses proving no undefined behavior:

| Function | Harness |
|----------|---------|
| `get` | `check_get` |
| `get_mut` | `check_get_mut` |
| `swap` | `check_swap` |
| `reserve_exact` | `check_reserve_exact` |
| `reserve` | `check_reserve` |
| `try_reserve_exact` | `check_try_reserve_exact` |
| `try_reserve` | `check_try_reserve` |
| `shrink_to` | `check_shrink_to` |
| `truncate` | `check_truncate` |
| `as_slices` | `check_as_slices` |
| `as_mut_slices` | `check_as_mut_slices` |
| `range` | `check_range` |
| `range_mut` | `check_range_mut` |
| `drain` | `check_drain` |
| `pop_front` | `check_pop_front` |
| `pop_back` | `check_pop_back` |
| `push_front` | `check_push_front` |
| `push_back` | `check_push_back` |
| `insert` | `check_insert` |
| `remove` | `check_remove` |
| `split_off` | `check_split_off` |
| `append` | `check_append` |
| `retain_mut` | `check_retain_mut` |
| `grow` | `check_grow` |
| `resize_with` | `check_resize_with` |
| `make_contiguous` | `check_make_contiguous` |
| `rotate_left` | `check_rotate_left` |
| `rotate_right` | `check_rotate_right` |
