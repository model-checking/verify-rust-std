# Partial verification of `core::slice` with VeriFast

With certain [caveats](#caveats), this proof verifies [soundness](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) (absence of Undefined Behavior and semantic well-typedness) and functional specifications for core slice operations across `core/src/slice/mod.rs`, `core/src/slice/raw.rs`, and `core/src/slice/rotate.rs`:

- **Slice queries and pointer conversions (`[T]`)**:
  - `len`, `as_ptr`, `as_mut_ptr`, `as_mut_ptr_range`
- **Raw slice construction (`core::slice::raw`)**:
  - `from_raw_parts`, `from_raw_parts_mut`
- **Unchecked indexing and splitting (`[T]`)**:
  - `get_unchecked`, `get_unchecked_mut`
  - `split_at`, `split_at_mut`, `split_at_unchecked`, `split_at_mut_unchecked`, `split_at_checked`, `split_at_mut_checked`
- **Fixed-size array chunking and flattening (`[T]` and `[[T; N]]`)**:
  - `first_chunk`, `first_chunk_mut`, `split_first_chunk`, `split_first_chunk_mut`, `split_last_chunk`, `split_last_chunk_mut`, `last_chunk`, `last_chunk_mut`
  - `as_chunks`, `as_chunks_unchecked`, `as_chunks_mut`, `as_chunks_unchecked_mut`, `as_rchunks`, `as_rchunks_mut`
  - `as_flattened`, `as_flattened_mut`
- **In-place permutation, reversal, and rotation (`[T]` and `core::slice::rotate`)**:
  - `swap_unchecked`, `reverse` (and internal `revswap`)
  - `rotate_left`, `rotate_right`
  - `ptr_rotate`, `ptr_rotate_memmove`, `ptr_rotate_gcd`, `ptr_rotate_swap`, `const_min`
- **Bulk copying and swapping (`[T]`)**:
  - `copy_from_slice` (and internal `copy_from_slice_impl`), `copy_within`, `swap_with_slice`
- **Searching and deduplication (`[T]`)**:
  - `binary_search_by`, `partition_dedup_by`
- **Transmutation and alignment (`[T]`)**:
  - `align_to`, `align_to_mut` (and internal `gcd`, `align_to_offsets`), `as_simd`, `as_simd_mut`
- **Disjoint mutable indexing (`[T]` and `GetDisjointMutIndex`)**:
  - `get_disjoint_mut`, `get_disjoint_unchecked_mut`, `get_disjoint_check_valid`
  - `GetDisjointMutIndex::is_in_bounds` and `GetDisjointMutIndex::is_overlapping` for `Range<usize>` and `RangeInclusive<usize>`

## Tour of the proof

### Crate setup and `refinement-checker`

Because `core::slice` is part of `core` itself, verifying `core/src/slice/mod.rs` with `rustc` requires compiling against a version of `core` that does not duplicate the slice inherent implementations under test (`libcore_noslice.rlib`), created by `verify.sh`. That sysroot `core` is built from the `rust-src` component of the Rust toolchain that VeriFast 26.10 targets (`nightly-2026-09-25`, see `setup-verifast-home`), not from this repository's `library/core` subtree: VeriFast's `rustc` frontend can only compile a `core` that matches its own nightly, while the subtree tracks a newer one (at the time of writing `nightly-2026-10-12`, whose `abort_immediate`/`type_id_*` intrinsics and stabilized `optimize` attribute the older frontend rejects). The files under verification (`slice.rs`, `slice/raw.rs`, `slice/rotate.rs`) are the repository's, byte-for-byte; only the surrounding `core` they are compiled against comes from VeriFast's toolchain, in the same way that the `LinkedList` and `RawVec` proofs verify the repository's `alloc` sources against VeriFast's own `std` specifications.

As in the `RawVec` and `LinkedList` proofs, verification proceeds in three steps in `verify.sh`:
1. **`verifast`** verifies `verified/lib.rs` (which includes `verified/slice.rs`, `verified/slice/raw.rs`, and `verified/slice/rotate.rs`) with `0 errors found`.
2. **`refinement-checker`** checks that `original/lib.rs` is refined by `verified/lib.rs` with `0 errors`, ensuring that any syntactic rewrites or helper wrappers introduced for VeriFast preserve the exact MIR semantics of the original code.
3. **`diff`** checks that `original/slice.rs`, `original/slice/raw.rs`, and `original/slice/rotate.rs` are byte-for-byte identical to `library/core/src/slice/mod.rs`, `library/core/src/slice/raw.rs`, and `library/core/src/slice/rotate.rs`.

### Ownership and borrowing of slices

In VeriFast's RustBelt separation logic encoding:
- **Raw contiguous array ownership** at pointer `p: *T` of length `len` is represented by `p[..len] |-> ?elems` (where `elems: list<T>` has `length(elems) == len`), together with element-wise thread ownership `foreach(elems, own::<T>(t))` when exclusive semantic ownership of elements is required.
- **Shared slice references (`&'a [T]`)** are represented by the duplicable shared ownership predicate `[_](<[T]>.share('a, t, s))`. By lemma `slice_share_inv`, shared ownership of a slice `s` guarantees that its metadata length satisfies `s.len() * std::mem::size_of::<T>() <= isize::MAX` and `pointer_within_limits(strip_pointer_metadata(s as pointer) as *T) == true`.
- **Mutable slice references (`&'a mut [T]`)** whose lifetime `'a` appears in the return type (such as `split_at_mut`, `first_chunk_mut`, `align_to_mut`, `partition_dedup_by`) are represented using a full borrow `full_borrow('a, <[T]>.full_borrow_content(t, s))` accompanied by a fractional `lifetime_token('a)`. Functions that mutate a slice in place without returning sub-borrows tied to `'a` (such as `swap_unchecked`, `rotate_left`, `rotate_right`, `copy_from_slice`, `copy_within`, `swap_with_slice`) operate directly on the array points-to resource `((strip_pointer_metadata(self as pointer) as *T)[..self.len()] |-> ?elems)` and provide a `safety_proof` block that opens `<[T]>.full_borrow_content(t, self)` before `call()` and closes it afterwards.

### Raw slice construction (`from_raw_parts` and `from_raw_parts_mut`)

In `verified/slice/raw.rs`, `from_raw_parts` and `from_raw_parts_mut` construct shared and mutable slice references from a raw pointer `data` and length `len`:

```rust
pub const unsafe fn from_raw_parts<'a, T>(data: *const T, len: usize) -> &'a [T]
//@ req thread_token(?t) &*& [_](<[T]>.share('a, t, ptr::mk_slice::<T>(data, len)));
//@ ens thread_token(t) &*& result == ptr::mk_slice::<T>(data, len) &*& [_](<[T]>.share('a, t, result));
//@ on_unwind_ens false;
{
    unsafe { &*ptr::slice_from_raw_parts(data, len) }
}
```

### Splitting slices (`split_at` and `split_at_mut`)

`split_at_unchecked` and `split_at_mut_unchecked` require `0 <= mid &*& mid <= self.len()` and split a shared borrow `[_](<[T]>.share('a, t, self))` (via `array_share_split`) or full borrow `full_borrow('a, <[T]>.full_borrow_content(t, self))` (via `open_full_borrow_strong_` and `full_borrow_split`) at index `mid` into two contiguous sub-slices of lengths `mid` and `self.len() - mid`:

```rust
pub const unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut [T], &mut [T])
//@ req thread_token(?t) &*& [?q]lifetime_token(?k) &*& full_borrow(k, <[T]>.full_borrow_content(t, self)) &*& 0 <= mid &*& mid <= self.len();
//@ ens thread_token(t) &*& [q]lifetime_token(k) &*& full_borrow(k, <[T]>.full_borrow_content(t, result.0)) &*& full_borrow(k, <[T]>.full_borrow_content(t, result.1)) &*& result.0.len() == mid &*& result.1.len() == self.len() - mid;
//@ on_unwind_ens false;
```

The safe functions `split_at_checked`, `split_at_mut_checked`, `split_at`, and `split_at_mut` check `mid <= self.len()` and then delegate to `split_at_unchecked` / `split_at_mut_unchecked`, proving semantic well-typedness without callers needing any precondition beyond standard type interpretations.

### In-place rotation (`rotate_left`, `rotate_right`, and `core::slice::rotate`)

`rotate_left` and `rotate_right` validate `mid <= self.len()` (or `k <= self.len()`) and invoke `slice::rotate::ptr_rotate(left, mid_ptr, right)` on the underlying buffer split at `mid`:

```rust
pub(super) const unsafe fn ptr_rotate<T>(left: usize, mid: *mut T, right: usize)
//@ req (mid - left)[..left] |-> ?elems_left &*& mid[..right] |-> ?elems_right &*& (left + right) * std::mem::size_of::<T>() <= isize::MAX;
//@ ens (mid - left)[..left + right] |-> ?elems_out &*& length(elems_out) == left + right;
//@ on_unwind_ens false;
```

In `verified/slice/rotate.rs`, all three rotation algorithms in `core::slice::rotate` are verified against this contract:
1. **`ptr_rotate_memmove`**: Copies the smaller of the `left` or `right` segments into a temporary stack buffer `Rawarray<T>`, shifts the remaining elements via `ptr::copy`, and copies the buffered elements into place.
2. **`ptr_rotate_gcd`**: Divides the array into cycles using greatest-common-divisor stride arithmetic and shifts elements around each cycle using `ptr_replace` and `ptr::swap_nonoverlapping`.
3. **`ptr_rotate_swap`**: Iteratively swaps min-length blocks across the pivot `mid` using `ptr::swap_nonoverlapping` and adjusts `left`, `mid`, and `right` until one side reaches zero.

## Caveats

First of all, this proof was performed with the following VeriFast command-line flags:
- `-skip_specless_fns`: VeriFast ignores the functions that do not have a `req` or `ens` clause.
- `-ignore_unwind_paths`: This proof ignores code that is reachable only when unwinding.
- `-allow_assume`: This proof uses `assume` ghost statements and `assume_correct` clauses in the following specific places, which must be audited:
  - **RustBelt lifetime-logic reborrowing / transmutation and tuple-ownership bridge lemmas**:
    - `close_slice_pair_own`, `close_mut_slice_pair_own`, `close_slice_triple_own`, `close_mut_slice_triple_own`, `close_Range_own`: In VeriFast 26.10, `prelude.rsspec` declares `std_tuple_2_<T1, T2>` and `std_tuple_3_<T1, T2, T3>` as `struct` types (`rust_parser.ml:1147` generates uninterpreted `std_tuple_2__own` and `std_tuple_3__own` predicates for `struct` types), and `prelude.rsspec` only provides `close_tuple_0_own` and `close_tuple_4_own`. Similarly, `rust/std/lib.rsspec` declares `struct Range<Idx>` without a `close_Range_own` lemma.
    - `slice_share_inv`, `pointer_metadata_as_usize_limits`, `share_slice_prefix_as_chunk`, `full_borrow_slice_prefix_as_chunk`, `share_slice_as_chunks`, `full_borrow_slice_as_chunks`, `share_chunks_as_flattened`, `full_borrow_chunks_as_flattened`, `share_transmute_middle`, `full_borrow_transmute_middle`, `open_shared_slice_copy`, `close_shared_slice_copy`, `copy_trait_bound`, `copy_elem_own_dup`, `disjoint_mut_loop_*`, and `rawarray_to_buf` / `buf_to_rawarray` in `rotate.rs`: Helper lemmas that axiomatize RustBelt shared/full borrow conversion and transmutation across fixed-size array chunks (`is_array_of::<T, Chunk>(n)`), `Copy` slices, stack `Rawarray` buffers, and disjoint index sets. Note that `split_at_unchecked`, `split_at_mut_unchecked`, `slice_full_borrow_inv`, `flatten_non_zst_no_overflow`, `gcd_proof__VeriFast_wrapper`, and `align_to_offsets_proof__VeriFast_wrapper` are proved mechanically without `assume(false)`, and `T::IS_ZST` branches are discharged mechanically via `std::alloc::is_valid_layout_size_of_align_of` without inline `assume` statements.
  - **Const-generic functions (`<const N: usize>`) and `is_array_of::<T, Chunk>(n)`**: In VeriFast 26.10, placing a specification directly on a function with a const-generic parameter `const N: usize` fails in `verifast` with `error: Todo: ConstKind::Param` (`vf_mir_translator.ml:1787`), and calling a helper from a `<const N: usize>` function fails in `refinement-checker` with `Fatal error: exception Failure("Clause kind not supported")` (`refinement_checker.ml:2338`, triggered by `ClauseKind::ConstArgHasType`). Therefore, const-generic array chunking, flattening, SIMD, and `get_disjoint_mut` functions are verified via parametric helper functions taking `(Chunk, n: usize)` with concrete `fix is_array_of<T, Chunk>(n: usize) -> bool` (or `&[I]` for `get_disjoint_*`).
  - **Single local macro `vf_revswap!` in `reverse`**: `reverse` defines a nested generic function `fn revswap<T>(a: &mut [T], b: &mut [T], n: usize)`. In VeriFast 26.10, `vf_mir_exporter/src/lib.rs:434,940` only matches top-level `ItemKind::Fn` and `ItemKind::Impl`, ignoring inline specifications on functions nested inside a statement block, and `rust_parser.ml:1036` rejects `impl<T> [T]` in `.rsspec` files. Therefore `revswap` is verified as the top-level function `revswap_proof__VeriFast_wrapper` and invoked via `vf_revswap!` while keeping `revswap` in place for `refinement-checker`.
  - **`assume_correct` on low-level primitive / external wrappers**: `[T]::len` is verified directly against `ptr::metadata` in `core.rsspec`, and `exact_div_usize__VeriFast_wrapper` is verified directly against `intrinsics::exact_div`. In `align_to_offsets`, the inline `const { gcd(size_of::<T>(), size_of::<U>()) }` block is translated by `vf_mir_translator.ml:2228` to `std::verifast::unevaluated_constant::<usize>()` (`std/lib.rsspec:15`, which discards the `const` block body and has postcondition `ens true`), and its nested `const fn gcd` item is ignored by `vf_mir_exporter/src/lib.rs:434,940`; therefore `align_to_offsets` is annotated with `//@ assume_correct` for callers while its complete body and `gcd` are verified without `assume_correct` or `assume(false)` in `align_to_offsets_proof__VeriFast_wrapper` and `gcd_proof__VeriFast_wrapper`. Thin wrappers around external library calls or unsupported MIR constructs (`slice_index_mut__VeriFast_wrapper`, `slice_index_shared__VeriFast_wrapper`, `slice_range__VeriFast_wrapper`, `empty_slice__VeriFast_wrapper`, `empty_mut_slice_arg__VeriFast_wrapper`, `call_same_bucket__VeriFast_wrapper`, `checked_mul_or_panic__VeriFast_wrapper`, `clone_disjoint_index__VeriFast_wrapper`, `write_disjoint_mut_elem__VeriFast_wrapper`, `uninit_buf__VeriFast_wrapper`, `uninit_buf_as_mut_ptr__VeriFast_wrapper`, `ptr_replace__VeriFast_wrapper`) use `//@ assume_correct` because `vf_mir_translator.ml:418` hardcodes `[ prelude_path ]` (`prelude.rsspec` only, excluding `rust/std/lib.rsspec`) as the header dependency list of `-extern_spec` files (preventing `Option`, `Range`, and `MaybeUninit` from being referenced in `core.rsspec`), and `rust_parser.ml:1036` rejects `impl<T> *mut T` in `.rsspec` files.

Secondly, since VeriFast uses the `rustc` frontend, which assumes a particular target architecture, VeriFast's results hold only for the used Rust toolchain's target architecture (and, as explained above, the slice sources are compiled against the `core` of VeriFast's own toolchain, `nightly-2026-09-25`, rather than the `core` of the subtree they were taken from). When VeriFast reports "0 errors found" for a Rust program, it always reports the targeted architecture as well (e.g. `0 errors found (1712 statements verified) (target: arm64-apple-macosx (LP64))`).

Thirdly, VeriFast has a number of [known unsoundnesses](https://github.com/verifast/verifast/issues?q=is%3Aissue+is%3Aopen+label%3Aunsoundness) (reasons why VeriFast might in some cases incorrectly accept a program), including the following:
- VeriFast does not yet fully verify compliance with Rust's [pointer aliasing rules](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).
- VeriFast does not yet properly verify compliance of custom type interpretations with Rust's [variance](https://doc.rust-lang.org/reference/subtyping.html#variance) rules.

Fourthly, unlike foundational tools such as [RefinedRust](https://plv.mpi-sws.org/refinedrust/), VeriFast has not itself been verified, so there are undoubtedly also unknown unsoundnesses. Such unsoundnesses might exist in VeriFast's [symbolic execution engine](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2531006855) [itself](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2534922580) or in its [prelude](https://github.com/verifast/verifast/tree/master/bin/rust) (definitions and axioms automatically imported at the start of every verification run) or in the [specifications](https://github.com/verifast/verifast/blob/master/bin/rust/std/lib.rsspec) it uses for the Rust standard library functions called by the program being verified.
