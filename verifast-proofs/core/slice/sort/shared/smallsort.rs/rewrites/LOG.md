# Code rewrites: review log

`rewrites/apply.sh` applies the patches `rewrites/NNN-*.patch` in order to `original/` (byte-identical to the
library file `library/core/src/slice/sort/shared/smallsort.rs`) to produce `rewritten/`. `verify.sh` pins the
patch set and `apply.sh` (sha256), rebuilds `rewritten/` from `original/` and compares, and checks with
refinement-checker that every target crate's code refines `rewritten/`.

"Runtime-equivalent" means: for every input, the same results, side effects (memory writes, calls of the
comparator, drops) and panic-vs-no-panic behaviour, with `-C overflow-checks` on and off and
`-C debug-assertions` on and off.

Only changes that refinement-checker cannot check are patches here. The other code changes of the target
crates (calls of trusted wrappers in place of the calls they wrap, and two `for` loops written as their own
desugaring) are checked by refinement-checker against `rewritten/` (README.md, "Code changes").

## 001-insert-tail-explicit-guard-drop

- **Location:** `insert_tail`, end of its `unsafe` block (after the `loop`).
- **Original:** the block ends; `gap_guard: CopyOnDrop<T>` goes out of scope and is dropped, i.e.
  `<CopyOnDrop<T> as Drop>::drop(&mut gap_guard)` runs, whose body is
  `ptr::copy_nonoverlapping(self.src, self.dst, self.len)`. (`tmp: ManuallyDrop<T>` has no drop glue.)
- **Rewritten:** the same block ends with
  `ptr::copy_nonoverlapping(gap_guard.src, gap_guard.dst, gap_guard.len); mem::forget(gap_guard);`.
- **VeriFast error removed:** VeriFast 26.10 translates the implicit drop of a local whose type has a `Drop`
  impl as a call of `std::ptr::drop_in_place` with its generic spec (`req <T>.own(t, v); ens *to_drop |-> _`),
  so the effect of the drop, the write of `tmp` into the gap that completes the insertion, cannot be
  expressed: every caller's sortedness/permutation postcondition is unprovable. (Probe: a `Drop` impl that
  writes through a field is not reflected at the caller.)
- **Equivalence:** on the normal path the drop of `gap_guard` executes exactly `CopyOnDrop::drop`'s body on
  the current field values, which is the inserted call; `mem::forget` then suppresses the drop, and
  `CopyOnDrop<T>` has no fields with drop glue (two raw pointers and a `usize`), so forgetting it has no other
  effect. Nothing between the end of the loop and the end of the block can panic in either version. The
  unwind paths (a comparator panic inside the loop) are unchanged: the guard is still live there and is
  dropped by unwinding exactly as before. After the rewrite `CopyOnDrop::drop` runs only while unwinding, in
  every function of the module (`small_sort_general_with_scratch` already forgets its guard on the normal
  path).
- **Evidence:** `rewrites/tests/run.sh` builds `rewrites/tests/difftest/main.rs`, which contains both
  `original/smallsort.rs` and `rewritten/smallsort.rs` as modules, with nightly-2026-10-12 in the four
  configurations `-C overflow-checks={on,off}` x `-C debug-assertions={on,off}`. It runs 4000 random cases per
  version (lengths 0..39, values with many duplicates, offsets 1..len) of `insertion_sort_shift_left` on
  `i64` and on a type with a destructor that counts drops, and of the three trait `small_sort`s, with four
  comparators: a correct `<`, random answers, a correct `<` that panics at the k-th call (caught with
  `catch_unwind`; the slice is printed after the panic), and an inconsistent reversed order. The 12000-line
  traces (results, panic/no-panic, slice contents after return or panic, drop counts) of the two versions are
  identical in all four configurations (`trace_*.txt`, `result_*.txt`); 2377 of the 12000 runs panic, and no
  run drops an element during sorting (no duplication or loss, also under panics).
