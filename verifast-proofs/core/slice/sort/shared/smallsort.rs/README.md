# Verification of `smallsort` with VeriFast (Challenge 8)

This directory contains a [VeriFast](../../../../../../doc/src/tools/verifast.md) 26.10 proof for
[Challenge 8: Contracts for SmallSort](../../../../../../doc/src/challenges/0008-smallsort.md), i.e. for
`library/core/src/slice/sort/shared/smallsort.rs`.

With the [caveats](#caveats) listed below, the proof shows:

- **Absence of undefined behavior** for all seven functions in the challenge, for every slice length and
  every comparator, including comparators that are not orders or that mutate their own state, on all
  normal-return paths (unwind paths, i.e. what happens after a comparator panics, are not verified; see
  [Caveats](#caveats)):
  1. `<T as StableSmallSortTypeImpl>::small_sort`
  2. `<T as UnstableSmallSortTypeImpl>::small_sort`
  3. `<T as UnstableSmallSortFreezeTypeImpl>::small_sort`
  4. `swap_if_less`
  5. `insertion_sort_shift_left`
  6. `sort4_stable`
  7. `has_efficient_in_place_swap`
- **Functional correctness** of the three `small_sort` trait methods (all their impls): for every comparator
  that implements a strict weak order, the slice afterwards is a permutation of the slice before, and it is
  sorted with respect to that order. The proof also gives functional specs for `swap_if_less`,
  `insertion_sort_shift_left`, `sort4_stable` and `has_efficient_in_place_swap` (see [Specifications](#specifications)).

Run the proof with `bash verify.sh` (all crates, about 1.5 hours; see [Running the proof](#running-the-proof)).
It is part of `verifast-proofs/check-verifast-proofs.sh`, i.e. of the VeriFast CI job.

## Layout

| Path | Contents |
|---|---|
| `original/smallsort.rs` | Byte-identical copy of `library/core/src/slice/sort/shared/smallsort.rs` (checked by `verify.sh`). |
| `original/lib.rs` | Crate root around the module: re-exports the `core` items the module refers to as `crate::mem`, `crate::{hint, intrinsics, ptr, slice}`, and a copy of the `FreezeMarker` declaration. No executable code. |
| `rewrites/`, `rewritten/` | `rewritten/` = `original/` + the one code rewrite `rewrites/001-*.patch` that refinement-checker cannot check (see [Code changes](#code-changes)); `rewrites/LOG.md` is its review log, `rewrites/tests/` its differential test. |
| `targets/<entry>/[<impl>/]` | The verified crates (`lib.rs`, `smallsort.rs` with specs, proofs and ghost code, `std_extra.rsspec`): one per entry function, and one per impl for the three trait methods. 10 crates. |
| `trusted/` | Master copies of everything trusted. Each crate contains these blocks verbatim (checked). |
| `spec/entry_spec_pins.json`, `tools/` | Pinned entry specs and checks run by `verify.sh` (see [What `verify.sh` checks](#what-verifysh-checks)). |
| `tests/` | Audit scripts (not run by CI): vacuity and consistency probes, soundness probes for the trusted wrappers, tamper tests for `verify.sh`. |
| `verify.sh`, `update.sh` | Proof check (CI), and the merge script used by `verifast-proofs/patch-verifast-proofs.sh`. |

### Why 10 crates

Each `small_sort` trait has a default impl (`impl<T> Trait for T`) and a specialized one
(`impl<T: FreezeMarker> Trait for T`, or `T: FreezeMarker + CopyMarker` for `UnstableSmallSortFreezeTypeImpl`).
VeriFast 26.10 names both methods `<T as Trait>::small_sort`, so it cannot hold specs for both in one crate
("Duplicate function prototype"). Each impl therefore gets its own crate, with the *same* spec:

| Entry function | Crates |
|---|---|
| `<T as StableSmallSortTypeImpl>::small_sort` | `targets/stable_small_sort/default`, `targets/stable_small_sort/specialized` |
| `<T as UnstableSmallSortTypeImpl>::small_sort` | `targets/unstable_small_sort/default`, `targets/unstable_small_sort/specialized` |
| `<T as UnstableSmallSortFreezeTypeImpl>::small_sort` | `targets/unstable_freeze_small_sort/default`, `targets/unstable_freeze_small_sort/copy` |
| `swap_if_less` | `targets/swap_if_less` |
| `insertion_sort_shift_left` | `targets/insertion_sort_shift_left` |
| `sort4_stable` | `targets/sort4_stable` |
| `has_efficient_in_place_swap` | `targets/has_efficient_in_place_swap` |

Every function that has a spec in a crate is verified in that crate (`-skip_specless_fns` only skips functions
without a spec), so the crates together verify every function listed, against its spec, in every impl.

## Specifications

The ghost vocabulary (top of each `smallsort.rs`) defines `is_perm(xs, ys)` (permutation), `sorted_by(lt, xs)`
(no element is `lt` its predecessor), `update_nth`, and uses the trusted comparator model `is_less_models` /
`is_less_model_of` ([Trusted base](#trusted-base)).

All specs move the slice contents (`array::<T>(..) &*& foreach(vs, own::<T>(t))`) and the comparator
(`*is_less |-> f0 &*& <F>.own(t, f0)`) in and back out. This is the memory-safety part: it holds for every
comparator and does not depend on the comparator model. For the safe functions this has the shape of
VeriFast's generated spec (semantic well-typedness), and VeriFast checks that the explicit spec is implied by
the generated one. The functional part is guarded by `is_less_models::<T, F>(f0)`, in the postcondition (a
safe function's precondition cannot assume anything about the comparator). For example, for the default impl
of `StableSmallSortTypeImpl::small_sort`:

```rust
default fn small_sort<F: FnMut(&T, &T) -> bool>(v: &mut [T], _scratch: &mut [MaybeUninit<T>], is_less: &mut F)
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    array::<std::mem::MaybeUninit<T>>(strip_pointer_metadata(_scratch as pointer) as *std::mem::MaybeUninit<T>, _scratch.len(), ?ss) &*&
    foreach(ss, own::<std::mem::MaybeUninit<T>>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    array::<std::mem::MaybeUninit<T>>(strip_pointer_metadata(_scratch as pointer) as *std::mem::MaybeUninit<T>, _scratch.len(), ?ss1) &*&
    foreach(ss1, own::<std::mem::MaybeUninit<T>>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        is_perm(vs1, vs) && sorted_by(is_less_model_of::<T, F>(f0), vs1)
    } else {
        true
    };
@*/
```

The guarantees under `is_less_models(f0)`:

- **`small_sort` (all three traits, all impls):** the result is a permutation of the input, sorted by the order.
- **`insertion_sort_shift_left(v, offset, is_less)`:** the result is a permutation; if `v[..offset]` was sorted, the result is sorted.
- **`swap_if_less(v_base, a_pos, b_pos, is_less)`:** `v[a_pos]` and `v[b_pos]` are swapped exactly when `v[b_pos] < v[a_pos]`; nothing else changes.
- **`sort4_stable(v_base, dst, is_less)`:** `v_base[0..4]` is unchanged and `dst[0..4]` holds its elements, sorted. For every comparator, `dst[0..4]` is a permutation of `v_base[0..4]`.
- **`has_efficient_in_place_swap::<T>()`:** returns `size_of::<T>() <= 8` (no guard needed).

Stability (the relative order of equal elements) is not specified.

The entry specs are pinned in `spec/entry_spec_pins.json`; `verify.sh` rejects a crate whose entry spec
was changed or removed.

## Tour of the proof

All helpers have specs and are verified: `insert_tail`, `insertion_sort_shift_left`,
`small_sort_fallback`, `small_sort_general`, `small_sort_general_with_scratch`, `small_sort_network`,
`sort4_stable`, `sort8_stable`, `sort9_optimal`, `sort13_optimal`, `swap_if_less`, `bidirectional_merge`,
`merge_up`, `merge_down`, `panic_on_ord_violation`. The ghost library (identical in every crate) proves its
lemmas: permutations (`is_perm` is an equivalence; swaps, insertions, appends preserve it), sortedness
(insertion into a sorted list, joining sorted runs), derived order facts (asymmetry, negative transitivity
from the three order axioms), array split/join with explicit counts, and zero-sized-type facts.

- **`insert_tail` / `insertion_sort_shift_left`.** The invariant tracks the "gap" left by the element being
  inserted, held by the `CopyOnDrop` guard. For zero-sized `T`, `sift == begin` does not imply index
  equality; those cases are shown impossible under a well-behaved comparator.
- **`sort4_stable`, `sort8_stable`.** Straight-line proofs over the `select_unpredictable` results; the two
  shared references to the same element are handled by splitting the points-to chunk.
- **`bidirectional_merge`, `merge_up`, `merge_down`.** The forward and backward runs are tracked by their
  consumed counts. The invariant keeps both output runs sorted and each a permutation of the consumed
  inputs. The final check `left == left_end && right == right_end` gives that both runs consumed everything,
  so the output is a sorted permutation; otherwise `panic_on_ord_violation` is called (which never returns).
  The backward pointer may go one element below the slice and back (`wrapping_sub`/`wrapping_add`),
  which the proof handles with exact wrapping-pointer specs.
- **`sort9_optimal`, `sort13_optimal`.** Proven by the 0-1 principle: each compare-exchange commutes with
  every threshold map `x ↦ (c < x)`; the networks sort every 0-1 input (lemmas `net9_01` and `net13_01`,
  checked exhaustively, 512 and 8192 cases); applied with `c` = each output element, every adjacent pair of
  the output is ordered.
- **`small_sort_general_with_scratch`, `small_sort_network`, `small_sort_general`.** The scratch regions are
  tracked by a region predicate; the stack arrays `MaybeUninit<[T; N]>` are converted to element arrays and
  back through their bytes.
- **`<T as UnstableSmallSortTypeImpl>::small_sort`, specialized impl.** It calls
  `<T as UnstableSmallSortFreezeTypeImpl>::small_sort` for a generic `T`. VeriFast resolves such a call to
  the trait declaration, which cannot carry an explicit spec. The call therefore goes through a wrapper
  (`trusted/freeze_small_sort_wrapper.rs`, only in that crate) whose body is the original call
  (refinement-checker) and whose spec is *exactly* the spec of `UnstableSmallSortFreezeTypeImpl::small_sort`
  (`verify.sh` compares the texts). The two impls of that trait (`targets/unstable_freeze_small_sort/default`
  and `.../copy`) are verified against that spec, so whichever impl the call dispatches to satisfies it.
  Those are the only impls (the trait is `pub(crate)`), and neither calls back into `UnstableSmallSortTypeImpl`.

## Code changes

`verify.sh` checks with refinement-checker that the code of every crate refines `rewritten/`. The changes,
identical in every crate:

1. **Calls through wrappers** (checked by refinement-checker, which inlines each wrapper; a wrapper body that
   is not exactly the original call is rejected): `v.as_mut_ptr()` on slices and `MaybeUninit`,
   `wrapping_sub`/`wrapping_add(1)` on `*const T`, `ptr::copy(.., .., 1)`, `MaybeUninit::uninit()`,
   `len + 16`, the comparator calls `is_less(&x, &y)`, and (one crate) the generic freeze `small_sort` call.
   These give VeriFast specs for functions it does not specify, see [Trusted base](#trusted-base).
2. **Two `for` loops written as their own desugaring** (in `bidirectional_merge` and
   `small_sort_general_with_scratch`), so that the iterator can be named in the loop invariant (checked by
   refinement-checker).
3. **Rewrite 001** (`rewrites/001-insert-tail-explicit-guard-drop.patch`; not checkable by refinement-checker,
   so it is a reviewed patch, pinned by hash, and `verify.sh` rebuilds `rewritten/` from `original/` and
   compares). At the end of `insert_tail`'s `unsafe` block, the implicit drop of the guard `gap_guard:
   CopyOnDrop<T>` is written out as `ptr::copy_nonoverlapping(gap_guard.src, gap_guard.dst, gap_guard.len);
   mem::forget(gap_guard);`, i.e. `CopyOnDrop::drop`'s body followed by `mem::forget`. VeriFast 26.10
   translates an implicit drop as a call of `drop_in_place` with its generic spec, which loses the drop's
   write (the write that completes the insertion), so no caller's postcondition could be proven. The
   rewrite is runtime-equivalent: on the normal path the drop executes exactly that body on the current field
   values, `CopyOnDrop<T>` has no fields with drop glue, nothing in between can panic, and the unwind paths
   (comparator panics inside the loop) are unchanged. `rewrites/LOG.md` gives the argument in full;
   `rewrites/tests/run.sh` compares both versions on 12000 random runs (including panicking and inconsistent
   comparators and element types with destructors) in four build configurations, with identical traces.

`lib.rs` is identical in `original/`, `rewritten/` and all crates except the first line comment.
`intrinsics::abort_immediate` is newer than the nightly VeriFast 26.10 is built on, so `lib.rs` re-exports
`core::intrinsics::abort` under that name (both abort immediately).

## Trusted base

Everything trusted lives in `trusted/` and is pinned by a hash in `verify.sh`; every crate must contain each
block verbatim, and `assume` / `assume_correct` may appear nowhere else (`verify.sh` checks both).

1. **Comparator model** (`trusted/comparator_model.rs`). VeriFast's spec of `FnMut::call_mut` says nothing
   about the result, so correctness needs a model: uninterpreted `is_less_models(f)` ("`f` is well-behaved")
   and `is_less_model_of(f)` ("the order `f` computes"), plus three axioms that make that order a strict
   weak order (irreflexive, transitive, incomparability transitive). They are satisfiable by any strict weak
   order; a comparator that is not one simply has `is_less_models(f) == false`, and then only memory safety
   is claimed.
2. **Comparator call wrapper** (`trusted/comparator_call_wrapper.rs`). Every `is_less(&x, &y)` goes through
   `is_less__VeriFast_wrapper(is_less, &x, &y)` (body: exactly the call). Its `assume_correct` spec: for a
   well-behaved comparator the call does not panic, changes neither the comparator nor the values, and
   returns `is_less_model_of(f0)(x, y)`; otherwise nothing is known about the result.
3. **Std wrappers and specs** (`trusted/std_wrappers.rs`, `trusted/std_extra.rsspec`), for std functions
   that VeriFast 26.10 does not specify, following core's documentation:
   `<[T]>::as_mut_ptr`, `MaybeUninit::as_mut_ptr`, `MaybeUninit::uninit`, `<*const T>::wrapping_sub` /
   `wrapping_add` (exact wrapping address, same provenance), the `[0, b].into_iter()` iterator, checked
   `usize + 16`, `hint::select_unpredictable`, `intrinsics::abort`, `usize::is_multiple_of`,
   `slice::from_raw_parts`, and a lemma that a slice length is at most `usize::MAX`. `ptr::copy(src, dst, 1)`
   also goes through a wrapper: VeriFast 26.10's own `ptr::copy` spec does not bound the offset in its
   overlapping case, which allows deriving `false` (`tests/soundness/` has the probe); the wrapper's spec is
   VeriFast's at `count = 1` with the offset bounded. `tools/copy_gate.py` rejects direct `ptr::copy`-family
   calls outside the trusted blocks.
4. **Model axioms** (`trusted/model_axioms.rs`): `<MaybeUninit<T>>.own` holds for every value (VeriFast
   leaves it undefined); the size and alignment of `MaybeUninit<[T; 48]>` and `MaybeUninit<[T; 32]>`
   (arrays of `N` elements aligned as `T`); and `48 * size_of::<T>() <= isize::MAX` for the `T`s the
   `UnstableSmallSortFreezeTypeImpl` impls are instantiated with (they instantiate `[T; 48]`, which rustc
   rejects for larger `T`).
5. **Freeze small-sort wrapper** (`trusted/freeze_small_sort_wrapper.rs`), see the [tour](#tour-of-the-proof).

## Caveats

- **Unwind paths are not verified** (`-ignore_unwind_paths`, as in the LinkedList and RawVec proofs): VeriFast
  26.10 has no way to run ghost code on unwind paths. The `on_unwind_ens` clauses in the specs are not checked.
  The results hold for `panic=abort`, and for the normal-return paths with `panic=unwind`.
- **Reference creation is not checked against Tree Borrows** (`-ignore_ref_creation`): VeriFast 26.10 needs a
  `ref_initialized` fact for `&local` (e.g. `&*tmp` for the `ManuallyDrop` local in `insert_tail`) that no
  lemma provides. Accesses through references and pointers are still checked (dangling, alignment,
  initialization, write permission); only the aliasing-model checks at reference creation are off.
- **Correctness assumes a well-behaved comparator**, through the trusted model above; memory safety does not.
- **Partial correctness.** VeriFast does not prove termination.
- **VeriFast is not foundational** and has [known unsoundnesses](https://github.com/verifast/verifast/blob/master/tests/rust/README.md);
  the proof found and works around one (the `ptr::copy` spec, see [Trusted base](#trusted-base)).
  `verify.sh` also reports when VeriFast's solver prints "Detected an inconsistency"; it does not for this proof.

### Findings about the code

Both are unreachable from the public sort APIs, which return early for zero-sized `T`, but are admitted by
the module-internal function contracts:

- For zero-sized `T` and `len > usize::MAX - 16`, `len + 16` in `small_sort_general_with_scratch` overflows
  (panics with overflow checks, wraps without them). Not UB; the proof uses checked-addition semantics.
- For zero-sized `T` and `18 <= len <= 32`, `small_sort_network` does not terminate (`region.as_ptr() !=
  v_base` never holds since `v_base + len / 2 == v_base`). Not UB (VeriFast proves partial correctness).

## What `verify.sh` checks

1. `original/smallsort.rs` is identical to the library file.
2. The trusted files, the check tools, the entry-spec pins, `rewrites/apply.sh` and the patch match a pinned
   sha256, and `trusted/` has no extra file.
3. `rewritten/` is exactly `original/` + the patch; the freeze wrapper's spec is exactly the spec of
   `UnstableSmallSortFreezeTypeImpl::small_sort` in both of its impl crates.
4. For each crate: it refines `rewritten/` (refinement-checker); its trusted blocks and `std_extra.rsspec`
   are the masters in `trusted/`; the freeze-wrapper block appears only in `unstable_small_sort/specialized`;
   no `assume` outside the trusted blocks; its entry spec is the pinned one (`tools/entry_spec_pin.py`); no
   ghost pointer-constructor tricks known to derive `false` in VeriFast 26.10 (`tools/ghost_gate.py`); no
   direct `ptr::copy` (`tools/copy_gate.py`); and VeriFast reports `0 errors found` with
   `-rustc_args "--edition 2024" -skip_specless_fns -allow_assume -allow_dead_code -ignore_unwind_paths
   -ignore_ref_creation -extern_spec std=std_extra.rsspec` (`--edition 2024` is the edition `core` is built
   with; `-allow_dead_code` because unwind-cleanup code after calls that cannot unwind is unreachable).

Audits done in addition (scripts in `tests/`, not run by CI): `//@ assert false;` at the end of every
proven function's body fails (no vacuous proof, `tests/vacuity_end.sh`), and at the start of every entry body
fails (consistent preconditions, `tests/consistency.sh`); the soundness probes of the comparator and
`ptr::copy` wrappers (`tests/soundness/run.sh`); 13 tampered copies (altered trusted blocks, call sites,
wrapper bodies, gates) are all rejected by `verify.sh` (`tests/tamper.sh`). The vacuity probes were run
on the final proof; the consistency, soundness and tamper scripts were last run on 2026-10-31, before the
model axioms (`trusted/model_axioms.rs`) were added.

## Running the proof

```
cd verifast-proofs/core/slice/sort/shared/smallsort.rs
bash verify.sh                                # all 10 crates
bash verify.sh targets/swap_if_less           # one crate
```

`VFVERSION` defaults to 26.10; if `VERIFAST_HOME` does not exist, VeriFast is downloaded through
`verifast-proofs/setup-verifast-home`. Each run is limited to `VF_TIMEOUT` seconds (default 5400) and, where
a systemd user session exists, to `VF_MEM` memory (default 8G). Times on one core:

| Crate | Time |
|---|---|
| `swap_if_less`, `insertion_sort_shift_left`, `sort4_stable`, `has_efficient_in_place_swap`, `stable_small_sort/default`, `unstable_small_sort/default`, `unstable_small_sort/specialized` | 5–10 s each |
| `stable_small_sort/specialized` | ≈ 26–31 min |
| `unstable_freeze_small_sort/default` | ≈ 29 min |
| `unstable_freeze_small_sort/copy` | ≈ 27 min |

When the library file changes, `verifast-proofs/patch-verifast-proofs.sh` calls `update.sh`, which merges
the change into every crate (`git merge-file`), updates `original/` and rebuilds `rewritten/`.
