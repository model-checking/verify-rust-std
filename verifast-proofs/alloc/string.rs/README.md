# Memory safety of the Challenge 10 String APIs

This proof targets the repository's [String implementation](../../../library/alloc/src/string.rs)
for [Challenge 10](../../../doc/src/challenges/0010-string.md).

| Tool | API coverage | Input size |
| --- | --- | --- |
| VeriFast | `from_utf16le`, `from_utf16le_lossy`, `from_utf16be`, `from_utf16be_lossy`, `remove_matches`, `insert_str`, `split_off`, `replace_range` | All lengths admitted by Rust's allocation and slice invariants |
| VeriFast | `retain` | All lengths under the fixed implementation argument below. The documented safety precondition remains a review item. |
| VeriFast | `pop`, `remove`, `insert`, `drain`, `into_boxed_str`, `leak` | All lengths admitted by the same invariants |
| Kani | `remove` | Eight fixed cases, an arbitrary scalar surrounded by arbitrary ASCII in a six-byte String, and separate panic checks for indices inside a scalar, at the end, and past the end |
| Kani | `into_boxed_str` | Up to two arbitrary Unicode scalars and allocation requests up to nine bytes |

The VeriFast proof tracks initialized bytes, allocation ownership and write
permissions for raw pointer accesses. The `String` ownership and reference
predicates require valid UTF-8. Character-producing operations establish the
Unicode scalar invariant. The iterator proof also covers `Drain::next`,
`Drain::next_back` and the algorithm in `Drain::drop`.

The lossy UTF-16 paths use the actual `String` character collector. The
proof starts with an empty allocation, preserves the initialized prefix
through reservation, and checks the capturing closure that calls
`String::push` for each scalar. Ownership of valid UTF-8 is restored after
each push and on unwind. The verifier checks which collector implementations
rustc chose for the native and byte-order-specific iterator types.

For `remove_matches`, the verified closure turns each match into a rejection
range and updates the captured endpoint. VeriFast checks the compiler-selected
`collect` bodies, including initialization of the first element and the
append loop. Collection owns the resulting vector of ordered ranges on valid
UTF-8 boundaries. The compaction invariant tracks its valid output prefix
and the unread suffix as it consumes the ranges. Each copy checks the
initialized source and writable destination. Both invariants hold for arbitrary
lengths. During collection, a panic from pattern setup, the callback or
allocation leaves the haystack unchanged. The proof follows the initialized
Vec prefix through cleanup, ends the callback's exclusive borrows before
dropping the searcher, and restores ownership of the original String.
[Collection proof annotations](remove_matches.vfproof)

The `remove` proof checks the indexed UTF-8 suffix, the decoded scalar
and the initialized source and writable destination of the overlapping
copy. It reuses the forward-copy proof used by `remove_matches`.
The `into_boxed_str` proof checks the initialized bytes and UTF-8 required
to transfer the owned byte slice into `Box<str>`.

## `String::retain` requires a review decision

The production implementation is unchanged. In the loop,
`guard.s.get_unchecked(guard.idx..len)` goes through `Deref`, `String::as_str`,
and `str::from_utf8_unchecked`. The call constructs a temporary `&str` over
the full initialized buffer. For example, when `retain` removes `'é'` from
`"éab"` and keeps `'a'`, moving `'a'` forward leaves the full buffer as
`[0x61, 0xA9, 0x61, 0x62]` before the guard shortens it. At that point
`idx` is 3, the retained prefix is `"a"`, and the unread suffix is `"b"`.
[Original `retain`](../../../library/alloc/src/string.rs)

**Language-level validity under the fixed implementation.** The Rust
Reference treats a `str` value as initialized bytes for validity. The
checker recognizes the pinned conversion's MIR as a wide-pointer conversion
with the same data address and length. This grants no UTF-8 borrow. The loop
owns the initialized allocation and proves the range `idx..len` is a valid
UTF-8 suffix before decoding it. The write proof checks the destination
permission and preserves the unread suffix. `SetLenOnDrop` restores the
valid retained prefix on return and unwind. Ordinary safe `String` and
`str` boundaries continue to require valid UTF-8.
[Rust Reference](https://doc.rust-lang.org/reference/behavior-considered-undefined.html#producing-invalid-values)

**Documented safety precondition.** `str::from_utf8_unchecked` requires
the whole input slice to contain valid UTF-8. The full buffer in the example
violates that precondition. The wide-pointer argument relies on the pinned
implementation and its suffix accesses. Reviewers must decide whether to
accept that argument for the challenge or require a production change that
constructs the `&str` from the valid suffix before rerunning this proof.
[Conversion contract](../../../library/core/src/str/converts.rs)

## Running the checks

From the repository root, run the following commands.

```bash
bash verifast-proofs/alloc/string.rs/verify.sh
bash verifast-proofs/alloc/string.rs-negative/verify.sh
bash scripts/run-kani.sh --kani-args \
  --harness harness_string_remove --harness harness_string_into_boxed_str
```

The [Kani harnesses](../../../library/alloc/src/string.rs) live in the String
source file's `#[cfg(kani)] mod verify` and use the regular
standard-library entry points. The harnesses construct inputs in the stated
domains and run with unwinding checks enabled and no explicit unwind bound.
The valid removal cases exercise overlapping copy ranges, an empty result,
and first, interior, and final indices. The symbolic removal starts the
encoding at byte 0, 1, or 2 and covers all four scalar widths. The removal
and boxing assertions choose an arbitrary result byte within their bounded
input domains. Boxing covers empty, full, and spare-capacity allocations.
Each panic harness reaches its designated input case and exercises the
corresponding panic in the real implementation.
Kani's experimental initialization pass rejects the recursive slice-index
panic formatter. The initialization-only run for boxing timed out. The
experimental validity pass reports unsupported instrumentation for raw byte
copies. The VeriFast proofs check initialization and validity for these
normal paths. The bounded results provide additional checks of byte and scalar
behavior and of the documented removal panics.

The VeriFast runner checks the annotated implementation in `verified/`, runs the
refinement checker from `original/` to `verified/`, and compares
`original/string.rs` byte-for-byte with the repository source. On x86-64 Linux,
the runner builds an isolated VeriFast from the pinned upstream sources and
runs the positive checks on the native target and on `s390x-unknown-linux-gnu`.
The two targets exercise the aligned native-endian branch for each UTF-16 entry
point. Both targets check normal returns and Rust unwind edges in a single
whole-module run, including the imported Vec collection bodies and closure.
The negative runner applies temporary mutations on the native target.
The first makes `replace_range` test the start boundary twice.
The range still has valid byte bounds, but the unchecked end can cut through a
UTF-8 sequence. Both tools must reject that change with their expected diagnostics.
Two further mutations forget the `Vec::Splice` or `Vec::Drain` that the original
statement drops. VeriFast must reject each mutation because ownership of the Vec
is still held by the iterator's recovery handle. The runner also checks that an
unverified local function item is rejected and that two branches can resolve the
same stack slot's erased lifetime independently. Separate temporary sysroots
add a function call to the `Iterator::collect` debug closure and an extra
destructor to its cleanup path. Each mutation must be rejected before using
the prelude contract. The suite also rejects an `IntoIter` specialization
at a marked default-Vec call and checks the layout of a zero-sized
`MaybeUninit<T>`.
[Negative and tool fixtures](../string.rs-negative/)

To update the snapshots after an upstream edit, run
`bash verifast-proofs/patch-verifast-proofs.sh`. The String updater uses
`git merge-file --diff3` with the old original as the base. The repository
updater checks both the proof and its mutation before keeping the merged files.

## Trusted computing base

The checks use VeriFast 26.10 and its refinement checker with the ordered
tool patches below, their RustBelt and memory models, the verifier's solver,
and the Rust compiler `nightly-2026-09-25`. `-skip_specless_fns` selects
the annotated bodies.
The verifier follows Rust unwind edges alongside normal control flow.
The String runner uses `-allow_dead_code` because the specialized debug guard
proves that an `Option::Some` branch and its formatting panic are unreachable.
The flag changes reachability diagnostics. The contracts below state the
assumptions about allocation and dropping the byte iterators used by
`replace_range` and `Drain::drop`.
The UTF-16 inputs use borrowed slices and the standard byte conversion
functions as their iterator sources. At each capacity change the decoder's
output accumulated so far has valid UTF-8.

### Local VeriFast build

The build uses the 26.10 source archive and the release's `vfdeps` bundle,
both checked by SHA-256, and `capnpc-ocaml-decoder` at a pinned revision.
It needs an x86-64 Linux C toolchain and Rustup. First use may download the
archives, build dependencies and the matching Rust components. The source
and build trees are temporary. The verifier, refinement checker, and MIR
exporter are cached by the patch and build-script hashes in
`library/target/vf_verifast_patched/` and share the same MIR schema.
The runner uses the release's remaining binaries and specifications.
[Build script](../../tools/build-patched-verifast.sh)

| Tool change | Scope |
| --- | --- |
| Inherent slice specs | Parses `impl<T> [T]` and resolves the inherent method name to the compiler's MIR spelling. |
| Pointer metadata | Lowers the MIR metadata operation for slice and `str` pointers to the existing length expression and its type check. |
| Function items | Gives each admitted monomorphic function item a distinct nominal zero-sized type. The exporter records safety and crate origin. The translator permits value ownership only for safe external items or safe local items admitted to body verification with a checked contract. |
| `impl Trait` | Gives synthetic type parameters a name based on the compiler's parameter index, consistently in the definition, signature, and uses. |
| `for` loop invariants | Attaches an invariant from a loop body to the natural loop's header before the compiler-generated `next`. Verification checks it at entry and on every back edge. The compiler's `iter` debug binding refers to the actual iterator. |
| Rust stack cleanup | After MIR drops a local struct, accepts the entire stack slot's `points_to_` chunk at the matching address and type. The same required permission fraction is consumed as for fieldwise cleanup. |
| Closures | Uses Rust's exported MIR argument types, capture tuple and definition identity. The stateless lossy mappers have empty nominal environments. The `remove_matches` closure has two mutable reference captures. The tool translates its field projections, checks its body and checks its RustBelt safety obligation against the generic receiver ownership. |
| Constant slice indices | Exports the index offset, minimum length and direction. The verifier models a shared pattern binding into a byte slice with an in-bounds, initialized element loan. Refinement compares the complete projection data. |
| Associated types in refinement | Compares the MIR alias kind, definition path and generic arguments. It takes a closure's enclosing generic parameters from its actual parent body so the captured `Pattern::Searcher` type is compared in the right environment. |
| Crate-local external specs and specialization | Resolves explicit method and type patterns against compiler substitutions. Matching a repeated tuple argument checks every component. Crate-local specifications may name the actual `String` and closure types. The `Add` call resolves to the verified `Add<&str> for String` implementation. |
| Layout and provenance | Removes the inverse axiom that tried to recover a base pointer address from a field's provenance and offset. Rust structs admit zero-sized instantiations, and each modeled real field fits in its containing struct. The String runner rejects solver reports of axiom inconsistency. |
| `FromFn` | Checks in compiler MIR that the constructor moves its argument into the sole field, and that `next` reborrows that field and forwards the actual unit call to the same compiler-resolved `FnMut` closure. The adapter consumes and returns the field’s loans. |
| Collection MIR import | A call-site annotation selects the `collect` expression. The importer checks the compiler bodies against the numbered ghost annotations. Each retained call uses the index of its exact instantiated body. [Vec collection dispatch](#vec-collection-dispatch) |
| Collection loop and storage | Retains the checked addition and its carry bit. The addition cannot wrap on the continuing path once the next slot has been reserved. The two-element tuple owns both fields. A compiler-confirmed trivial drop ends the slot's initialization while leaving its storage. |
| Debug `size_hint` check | Checks the actual `size_hint` implementation and the `None` path of `Option::is_none_or`. It imports the debug callback's capture layout. Its executable body is unavailable to the proof, so reaching the callback would fail verification. |
| `retain` pointer views | A call-site annotation selects the compiled conversions reached by `String::as_str` and `String::as_mut_str`. The exporter accepts a same-lifetime wide-pointer transmute, a checked forwarding call, or the mutable reborrow through a raw pointer of identical layout. The verifier copies the data pointer and length without granting a UTF-8 borrow. The separate safety proofs grant such a borrow only from a valid `String`. [Isolated proof adapter](../../tools/patches/verifast-26.10/91-byte-slice-view.patch) |
| Predicate argument | The ownership assertion for a one-element tuple is derived from the ownership assertion for its sole field. The generic `FnMut` call requires ownership of the closure and the Unicode scalar argument. |
| Cleanup dispatch | Exports the actual MIR drop-place type and applies an explicit specialization only when its type pattern matches. The solver's `ignore_unwind_paths()` value reflects the configured mode so the RustBelt obligations can check normal and unwind outcomes. |
| MIR drop outcomes and stack slots | The checked result of an in-place destructor follows the compiler's corresponding normal or unwind edge. Stack finalization consumes the remaining storage. Rust inference bindings and their type IDs follow the solver's scope stack, so leaving a symbolic path restores both together. |
| Collection unwind annotations | A source annotation is matched by the end location of a compiled call. An imported annotation names its MIR block. Both are checked as ghost statements on the call's unwind edge. The translator inlines the compiler's acyclic cleanup blocks for source annotations so their destructors run before the Rust slots leave scope. The imported contracts distinguish normal and unwind outcomes. |
| Local collector dispatch | The exporter uses rustc's `Instance::try_resolve` to find the actual local `FromIterator` implementation and the local implementations selected by its trait calls. VeriFast requires each selected body to have a contract in the proof. The forwarding check covers the original iterator move, the return slot, the only normal return and the cleanup blocks. It checks the debug callback's MIR separately and permits only typed scalar reads and comparisons. The translated return comes from the selected local `FromIterator` body. |
| Unsized `str` and String dependencies | The translator admits `str` as a type argument and rejects treating it as a sized MIR value. The exporter follows rustc's concrete `Index<RangeFrom<usize>>` resolution to the actual local body and checks that it forwards the original range and the `as_str` view. The boxed conversion must be the checked `Box::into_raw`, wide pointer cast, and `Box::from_raw` sequence for `[u8]` and `str`. |

### Vec collection dispatch

At the polymorphic `remove_matches` call site, the pinned rustc returns
`None` from `Instance::try_resolve` for the non-final `SpecFromIter::from_iter`,
`SpecFromIterNested::from_iter`, and `SpecExtend::spec_extend` methods. The
local importer eliminates impossible implementations, keeps candidates whose
bounds are unresolved, and requires a unique remaining implementation.
It checks that `codegen_select_candidate` agrees and requires the default
bodies before applying the ghost annotations. The `IntoIter` regression
checks that a non-default specialization is rejected.
[Local importer](../../tools/patches/verifast-26.10/92-default-vec-collect-mir-import.patch)

Both targets check this concrete collection chain, from the first insertion
through the append loop and unwind cleanup. The proof uses the allocation
and initialization contracts in `string_deps.rsspec` and the bundled Vec
model. The caller's searcher and callback invariants establish the range
order required for compaction. [Collection annotations](remove_matches.vfproof)

A future standalone `alloc/vec` proof would check the default collection
chain for generic `T` and `I: Iterator<Item = T>`, with its own refinement
and source-diff gates. Its shared contract must link verified iterator
transitions to the collected element sequence and carry a certificate of the
actual specialization chosen at the call site.

### Upstream patch plan

The build applies the numbered patches in order. Each row in the first group
is a proposed upstream PR. Later PRs use the earlier frontend and MIR schema
changes. The second group contains proof adapters for this repository.

| Patch | Proposed upstream scope |
| --- | --- |
| [01 Rust layout axioms](../../tools/patches/verifast-26.10/01-rust-layout-axioms.patch) | Correct field provenance and allow Rust zero-sized structs. The layout regression uses `MaybeUninit<T>` with zero-sized `T`. |
| [02 MIR types and function items](../../tools/patches/verifast-26.10/02-rust-mir-types-and-function-items.patch) | Export constant index data and compare aliases in refinement. Support inherent slice specifications, synthetic type parameters and safe monomorphic function items. Check safe local function item eligibility against the verified bodies. |
| [03 Capturing closures and projection contracts](../../tools/patches/verifast-26.10/03-capturing-closures-and-projection-contracts.patch) | Associate ghost spans with the innermost MIR body. Model captures, checked `FromFn` forwarding, associated types, call specialization and checked addition. |
| [04 Drop types and tuple ownership](../../tools/patches/verifast-26.10/04-rust-drop-and-tuple-ownership.patch) | Dispatch typed in-place drops and derive one-element tuple ownership from its field. |
| [05 `str` DST and boxed conversions](../../tools/patches/verifast-26.10/05-str-dst-and-boxed-conversions.patch) | Accept unsized `str` type arguments and certify the boxed wide-pointer conversion. The call still requires the UTF-8 ownership contract. |
| [06 MIR unwind and inference scopes](../../tools/patches/verifast-26.10/06-rust-unwind-and-inference-scopes.patch) | Follow cleanup outcomes, keep scoped stack storage live through destruction, and restore inferred lifetime bindings and type IDs on branch exit. |
| [07 Checked `collect` forwarding](../../tools/patches/verifast-26.10/07-checked-collect-forwarding.patch) | Resolve the actual local `FromIterator` and validate cleanup and debug callback MIR before calling its checked contract. Include the conservative prelude specification and both rejection tests in the upstream review. |

| Local adapter | Review disposition |
| --- | --- |
| [90 String index contract bridge](../../tools/patches/verifast-26.10/90-string-index-contract-bridge.patch) | Uses the compiler diagnostic identity for `String::as_str` and the checked forwarding body. Upstream submission needs a general way to attach that verified relationship to a resolved call. |
| [91 Byte-slice view](../../tools/patches/verifast-26.10/91-byte-slice-view.patch) | Isolates the explicit pointer-view exception pending the `retain` review decision. |
| [92 Default Vec collection MIR import](../../tools/patches/verifast-26.10/92-default-vec-collect-mir-import.patch) | The marked call and its enclosing module select the proof. A proof file is required and generated names occupy an internal namespace. The specialization check and numbered MIR annotations remain local pending the generic Vec theorem. |

For an offline build, provide the pinned source tarball through
`VF_STRING_SOURCE_ARCHIVE`, the extracted `vfdeps` through `VF_STRING_VFDEPS`,
and the pinned executable through `VF_STRING_DECODER`.
`VF_PATCHED_VERIFAST_BIN` accepts an absolute path to the matching binaries
and prelude directory, or to its `verifast` executable.
### Compilation environment

The [crate roots](original/lib.rs) provide the `alloc` namespace and features
needed to compile the checked source as a separate library. The local
`Borrow`, `ToOwned`, `Cow`, `fmt::format` and `str::into_string` shims serve
out-of-scope bodies that type-check with the proof crate's `String`. The
covered methods use the compiled dependencies and the annotated helpers.

- [`core-sysroot.patch`](core-sysroot.patch) exposes
  `str::EscapeDefault::into_parts` by forwarding to the underlying iterator and
  makes `Pattern` an unsafe trait so the copied source can compile its unsafe
  implementation. The patch marks the corresponding existing implementations
  unsafe and preserves their bodies. The proof of `remove_matches` uses the
  repository's unsafe `Pattern` contract.
- [`alloc-sysroot.patch`](alloc-sysroot.patch) removes the `String` language item
  and the duplicate diagnostic items for `String::new`, `from_utf8`, `as_str`,
  `as_mut_str`, `push_str`, `insert_str` and `ToString`. The patch matches the
  `Pattern` trait change, hides `str::into_string` from the external crate,
  and exposes `Vec::try_extend_from_slice_of_bytes` for type-checking. It
  preserves the existing Vec and String algorithm bodies.
- [`verify.sh`](verify.sh) builds these dependencies from the pinned
  toolchain's `rust-src`. Both tools use the same compiled libraries. The
  `compiler_builtins` placeholder supplies crate metadata for MIR extraction.
  The sysroot and copied sources stay in one temporary directory until both
  gates finish so the compiler's MIR locations can still resolve. The runner
  removes the directory on exit.

The source audit for `remove_matches` compared the pinned toolchain sources
with the repository. The `FromFn` and three Vec specialization files matched
byte-for-byte. The imported `collect`, default `size_hint`, blanket
`into_iter`, `is_none_or`, `Vec::from_iter` and `extend_desugared` bodies
matched after excluding comments and whitespace.

### Standard library specifications

The runner reads `string_deps.rsspec` and appends its standard library
contracts to a temporary copy of the bundled specification. It loads the
contracts that refer to the checked crate's types through the explicit
`self` scope. It also strengthens the `None` case of
`Chars::next` to preserve the empty slice's address and length. The empty
slice iterator returns before advancing its cursor. The temporary
`ptr::drop_in_place` and freezing specifications retain potentially
uninitialized storage after a value’s lifetime ends. Each overlap
case of `ptr::copy` has an explicit non-unwinding outcome, matching
the intrinsic once its pointer and length requirements hold.
[String dependency specifications](string_deps.rsspec)

| Model | Trusted behavior |
| --- | --- |
| `RangeTo`, `RangeBounds`, `slice::range` | A successful call normalizes the range to `0 <= start <= end <= len`. Arbitrary `RangeBounds` implementations are allowed. String uses the normalized range for all later checks and edits. |
| `[T]::as_chunks`, `[T]::align_to`, `[T]::iter`, `[T]::is_empty` | The resulting slices borrow the input allocation for the input lifetime. Chunking preserves the base pointer and accounts for the remainder. Alignment is modeled for `u8` to `u16`, where all initialized pairs are valid `u16` values and the middle slice is aligned. The iterator takes a live shared slice and retains its borrow. `is_empty` tests the length metadata. |
| `borrow_constant_u8` | A shared pattern binding requires the source slice's live shared borrow and the compiler's minimum length. It returns the shared loan at the checked element address. |
| `Iterator::copied`, `Iterator::cloned`, `Iterator::map` | These constructors retain ownership of the iterator and, for `map`, the conversion function. The function items used here are the standard LE and BE conversions from `[u8; 2]` to `u16`. |
| `char::decode_utf16`, `DecodeUtf16` iterator | The inputs at the verified call sites are already iterators. Their blanket `IntoIterator` implementation returns the same iterator, as does `into_iter` on the decoder. `next` preserves decoder ownership and yields a valid scalar, an error holding an unpaired surrogate, or exhaustion. The verifier checks the complete `String::from_utf16_units` loop and its UTF-16 error return using this decoder contract. |
| `Result::unwrap_or` specialization | For `Result<char, DecodeUtf16Error>`, returns the successful scalar or the specified scalar default. The unused error and default contain primitive values and have trivial destruction. The actual mapper bodies establish this contract's preconditions. |
| Local `Iterator::collect` prelude | The exporter checks the standard size-hint call, the typed `Option<usize>` guard and formatting of the size-hint tuple. Cleanup can drop the owned iterator and follow the compiler's unwind edges. The summary transfers the resulting owned iterator to the verified builder on return and consumes it on unwind. |
| Character iterator interfaces | `IntoIterator::into_iter` transfers typed iterator ownership. `Iterator::size_hint` takes both halves of an owned stack slot's permission and returns the full slot with the updated iterator on return or unwind. The proof-only mutability annotations preserve full ownership of those private slots before the borrow. The refinement exporter uses rustc's original mutability. `Iterator::for_each` consumes the iterator and callback. The checked callback restores the exclusive String borrow after each call. |
| Private String character collector interfaces | The actual selected `FromCharIterSpec` and `SpecExtendChars` bodies have checked RustBelt safety contracts. Their concrete selection connects the generic safe trait calls to those bodies. The initialization and UTF-8 postcondition follow from `String::with_capacity`, `String::reserve`, and the verified push closure. Calls to `push` and `push_str` use their local checked contracts and restore the owning invariant on every return and unwind. |
| `str::is_char_boundary` | Checks the endpoint cases and the byte at the index when it is in bounds. The model requires readable initialized bytes and preserves them. |
| `Pattern::into_searcher` and `Searcher::next_match` | The unsafe trait contracts tie the searcher to the original slice and require forward, non-overlapping matches whose endpoints are character boundaries. The ghost cursor records the last endpoint without restricting the input pattern or length. The actual closure body proves the transformation from these matches to rejection ranges. [Trait guarantees](../../../library/core/src/str/pattern.rs) |
| `str::bytes`, `Bytes::as_str`, `bytes_iter_str`, `is_str_bytes_iter` | The iterator records the source slice's pointer and length, yields its bytes in order and has an exact length. The splice model requires this iterator type and readable source bytes. |
| `Chars_as_str_upcast`, `Chars_as_str_lft`, `points_to_Chars_lft`, `usize_upcast` | Lifetime erasure and shortening preserve values, metadata and storage. Retyping a `Chars` field retains its points-to fraction. These facts supply layout identities and confer no permission to read the backing bytes. |
| `DoubleEndedIterator`, `Rev::inner`, `Iterator::rev`, `Chars::next_back`, `Rev<Chars>::next` | Reversal delegates to the underlying iterator's back end. From valid UTF-8, a successful step removes exactly the last scalar's encoding and leaves a valid prefix. An exhausted step preserves the cursor. |
| `ExactSizeIterator::len` for `Range<usize>` | The normalized, ordered range reports `end - start`. |
| `<char>.own`, `encode_utf8_raw_unchecked` | The type predicate aliases the tool's scalar-value predicate. The encoder requires a scalar and a writable region of the encoded length, initializes exactly that region and yields its UTF-8 bytes. |
| `Vec_buf`, `Vec_minus_elems`, `Vec_separate_elems`, `Vec_unseparate_elems` | Splitting ownership exposes only the initialized prefix. The header, allocation and spare capacity stay in the residual predicate. Recombining requires the same buffer, length and fractions. |
| `Vec_u8_to_own`, `Vec_minus_buffer_merge`, `cast_u8_list` | The byte elements have trivial ownership, two fractions of one precise Vec predicate can be combined, and casting a byte list to the same element type preserves it. |
| `Vec::with_capacity`, `as_slice`, `as_mut_slice`, `extend_from_slice`, `split_off`, `leak` | Capacity covers the request, slice metadata matches the allocation's initialized prefix, byte extension appends initialized bytes, splitting transfers the suffix, and leaking transfers writable initialized storage. The Rust implementations own the associated allocation operations. |
| `Vec::capacity`, `Vec_separate_spare`, `Vec_unseparate_spare`, saturating addition | For nonzero-sized elements, the capacity is the size of the buffer in elements. The storage between length and capacity is writable and may be uninitialized. The collection proof checks `ptr::write` on that storage, then includes the newly initialized element when reassembling the vector. Saturating addition returns the smaller of the mathematical sum and `usize::MAX`. |
| `Vec::drain` and `Vec::splice` | These models cover `Vec<u8, Global>` with a checked `Range<usize>`. Construction transfers the Vec into a linear handle tied to the returned iterator. Splice also transfers its replacement byte read permission and requires enough reserved capacity. |
| Dropping a byte drain or reserved byte splice | Only the specialized destructor consumes the handle and returns the updated Vec, along with the replacement byte read permission for `Splice`. Dropping `u8` elements calls no user code. A byte drain moves the tail without allocating. With the exact remaining length of `str::Bytes` and the checked capacity, a splice can move the tail without another allocation. |
| Forward `Chain` of `Vec::IntoIter` and `Once` | The two optional fields own their respective remaining elements. The blanket `into_iter` returns the same iterator. A forward step reads one initialized element from the owning Vec iterator until exhausted, then consumes the optional element from `Once`. On exhaustion the returned iterator remains valid for destruction. The concrete chain of integer pairs calls no user destructor and frees its owning vector through the global allocator. The model gives the exact remaining sequence and transfers the ownership of each yielded element. The compaction proof separately requires and maintains the range invariant. |
| `std::mem::drop` and `std::ptr::drop_in_place` for the `retain` guard | Both use the verified destructor, which restores the String through the guard's original reference. The in-place form takes the guard's initialized storage and accounts for its deinitialization. The reference and integer fields require no additional destructor calls. |
| `String` indexing by `RangeFrom<usize>` | The checked forwarding body uses the verified `as_str` and core's `SliceIndex<str>` for that range. Core checks the start with `is_char_boundary`, then delegates to the concrete range `start..len`. Its failure path reads the same live string for panic formatting. The model yields an unchanged borrowed buffer, split at the checked boundary, and the corresponding suffix pointer and length. |
| `Vec<u8, Global>::into_boxed_slice` | `shrink_to_fit` retains the initialized prefix. Moving the Vec through `ManuallyDrop` keeps ownership with its raw allocation, and `buf.into_box(len)` transfers precisely that length. The contents supplied to `Box::assume_init` are the original byte list. The allocator and initialized region are retained in the stock `Box_in` ownership model. [RawVec proof](../raw_vec/mod.rs/) |
| Boxed UTF-8 cast | The checked sequence keeps the allocation and length as it moves through `Box::into_raw` and `Box::from_raw`. A byte slice and a string slice of the same length have the same size and alignment. The UTF-8 precondition justifies ownership of the resulting `Box<str>`. |
| Owning call contracts for `String::push` and `String::push_str` | The verifier checks both bodies, including the Vec state when reservation unwinds. Closing the points-to and String predicates gives the call contracts used by the UTF-16 builder and its final append. The borrowed replacement bytes retain their permissions. |

### Proof annotations

`Deref::deref` uses the one `ignore_ref_creation` directive for the
reborrow of the `&str` returned by the verified `as_str` method. The
method contract preserves the bytes, their read permissions, and the slice
metadata. Its safety proof returns a shared borrow of valid UTF-8.

VeriFast 26.10 rejects the anonymous lifetime in the original
`impl Drop for Drain<'_>` when verifying that impl directly. The
refinement-checked body delegates to `Drain_drop__VeriFast_wrapper`, whose
precondition is the live `Drain` ownership and lifetime token. The
delegation and trivial cleanup of the iterator field are reviewed at the
call site. The proof sysroot checks `needs_drop::<Chars<'static>>() == false`
at compile time on both targets. This drop glue is independent of the
lifetime argument. The wrapper proves that dropping the temporary Vec drain
restores a valid string. The `allow_dead_code` directives allow the bounds
checks in that body to have unreachable branches under its precondition.

The `SetLenOnDrop` bridge uses the verified nested destructor for explicit
`mem::drop` and in-place unwind cleanup. The destructor checks the retained
prefix and restores `String` ownership before returning. Its remaining fields
are a mutable reference and two `usize` values, all with trivial drop glue.

## Review checks

The production prefix in `library/alloc/src/string.rs` matches the upstream
snapshot. The only source addition is its trailing Kani `verify` module.
The proofs use inductive resource invariants and follow unwind edges. No
Kani contract, stub, assumption or explicit unwind bound is needed for the
six supplementary harnesses. Their 14 reachability covers include the
assertion paths and the documented removal panic cases.
[Challenge review](https://github.com/model-checking/verify-rust-std/pull/725),
[review checks used on Challenge 22](https://github.com/model-checking/verify-rust-std/pull/741)

The repository-wide gate still uses the stock toolchain for the legacy
`RawVec` proof, which contains two admitted variance lemmas and reports a
Redux axiom inconsistency when zero-sized `T` reaches `MaybeUninit<T>`.
The patched String gate rejects solver inconsistency diagnostics and its
zero-sized `MaybeUninit<T>` regression exercises the corrected layout rule.
[RawVec proof runner](../raw_vec/mod.rs/verify.sh)

A temporary Kani `from_utf16le` trial with symbolic input length hit pointer
offset and loop unwinding checks. With input limited to two bytes, the
contract proof timed out and the `stub_verified` caller failed to recover the
UTF-8 assertion for the returned heap value.
