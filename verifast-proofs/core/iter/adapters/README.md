# Generic iterator adapter proof port

This port proves generic contracts for part of Challenge 16. Hosted run
[34762580703](https://github.com/model-checking/verify-rust-std/actions/runs/34762580703)
at `6cc9cce69aac424a7fe6604165357921f26ac34d` passed the full adapter proof,
source refinement, source identity checks, and every backend regression gate.
Coverage is limited to the contracts below and depends on the documented
caller obligations and trusted backend extensions. Other Challenge 16 targets
and the complete safe abstraction remain open.

The functions retain generic type parameters. `Buffer<T, N>` also retains
symbolic `N`; there are no representative element types, fixed array sizes,
or unwind bounds. The target contracts are:

| Target | Contract being checked |
| --- | --- |
| `StepBy<I>::original_step` | Preserve the step field and return its nonzero successor, for any `I`. |
| `Buffer<T, N>::as_array_ref` | Derive the active window's reference from its shared borrow and valid buffer bounds. |
| `Buffer<T, N>::as_uninit_array_mut` | Derive a writable window from an exclusive borrow of the backing array, without requiring initialized `T` values. |
| `Buffer<T, N>::push` | Consume one new `T`, drop the old front, and preserve ownership of the shifted window on normal return. |
| `Buffer<T, N>::drop` | Drop exactly the initialized window and recover its storage on normal return and unwind. |

The two raw buffer pointer helpers also have contracts. `push` and `drop`
use the standard library specification of generic drop glue. The
`drop` safety proof recovers field storage on both outcomes through one lifetime
loan frame. The `push` unwind postcondition
retains the surviving values, backing storage, and borrow token in
`push_drop_frame`, together with the old front's storage after destruction.
`finish_push_storage` proves that those resources restore `live`, including
after a panicking element destructor.

## Ownership and bounds

`live` separates initialized slots from ownership of their values. Only the
active window carries `<T>.own`. Inactive storage can contain stale copied
bytes, but carries no ownership of `T`. The wraparound copy moves the
survivors' logical ownership to the destination. It does not duplicate it.
`initialized_slots` and `wrap_slots` recursively relate `MaybeUninit<T>`
storage to initialized `T` storage, without requiring `Copy`, `Clone`, or
a particular destructor.

The preconditions require `0 < N`, `start <= N`, representable `2 * N`,
and the allocation/layout limits of the real buffer. These follow from the
intended `MapWindows` constructor and Rust layout restrictions. They are
explicit caller obligations here. Constructor preservation and the surrounding
`MapWindows` iterator implementation are outside this projection.

The shared accessor requires a lifetime borrow of the window. The mutable
accessor requires a borrow of the whole backing array of initialized
`MaybeUninit` wrappers because its pointer helper borrows that array.
These wrappers can contain uninitialized bytes and need no `T` ownership.
Establishing those borrows from the full safe
abstraction is outside this port. The mutable accessor accepts storage that
does not yet own initialized `T` values, as required by the clone path.

## Source correspondence

The annotated projection expands the three window-bound `debug_assert!` calls
into their `if cfg!(debug_assertions) { assert!(...) }` bodies. Both refinement
inputs and the full proof explicitly enable debug assertions; refinement must
establish the equivalence of these bodies. A ghost assertion proves each bounds
condition before the expansion. Line-local reachability directives account for
the disabled configuration branch and the excluded assertion failure path.

One line-local `allow_dead_code` directive covers Rust's generated cleanup for
the `next` argument at the end of `push`. Hosted MIR inspection shows its drop
flag is cleared on both branches before the only potentially unwinding call.
An explicit `live` assertion after restoration keeps the normal completion
path subject to reachability checking. No global dead-code option is used.
A mandatory negative fixture gives a function contradictory preconditions and
permits only its generated return to be unreachable. The ghost assertion must
still be rejected, guarding the normal-path check used in `push`.

`source/` contains complete, hashed copies of the two std source files.
`source-map.json` records the exact lines projected into `original/`:
the actual struct declarations and selected method implementations.
Private core dependencies and unrelated iterator implementations are omitted.
The projections are not alternative iterator models.

`check_sources.py` checks snapshot hashes, equality with the current std files,
exact projection contents, matching crate roots, and the presence of a
contract on every selected method. It also rejects common proof suppression
directives. This lexical guard does not parse or validate VeriFast proofs.
Only a successful verifier run can establish the contracts.

The annotated version keeps the original pointer helper bodies and names
returned references so ghost assertions can follow their construction.
Private proof methods are marked `unsafe` to express their explicit caller
obligations. The upstream refinement checker permits this change for private
functions; the original projection and standard library keep their original
signatures. The `Drop` trait implementation retains its safe signature and
must establish its contract from the type ownership invariant.
`refinement-checker` must establish that these changes
preserve the projected Rust behavior. It is mandatory, even if VeriFast
passes. No compiler directives are ignored during refinement.

To deliberately refresh an original projection after reviewing a source
update, update the snapshot, its hash, and its ranges, then run:

```sh
python3 -I check_sources.py --generate-original
```

Normal checks never regenerate or silently accept changed sources.

## Validation with GitHub Actions

The [iterator adapter workflow](../../../../.github/workflows/verifast-iter-adapters.yml)
uses a temporary GitHub-hosted Ubuntu 24.04 runner. No separately maintained
machine is needed. It runs when these proof inputs change in a pull request,
or on pushes to `16-iter-adapters` and `main`, and for merge queue checks.
Actions must be enabled in the repository. Standard public-repository jobs use
[GitHub's free hosted runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).

The workflow checks the source snapshots and contract selection before
running the proof and refinement stages. A systemd service limits their
entire process tree to 4 GiB RAM, no swap, two CPUs, 256 tasks, and 25 minutes.
The job has a 30-minute timeout and cancels superseded runs. Tool errors,
proof failures, and resource-limit failures fail the job. Verification and
refinement stay sequential and retain the per-process limits below.

Run [34762580703](https://github.com/model-checking/verify-rust-std/actions/runs/34762580703)
verified 433 statements in the full adapter proof and 149 in the standalone
matrix-layout fixture on `x86_64-unknown-linux-gnu`. The full refinement checker
accepted the annotated implementations, and the source checker confirmed their
original projections against the current std snapshots. All positive and
negative backend fixtures passed, including the reachability guard. The source
checker also passed its nine tests. No compiler or verifier was run locally.

The runner uses VeriFast 26.09 plus the narrow frontend patch in
`backend/add-unchecked.patch`. It maps `AddUnchecked` to the existing integer
addition operation, whose symbolic execution checks overflow. On inputs
where no overflow occurs, unchecked addition has the same result. Outside
that domain, unchecked addition is undefined, and the verifier must reject it.
Before checking the adapters, the runner requires a valid successor proof
and an explicit overflow diagnostic for the same operation without its
range precondition. A frontend crash does not count as the negative result.

`backend/const-generics.patch` adds symbolic `usize` const arguments and
array lengths using the existing `typeid`/`usize_of_const` representation.
It keeps const parameters distinct from Rust types and does not add `Sized`
bounds to them. The exporter rejects other const parameter types. A positive
symbolic-length proof and an incorrect-length negative test must pass before
the adapter contracts are checked.

The same patch routes array ownership and borrowing through VeriFast's
existing type predicates. It also removes the upstream frontend's blanket
shortcut for mutable-reference creation. Mandatory regression gates cover
valid arithmetic, symbolic width,
shared array reborrowing, and mutable array reference creation; rejection
of overflow, a wrong width, missing shared ownership, and missing mutable
storage. The mutable test converts the new reference to a raw pointer to
test creation independently of a further return reborrow. These fixtures
validate the frontend extension, not the adapter contracts.

The `MaybeUninit` pointer `cast_init` translation is an ordinary raw-pointer
cast, matching its [Rust implementation](https://github.com/rust-lang/rust/blob/master/library/core/src/ptr/mut_ptr.rs).
It preserves the address and grants no permission to read or drop `T`.
The runner checks both address preservation and rejection of a read without
initialized storage before checking the adapters.

The patch also preserves const operands and `ConstArgHasType` constraints
through the MIR schema and refinement checker. Constraints are compared after
generic parameter renaming; unsupported predicates still fail refinement.
The refinement fixtures require acceptance of a renamed const parameter and
rejection of a change in the returned value from `N` to `M`.

`backend/prepare.sh` pins the source commit, source archive hash, and upstream
dependency bundle hash. It builds the MIR exporter, verifier, and refinement
checker on the hosted Linux worker. Arithmetic rules and the existing borrowing
and destruction contracts are unchanged. Mandatory source refinement still
checks the selected implementations. The workflow caches these three
binaries and the library specification, keyed by the preparation script and
patches, with checksums checked on restoration. Every regression, proof, and
refinement gate reruns after a cache hit.

`backend/nonzero-usize.patch` adds one trusted library contract for the
`usize` instantiation of `NonZero::new_unchecked`. It requires a positive
input, preserves its value through `get()`, and cannot unwind. This matches
the [standard library implementation and its safety requirement](../../../../library/core/src/num/nonzero.rs).
The frontend routes only the `usize` instantiation to this specification.
Other instantiations remain unsupported. The constructor implementation is
not proved by this port; the new specification is part of its trusted library
boundary. A positive fixture and rejection of a missing nonzero precondition
are mandatory.

`backend/maybeuninit-ownership.patch` extends the trusted library specification
with introduction and disposal rules for `MaybeUninit<T>` ownership. Owning
that wrapper does not require ownership of a contained `T`; its memory remains
tracked by separate storage predicates. These rules model the wrapper's
ownership semantics and are not proved from its implementation by this port.
A positive wrapper fixture and rejection of missing ownership of an ordinary
`T` are mandatory. No new borrowing or generic drop contract is introduced.

`backend/array-layout.patch` supplies trusted size and alignment relations for
array type IDs and `MaybeUninit<T>`. The facts follow the
[Rust array layout guarantee](https://doc.rust-lang.org/reference/type-layout.html#array-layout)
and the wrapper's documented layout. They include zero-sized element types.
The matrix conversion and writable-window proofs remain mandatory; the layout
facts do not grant storage or ownership permissions.
The patch also removes implicit `Sized` bounds from the array length parameters
of the existing array conversion lemmas. Symbolic const parameters are
not Rust value types. The element type bounds and every storage precondition
remain in force, and the patched prelude is cached with checksum validation.

`backend/array-subtyping.patch` models the standard covariance, fixed element
count, and `Send` conditions of arrays and `MaybeUninit<T>`, plus representation
preservation under [Rust subtyping](https://doc.rust-lang.org/reference/subtyping.html).
The `Send` conditions follow the [array](https://doc.rust-lang.org/std/primitive.array.html#impl-Send-for-%5BT;+N%5D)
and [wrapper](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#impl-Send-for-MaybeUninit%3CT%3E)
implementations. These are trusted type-model facts. The
`Buffer` ownership proofs must still transfer every active element's ownership;
they cannot produce generic `T` ownership from those facts. Negative fixtures
require rejection when the subtype relation or `T: Send` is missing.

## Local static checks and optional manual verification

The static check reads small files and starts no compiler or solver:

```sh
bash verifast-proofs/core/iter/adapters/verify.sh --static
```

On a separate Linux machine with at least 8 GiB currently available RAM:

```sh
bash verifast-proofs/core/iter/adapters/verify.sh --remote
```

The runner uses the repository's VeriFast 26.09 wrappers and Rust
nightly 2026-02-05, with the frontend patch described above. The wrappers
can download their toolchains. The remote build needs `capnp`, `rustc-dev`,
and `llvm-tools`; the workflow installs them. Each proof process
has a 2 GiB address-space limit, each verification stage has a ten-minute
wall limit, and the stages run sequentially. Address-space limits are per
process, not a combined memory cap. Use an otherwise idle remote worker with
sufficient headroom. The runner refuses proof execution on macOS.

The command must pass all three gates: proof verification, refinement, and
source identity. `-skip_specless_fns` skips derived trait implementations
without contracts, while the source check requires contracts on every target.
The runner does not suppress unwind paths, overflow checks, or reference
creation checks, and does not allow assumed proof obligations.

The existing VeriFast workflow is unchanged. The separate adapter job checks
these contracts without altering the existing LinkedList and RawVec checks.

## Remaining work

- Prove constructor preservation and establish the accessor borrows from the
  full safe abstraction, including the surrounding `MapWindows` implementation.
- Port the remaining Challenge 16 targets, including arbitrary-length filter,
  filter-map, and zip iteration. This package has no proof of those loops.
- Reconcile the real nonempty-source `next_chunk::<0>()` defect in filter and
  filter-map. The `MapWindows` constructor's exclusion of zero-sized windows
  does not justify excluding that separate, valid filter input domain.

Existing Kani results remain bounded where documented. The successful VeriFast
run establishes only the selected contracts, not completion of Challenge 16.
