# Generic iterator adapter proof port

This is an **unvalidated VeriFast port candidate** for part of Challenge 16.
Hosted verification passes the frontend regression checks and full adapter
source refinement. The adapter contracts still need a passing proof verdict.
See the hosted results below.
The files under `verified/` are proof inputs, not evidence of a successful
proof. This port does not yet close Felipe's review requests on PR #602.

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
use the standard library specification of generic drop glue. The candidate
`drop` safety proof recovers field storage on both outcomes through one lifetime
loan frame. This proof has not passed validation. The `push` unwind postcondition
returns the thread token only; preserving its buffer state after a panicking
element destructor remains a safe-abstraction obligation.

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
accessor requires a borrow of the whole backing array because its pointer
helper borrows that array. Establishing those borrows from the full safe
abstraction is outside this port. The mutable accessor accepts storage that
does not yet own initialized `T` values, as required by the clone path.

## Source correspondence

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

Hosted run [34733601368](https://github.com/MavenRain/verify-rust-std/actions/runs/34733601368)
at commit `9e95bb7e83553d0e47035821eaecf4be030cab6b` passed the source checks
and their nine tests, then failed before proof checking. The Rust MIR exporter
encountered `AddUnchecked` in `StepBy<I>::original_step` and panicked with
`not yet implemented` at `src/lib.rs:2455`. The earlier missing
`cast_maybe_uninit` feature flag was fixed in that commit.

The [25.11 exporter](https://github.com/verifast/verifast/blob/25.11/src/rust_frontend/vf_mir_exporter/src/lib.rs#L2436-L2455)
has no `AddUnchecked` case. Static inspection of the
[26.01 exporter](https://github.com/verifast/verifast/blob/26.01/src/rust_frontend/vf_mir_exporter/src/lib.rs#L2445-L2464)
found the same omission, so that release alone does not address this failure.
That original run established neither the contracts nor source refinement.
The current runner uses VeriFast 26.09 plus the narrow frontend patch in
`backend/add-unchecked.patch`. It maps `AddUnchecked` to the existing integer
addition operation, whose symbolic execution checks overflow. On inputs
where no overflow occurs, unchecked addition has the same result. Outside
that domain, unchecked addition is undefined, and the verifier must reject it.
Before checking the adapters, the runner requires a valid successor proof
and an explicit overflow diagnostic for the same operation without its
range precondition. A frontend crash does not count as the negative result.

The unchecked-add regression passed in hosted run
[34744234144](https://github.com/MavenRain/verify-rust-std/actions/runs/34744234144).
That run then reached the translator's unsupported const-parameter check.
`backend/const-generics.patch` adds symbolic `usize` const arguments and
array lengths using the existing `typeid`/`usize_of_const` representation.
It keeps const parameters distinct from Rust types and does not add `Sized`
bounds to them. The exporter rejects other const parameter types. A positive
symbolic-length proof and an incorrect-length negative test must pass before
the adapter contracts are checked. Both passed in hosted run
[34745790943](https://github.com/model-checking/verify-rust-std/actions/runs/34745790943).

The same patch routes array ownership and borrowing through VeriFast's
existing type predicates. It also removes the upstream frontend's blanket
shortcut for mutable-reference creation. Hosted run
[34748227762](https://github.com/model-checking/verify-rust-std/actions/runs/34748227762)
passed every backend regression gate: valid arithmetic, symbolic width,
shared array reborrowing, and mutable array reference creation; rejection
of overflow, a wrong width, missing shared ownership, and missing mutable
storage. The mutable test converts the new reference to a raw pointer to
test creation independently of a further return reborrow. These fixtures
validate the frontend extension, not the adapter contracts.

The patch also preserves const operands and `ConstArgHasType` constraints
through the MIR schema and refinement checker. Constraints are compared after
generic parameter renaming; unsupported predicates still fail refinement.
Hosted run [34749576406](https://github.com/model-checking/verify-rust-std/actions/runs/34749576406)
accepted a renamed const parameter and rejected changing the return from
`N` to `M`. Run [34749771017](https://github.com/model-checking/verify-rust-std/actions/runs/34749771017)
then passed refinement of the full adapter projection. Its contract proof
failed, so the workflow correctly remained unsuccessful.

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
of the three existing array conversion lemmas. Symbolic const parameters are
not Rust value types. The element type bounds and every storage precondition
remain in force, and the patched prelude is cached with checksum validation.

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
this candidate without altering the existing LinkedList and RawVec checks.

## Remaining work

- Obtain verifier and refinement verdicts for the adapters, including symbolic const
  sizes, `NonZero::new_unchecked`, reference creation, and generic slice drop glue.
  The lifetime loans in `drop` must connect element storage to the slice
  contract and recover storage on both outcomes. There is no adapter-specific
  borrowing or drop axiom.
- Complete the safe-abstraction and unwind-state obligations described above.
- Port the remaining Challenge 16 targets, including arbitrary-length filter,
  filter-map, and zip iteration. This package has no proof of those loops.
- Reconcile the real nonempty-source `next_chunk::<0>()` defect in filter and
  filter-map. The `MapWindows` constructor's exclusion of zero-sized windows
  does not justify excluding that separate, valid filter input domain.

Existing Kani results remain bounded where documented. Existing PR CI at
`4459557` predates this port and does not validate it.
