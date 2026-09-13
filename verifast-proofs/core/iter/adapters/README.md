# Generic iterator adapter proof port

This is an **unvalidated VeriFast port candidate** for part of Challenge 16.
Hosted verification previously stopped in the VeriFast Rust frontend.
The current revision includes a frontend fix awaiting hosted validation;
the refinement checker has not passed. See the hosted results below.
The files under `verified/` are proof inputs, not evidence of a successful
proof. This port does not yet close Felipe's review requests on PR #602.

The functions retain generic type parameters. `Buffer<T, N>` also retains
symbolic `N`; there are no representative element types, fixed array sizes,
or unwind bounds. The target contracts are:

| Target | Contract being checked |
| --- | --- |
| `StepBy<I>::original_step` | Preserve the step field and return its nonzero successor, for any `I`. |
| `Buffer<T, N>::as_array_ref` | Derive the active window's reference from its shared borrow and valid buffer bounds. |
| `Buffer<T, N>::as_uninit_array_mut` | Derive a writable window from its exclusive storage borrow, without requiring initialized `T` values. |
| `Buffer<T, N>::push` | Consume one new `T`, drop the old front, and preserve ownership of the shifted window on normal return. |
| `Buffer<T, N>::drop` | Drop exactly the initialized window and recover its storage on normal return. |

The two raw buffer pointer helpers also have contracts. `push` and `drop`
use the standard library specification of generic drop glue. Their unwind
postconditions return the thread token only. Unwind paths remain enabled,
but these contracts do not establish buffer-state recovery after a panicking
destructor. This is a remaining obligation for a full safe-abstraction proof.

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

The reference accessors require the corresponding lifetime borrow of the
window. Establishing those borrows from the full safe abstraction is also
outside this port. The mutable accessor deliberately accepts storage that
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

The annotated version changes the two pointer helpers to raw field-address
expressions and names the returned references so ghost assertions can follow
their construction. `refinement-checker` must establish that these changes
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
Neither the generic contracts nor source refinement have a passing verdict.
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
the adapter contracts are checked. This extension awaits hosted validation.

`backend/prepare.sh` pins the source commit, source archive hash, and upstream
dependency bundle hash. It builds the MIR exporter and the verifier's Rust
translator on the hosted Linux worker. Arithmetic rules and library contracts
are unchanged. Source projections and mandatory refinement remain unchanged.

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

- Validate the frontend's `AddUnchecked` mapping and both regression checks. Then
  obtain verifier and refinement verdicts, including checks of symbolic const
  sizes, `NonZero::new_unchecked`, reference creation, and generic slice drop glue.
  The explicit slice assertions in `drop` must be proved by that memory
  model; no local axiom has been added to make them pass.
- Complete the safe-abstraction and unwind-state obligations described above.
- Port the remaining Challenge 16 targets, including arbitrary-length filter,
  filter-map, and zip iteration. This package has no proof of those loops.
- Reconcile the real nonempty-source `next_chunk::<0>()` defect in filter and
  filter-map. The `MapWindows` constructor's exclusion of zero-sized windows
  does not justify excluding that separate, valid filter input domain.

Existing Kani results remain bounded where documented. Existing PR CI at
`4459557` predates this port and does not validate it.
