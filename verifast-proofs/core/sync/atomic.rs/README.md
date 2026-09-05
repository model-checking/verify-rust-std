# Challenge 7: atomic safety

This is an independently authored proposed solution for
[Challenge 7](https://github.com/model-checking/verify-rust-std/issues/83). It uses
VeriFast with the explicit source update in `toolchain/`. VeriFast is an approved
tool; this particular update is unreleased and requires review. Passing this
directory's checks does not by itself establish committee acceptance.

## Verified scope

| Requirement | Proof and enforced coverage |
| --- | --- |
| `from_ptr` | Bool, generic Ptr, all signed/unsigned 8/16/32/64/128-bit types, and Isize/Usize: all 14 bodies must appear in verifier output. |
| Pointer values and element sizes | The pointer proof is generic over sized `T`, with arbitrary stored addresses. Concrete intrinsic callers also cover element sizes 0, 1, 2, 3, and 4. |
| Unsafe operation wrappers | All 15 current wrappers, including signed minimum and both compare-exchange variants. |
| Intrinsics | All 91 legal ordering combinations of the 15 current const-generic intrinsics, matched to the challenge's order-suffixed names. |
| Panic paths | Invalid load/store and compare-exchange failure orderings execute the real panic paths and preserve atomic permissions on unwind. |
| Source connection | Pinned source digests, complete module refinement after documented metadata preparation, and explicit coverage checks. |

The proof covers the challenge's required unsafe functions. It does not claim
that every public safe method in the atomic module has been verified. Optional
panic-avoidance contracts for those public methods are not part of this solution.
No runtime implementation in `library/` is changed.

## Ownership and validity

`from_ptr` accepts either initialized ordinary ownership or an existing atomic
share. A ghost boolean selects the permission path. Fresh conversion borrows
the ordinary storage for the returned reference's lifetime and retains a unique
recovery token. Reusing a share creates no recovery token. Both paths return
sharing and reference-initialization permissions. Fourteen concrete callers
each create and use two references to the same storage.

The sharing interpretation contains a fractional lifetime borrow of typed
atomic ownership. Integers and raw pointers accept all values of their type;
the boolean interpretation accepts only bytes 0 and 1. Ordinary ownership
establishes allocation validity and initialization. Atomic ownership additionally
requires actual atomic alignment and excludes conflicting ordinary or mixed-size
accesses through the verifier's existing atomic-mask model. Splitting the
atomic resource permits concurrent atomic access; converting it back requires
recovering its complete permission and ending the relevant borrow.

Intrinsic contracts require the correct operand domain. `T: Copy` alone is
insufficient. Integer updates use the same integer type; pointer updates use
`usize`; signed and unsigned min/max have separate domains. Pointer-domain
lemmas require a sized pointee. Stores, swaps, and compare-exchanges require a
valid new value. Arithmetic and bitwise updates require a proved closure witness
carrying the operand type identities, operation, invariant, and update value.
Boolean AND/OR/XOR witnesses pass; invariant-breaking NAND/addition witnesses
fail. Loads preserve validity and may use a resource derived from fractional
ordinary ownership. Writes require a resource derived from full ordinary ownership.

## Trusted boundary and source preparation

The trusted boundary consists of Rust's primitive atomic semantics, VeriFast's
existing RustBelt lifetime/atomic model, the primitive contracts added by the
patch, and rustc's exported ABI layout. The model proves safety under its
permissions and invariants; it does not establish general concurrent functional
correctness or a hardware memory-model theorem.

The patch adds concrete atomic-order translation, operand guards, compiler
resolved `Self`, propagation of macro contracts to every expansion, and
compiler-derived struct alignment. Generic `repr(align(N))` supplies a minimum
alignment and divisibility fact, not an assertion of exact alignment. The
primitive update model includes explicit u8 equations and restricted boolean-byte
value tables. Those primitive facts remain reviewable trusted contracts.

`source-lock.json` pins both the atomic implementation and intrinsic declarations.
The generator copies the current complete atomic module and replaces its 18
`rustc_diagnostic_item` attributes with documentation attributes in both proof
inputs. This prevents duplicate diagnostic items when checking the module beside
the compiler's `core` dependency. The refinement claim is between these prepared
inputs. In the verified input, the existing reference expression is assigned to
a local result variable to attach ghost steps; whole-module refinement checks
that transformation. All other executable code is preserved.

No reference-creation check, unwind path, or dead-code check is disabled. No false
precondition skips required types or orderings. Negative controls reject invalid
types/orderings, missing domain or closure witnesses, ordinary/fractional write
permissions, invalid boolean values, uninitialized conversion, and duplicate
ownership/recovery. Isolated mutated-MIR decoder tests are not counted as Rust
proofs; their replay exporter is never used in the real proof runtime.

## Reproduction

Use native ARM64 macOS with Python 3.12 or newer and the pinned Rust toolchain:

```sh
rustup toolchain install nightly-2025-11-25 --profile minimal --component rustc-dev,llvm-tools-preview,rust-src
python3 verifast-proofs/core/sync/atomic.rs/toolchain/build.py \
  --workdir /tmp/atomic-build \
  --downloads /tmp/atomic-downloads \
  --cargo-home /tmp/atomic-cargo \
  --check
```

The build directory must not exist. Archives and the patch are checked against
pinned SHA-256 digests. The decoder revision and Cargo dependency locks are
pinned. The script extracts fresh sources/dependencies, builds the verifier,
refinement checker, and Rust MIR exporter, then runs all proof and rejection
checks. It writes logs, a build manifest, and a relocation wrapper in that build
directory. `--offline` is supported when all archive and Cargo inputs are cached.

The dedicated GitHub workflow uses `macos-14` because the pinned x86_64 Linux
target does not expose 128-bit atomics, including with `cmpxchg16b` enabled. The
proof runner fails if either 128-bit instantiation is missing. GitHub documents
`macos-14` as an ARM64 standard runner in its
[runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).

The CI artifact includes the generated proof sources, per-function coverage,
control results, and fresh-build manifest. To rerun checks using a built runtime:

```sh
/tmp/atomic-build/with-build-env python3 verifast-proofs/core/sync/atomic.rs/check.py \
  /tmp/atomic-build/verifast-26.01/bin
```
