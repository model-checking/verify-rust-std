# 0003. Grisu and Dragon strategies need contract decomposition

Status: accepted

## Context

The remaining six Challenge 28 targets are the four Grisu and two Dragon strategy functions: `format_shortest_opt`, `format_shortest`, `format_exact_opt`, `format_exact` in `flt2dec::strategy::grisu`, plus `format_shortest`, `format_exact` in `flt2dec::strategy::dragon`. The `_opt` functions are the actual digit-generation algorithms (~290 lines of dense unsafe + arithmetic). The non-`_opt` versions are thin wrappers that launder a lifetime through `unsafe { &mut *(buf as *mut _) }` and fall back to Dragon when Grisu returns `None`.

Whole-program Kani harnesses for the wrappers were attempted (see git history). Even with aggressive constraints (`mant <= 0xFF`, `plus <= 0x0F`, `exp` in `[-4, 4]`, `#[kani::unwind(32)]`, 12 GiB memory cap), CBMC OOM-killed during the bit-blast phase. The algorithm's nested loops over u64/u128 arithmetic produce a SAT formula that exceeds available memory at any input bound large enough to exercise the digit-generation loop.

## Options considered

- **Whole-program verification of the wrappers** (rejected) - Forces Kani to trace into `format_shortest_opt` / `format_exact_opt`. OOM at the first grisu harness even with tight bounds. The CBMC formula for the digit-generation main loop alone has hundreds of thousands of clauses; combined with the surrounding arithmetic, the in-memory formula exceeds 12-24 GiB.
- **Stub the `_opt` functions in the wrapper harness via `#[kani::stub]`** (rejected for now) - Possible but `#[kani::stub]` needs the stub to live somewhere Kani can find it during std verification. Plumbing this in the std crate is not standard; existing verified files in this repo do not use `kani::stub`. Worth revisiting if contract decomposition turns out to be slower than expected.
- **Contract-based decomposition** (chosen) - Add `#[ensures]` (and likely `#[requires]`, `#[modifies]`) contracts to `format_shortest_opt` / `format_exact_opt` / dragon's `format_shortest` / dragon's `format_exact`. Verify each `_opt` against its own contract with `#[kani::proof_for_contract(...)]` in isolation. Then verify the wrappers (`format_shortest`, `format_exact`) using the contracts as stubs via `#[kani::stub_for_contract(...)]`. The wrapper proofs become cheap because Kani never traces into the algorithm.
- **Skip the strategies entirely** (rejected) - Half the challenge would remain unsolved. The contract path is the well-trodden Kani idiom for exactly this situation.

## Decision

Defer the six strategy functions to a follow-up using contract decomposition.

For each algorithm function (`format_shortest_opt`, `format_exact_opt`, dragon's `format_shortest`, dragon's `format_exact`):

1. Write a `#[requires]` contract capturing the documented preconditions (the `assert!`s at the top of the function body).
2. Write an `#[ensures]` contract capturing the relevant well-encapsulation invariant: the returned `&[u8]` is either empty (signalling failure) or has `result.0[0] > b'0'`. Crucially, ensure that the function did not read uninitialised memory through the supplied `MaybeUninit` buffer.
3. Write a `#[kani::proof_for_contract(path)]` harness that calls the function with symbolic inputs and trusts Kani to check the contract.
4. Tighten the contract until the proof passes within memory budget. This may require splitting harnesses per branch of the algorithm.

For each lifetime-laundering wrapper (`format_shortest`, `format_exact` in grisu):

1. Write a `#[kani::proof]` harness annotated with `#[kani::stub_for_contract(format_shortest_opt)]` (and the dragon fallback). This replaces the call to the algorithm with its contract's stub, so Kani only verifies the unsafe reborrow.
2. The harness should run in seconds, not minutes.

## Consequences

- The current branch lands six of twelve Challenge 28 functions verified, with a clear road map for the remaining six. PRs against verify-rust-std historically accept partial coverage if the approach generalises.
- A reviewer can read this ADR plus `decisions/0001-target-flt2dec-helpers-first.md` to understand both the picked subset and the deferred portion.
- The contract approach is the canonical Kani technique for verifying unsafe code that wraps algorithmically dense helpers. Adopting it here keeps the proofs maintainable.
- A second `nix run .#verify -- flt2dec-grisu` invocation is wired up for the deferred harnesses; it currently OOMs but exists as a sentinel for the contract refactor.
- Memory cap (12 GiB by default, override via `VERIFY_MEMORY_MAX`) was introduced for this experiment and stays. It protects the host from runaway CBMC instances regardless of which challenge is being verified.
