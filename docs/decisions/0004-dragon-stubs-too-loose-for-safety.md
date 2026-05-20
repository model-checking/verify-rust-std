# 0004. Dragon strategy stubs are too loose to prove safety

Status: accepted

## Context

The Grisu strategy harnesses (`format_shortest_opt`, `format_exact_opt`) verify SUCCESSFULLY under the Loitsch-paper-derived stubs (`Fp::mul`, `cached_power`, `max_pow10_no_more_than`) combined with a deterministic identity-on-`f` `Fp::mul`. The key insight there was that the algorithm's safety depends on a *monotonic ordering* of three successive `Fp::mul` calls; a stateless stub that picks each result independently breaks that ordering, but `result.f = self.f` (identity) trivially preserves it.

We attempted the analogous approach for the Dragon strategy harnesses (`format_shortest`, `format_exact`). The four target functions and their wrappers run through the `Big32x40` 40-limb bignum, with operations:

- `mul_small`, `mul_pow2`, `mul_pow5`, `mul_digits`, `add`, `add_small`, `sub`, `div_rem_small`
- `cmp`, `eq` (via `Ord`/`PartialEq`)
- `bit_length`

All of these are now stubbed, and the harnesses compile and run within the 24 GiB memory cap. But they fail verification with check failures of two kinds:

1. **debug_assert panics**: `d < 10`, `mant < scale`, `*x < *scale`. The algorithm guarantees these via the bignum invariant `mant < scale * 10` (which makes the per-iteration peeled digit `d` strictly less than 10). With `cmp` returning a nondet `Ordering`, the algorithm's decisions are arbitrary and the invariant is broken.

2. **buffer-bounds panics**: `buf[i] = MaybeUninit::new(b'0' + d)` at lines 203 and 260 of `dragon.rs`. These rely on the algorithm terminating within `MAX_SIG_DIGITS = 17` iterations of the main loop. With nondet `cmp`, the loop's `if down || up { break; }` exit becomes nondet and can run up to the `#[kani::unwind(20)]` cap of 20 iterations, exceeding the buffer.

Both failure modes are *consequences of stub imprecision*, not real bugs in the algorithm. They are panics, not undefined behaviour: `buf[i]` uses the checked `Index` trait, so OOB triggers a Rust panic rather than a raw out-of-bounds memory write. The Challenge 28 safety property is "no UB on the `MaybeUninit` buffer", which is technically satisfied.

## Options considered

- **Identity-on-`f` analogue.** Grisu's win was that `Fp::mul` could be modelled as the identity on the 64-bit mantissa, which preserves the algorithm's required ordering. The bignum analogue would need a single 40-limb numeric value carried through every operation. Doing that without re-implementing the bignum is exactly the OOM-inducing case we were trying to avoid.

- **Tracking an abstract scalar through Big32x40.** Augment the `Big` type with a `#[cfg(kani)]` ghost `u128` field that's updated by each stub to reflect a small approximation of the real value. `cmp` consults this ghost. This is feasible but invasive (touches `bignum.rs` and every stub) and the ghost arithmetic is its own source of overflow / soundness concerns.

- **Contracts + `stub_verified` on each bignum method.** Add `#[ensures]` to `Big32x40::mul_small` etc., prove those contracts in isolation (small harnesses, tractable), and then have `format_shortest`/`format_exact` use them via `kani::stub_verified`. This is the canonical Kani idiom but requires writing and verifying ~10 separate contracts on the bignum, each with its own postcondition (size growth bounds, division remainder bounds, etc.).

- **Accept partial coverage.** Ship the dragon stub framework as-is with this ADR explaining the precision gap. The harnesses compile and run, so future contributors can iterate on tightening the stubs without re-deriving the abstraction. The Challenge 28 spec's "or safety contracts should be added" clause is satisfied by the contracts on `format_shortest` and `format_exact` already merged.

## Decision

Accept partial coverage for Dragon. Ship:

- Safety contracts on `dragon::format_shortest` and `dragon::format_exact` (already merged).
- The stub framework in `dragon::verify` (already merged) so the harnesses compile and CBMC finishes in under 10 minutes per run.
- This ADR explaining the precision gap and the path forward.

The path forward for full verification is contract decomposition on the bignum primitives, analogous to ADR 0003 for Grisu but applied one layer deeper.

## Consequences

- Verified count for Challenge 28 stands at **8 of 12** end-to-end Kani-verified, plus safety contracts on the 4 dragon strategy functions.
- Future contributor has a clear roadmap: write `#[ensures]` on the Big32x40 methods, verify each in isolation, and then drop the loose stubs in favour of `stub_verified`.
- The `kani_havoc` helper in `bignum.rs` remains for future contract verification; it is a reasonable foundation for the per-method proofs.
- The dragon harnesses are wired up under the `flt2dec-dragon-strategies` flake app and exercise the stub framework end-to-end, so any future tightening of the stubs is easy to test.
