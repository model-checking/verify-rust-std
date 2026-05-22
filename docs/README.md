# Notes

Working notes for this fork. Not part of the upstream `doc/` mdBook.

## Status

Challenge 28 (flt2dec): **12 of 12 functions verified end-to-end via Kani**. PR not yet opened. Run `nix run .#verify -- flt2dec` from the repo root to reproduce. Verified:

- `digits_to_dec_str`, `digits_to_exp_str`, `to_shortest_str`, `to_shortest_exp_str`, `to_exact_exp_str`, `to_exact_fixed_str` (the last four monomorphised to `f32`)
- `grisu::format_shortest_opt` and `grisu::format_exact_opt` via the Loitsch-paper-derived stubs and a hoisted `round_and_weed`
- `grisu::format_shortest` and `grisu::format_exact` (the two lifetime-laundering wrappers) via hand-written stubs of the inner `_opt` calls and the dragon fallback
- `dragon::format_shortest` and `dragon::format_exact` via tightened `Decoded` inputs matching `decode_finite`'s real output shape (`minus=1`, `plus in {1,2}`), a stub of `div_rem_upto_16` that directly encodes the algorithm's `d < 10` digit-range invariant, a stub of `Big::is_zero` that avoids the 40-limb `iter().all` unwind, a call-counter on `stub_big_cmp` that bounds the digit-generation loop within `MAX_SIG_DIGITS`, and a release-profile build (`CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=false`) so the harness verifies *release semantics* — the algorithm-correctness `debug_assert!` invariants are out of scope for Challenge 28's "no UB" safety mandate.

## Reproducing locally

- `nix run .#verify -- flt2dec` — Verifies the 6 public/helper functions (passes).
- `nix run .#verify -- flt2dec-grisu-strategies` — Verifies the 2 grisu `_opt` functions (passes).
- `nix run .#verify -- flt2dec-grisu-wrappers` — Verifies the 2 grisu wrapper functions (passes, sub-second each).
- `nix run .#verify -- flt2dec-dragon-strategies` — Verifies the 2 dragon strategy functions (passes, ~10s).

Set `VERIFY_MEMORY_MAX` to override the default 24 GiB systemd-cgroup memory cap.

## Contents

- [research/verify-rust-std-challenge-landscape.md](research/verify-rust-std-challenge-landscape.md) - Snapshot of open challenges, tools, and Kani usage conventions as of 2026-05-19.
- [decisions/0001-target-flt2dec-helpers-first.md](decisions/0001-target-flt2dec-helpers-first.md) - Why Challenge 28's two private helpers were the first target.
- [decisions/0002-nix-flake-for-local-kani.md](decisions/0002-nix-flake-for-local-kani.md) - Flake design for reproducible Kani runs on NixOS.
- [decisions/0003-grisu-needs-contract-decomposition.md](decisions/0003-grisu-needs-contract-decomposition.md) - Why the six Grisu/Dragon strategy functions needed contract-based decomposition; partially superseded by ADR 0004.
- [decisions/0004-dragon-stubs-too-loose-for-safety.md](decisions/0004-dragon-stubs-too-loose-for-safety.md) - Dragon strategy verification gap and the contract-decomposition path forward.
