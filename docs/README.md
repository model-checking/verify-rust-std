# Notes

Working notes for this fork. Not part of the upstream `doc/` mdBook.

## Status

Challenge 28 (flt2dec): **8 of 12 functions verified end-to-end via Kani**, plus safety contracts on the remaining 4. PR not yet opened. Run `nix run .#verify -- flt2dec` from the repo root to reproduce. Verified so far:

- `digits_to_dec_str`, `digits_to_exp_str`, `to_shortest_str`, `to_shortest_exp_str`, `to_exact_exp_str`, `to_exact_fixed_str` (the last four monomorphised to `f32`)
- `grisu::format_shortest_opt` and `grisu::format_exact_opt` via the Loitsch-paper-derived stubs and a hoisted `round_and_weed`

The remaining four (`grisu::format_shortest`, `grisu::format_exact`, `dragon::format_shortest`, `dragon::format_exact`) have safety contracts merged. The two dragon strategy functions additionally have a working Kani harness scaffold under `flt2dec-dragon-strategies` that runs to completion within the memory cap but reports stub-precision failures; see [decisions/0004](decisions/0004-dragon-stubs-too-loose-for-safety.md) for the gap and the path forward.

## Reproducing locally

- `nix run .#verify -- flt2dec` — Verifies the 6 public/helper functions (passes).
- `nix run .#verify -- flt2dec-grisu-strategies` — Verifies the 2 grisu `_opt` functions (passes).
- `nix run .#verify -- flt2dec-dragon-strategies` — Runs the dragon strategy harnesses (currently reports stub-precision failures, see ADR 0004).

Set `VERIFY_MEMORY_MAX` to override the default 24 GiB systemd-cgroup memory cap.

## Contents

- [research/verify-rust-std-challenge-landscape.md](research/verify-rust-std-challenge-landscape.md) - Snapshot of open challenges, tools, and Kani usage conventions as of 2026-05-19.
- [decisions/0001-target-flt2dec-helpers-first.md](decisions/0001-target-flt2dec-helpers-first.md) - Why Challenge 28's two private helpers were the first target.
- [decisions/0002-nix-flake-for-local-kani.md](decisions/0002-nix-flake-for-local-kani.md) - Flake design for reproducible Kani runs on NixOS.
- [decisions/0003-grisu-needs-contract-decomposition.md](decisions/0003-grisu-needs-contract-decomposition.md) - Why the six Grisu/Dragon strategy functions needed contract-based decomposition; partially superseded by ADR 0004.
- [decisions/0004-dragon-stubs-too-loose-for-safety.md](decisions/0004-dragon-stubs-too-loose-for-safety.md) - Dragon strategy verification gap and the contract-decomposition path forward.
