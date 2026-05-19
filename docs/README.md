# Notes

Working notes for this fork. Not part of the upstream `doc/` mdBook.

## Status

Challenge 28 (flt2dec): **6 of 12 functions verified locally via Kani**. PR not yet opened. Run `nix run .#verify -- flt2dec` from the repo root to reproduce. Verified so far: `digits_to_dec_str`, `digits_to_exp_str`, `to_shortest_str`, `to_shortest_exp_str`, `to_exact_exp_str`, `to_exact_fixed_str` (the last four monomorphised to `f32`). The remaining six (Grisu and Dragon strategy functions) need contract-based decomposition; see [decisions/0003](decisions/0003-grisu-needs-contract-decomposition.md). An experimental harness pair for the grisu lifetime-laundering wrappers is wired up at `nix run .#verify -- flt2dec-grisu`; both currently OOM at 12 GiB.

## Contents

- [research/verify-rust-std-challenge-landscape.md](research/verify-rust-std-challenge-landscape.md) - Snapshot of open challenges, tools, and Kani usage conventions as of 2026-05-19.
- [decisions/0001-target-flt2dec-helpers-first.md](decisions/0001-target-flt2dec-helpers-first.md) - Why Challenge 28's two private helpers were the first target.
- [decisions/0002-nix-flake-for-local-kani.md](decisions/0002-nix-flake-for-local-kani.md) - Flake design for reproducible Kani runs on NixOS.
- [decisions/0003-grisu-needs-contract-decomposition.md](decisions/0003-grisu-needs-contract-decomposition.md) - Why the six Grisu/Dragon strategy functions need contract-based decomposition instead of whole-program verification.
