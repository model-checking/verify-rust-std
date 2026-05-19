# Notes

Working notes for this fork. Not part of the upstream `doc/` mdBook.

## Status

Challenge 28 (flt2dec): **2 of 12 functions verified locally via Kani**. PR not yet opened. Run `nix run .#verify -- flt2dec` from the repo root to reproduce.

## Contents

- [research/verify-rust-std-challenge-landscape.md](research/verify-rust-std-challenge-landscape.md) - Snapshot of open challenges, tools, and Kani usage conventions as of 2026-05-19.
- [decisions/0001-target-flt2dec-helpers-first.md](decisions/0001-target-flt2dec-helpers-first.md) - Why Challenge 28's two private helpers were the first target.
- [decisions/0002-nix-flake-for-local-kani.md](decisions/0002-nix-flake-for-local-kani.md) - Flake design for reproducible Kani runs on NixOS.
