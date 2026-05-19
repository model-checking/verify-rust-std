# 0002. Nix flake for local Kani runs

Status: accepted

## Context

verify-rust-std's `scripts/run-kani.sh` clones Kani from a pinned commit and builds it from source. The build needs nightly Rust (matching `rust-toolchain.toml`), CBMC, kissat, plus the assumption that the dev environment looks like a rustup-managed Ubuntu box. On NixOS none of those assumptions hold: there is no `/bin/bash`, no rustup, the apt-based dep installer (`scripts/setup/ubuntu/install_deps.sh`) does not run, and CBMC / kissat live in `/nix/store` rather than `/usr/bin`.

Without local verification, contributors rely on the project's CI to learn whether harnesses compile and pass. That feedback loop is too slow for iteration. See `docs/decisions/0001-target-flt2dec-helpers-first.md`, which initially deferred local runs for exactly this reason.

## Options considered

- **Nix flake providing tools, run-kani.sh does the Kani build** (chosen) - Flake exposes a devShell with fenix-managed nightly Rust, cbmc, kissat, python3, jq, build basics. A `nix run .#verify -- <challenge>` app wraps `run-kani.sh` after applying a few targeted patches (rustup-layout shim, cargo +toolchain wrapper, /bin/bash shebang fixes). First run rebuilds Kani from source against the pinned commit; subsequent runs are seconds.
- **Build Kani itself in Nix (custom derivation)** - Cleanest in theory: Kani becomes a reproducible Nix package. Rejected as out of scope for a contributor environment - Kani's build assumes rustup and pulls a specific CBMC version; packaging it correctly is non-trivial and would diverge from the upstream build process.
- **Docker / OCI container** - Avoids NixOS quirks by running an Ubuntu environment. Rejected because it adds a layer of virtualization, slows iteration, and contradicts the user's existing Nix-first workflow.
- **Defer to CI only** - Rejected: slow feedback loop, no ability to debug locally, harness errors only visible after pushing.

## Decision

Ship `flake.nix` with a `devShells.default` and `apps.verify`. Map challenge names to fully-qualified harness identifiers in the app's case statement. Patch around five NixOS-specific issues at runtime:

1. `/bin/bash` shebang in `run-kani.sh` and friends - rewrite to `/usr/bin/env bash`.
2. `env!("RUSTUP_TOOLCHAIN")` in `build-kani/src/main.rs` - export it from `rust-toolchain.toml`.
3. `RUSTUP_HOME/toolchains/$TC/lib` rpath in `kani-compiler/build.rs` - synthesise a fake `$PWD/.rustup-fake` whose toolchain symlink points at the fenix sysroot.
4. `cargo +<toolchain>` invocation by kani-driver - install a thin shim `cargo` in `$PWD/.toolchain-wrapper` that strips the leading `+` arg and forwards.
5. `kani_build/` left half-built by a previous failed run trips the script's "is Kani up to date" check (which only inspects the git commit, not the binary) - detect and clean.

## Consequences

- `nix run .#verify -- flt2dec` runs end-to-end on NixOS. Both harnesses verify, 254 individual safety checks succeed, verification time around 1.5 seconds after Kani is built.
- The two flt2dec helper functions (`digits_to_dec_str`, `digits_to_exp_str`) move from "harnesses-written" to "machine-verified" status. The challenge as a whole stays open: 10 functions remain.
- CBMC / kissat versions in nixpkgs are newer than Kani's pinned versions (6.9.0 vs 6.7.1, 4.0.4 vs 4.0.1). Kani's version-check scripts use "newer is fine" comparisons, so the mismatch does not trip the apt fallback. Worth re-verifying if Kani's pinned versions change.
- The first run of `nix run .#verify` takes 10-20 minutes (Kani builds from source). Subsequent runs are seconds. `kani_build/` is gitignored.
- The flake is verify-rust-std-specific; it does not generalise to other Nix-on-Rust setups without adjustment.
