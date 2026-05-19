# verify-rust-std Challenge Landscape

Date: 2026-05-19
Status: complete

## Summary

verify-rust-std is the model-checking / Rust Foundation effort to formally verify the Rust standard library. Contributors take numbered "challenges" (specs under `doc/src/challenges/`), add tool annotations to `library/` and submit a PR for committee review. Of 29 challenges, 8 are fully solved, 1 is the just-created flt2dec challenge with no competing PRs, and the rest have at least one open PR (mostly from a single contributor `Samuelsills` filed March-April 2026).

For a one-session contribution, **Challenge 28 (flt2dec)** is the cleanest entry: 12 concrete safe-fn targets, all centred on `MaybeUninit::assume_init` correctness, 5000 USD bounty, no competition, deadline 2026-08-31.

## What the project is

- Fork of rust-lang/rust whose `library/` is the verification target. Periodically updated to track upstream std.
- Each challenge has a spec in `doc/src/challenges/NNNN-*.md`, a tracking issue, and a status column in the README.
- Two committee approvals required per PR. Bounties range 5k-25k USD.
- Approved tools: Kani (primary), VeriFast, GOTO Transcoder / ESBMC, Flux. Tool runners live in `scripts/run-kani.sh` etc.; CI workflows under `.github/workflows/`.

## Approved tools, brief

| Tool | What it is | Best at |
|---|---|---|
| Kani | CBMC-backed bounded model checker for Rust MIR. Supports function contracts (`requires`/`ensures`/`modifies`), harnesses, loop invariants. | Unsafe primitive code, UB checks. Weak on concurrency. |
| VeriFast | Separation-logic deductive verifier. | Linked data structures (used for `LinkedList`, `RawVec`). |
| ESBMC / GOTO Transcoder | Goto-program model checker. | Alternative engine for Kani-translated programs. |
| Flux | Refinement-type checker. | Lightweight invariants on indices / lengths. |

Adjacent tools not yet integrated here: Creusot, Prusti (deductive via Viper), Aeneas (Coq/F* extraction), MIRAI (abstract interpretation), RefinedRust. None are needed for current challenges.

## Open challenges as of 2026-05-19

Status verified against the README, tracking issues, and `gh pr list`. "Open PRs" reflects state before this scouting pass.

| # | Title | Module | Open PRs | Notes |
|---|---|---|---|---|
| 2 | core intrinsics with raw pointers | `core::intrinsics` | none | Deep unsafe, medium |
| 4 | BTreeMap node | `alloc::collections::btree::node` | #577 | Large, complex unsafe |
| 7 | Atomic types & intrinsics | `core::sync::atomic` | #578 (Part 1) | 3 parts, ~60 intrinsics |
| 8 | SmallSort contracts | `core::slice::sort::shared::smallsort` | #576 | Medium, heavy unsafe + loops |
| 10 | String memory safety | `alloc::string` | #571, #558 | Large |
| 12 | NonZero | `core::num::nonzero` | #565, #544 | Many thin wrappers, partial work in tree |
| 13 | CStr Part 4 | `core::ffi::c_str` | #543 | Parts 1-3 already merged |
| 15 | SIMD intrinsics | `core::intrinsics::simd` | none | Huge, exotic |
| 16 | Iterator funcs | `core::iter` | #549 | Large |
| 17/18 | slice / slice iter | `core::slice` | several | Large; 18 allows VeriFast |
| 20/21 | str::pattern parts | `core::str::pattern` | none | Large, 25k each |
| 22 | str iter | `core::str` iterators | several | Medium |
| 23/24 | Vec parts 1+2 | `alloc::vec` | several | Large |
| 25 | VecDeque | `alloc::collections::vec_deque` | #564 | Large |
| 26/27 | Rc / Arc | `alloc::rc`, `alloc::sync` | several | Medium-large |
| 28 | flt2dec | `core::num::flt2dec` | none | **12 targets, greenfield** |
| 29 | Box | `alloc::boxed` | #573, #589 | Medium |

Already resolved (do not touch): 1, 3, 5, 6, 9, 11, 14, 19.

## Kani minimum surface area used here

- `#[cfg(kani)] #[unstable(feature = "kani", issue = "none")] mod verify { use super::*; ... }` block appended to the target file.
- `#[kani::proof]` for free-form harnesses; `#[kani::proof_for_contract(path::to::fn)]` when the function has a `#[requires]`/`#[ensures]` contract attached.
- `kani::any::<T>()` for symbolic input, `kani::assume(cond)` for preconditions, `kani::slice::any_slice_of_array(&arr)` to pick an arbitrary-length sub-slice.
- `#[kani::unwind(N)]` only when the target contains loops.
- Repo runner: `./scripts/run-kani.sh --kani-args --harness <module::verify::name>`. Note that running this locally builds Kani from source against pinned commit in `tool_config/kani-version.toml`, which requires nightly Rust, CBMC, and Kissat. CI is the practical verification path for a fresh contributor.

## Recommendations

1. **Pick Challenge 28 first.** Smallest greenfield target, no competing PRs, the spec lists 12 concrete functions, all are safe-fn-with-unsafe-bodies focused on `MaybeUninit::assume_init` well-encapsulation. The two private helpers (`digits_to_dec_str`, `digits_to_exp_str`) are the simplest entry point and a natural template for the remaining ten.
2. **Skip Challenge 13 part 4** unless PR #543 stalls past its current review. Direct competition for the same harnesses.
3. **Skip Challenge 12** unless you can find a function that PRs #565 and #544 both missed.

## Open questions

- Does Kani's build script work on NixOS? `./scripts/run-kani.sh` runs `./scripts/setup/ubuntu/install_deps.sh` inside the cloned Kani repo, which assumes apt. A nix-shell with `rustup`, `cbmc`, and `kissat` may bypass the setup script if `cargo build-dev --release` is invoked directly.
- Is autoharness (`scripts/run-kani.sh --run autoharness`) usable on flt2dec? Could produce a starting point for the remaining ten functions.
