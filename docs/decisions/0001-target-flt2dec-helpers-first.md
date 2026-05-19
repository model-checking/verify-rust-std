# 0001. Target flt2dec private helpers first for Challenge 28

Status: accepted

## Context

Challenge 28 (flt2dec, 5000 USD bounty) requires proving twelve safe functions whose bodies contain `unsafe` code. All twelve centre on the same property: `MaybeUninit::assume_init*` calls must be preceded by full initialization of the indices they cover, and any lifetime laundering must be sound. No competing PRs are filed as of 2026-05-19. See `docs/research/verify-rust-std-challenge-landscape.md` for the wider landscape.

A single-session contribution cannot realistically cover all twelve. Picking which subset to tackle first determines whether the work compiles and verifies, and whether the resulting harnesses provide a usable template for the remaining functions.

## Options considered

- **Private helpers `digits_to_dec_str` and `digits_to_exp_str`** (chosen) - Both are concrete, non-generic, no loops, no calls into the grisu/dragon strategies. All `assume_init_ref` calls are local to the function bodies. Preconditions are visible as `assert!` statements at the top. Together they cover six branches and exercise every variant of the `Part` enum. Small enough to verify fast, complete enough to be a real contribution.
- **Public wrappers `to_shortest_str` and `to_shortest_exp_str`** - These call the private helpers; verifying them would transitively verify the helpers, but generic type parameters (`T: DecodableFloat`, `F: FnMut(&Decoded, &mut [u8]) -> (usize, i16)`) complicate harness construction. The spec allows restricting generics to primitive types, but that adds noise.
- **Strategy entry points `format_shortest` / `format_exact` in grisu/dragon** - The most algorithmically interesting targets and the deepest use of unsafe, but they contain loops requiring `#[kani::unwind(N)]` bounds and substantial domain reasoning about the digit-generation invariants. Out of scope for an opening contribution.

## Decision

Land harnesses for `digits_to_dec_str` and `digits_to_exp_str` first. They are simple enough that the harness pattern (symbolic bounded inputs, assumption of documented preconditions, full read-back of returned `&[Part<'a>]`) generalizes to every other target in the challenge.

## Consequences

- Two of twelve target functions get covered in this initial cut. The remaining ten require follow-up work that can reuse the same `verify` module structure.
- The harnesses are not run locally - building Kani on NixOS would require a nix-shell with rustup, cbmc, and kissat, plus bypassing the Ubuntu setup script. The project CI (Kani workflow) is the authoritative verification path; we rely on it.
- The chosen targets ship as a `#[cfg(kani)] mod verify` block appended to `library/core/src/num/flt2dec/mod.rs`. The function bodies are untouched, which keeps the change clean and reduces review friction.
- A reviewer might ask why `frac_digits` is bounded to `<= 8` rather than fully symbolic. The answer is verification-time tractability; an unbounded `usize` would explore arithmetic paths like `frac_digits - buf.len() - minus_exp` overflow but blow up the search. A follow-up harness can address overflow paths separately.
- The lifetime-laundering aspect of the challenge is implicitly covered: the returned `&[Part<'a>]` borrows from `buf` and `parts_storage`, and the harness reads every element while both are still live. There is no explicit transmute or pointer cast in these two functions, so no separate lifetime proof is needed.
