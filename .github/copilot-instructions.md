# Verify Rust Standard Library — Code Review Guidelines

## Purpose & Scope

This repository is a fork of the Rust standard library used exclusively for formal verification. Verification targets include memory safety, undefined behavior, and functional correctness, depending on the specific challenge. PRs fall into four categories: **solving challenges**, **proposing new challenges**, **proposing new tools**, and **maintenance**.

## Approved Verification Tools

Only these tools are accepted: **Kani**, **VeriFast**, **Flux**, and **ESBMC (GOTO-Transcoder)**. Flag any PR that uses a tool not on this list — it must go through a separate tool application process first.

---

## General Rules (All PRs)

- The contribution must be automated and pass as part of PR CI checks.
- Changes must not alter the runtime logic of the standard library unless the change is proposed and incorporated upstream into the official Rust standard library.
- All contributors must be properly credited. By submitting, contributors confirm they can use, modify, copy, and redistribute their contribution.
- PRs should reference the relevant tracking issue (e.g., `Resolves #ISSUE-NUMBER`).
- Merging requires approval from at least two committee members listed in `.github/pull_requests.toml`.

---

## Challenge Solutions (Highest Priority)

These PRs solve open verification challenges. Apply the strictest review criteria:

### Success Criteria Compliance
- Verify the PR meets **every** success criterion listed in the specific challenge description. Partial solutions should be flagged.
- Check the challenge page at `doc/src/challenges/` or the [challenge book](https://model-checking.github.io/verify-rust-std/challenges/) for the exact requirements.

### Formal Verification Rigor
- **No vacuous proofs.** Ensure harnesses and contracts actually exercise the property under verification. A proof that passes trivially (e.g., with an unsatisfiable precondition or an empty harness body) is unacceptable.
- **No unjustified assumptions.** Every `#[kani::assume]`, `requires`, or equivalent precondition must be justified by the function's documented safety contract or API invariants. Flag assumptions that over-constrain inputs to make verification pass.
- **Contracts must reflect documented safety conditions.** Cross-reference preconditions and postconditions against the function's `# Safety` doc comments and the [official std library documentation](https://doc.rust-lang.org/std/).
- **Harnesses must cover meaningful input ranges**, not just trivial or degenerate cases.
- **Verification must actually run in CI** using one of the approved tools. Check that the relevant workflow (kani.yml, verifast.yml, flux.yml, goto-transcoder.yml) executes the new proofs.

### Code Quality for the Rust Standard Library
- Code should be **idiomatic Rust** and match the style of the surrounding standard library code.
- Unsafe code blocks must have a `// SAFETY:` comment explaining why the usage is sound.
- Use `#[inline]` only on public, small, non-generic functions. Do not add `#[inline]` to generic methods or trait methods without default implementations. Avoid `#[inline(always)]` unless justified by benchmarks.
- Contracts and harness code should be **readable and well-documented** so that someone unfamiliar can understand what property is being verified and why.
- Verification annotations (contracts, harnesses, proof attributes) should be clearly separated from the library's functional code using `cfg` attributes (e.g., `#[cfg(kani)]`) so they don't affect normal compilation.
- Do not introduce new public API surface unless the challenge explicitly requires it.

---

## New Challenge Proposals

- Must follow the template at `doc/src/challenge_template.md`.
- Must include a tracking issue created with the challenge issue template.
- Must add an entry in `doc/src/SUMMARY.md`.
- Success criteria must be specific, measurable, and achievable with the currently approved tools.
- Flag vague or overly broad success criteria.

---

## New Tool Applications

- Must be submitted as a separate issue using the "Tool Application" template before any PR using the tool.
- The PR must include a new CI workflow that runs the tool against the standard library.
- The PR must add a new entry to the "Approved Tools" section of the book.

---

## Maintenance PRs

- Repository updates, CI fixes, documentation improvements, and dependency bumps.
- Should not change verification semantics or weaken existing proofs.
- Flag any maintenance PR that removes or weakens existing contracts, harnesses, or proof obligations.

---

## Common Red Flags to Watch For

- Harness with no assertions or only trivial assertions.
- `kani::assume(false)` or preconditions that make the proof vacuously true.
- Assumptions that are stricter than what the function's safety docs require.
- Contracts that don't match the `# Safety` section of the function being verified.
- Verification code that is not gated behind a tool-specific `cfg` (e.g., `#[cfg(kani)]`).
- Changes to `library/` source files that alter runtime behavior without upstream justification.
- Missing or incorrect tracking issue references.
- Use of a verification tool not in the approved list.
- Large, hard-to-review PRs that should be split into smaller logical units.
