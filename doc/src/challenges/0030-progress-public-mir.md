# Challenge 30: Progressing Public MIR for verification tool infrastructure

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** [#591](https://github.com/model-checking/verify-rust-std/issues/591)
- **Start date:** *TBD*
- **End date:** *TBD*
- **Reward:** *TBD*

-------------------


## Goal

Progress the [`rustc_public`](https://github.com/rust-lang/project-stable-mir)
(formerly Stable MIR) interface so that verification tools targeting the Rust
standard library can consume post-analysis MIR without falling back to
`rustc_internal` APIs. This challenge is infrastructure-focused: it does not
verify a specific standard library module, but rather removes a class of
fragility that affects tools in this repository that operates on Public MIR
(Kani, KMIR, and any future consumer of Public MIR).

## Motivation

The Rust compiler exposes multiple intermediate representations. MIR after
borrow-check is the most useful endpoint for third-party static and dynamic
analyses, and the `rustc_public` crate (split into `rustc_public` and
`rustc_public_bridge` upstream) is the stable(r) surface intended for such tools.

In practice, `rustc_public` is incomplete. Tools that consume MIR today
routinely round-trip through `rustc_internal` to retrieve information that
should be available through the public API. Two concrete examples from
verification tools used or targeted by this repository:

- Kani maintains an internal MIR helper
  [internal_mir.rs](https://github.com/model-checking/kani/blob/main/kani-compiler/src/kani_middle/transform/internal_mir.rs)
  that reaches into compiler-private types to reconstruct data the public API
  cannot yet provide. The file exists because Kani's delayed-UB instrumentation
  relies on rustc's MIR dataflow framework, which operates on internal MIR only.
  Kani carries them in-tree today, but without upstream inclusion the benefit
  is likely not distributed to other consumers of Public MIR. This challenge
  therefore cannot be treated as a purely mechanical lifting of Kani's helpers
  and other missing components; part of the work is re-opening that design
  conversation in the workgroup.
- Stable MIR JSON (the serialisation layer used by KMIR) has had to carry
  fixes to issues such as [94](https://github.com/rust-lang/project-stable-mir/issues/94)
  that were simply misuse of internel vs. public APIs.

Internal APIs may change on any nightly, reducing the effectiveness of a
stablised interface. Furthermore, tools that require calls an
internal API instead of a public one run the risk of accessing an _incorrect_
API for their purpose. This is both easy to do and hard to detect. This
creates friction for verification tooling built on Public MIR and effictively
narrows the verification techniques available by creating unnecessary hurdles
that are antipatterns to the goals of Public MIR (discouraging adoption).

## Description

`rustc_public` today exposes a mostly-stable view of MIR, but three classes
of problem push tool authors back into `rustc_internal`:

1. **Missing coverage.**  In-source `todo!()` and `FIXME` markers are a
  direct in-source signal, but are not entirely informative. These are often
  linked to experimental or planned features in Public MIR and not
  representative of the gaps downstream users are running into currently.
  However, these places will be considered and closed opportunitistically.

   The higher-signal picture of where `rustc_public` falls short for
   verification tools is the workarounds tool authors have had to produce to
   get the data unavailable through the Public MIR API. Kani documents this in
   [internal_mir.rs](https://github.com/model-checking/kani/blob/main/kani-compiler/src/kani_middle/transform/internal_mir.rs),
   with similar challenges faced by
   [stable-mir-json](https://github.com/runtimeverification/stable-mir-json/). The
   [project-stable-mir issue tracker](https://github.com/rust-lang/project-stable-mir/issues)
   also offers insight into current gaps that are actually being hit by consumers
   of Public MIR. The subject of this challenge is that body of work: the design
   conversations with the workgroup, the upstream API additions that unblock tool
   migrations, and the consumer-side deletions that follow.
2. **Dialect ambiguity.** The internal MIR pipeline exposes four distinct
   phases (built, const-eval, optimised, post-analysis). The access point
   for all versions of MIR is the `after_analysis` callback. `rustc_public`
   itself does not commit to any single phase at the API boundary, with
   different dialects being accessible by applying transformations on the
   _internal_ MIR and then bridging to _public_ MIR. The MIR collected via
   the callback is polymorphic; tools that want monomorphised MIR
   therefore perform manual monomorphisation from that callback. However,
   subtle intricacies with this method and missing coverage (see 1.) make
   it easy to mix monomorphised MIR with MIR from another phase leaving the
   resulting MIR in a state that no specific tool is designed to consume.

   Clarifying what phase(s) `rustc_public` is willing to expose, and providing
   documentation, better API coverage, and potentially enforced guards on
   dialect access would let tools access the dialects they expect in a clearly
   defined manner.
3. **Typing-context leakage.** Several operations that appear public still
   require reaching into `TyCtxt`. Lifting these behind `rustc_public`
   wrappers is the remainder of the work started upstream; see the discussion
   in the project-stable-mir workgroup and related issues
   (e.g. [project-stable-mir#94](https://github.com/rust-lang/project-stable-mir/issues/94)).

The challenge is a time-boxed effort to close these gaps upstream, and to
demonstrate the result by removing the corresponding internal-API usage from
verification tools that (current or future) that can contribute to
verification of Rust `std` library.

### Assumptions

- Experimental nightly-only constructs that are not yet meaningfully present
  in internal MIR (for example, features gated behind unstable flags such as
  `tail_call`-style terminators) are out of scope beyond mechanical plumbing.
  If supporting them in `rustc_public` would require redesigning the
  corresponding internal MIR surface, that redesign is out of scope.
- The split between `rustc_public` (stable-facing crate) and
  `rustc_public_bridge` (internal adapter) is assumed to be the intended
  long-term architecture. Work targets these crates rather than proposing a
  new location.
- Solutions are landed upstream in `rust-lang/rust` via the
  [project-stable-mir](https://github.com/rust-lang/project-stable-mir)
  workgroup.

### Success Criteria

Since this challenge does not directly verify components of `std`, but
improves the landscape for verification, the success criteria are stated as
API-surface and tool-integration deliverables rather than per-function
safety contracts.

**A. Time-boxed, best-effort migration.** Within the engagement, convert as
many verification-tool API calls from `rustc_internal` to `rustc_public` as
is feasible, and implement missing `rustc_public` surface where a conversion
target does not yet exist. A complete migration of the consumer surfaces
named in the Motivation (Kani's `internal_mir.rs`, stable-mir-json, and
similar shims) is attempted, with the understanding that community consensus
has historically blocked some conversions.

Where a similar blocker re-surfaces during the engagement, the deliverable
for that surface is a **taxonomy of possible solutions** (for example:
lift conversions into `rustc_public`, expose a narrower data-only API,
add an opt-in dataflow adapter, or leave the consumer-side shim documented
as intentional) with enough analysis for the workgroup to continue the
conversation after the engagement closes. A blocker presented with this
analysis counts toward the criterion; a blocker only noted without analysis
does not.

**B. Dialect clarity.** The four MIR dialects exposed through the compiler
pipeline are addressed in one of two ways at the `rustc_public` boundary:
(i) the boundary is explicitly restricted to a documented subset (the
specific phase or phases are to be decided in workgroup discussion, with
post-analysis and post-monomorphisation as the leading candidates), or
(ii) the API documents the invariants each reachable dialect satisfies so
that consumers can tell which state they are observing.

**C. Residual roundtrips are documented.** Any internal-MIR roundtrips that
cannot be removed within the time box are enumerated in an upstream-visible
document (workgroup notes or tracking issue) with a short description of
why each roundtrip is still required. This is an explicit success criterion:
a catalogued gap is valuable in lieu of a closed one.

Additional scope for the time-boxed effort may be drawn from the
[open issues on project-stable-mir](https://github.com/rust-lang/project-stable-mir/issues),
prioritised by impact on verification tools targeting this repository. Which
of those issues are addressed, deferred, or re-scoped during the engagement
is itself part of the workgroup conversation, and a justified triage of that
issue list counts toward criterion **C**.

**D. Verification-tool CI still passes.** At least one verification tool
used in this repository's CI (Kani, or KMIR once integrated) is rebuilt
against a toolchain carrying the changes, with all of its proofs for the
currently-resolved challenges still succeeding. This ensures the
stabilisation work does not regress existing verification results.

## Correctness Criteria

The Rust reference's list of undefined behaviour does not apply to this
challenge, because the deliverable is compiler infrastructure rather than
a run-time construct. In its place, solutions must satisfy the following
correctness properties:

- For every new `rustc_public` lowering added under criterion **A**, the
  public surface faithfully represents the post-analysis internal MIR node:
  a round-trip lowering (where the construct allows one) preserves shape and
  referenced identifiers, and the serialised output from Stable MIR JSON
  round-trips through its consumer without data loss.
- `rustc_public` APIs introduced to replace consumer-side shims under
  criterion **A** do not require the caller to hold or construct a `TyCtxt`,
  and do not re-export `rustc_internal` types in their signatures.
- Solutions are landed as merged pull requests against `rust-lang/rust`.

Note: All solutions to verification challenges need to satisfy the criteria
established in the [challenge book](../general-rules.md) in addition to the
ones listed above.
