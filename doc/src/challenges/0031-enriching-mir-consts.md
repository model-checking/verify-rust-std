# Challenge 31: Enriching MIR constants

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** *https://github.com/model-checking/verify-rust-std/issues/594*
- **Start date:** *TBD*
- **End date:** *TBD*
- **Reward:** *TBD*

-------------------


## Goal

Investigate, and where feasible implement, changes to the way MIR constants
are represented and exposed, on both the internal (`mir::Const`, `ty::Const`)
and public (`MirConst`, `TyConst`) sides, so that verification tools can
reason about Rust constants in a form that matches their semantic role rather
than being forced through whichever byte-level representation the current
access path happens to hand them. Two distinct gaps are in scope:

1. **Preserve `Unevaluated` variants.** In rustc today, monomorphisation
   and constant evaluation are mutually entangled in the same flow, a
   uroboros: substitution feeds evaluation with the concrete types and
   arguments it needs, while evaluation feeds substitution back with values
   for const generic parameters and feeds the mono collector with the
   cross-item provenance through which further reachable items are
   discovered. The pipeline that delivers monomorphised MIR to a consumer
   therefore consumes the evaluated values rather than propagating the
   `Unevaluated` form through. A tool that wants to reason about a symbolic
   constant reference at a high level has to either fall back to
   pre-monomorphisation MIR, or reverse the evaluation step by hand to
   reconstruct high-level values (as
   [KMIR](https://github.com/runtimeverification/mir-semantics/) and
   [mir-json](https://github.com/GaloisInc/mir-json) do today).
2. **Enrich Public MIR evaluated representation.** Bridge structured forms
   (`ValTree`) on the public side for use of high-level data, instead of
   collapsing every evaluated constant into `Allocation`. This gap is
   acknowledged upstream by comment
   ["FIXME: These should be a valtree"](https://github.com/rust-lang/rust/blob/36ba2c7712052d731a7082d0eba5ed3d9d56c133/compiler/rustc_public/src/ty.rs#L149).

This is an infrastructure challenge: it does not verify a specific standard
library module, but it enables a class of verification techniques that today
must either reason over layout-dependent byte blobs or reverse the compiler's
evaluation steps at the tool level.

## Motivation

Both the internal MIR surface (`mir::Const`, `ty::Const`) and the public
`rustc_public` surface (`MirConst`, `TyConst`) already model unevaluated
constants through their `Unevaluated` variants. What does not exist, in
practice, is a path by which a tool can obtain a monomorphised MIR body that
still contains those unevaluated forms. The access routes that deliver
monomorphised MIR to consumers run constant evaluation as part of the same
flow, and constants are lowered to `ConstValue` before becoming accesible
again.

Evidence that this matters to tool authors:
- [mir-json](https://github.com/GaloisInc/mir-json) (the MIR exporter behind
  `crux-mir` / Crucible) ships a hand-rolled post-evaluation
  [MIR decoder](https://github.com/GaloisInc/mir-json/blob/2fc80d73eaede1e394a4ec6970fb5ca9e33efd73/src/analyz/ty_json.rs#L1240-L1464).
  While the problem is solved for `mir-json`, without an upstream solution it
  is likely that any other project that has the same requirements will attempt
  to re-implement this work.
- [mir-semantics](https://github.com/runtimeverification/mir-semantics/)
  implements a similar solution decoding constant `Allocation`s Public MIR
  [during parsing](https://github.com/runtimeverification/mir-semantics/blob/master/kmir/src/kmir/decoding.py)
  of the exported Stable MIR JSON.
- Open project-stable-mir issues
  [#96](https://github.com/rust-lang/project-stable-mir/issues/96) and
  [#101](https://github.com/rust-lang/project-stable-mir/issues/101) are
  concrete symptoms of the brittleness. Improvements to the constant
  representations or access patterns should be solutions to both.

The objective is to make a high-level constant form (`UnevaluatedConst`
variants, or an equivalent structured representation that preserves
cross-item reachability without committing to a particular byte layout)
available in MIR bodies that are otherwise monomorphised and evaluated,
without harming downstream codegen performance. Which of several candidate
implementations is the right one is itself part of the engagement.

## Description

There are two intertwined gaps, corresponding to the two bullets in the Goal:
the MIR pipeline couples monomorphisation with constant evaluation, and the
public constant surface collapses several distinct internal shapes into a
single byte-level form. Each is described in turn below.

**Monomorphisation and constant evaluation.** Inside
[collect_and_partition_mono_items](https://github.com/rust-lang/rust/blob/37d85e592f9ae5f20f7d9a9f99785246fa7298da/compiler/rustc_monomorphize/src/partitioning.rs#L1132-L1237),
constant evaluation is reached on the mono path through three sites in
`compiler/rustc_monomorphize/src/collector.rs`:

- [Const::eval(...)](https://github.com/rust-lang/rust/blob/37d85e592f9ae5f20f7d9a9f99785246fa7298da/compiler/rustc_monomorphize/src/collector.rs#L707-L722)
  from `MirUsedCollector::eval_constant`, hit on every MIR const operand
  encountered during a body walk.
- [tcx.eval_static_initializer](https://github.com/rust-lang/rust/blob/37d85e592f9ae5f20f7d9a9f99785246fa7298da/compiler/rustc_monomorphize/src/collector.rs#L440-L444)
  run once per `MonoItem::Static` root.
- [tcx.const_eval_poly](https://github.com/rust-lang/rust/blob/37d85e592f9ae5f20f7d9a9f99785246fa7298da/compiler/rustc_monomorphize/src/collector.rs#L1580-L1582)
  from `RootCollector::process_item`, run on top-level const items under
  `MonoItemCollectionStrategy::Eager`. In the default Lazy mode this site is
  inert; consts there are reached through their use sites via first method.

By the time a downstream tool sees the resulting MIR,
`ConstantKind::Unevaluated` and `ty::ConstKind::Unevaluated` have been
consumed and replaced with thier evaluated representations.

The design space admits several candidate approaches:

1. **Skip "`evaluate_const`" on the monomorphisation path.** Do not run
   constant evaluation as part of producing the MIR that downstream tools
   receive; tools that need evaluation call "`evaluate_const`" themselves.
   This is reasonable for any constant whose value is `ValTree`-shaped
   (pointer-free data: integers, bools, chars, etc.), where the evaluated form
   carries no information beyond the structured value itself. It is *not*
   (currently) reasonable for pointer-bearing constants. The cross-item
   reachability the collector relies on (function pointers in const tables,
   vtables in `&dyn` consts, etc.) lives in the provenance field of the
   evaluated `Allocation`. Skipping evaluation there silently drops those edges
   from the discovered item set.
2. **Evaluate, then lift back to a high-level form as a compiler query.**
   Continue evaluating constants, but expose the result through a query that
   lifts an evaluated form into a structured tree shaped like an extended
   `ValTree`. This tree form would encode `GlobalAlloc::Function`, `Static`,
   and `VTable` references as named edges rather than as opaque provenance
   bytes. `mir-json` already does this in
   [`try_render_opty`](https://github.com/GaloisInc/mir-json/blob/2fc80d73eaede1e394a4ec6970fb5ca9e33efd73/src/analyz/ty_json.rs#L1240-L1464);
   upstreaming a query of that shape gives every downstream tool the
   same lifting without each having to re-derive it, preserves
   cross-item reachability, and abandons commitment to a particular byte
   layout.
3. **Process both pre- and post-evaluation MIR and merge.** Produce both
   shapes, keep the monomorphised, optimised body, and replace the
   evaluated constant leaves with their unevaluated counterparts where
   the type admits it.
4. **Something else.** An approach not yet enumerated, for example an
   opt-in callback positioned between optimisation and constant lowering.

The constraint these approaches must respect is that on the
monomorphisation path, evaluation is what surfaces cross-item
reachability via allocation provenance. Approach 1 therefore cannot
stand alone for any program that uses pointer-bearing constants. To
make it cover those cases, the constant types themselves would have to grow
a high level representation for refernces (for example, extending `ValTree` to
carry `Function`, `Static`, and `VTable` references as named branches), at
which point it converges with Approach 2's lift. Approaches 2 and 3 execute
constant evaluation fully and so retain the allocation information; their
feasibility turns on landing the lifting or the merge without regressing codegen
quality and performance.

Each candidate may also turn out to be infeasible for reasons not
visible from outside the compiler (evaluation-order dependencies inside
later passes, query-graph cycles, performance regressions); the
engagement starts with the candidate the workgroup considers most
promising and falls back to the next as evidence accumulates.

**Constant representations across the bridge.** The public API collapses
several distinct internal shapes (`ValTree`, `ConstValue`) into a single
byte-level `Allocation`. That collapse loses placeless type-identity
semantics (the FIXME at `compiler/rustc_public/src/ty.rs:149` reads simply
"These should be a valtree") and makes the `TyConst -> MirConst` lowering
lossy, since padding and allocation identifiers survive the bridge even
though they carry no const-identity information. The diagram below shows the
type surface on each side. Variants marked `(no link)` have no constructor
in the bridge: for most of these the internal converter hits
`unimplemented!()` or `unreachable!()`; `ConstantKind::Param` on the public
side is declared but never produced. The `ZSTValue` special case on the
public side is a one-type-class preservation of placelessness; extending it
to general `ValTree`-shaped types is a scaling of an existing pattern, not a
new direction.

```text
  INTERNAL  (rustc)                         PUBLIC  (rustc_public)
  =================                         ======================

  ty::Const / ty::ConstKind                 TyConst / TyConstKind
  +----------------------+                  +------------------------------+
  | Param                | -- mirror ---->  | Param                        |
  | Unevaluated(Def,..)  | -- mirror ---->  | Unevaluated(ConstDef,Args)   |
  | Value(ValTree)       | -- collapse -->  | Value(Ty, Allocation)        |
  |   ValTreeKind:       |  | ValTree to    |                              |
  |     Leaf(ScalarInt)  |  | Allocation    |                              |
  |     Branch([...])    |  +------------>  | ZSTValue(Ty)                 |
  | Error etc. (no link) |    or ZSTValue   |                              |
  | Bound (no link)      |                  | Bound (no link)              |
  +----------+-----------+                  +--------------+---------------+
             |                                             |
             | wrapped as                                  | wrapped as
             | mir::Const::Ty                              | ConstantKind::Ty
             v                                             v
  mir::Const                                MirConst / ConstantKind
  +----------------------+                  +-------------------------------+
  | Ty(Ty, ty::Const)    | -- mirror ---->  | Ty(TyConst)                   |
  | Unevaluated(.., Ty)  | -- mirror ---->  | Unevaluated(UnevaluatedConst) |
  | Val(ConstValue, Ty)  | -- collapse -->  | Allocated(Allocation)         |
  |   ConstValue:        |  | ConstValue to |                               |
  |     Scalar           |  | Allocation    |                               |
  |     ZeroSized        |  +------------>  | ZeroSized                     |
  |     Slice{..}        |    or ZeroSized  |                               |
  |     Indirect{..}     |                  | Param(ParamConst) (no link)   |
  +----------------------+                  +-------------------------------+
```

### Assumptions

- Changes land upstream in `rust-lang/rust`. Patches carried only in a fork do
  not satisfy the challenge.
- Performance and correctness of the existing codegen path are preserved.
  Approaches that produce slower or incorrect code, even as an opt-in, are out
  of scope unless the performance cost is demonstrably small and the opt-in is
  off by default.
- The goal is high-level constant visibility for downstream tools, whether
  surfaced as `UnevaluatedConst` or as an equivalent structured
  representation. Exposing that visibility through `rustc_public` is in
  scope only to the extent needed to demonstrate the feature; broader
  `rustc_public` stabilisation work belongs to a separate challenge.

### Success Criteria

This is an infrastructure challenge. The engagement targets a landed
implementation upstream; the criteria below describe that target and the
analysis that accompanies it.

**A. Implementation landed upstream.** An opt-in change is merged into
`rust-lang/rust` that makes a high-level constant form (`UnevaluatedConst`,
or an equivalent structured representation) visible to downstream tools
consuming monomorphisation-path MIR. The engagement begins with the
candidate the workgroup considers most promising and pivots between
candidates as feasibility evidence and upstream review dictate.

**B. Engineering analysis.** The implementation is delivered alongside a
written analysis of the candidate approaches the engagement explored: the
codegen invariants each preserves or breaks, performance cost or benefit
(measured where measurable), and any compiler-internal assumptions or
upstream feedback that constrained the choice. The analysis grounds the
candidate that landed and records the reasoning behind those that did
not, so future contributors revisiting the design space have a starting
point. In the tail case where no candidate clears upstream review during
the engagement, the analysis substitutes for the merged change as the
deliverable.

## Correctness Criteria

The Rust reference's list of undefined behaviour does not apply to this
challenge; the deliverable is compiler infrastructure rather than a run-time
construct. Correctness properties instead:

- Any MIR construct reachable through existing APIs before the change is
  reachable after the change, with the same semantics, unless the change is
  opt-in and the caller has opted in.
- High-level constant visibility, where achieved, is additive: a tool that
  does not engage with constants at all observes no difference in the MIR
  it consumes.
- Any non-default mode that surfaces a high-level constant form preserves
  the cross-item reachability the existing eval path discovers via
  allocation provenance. Where reachability is recovered through a
  different mechanism, gaps relative to the eval-path baseline are
  documented.
- The default behaviour of the compiler, including optimisation quality and
  codegen output, is unchanged outside of the specific opt-in path introduced
  by the change.
- Solutions are landed as merged pull requests against `rust-lang/rust`.

Note: All solutions to verification challenges need to satisfy the criteria
established in the [challenge book](../general-rules.md) in addition to the
ones listed above.
