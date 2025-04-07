## Tool Name
**KMIR**

## Description

[KMIR](https://github.com/runtimeverification/mir-semantics) is a formal
verification tool for Rust that defines the operational semantics of Rust’s
Middle Intermediate Representation (MIR) in K (through Stable MIR). By
leveraging the [K framework](https://kframework.org/), KMIR provides a parser,
interpreter, and symbolic execution engine for MIR programs. This tool enables
direct execution of concrete and symbolic input, with step-by-step inspection of
the internal state of the MIR program's execution, serving as a foundational
step toward full formal verification of Rust programs. Through the dependency
[Stable MIR JSON](https://github.com/runtimeverification/stable-mir-json/), KMIR
allows developers to extract serialized Stable MIR from Rust’s compilation
process, execute it, and eventually prove critical properties of their
code.

This diagram describes the extraction and verification workflow for KMIR:

![kmir_env_diagram_march_2025](https://github.com/user-attachments/assets/bf426c8d-f241-4ad6-8cb2-86ca06d8d15b)


To understand how KMIR works the K Framework must first be understood, and the
best description can be found at [kframework.org](https://kframework.org/):

> K is a rewrite-based executable semantic framework in which programming
> languages, type systems and formal analysis tools can be defined using
> configurations and rules. Configurations organize the state in units called
> cells, which are labeled and can be nested. K rewrite rules make it explicit
> which parts of the term are read-only, write-only, read-write, or unused. This
> makes K suitable for defining truly concurrent languages even in the presence
> of sharing. Computations are represented as syntactic extensions of the
> original language abstract syntax, using a nested list structure which
> sequentializes computational tasks, such as program fragments. Computations
> are like any other terms in a rewriting environment: they can be matched,
> moved from one place to another, modified, or deleted. This makes K suitable
> for defining control-intensive features such as abrupt termination,
> exceptions, or call/cc.

K (and thus KMIR) verifies program correctness using the
symbolic execution engine and verifier derived from the
K encoding of the languages operational semantics, in this case the Stable MIR semantics.
The K semantics framework is based on
reachability logic, which is a theory describing transition systems in [matching
logic](http://www.matching-logic.org/). Transition rules of the semantics are
rewriting steps that match patterns and transform the current continuation and
state accordingly. An all-path-reachability proof in this system verifies that a
particular _target_ end state is _always_ reachable from a given starting
state. The rewrite rules branch on symbolic inputs covering the possible
transitions, creating a model that is provably complete, and requiring
unification on every leaf state. A one-path-reachability proof is similar to the
above, but the proof requirement is that at least one leaf state unifies with
the target state. One feature of such a system is that the requirement for an
SMT is minimized to determining completeness on path conditions when branching
would occur.

KMIR also prioritizes UI with interactive proof exploration available
out-of-the-box through the terminal KCFG (K Control Flow Graph) viewer, allowing
users to inspect intermediate states of the proof to get feedback on the
successful path conditions and failing at unifying with the target state. An
example of a KMIR proof being analyzed using the KCFG viewer can be seen below:

<img width="1231" alt="image" src="https://github.com/user-attachments/assets/a9f86957-7ea5-4bf6-bee2-202487aacc9b" />


## Tool Information

* [x] Does the tool perform Rust verification?
  *Yes – It performs verification at the MIR level, an intermediate
  representation of Rust programs in the Rust compiler `rustc`.*
* [x] Does the tool deal with *unsafe* Rust code?
  *Yes – By operating on MIR, KMIR can analyze both safe and unsafe Rust code.*
* [x] Does the tool run independently in CI?
  *Yes – KMIR can be integrated into CI workflows via our package manager and
  Nix-based build system or through a docker image provided.*
* [x] Is the tool open source?
  *Yes – KMIR is [open source and available on GitHub](https://github.com/runtimeverification/mir-semantics).*
* [x] Is the tool under development?
  *Yes – KMIR is actively under development, with ongoing improvements to MIR
  syntax coverage and verification capabilities.*
* [x] Will you or your team be able to provide support for the tool?
  *Yes – The Runtime Verification team is committed to supporting KMIR and will
  provide ongoing maintenance and community support.*

## Licenses
KMIR is released under an OSI-approved open source license. It is distributed
under the BSD-3 clause license, which is compatible with the Rust standard
library licenses. Please refer to the [KMIR GitHub
repository](https://github.com/runtimeverification/mir-semantics?tab=BSD-3-Clause-1-ov-file)
for full license details.

## Comparison to Other Approved Tools
The other tools approved at the time of writing are Kani, Verifast, and
Goto-transcoder (ESBMC).

- **Verification Backend:** KMIR primarily differs from all of these tools by
  utilizing a unique verification backend through the K framework and
  reachability logic (as explained in the description above). KMIR has little
  dependence on an SAT solver or SMT solver. Kani's CBMC backend and
  Goto-transcoder (ESBMC) encode the verification problem into an SAT / SMT
  verification condition to be discharged by the appropriate solver. Kani
  recently added a Lean backend through Aeneas, however Lean does not support
  matching or reachability logic currently. Verifast performs symbollic
  execution of the verification target like KMIR, however reasoning is performed
  by annotating functions with design-by-contract components in separation
  logic.
- **Verification Input:** KMIR takes input from Stable MIR JSON, an effort to
  serialize the internal MIR in a portable way that can be reusable by other
  projects.
- **K Ecosystem:** Since all tools in the K ecosystem share a common foundation
  of K, all projects benefit from development done by other K projects. This
  means that performance and user experience are projected to improve due to the
  continued development of other semantics.

## Steps to Use the Tool

The [KMIR docker
image](https://github.com/runtimeverification/mir-semantics/blob/c221c81d73a56c48692a087a2ced29917de99246/Dockerfile.kmir)
is currently the best option for casual users of KMIR. It contains an
installation of K Framework, the tool `kmir`, and the `stable-mir-json`
extraction tool, which is a custom version of `rustc` which extracts Stable MIR
as JSON or as graphviz' *.dot when compiling a crate.
The image is [available on Docker Hub](https://hub.docker.com/r/runtimeverificationinc/kmir/tags).

Alternatively, the tools for `kmir` can be built from source as [described in
the `mir-semantics` repository's
`README.md`](https://github.com/runtimeverification/mir-semantics). This
requires an installation of `K Framework`, best done [using the `kup`
tool](https://github.com/runtimeverification/kup/README.md), and includes a
git submodule dependency on `stable-mir-json`.

The `stable-mir-json` tool is a custom version of `rustc` which, while compiling
Rust code, writes the code's Stable MIR, represented in a JSON format, to a
file.  Just like `rustc` itself, `stable-mir-json` extracts MIR of a single
crate and must be invoked via `cargo` for multi-crate programs. Besides the JSON
extraction, `stable-mir-json` can also write a graphviz `dot` file representing
the Stable MIR structure of all functions and their call graph within the crate.

The `kmir` tool provides commands to work with the Stable MIR representation of
Rust programs that `stable-mir-json` extracts.

* Run Stable MIR code extracted from Rust programs (`kmir run my-program.smir.json`);
* Prove a property about a Rust program, which is given as a K "claim" and
  proven using an all-path reachability proof in K (`kmir prove run my-program-spec.k`);
* Inspect the control flow graph of a program's proof constructed by the `kmir
  prove run` command (`kmir prove view Module.Proof-Identifier`).

Examples of proofs using KMIR, and how to derive them from a Rust program
manually, are [provided in the `kmir-proofs`
directory](https://github.com/model-checking/verify-rust-std/tree/main/kmir-proofs).

The `kmir` tool is under active development at the time of writing.
Constructing a K claim from a given Rust program is currently a manual process
but will be automated in a future version. Likewise, at the time of writing, the
`kmir` tool does not automatically extract Stable MIR from a Rust program, the
Stable MIR must be extracted by invoking `stable-mir-json` manually.


## Background Reading

- **[Matching Logic](http://www.matching-logic.org/)**
  Matching Logic is a foundational logic underpinning the K framework, providing
  a unified approach to specifying, verifying, and reasoning about programming
  languages and their properties in a correct-by-construction manner.

- **[K Framework](https://kframework.org/)**
  The K Framework is a rewrite-based executable semantic framework designed for
  defining programming languages, type systems, and formal analysis tools. It
  automatically generates language analysis tools directly from their formal
  semantics.
