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


The K Framework ([kframework.org](https://kframework.org/) is the basis of how
KMIR operates to guarantee properties of Rust programs. K is a rewrite-based
semantic framework based on [matching logic](http://www.matching-logic.org/) in
which programming languages, their operational semantics and type systems, and
formal analysis tools can be defined through syntax, configurations, and rules.
The _syntax_ definitions in KMIR model the AST of Stable MIR (e.g., the
statements and terminator of a basic block in a function body) and configuration
data that exists at runtime (e.g., the stack frame structure of a function
call).
The _configuration_ of a KMIR program organizes the state of an executed program in
nested configuration units called cells (e.g., a stack frame is part of a stack
stored in the configuration).
_K Framework transition rules_ of the KMIR semantics are rewriting steps that
match patterns and transform the current continuation and state accordingly.
They describe how program configuration and its contained data changes when
particular program statements or terminators are executed (e.g., a returning
function modifies the call stack and writes a return value into the caller's
local variables).

Using the K semantics of Stable MIR, the KMIR execution of an entire Rust
program represented as Stable MIR breaks down to a series of configuration
rewrites that compute data held in local variables, and the program may either
terminate normally or reach an exception or construct with undefined behaviour,
which terminates the execution abnormally. Programs modelled in K Framework can
be executed _symbolically_, i.e., operating on abstract input which is not fully
specified but characterised by _path conditions_ (e.g., that an integer variable
holds an unknown but non-negative value).

K (and thus KMIR) verifies program correctness by performing an
_all-path-reachability proof_ using the symbolic execution engine and verifier
derived from the K encoding of the Stable MIR operational semantics.
The K semantics framework is based on reachability logic, which is a theory
describing transition systems in [matching logic](http://www.matching-logic.org/).
An all-path-reachability proof in this system verifies that a particular
_target_ end state is _always_ reached from a given starting state.
The rewrite rules branch on symbolic inputs covering the possible transitions,
creating a model that is provably complete. For all-path reachability, every
leaf state is required to unify with the target state.
A one-path-reachability proof is similar to the above, but the proof requirement
is that _at least one_ leaf state unifies with the target state.

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
