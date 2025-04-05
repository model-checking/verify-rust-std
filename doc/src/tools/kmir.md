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
code. Soon, KMIR will be available via our package manager,
[kup](https://github.com/runtimeverification/kup), which will make it easily
installable and integrable into various workflows.

This diagram describes the extraction and verification workflow for KMIR:

![kmir_env_diagram_march_2025](https://github.com/user-attachments/assets/bf426c8d-f241-4ad6-8cb2-86ca06d8d15b)


Particular to this challenge, KMIR verifies program correctness using the
correct-by-construction symbolic execution engine and verifier derived from the
K encoding of the Stable MIR semantics. The K semantics framework is based on
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
  *Yes – It performs verification at the MIR level, which is a critical
  intermediate representation of Rust programs.*
* [x] Does the tool deal with *unsafe* Rust code?
  *Yes – By operating on MIR, KMIR can analyze both safe and unsafe Rust code.*
* [x] Does the tool run independently in CI?
  *Yes – KMIR can be integrated into CI workflows via our package manager and
  Nix-based build system.*
* [x] Is the tool open source?
  *Yes – KMIR is open source and available on GitHub.*
* [x] Is the tool under development?
  *Yes – KMIR is actively under development, with ongoing improvements to MIR
  syntax coverage and verification capabilities.*
* [x] Will you or your team be able to provide support for the tool?
  *Yes – The Runtime Verification team is committed to supporting KMIR and will
  provide ongoing maintenance and community support.*

## Comparison to Other Approved Tools
The other tools approved at the time of writing are Kani, Verifast, and
Goto-transcoder (ESBMC).

- **Verification Backend:** KMIR primarily differs from all of these tools by
  utilizing a unique verification backend through the K framework and
  reachability logic (as explained in the description above). KMIR has little
  dependence on an SAT solver or SMT solver. Kani's CBMC backend and
  Goto-transcode (ESBMC) encode the verification problem into an SAT / SMT
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

## Licenses
KMIR is released under an OSI-approved open source license. It is distributed
under the BSD-3 clause license, which is compatible with the Rust standard
library licenses. Please refer to the [KMIR GitHub
repository](https://github.com/runtimeverification/mir-semantics?tab=BSD-3-Clause-1-ov-file)
for full license details.

## Steps to Use the Tool

At RV, we generally strives to use
[kup](https://github.com/runtimeverification/kup) , a `nix`-based software
installer, to distribute our software.  This is future work, at the moment
`kmir` requires a local build from source using the `K Framework` (installed
with `kup`).

The future workflow we imagine is to
1. Download [kup](https://github.com/runtimeverification/kup) and install
2. Install KMIR `kup install kmir`
3. Compile the desired verification target with `kmir build module.rs`.
   The `module.rs` should contain functions that act as property tests and are
   run with symbolic inputs.
4. Verify the target with `kmir prove module.rs --target target_function`.
   This executes `target_function` with symbolic arguments. The test is expected
   to contain assertions about computed values.
5. Inspect KCFG of proof with `kmir view module::target_function`

At the time of writing, step 3 requires manual work to set up a _claim_ in the K
language. We will automate this process in the frontend code to prevent the
user from having to write K code.

**To see the specifications and run proofs using KMIR, including a subsection of
the proofs required in the [Safety of Methods for Numeric Primitive
Types](https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html#challenge-11-safety-of-methods-for-numeric-primitive-types)
challenges, check this [instructional
document](https://github.com/runtimeverification/mir-semantics/blob/sample-challenge-11-proofs/rust-verification-proofs/README.md)
in our tool's repository.**

## Artifacts & Audit Mechanisms

- **[Matching Logic](http://www.matching-logic.org/)**
  Matching Logic is a foundational logic underpinning the K framework, providing
  a unified approach to specifying, verifying, and reasoning about programming
  languages and their properties in a correct-by-construction manner.

- **[K Framework](https://kframework.org/)**
  The K Framework is a rewrite-based executable semantic framework designed for
  defining programming languages, type systems, and formal analysis tools. It
  automatically generates language analysis tools directly from their formal
  semantics.

- **[Kontrol](https://kontrol.runtimeverification.com)**
  Kontrol is a formal verification tool built on K's semantics, enabling
  symbolic execution and proof construction for Ethereum smart contracts.

- **[KEVM Semantics](https://github.com/kframework/evm-semantics)**
  KEVM provides a practical, executable formal specification of the Ethereum
  Virtual Machine using the K Framework, demonstrating K’s real-world
  application for verifying blockchain virtual machines.

## Versioning
KMIR and Stable MIR JSON are both version controlled using git and hosted by
Github. Semantic version numbers are used as soon as releases are made.
Stable MIR JSON depends on a nightly Rust compiler of a particular version
(which is regularly updated, currently `nightly-2024-11-29`).
Dependencies for K and MIR JSON are tracked as pinned versions in the 'deps'
folder and updated as changes are published upstream and tested against
mir-semantics.

## CI
At Runtime Verification, we are regularly releasing and updating our tools using
GitHub Actions and publishing our updated tool releases to standardized
locations such as [Dockerhub](https://hub.docker.com/u/runtimeverificationinc) /
ghcr.io / [cachix](https://app.cachix.org/cache/k-framework-binary). Any changes
upstream to [K](https://github.com/runtimeverification/k) or
[stable-mir-json](https://github.com/runtimeverification/stable-mir-json/) are
immediately propagated to mir-semantics via workflow triggers to ensure the
latest release of the tool is getting the latest improvements from K.

For integrating KMIR into your project's CI pipeline, we recommend using our
pre-built packages. You can choose from several installation methods depending
on your needs:

Our current Registries / Caches are:

1. [Binary Cachix cache used by Kup](https://app.cachix.org/cache/k-framework-binary)
2. Source code on GitHub: [mir-semantics]](https://github.com/runtimeverification/mir-semantics) and [stable-mir-json](https://github.com/runtimeverification/stable-mir-json)
3. [Container image on Dockerhub](https://hub.docker.com/u/runtimeverificationinc)
