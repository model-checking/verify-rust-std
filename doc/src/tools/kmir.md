## Tool Name
**KMIR**

## Description

[KMIR](https://github.com/runtimeverification/mir-semantics) is a formal
verification tool for Rust that defines the operational semantics of Rust’s
Middle Intermediate Representation (MIR) in K (through Public / Stable MIR). By
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
which terminates the execution abnormally. KMIR is designed to provide sound 
assurances about undefined behavior (UB) in Rust’s MIR. Rather than statically 
over‑approximating or flagging UB at every unsafe block, KMIR models the full 
MIR semantics, including UB transitions, using a **refusal-to-execute** strategy.
This means that if symbolic execution reaches a MIR instruction and cannot prove 
that executing it would not result in UB (e.g., an out-of-bounds pointer dereference 
or an unchecked arithmetic overflow), execution halts in a `UB DETECTED` state. 
This state cannot be unified with a valid target state in the proof, so the proof 
fails. KMIR systematically explores all feasible paths under the user-supplied 
preconditions. Only when **every** path terminates without hitting UB *and* 
satisfies the target property does KMIR declare the program UB-free (and correct 
for the property). This ensures that any “no UB” claim holds under the sole assumption
that KMIR’s implementation is correct. 

Programs modelled in K Framework can be executed _symbolically_, i.e., operating 
on abstract input which is not fully specified but characterized by _path conditions_ 
(e.g., that an integer variable holds an unknown but non-negative value).

In practice, KMIR proof harnesses work similarly to property tests. Arguments
to the entry function are automatically instantiated as fully symbolic values,
so the proof covers all possible inputs. Post-conditions are expressed using
`assert!` statements. Pre-conditions can be added using `std::intrinsics::assume`,
which constrains the symbolic path condition to restrict the inputs under
consideration. This design allows users to write verification harnesses in
plain Rust without needing to learn write K (excepting advanced features).

```rust
#![feature(core_intrinsics)]
use std::intrinsics::assume;

fn abs_safe(x: i32) {
    unsafe { assume(x != i32::MIN); }
    let result = x.abs();
    assert!(result >= 0);
}
```

When KMIR is directed to prove `abs_safe`, `x` is instantiated symbolically.
The `assume` adds `x != i32::MIN` as a path constraint, and KMIR proves the
assertion holds for all values satisfying that constraint.

K (and thus KMIR) verifies program correctness by performing an
_all-path-reachability proof_ using the symbolic execution engine and verifier
derived from the K encoding of the Public MIR operational semantics.
The K semantics framework is based on reachability logic, which is a theory
describing transition systems in [matching logic](http://www.matching-logic.org/).
An all-path-reachability proof in this system verifies that a particular
_target_ end state is _always_ reached from a given starting state.
The rewrite rules branch on symbolic inputs covering the possible transitions,
creating a model that is provably complete. For all-path reachability, every
leaf state is required to unify with the target state.
A one-path-reachability proof is similar to the above, but the proof requirement
is that _at least one_ leaf state unifies with the target state.

When performing a proof of a program that involves recursion or a loop construct,
one of several possible techniques can be used:

1) K (and thus KMIR) are capable of unbounded verification via allowing the
   user to write loop invariants. However, these loop invariants would then
   need to be written in K's native language.
2) As potential future work, it would be possible to implement an annotation
   language to provide the required context for loop invariant directly in
   source code (as done in the past using natspec for Solidity code).
3) In general, K also supports bounded loop unrolling, by way of identifying
   loop heads and counting how many times the same loop head has been observed.
   This technique is managed by the all-path reachability prover library for
   K and works out of the box with suitable arguments, without requiring any
   special support from the back-end.

By default, KMIR will attempt to exhaustively unroll a loop. Loop invariants
have been applied to the verification of the Solana P-Token / SPL-Token
Equivalence (see Case Study 2.) to summarise the behaviour of iterator [
[P-Token Loop](https://github.com/runtimeverification/solana-token/blob/proofs/specs/shared/inner_test_validate_owner.rs),
[P-Token Lemma](https://github.com/runtimeverification/mir-semantics/blob/mk/lemmas-inner_test_validate_owner/kmir/src/kmir/kdist/mir-semantics/symbolic/inner_test_validate_owner.md)
].

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
  matching or reachability logic currently. Verifast performs symbolic
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

### Installation

3 methods to install KMIR are listed. Recommended is the Nix installation via kup.

<figure>
<img width="931" height="627" alt="Demo installing KMIR via kup" src="https://github.com/user-attachments/assets/e31c16ad-7d78-4b62-93a6-8c7e61948d50" />
<figcaption>Installing KMIR via kup (cached install shown; first install takes longer)</figcaption>
</figure>

#### Nix (via kup)

The recommended installation method uses
[`kup`](https://github.com/runtimeverification/kup), the K Framework package
manager. This installs K Framework, `kmir`, and `stable-mir-json` on your
system via [Nix](https://nixos.org/).

The following script installs Nix (if not already present) and `kup`:

```bash
bash <(curl https://kframework.org/install)
```

Then install `kmir`:

```bash
kup install kmir
```

`kmir` is now installed on the path:
```bash
kmir --help
```

#### Docker

KMIR is available as a Docker image on
[Docker Hub](https://hub.docker.com/r/runtimeverificationinc/kmir/tags).
The image contains K Framework, the `kmir` tool, and `stable-mir-json`.

The following commands may require `sudo` permissions.

```bash
docker run --rm \
  runtimeverificationinc/kmir:ubuntu-jammy-0.4.206 \
  kmir --help
```

To run a proof using Docker, mount your working directory into the container:

```bash
docker run --rm \
  -u $(id -u):$(id -g) \
  -v /path/to/your/files:/workspace \
  runtimeverificationinc/kmir:<LATEST-VERSION-FROM-DOCKERHUB> \
  kmir prove /workspace/program.rs --proof-dir /workspace/proofs --verbose
```

The `-u` flag ensures files created inside the container have the correct
ownership on the host. The `-v` flag mounts a host directory so that input
files are accessible and proof output persists after the container exits.

#### From source

The tools can be built from source as described in the
[`mir-semantics` repository](https://github.com/runtimeverification/mir-semantics).
This requires [Python](https://www.python.org/) >= 3.10,
[`uv`](https://docs.astral.sh/uv/),
[K Framework](https://github.com/runtimeverification/k), and Rust via
[`rustup`](https://rustup.rs/).

```bash
git clone --recurse-submodules https://github.com/runtimeverification/mir-semantics.git
cd mir-semantics
make build
make stable-mir-json
```

`kmir` can be invoked via `uv` (from repo root):

```bash
uv --project kmir/ -- kmir --help
```

### Usage (Verification)

The `kmir` tool works with Stable MIR extracted from Rust programs via
[`stable-mir-json`](https://github.com/runtimeverification/stable-mir-json),
a custom driver for `rustc` that serializes a crate's Stable MIR to JSON.

| Command             | Purpose                                                                      |
| ---                 | ---                                                                          |
| `kmir prove`        | Prove a Rust program (*.rs) terminates without panics or undefined behaviour |
| `kmir show`         | Inspect a static proof graph (nodes, statistics, rule applications)          |
| `kmir view`         | Interactive proof viewer                                                     |
| `kmir prune`        | Remove a node and its subtree from a proof                                   |
| `kmir section-edge` | Split a proof edge into finer sections                                       |
| `kmir link`         | Link multiple SMIR JSON files into one (for multi-crate projects)            |

To prove a program:

```bash
kmir prove <FILE>.rs --proof-dir <DIR> [--start-symbol <SYMBOL>] --verbose
```

Where `<FILE>` is the Rust source file to verify, `<DIR>` is the directory
where proof artifacts are stored, and `<SYMBOL>` is the entry function to
verify (defaults to `main` if omitted).

This invokes `stable-mir-json` internally, then performs an all-path
reachability proof that the program reaches normal termination under all
possible inputs. Any statements that would panic or cause undefined behaviour
terminate execution, so successful completion proves their absence.
Pre-conditions and post-conditions can be modelled using conditional execution
and assertions.

To inspect proof results, the proof ID is `<FILE>.<SYMBOL>`, e.g., proving
`program.rs` produces proof ID `program.main`:

```bash
kmir show <FILE>.<SYMBOL> --proof-dir <DIR> --leaves --statistics
kmir view <FILE>.<SYMBOL> --proof-dir <DIR>
```

<figure>
<img width="1276" height="560" alt="Passing KMIR proof with show" src="https://github.com/user-attachments/assets/936b42fe-9bdc-480d-962f-390576193634" />
<figcaption><code>kmir prove</code> on passing proof with <code>kmir show</code> (time is shortened, real time is in output)</figcaption>
</figure>

<figure>
<img width="1276" height="560" alt="Failing KMIR proof with view" src="https://github.com/user-attachments/assets/2638696b-6249-4b21-93a9-123edca5b66a" />
<figcaption><code>kmir prove</code> on failing proof with <code>kmir view</code> (time is shortened, real time is in output)</figcaption>
</figure>

#### Useful Prove Flags

Proof state is automatically written to disk at every branch point and leaf
node. Additional state can be emitted with flags to `kmir prove`.

It is recommended to use `--terminate-on-thunk`, which stops the proof when
an unevaluated symbolic value (thunk) is encountered. This does not affect
soundness, but gives feedback of the proof failure from the earliest point
a K rule could not apply.

If a `--proof-dir <DIR>` is supplied, proof progress is written to disk.
If a proof is cancelled before completion, calling the same command with
the same `--proof-dir <DIR>` will read the state from disk and continue
the proof from there. Otherwise the `--reload` flag will start the proof
overwriting the previous entry.

Furthermore, performance for a proof can be increased with parallelism.
We recommend `--max-workers 4` which empirical evidence suggests is an
optimal number of workers for a proof.

| Flag                         | Effect                                                                      |
| ---                          | ---                                                                         |
| `--reload`                   | Discard existing proof progress and restart from scratch                    |
| `--terminate-on-thunk`       | Stop proof at unevaluated thunks (recommended)                              |
| `--break-on-thunk`           | Emit state at thunk evaluation                                              |
| `--break-on-calls`           | Emit state at all function and intrinsic calls                              |
| `--break-on-function-calls`  | Emit state at function calls only                                           |
| `--break-on-intrinsic-calls` | Emit state at intrinsic calls only                                          |
| `--break-on-function <STR>`  | Emit state when calling a function whose name contains `<STR>` (repeatable) |
| `--max-depth <N>`            | Emit state every <N> steps                                                  |
| `--max-iterations <N>`       | Stop proof after <N> iterations (states are emitted)                        |
| `--fail-fast`                | Stop proof at the earliest failure (leaves other branches pending)          |
| `--max-workers <N>` (best 4) | Max workers for parallel execution                                          |


## KMIR Case Studies

### Case Study 1: Verify Std Rust Challenge 11

[Challenge 11](https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html)
requires verifying the safety of public unsafe methods for numeric primitives
in `core::num`. KMIR successfully verified the correctness of all scoped integer
operations. Float operations remain future work. For details, please visit the
[proof suite](https://github.com/runtimeverification/mir-semantics/tree/master/kmir/src/tests/integration/data/verify-rust-std/0011-floats-ints).

For each unsafe method, two harness files are written:

**PASSING** (
[unchecked_add.rs](https://github.com/runtimeverification/mir-semantics/blob/master/kmir/src/tests/integration/data/verify-rust-std/0011-floats-ints/unchecked_add.rs)
): calls the unsafe method only when its safety precondition holds. KMIR proves
all paths terminate without UB:

```rust
fn unchecked_add_u128(a: u128, b: u128) {
    if let Some(expected) = a.checked_add(b) {
        let result = unsafe { a.unchecked_add(b) };
        assert!(result == expected);
    }
}
```

**FAILING** (
[unchecked_add-fail.rs](https://github.com/runtimeverification/mir-semantics/blob/master/kmir/src/tests/integration/data/verify-rust-std/0011-floats-ints/unchecked_add-fail.rs)
): calls the unsafe method on arbitrary symbolic inputs without a precondition.
KMIR detects UB on overflow paths and the proof fails:

```rust
fn unchecked_add_u128(a: u128, b: u128) {
    let result = unsafe { a.unchecked_add(b) };
    assert!(result == a.wrapping_add(b)); // UB
}
```

Each failing test has an expected failure state recorded in the
[show](https://github.com/runtimeverification/mir-semantics/tree/master/kmir/src/tests/integration/data/verify-rust-std/0011-floats-ints/show)
directory.

The full set of verified methods covers all integer types (i8-i128, u8-u128):

| Method             | Types               | Status                  |
| ---                | ---                 | ---                     |
| `unchecked_add`    | all integer types   | verified                |
| `unchecked_sub`    | all integer types   | verified                |
| `unchecked_mul`    | all integer types   | verified                |
| `unchecked_shl`    | all integer types   | verified                |
| `unchecked_shr`    | all integer types   | verified                |
| `unchecked_neg`    | signed types only   | verified                |
| `wrapping_shl`     | all integer types   | verified                |
| `wrapping_shr`     | all integer types   | verified                |
| `widening_mul`     | u8, u16, u32, u64   | verified                |
| `carrying_mul`     | u8, u16, u32, u64   | verified                |
| `to_int_unchecked` | f16, f32, f64, f128 | pending (float support) |

### Case Study 2: Solana P-Token / SPL-Token Equivalence Proofs

KMIR has been used to formally verify the equivalence of the
[Solana P-Token](https://github.com/runtimeverification/solana-token/tree/proofs/p-token)
(a compute-optimized rewrite using
[Pinocchio](https://github.com/anza-xyz/pinocchio)) against the original
[Solana SPL-Token](https://github.com/runtimeverification/solana-token/tree/proofs/program)
program.

The verification proves that the P-Token program simulates the SPL-Token
program: for each SPL-Token state and instruction (a request to perform an
operation such as Transfer or Burn), there is an equivalent P-Token state
and instruction that produces the same result. Both programs must agree on
state transitions and error behaviour.

Each instruction is verified twice (once for each implementation) against a
shared specification harness that captures the initial account state, invokes
the instruction processor with symbolic input, and verifies the same
postcondition holds after execution. 41 proofs are required to demonstrate
equivalence.

For more details, please see:
- [Proof Status](https://github.com/runtimeverification/solana-token/issues/24)
- [Multisig Proof Status](https://github.com/runtimeverification/solana-token/issues/97)
- [Shared Specifications](https://github.com/runtimeverification/solana-token/tree/proofs/specs)
- [SPL-Token Implementation](https://github.com/runtimeverification/solana-token/blob/proofs/program/src/processor.rs)
- [P-Token Implementation](https://github.com/runtimeverification/solana-token/tree/proofs/p-token/src/processor)

A detailed report covering the Solana programming model, the formal
equivalence methodology, and per-instruction verification conditions is
available in the
[equivalence proofs report](https://github.com/runtimeverification/solana-token/blob/proofs/RV_EQUIVALENCE_PROOFS_REPORT.md).

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
