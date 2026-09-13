# Formal Rust Code Verification Using KMIR

This directory contains a collection of programs and specifications to
illustrate how KMIR can validate the properties of Rust programs and
standard library functions.

## Setup

KMIR verification can either be run from [docker images provided under
`runtimeverificationinc/kmir`](https://hub.docker.com/r/runtimeverificationinc/kmir),
or using a local installation of
[`mir-semantics`](https://github.com/runtimeverification/mir-semantics/)
with its dependency
[`stable-mir-json`](https://github.com/runtimeverification/stable-mir-json).
Installation is described in more detail in the
[KMIR tool documentation](../doc/src/tools/kmir.md#installation).

The following description assumes that the `kmir` tool and `stable-mir-json`
are installed and available on the path.

## Program Property Proofs in KMIR

The `kmir prove` command takes a Rust source file and proves that the given
entry function runs to completion without a panic or undefined behaviour.
Arguments of the entry function are instantiated as symbolic values, so a
proof covers all possible inputs.

Desired post-conditions of the program, such as properties of the computed
result, are expressed as `assert!` statements. Pre-conditions are modelled as
conditional execution: the operation under test is placed inside an `if` (or
`if let`) that only holds when the precondition is met, so paths violating it
exit cleanly without reaching the assertions.

KMIR stops executing the program as soon as any undefined behaviour arises
from the executed statements. Therefore, running to completion proves the
absence of undefined behaviour, as well as the post-conditions expressed as
assertions (under the assumption of the preconditions modelled as above).

## Example: Proving Absence of Undefined Behaviour in `unchecked_*` Arithmetic

The proofs in subdirectory [`0011-floats-ints`](0011-floats-ints) concern a
section of the challenge of securing [Safety of Methods for Numeric Primitive
Types](https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html#challenge-11-safety-of-methods-for-numeric-primitive-types)
of the Verify Rust Standard Library Effort.

Each unsafe method is covered by a pair of files. The passing file calls the
method only when its safety precondition holds, and asserts that the result
matches the checked equivalent:

```Rust
fn unchecked_add_i32(a: i32, b: i32) {
    if let Some(expected) = a.checked_add(b) {
        let result = unsafe { a.unchecked_add(b) };
        assert!(result == expected);
    }
}
```

According to the [documentation of the unchecked_add function for the i32
primitive type](https://doc.rust-lang.org/std/primitive.i32.html#method.unchecked_add),

> "This results in undefined behavior when `self + rhs > i32::MAX` or
> `self + rhs < i32::MIN`, i.e. when `checked_add` would return `None`"

The `if let Some(expected)` binding therefore serves two purposes: it
restricts execution to the inputs for which the operation is defined, and it
supplies the expected result to assert against.

The matching `-fail.rs` file calls the same method on unconstrained symbolic
inputs, without a precondition:

```Rust
fn unchecked_add_i32(a: i32, b: i32) {
    let result = unsafe { a.unchecked_add(b) };
    assert!(result == a.wrapping_add(b)); // UB when the addition overflows
}
```

Here KMIR halts on the overflowing paths and the proof fails, which
demonstrates that the UB is detected rather than silently accepted. These are
run as negative tests, where a failing proof is the expected outcome.

## Running the Proofs

The [`run-proofs.sh`](0011-floats-ints/run-proofs.sh) script runs the whole
suite, and is what the [KMIR CI workflow](../.github/workflows/kmir.yml)
invokes:

```shell
./0011-floats-ints/run-proofs.sh              # passing proofs
./0011-floats-ints/run-proofs.sh --negative   # negative proofs (expect failure)
```

The `--negative` mode inverts the exit code of each proof, so the script fails
if any proof that is expected to detect UB unexpectedly passes.

An individual proof can be run directly. Each file groups the harnesses for
all applicable integer types, so `--start-symbol` accepts a comma-separated
list of entry functions:

```shell
kmir prove unchecked_add.rs --proof-dir proofs \
  --start-symbol unchecked_add_i32 --terminate-on-thunk --verbose
```

`--proof-dir` retains data about the proof's intermediate states so that they
can be inspected afterwards, and `--terminate-on-thunk` reports a failure from
the earliest point at which a rule could not be applied. The `--verbose`
option allows for watching the proof being executed. Further useful flags are
described in the KMIR tool [documentation](../doc/src/tools/kmir.md#useful-prove-flags).

## Inspecting Proof Results

After a proof finishes, the prover reports whether it passed or failed, along
with some details about the execution control flow graph (such as the number
of nodes and leaves). A proof is identified by `<FILE>.<SYMBOL>`, so the
command above produces the proof ID `unchecked_add.unchecked_add_i32`. The
graph can be shown or interactively inspected using `kmir show` and
`kmir view`:

```shell
kmir show unchecked_add.unchecked_add_i32 --proof-dir proofs \
  --leaves --statistics
kmir view unchecked_add.unchecked_add_i32 --proof-dir proofs
```

While `kmir show` only prints the control flow graph, `kmir view` opens an
interactive viewer where the graph nodes can be selected and displayed in
different modes.
