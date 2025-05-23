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
[`stable-mir-json`](https://github.com/runtimeverification/stable-mir-json). The
installation is described in the repository's `README.md` files.

The following description assumes that the `kmir` tool and `stable-mir-json` are
installed and available on the path. 

## Program Property Proofs in KMIR 

The most user-friendly way to create and run a proof in KMIR is the `prove-rs`
functionality, which allows a user to prove that a given program will
run to completion without an error.

Desired post-conditions of the program, such as properties of the computed result,
can be formulated as simple `assert` statements. Preconditions can be modelled
as `if` statements which skip execution altogether if the precondition is not met.
They can be added to a test function using the following macro:

```Rust
/// If the precondition is not met, the program is not executed (exits cleanly, ex falso quodlibet)
macro_rules! precondition {
    ($pre:expr, $block:expr) => {
        if $pre { $block }
    };
}
```
If the precondition is not met, the statements in `$block` won't be executed. If
the `$block` is executed, we can assume that the boolean expression `$pre` holds
true.

KMIR will stop executing the program as soon as any undefined behaviour arises
from the executed statements. Therefore, running to completion proves the absense
of undefined behaviour, as well as the post-conditions expressed as assertions
(possibly under the assumption of preconditions modelled using the above macro).

## Example: Proving Absense of Undefined Behaviour in `unchecked_*` arithmetic

The proofs in subdirectory `unchecked_arithmetic` concern a section of
the challenge of securing [Safety of Methods for Numeric Primitive
Types](https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html#challenge-11-safety-of-methods-for-numeric-primitive-types)
of the Verify Rust Standard Library Effort.


As an example of a property proof in KMIR, consider the following function which
tests that `unchecked_add` does not trigger undefined behaviour if its safety
conditions are met by the arguments:

```Rust
fn unchecked_add_i32(a: i32, b: i32) {

    precondition!(
        ((a as i128 + b as i128) <= i32::MAX as i128) &&
        ( a as i128 + b as i128  >= i32::MIN as i128),
        // =========================================
         unsafe {
            let result = a.unchecked_add(b);
            assert!(result as i128 == a as i128 + b as i128)
        }
    );
}
```

According to the [documentation of the unchecked_add function for the i32 primitive
type](https://doc.rust-lang.org/std/primitive.i32.html#method.unchecked_add),

> "This results in undefined behavior when `self + rhs > i32::MAX` or
> `self + rhs < i32::MIN`, i.e. when `checked_add` would return `None`"


If the sum of the two arguments `a` and `b` does not exceed the bounds of type `i32`
(checked by computing it in range `i128`), the `unchecked_add` function should
not trigger undefined behaviour and produce the correct result, expressed by the
`precondition` macro and the assertion at the end of the unsafe block.

To run the proof, we execute `kmir prove-rs` and provide the function name as
the `--start-symbol`. The `--verbose` option allows for watching the proof being
executed, the `--proof-dir` will contain data about the proof's intermediate states
that can be inspected afterwards.

```shell
kmir prove-rs unchecked_arithmetic.rs --proof-dir proof --start-symbol unchecked_add_i32 --verbose
```

After the proof finishes, the prover reports whether it passed or failed, and some
details about the execution control flow graph (such as number of nodes and leaves).
The graph can be shown or interactively inspected using commands `kmir show` and `kmir view`:

```shell
kmir view --proof-dir proof unchecked_arithmetic.unchecked_add_i32
kmir show --proof-dir proof unchecked_arithmetic.unchecked_add_i32 [--no-full-printer]
```

While `kmir show` only prints the control flow graph, `kmir view` opens an interactive
viewer where the graph nodes can be selected and displayed in different modes.
