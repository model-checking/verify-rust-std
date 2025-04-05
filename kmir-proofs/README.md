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

## Example Proof: Proving a Maximum Finding Function That only Uses `lower-than`

Considering a function that receives three integer arguments, this
function should return the highest value among them. Assertions can be
used to enforce this condition, and an example code that tests this
function can be seen below:

```Rust
fn main() {

    let a:usize = 42;
    let b:usize = 43;
    let c:usize = 0;

    let result = maximum(a, b, c);

    assert!(result >= a && result >= b && result >= c
        && (result == a || result == b || result == c ) );
}

fn maximum(a: usize, b: usize, c: usize) -> usize {
    // max(max(a,b), c)
    let max_ab = if a < b {b} else {a};
    if max_ab < c {c} else {max_ab}
}
```

Notice in this case that `a`, `b`, and `c` are concrete, fixed
values. To turn the parameters of `maximum` into symbolic variables,
we can obtain the representation of the function call to `maximum`
executed using KMIR and then replace the concrete values of these
variables with symbolic values. Furthermore, the assertion specified
in the code can be manually translated as a requirement that should be
met by the symbolic variables, meaning that any value that they can
assume must respect the conditions contained in the
specification. Following this approach, we can utilize KMIR to give us
formal proof that, for any valid `isize` input, the maximum value
among the three parameters will be returned.

Work on KMIR is in progress and the way a Rust program is turned into
a K claim will be automated in the near future, but is currently a
manual process described in the longer [description of
`maximum-example-proof`](./maximum-example-proof/README.md).

To run this proof in your terminal from this folder, execute:

```sh
cd maximum-proof
kmir prove run  $PWD/maximum-spec.k --proof-dir $PWD/proof
```

If option `--proof-dir` was used, the finished (or an unfinished) proof can be inspected using the following command:

```sh
kmir prove view MAXIMUM-SPEC.maximum-spec --proof-dir $PWD/proof
```

## Example Proofs: Safety of Unsafe Arithmetic Operations

The proofs in subdirectory `unchecked_arithmetic` concern a section of
the challenge of securing [Safety of Methods for Numeric Primitive
Types](https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html#challenge-11-safety-of-methods-for-numeric-primitive-types)
of the Verify Rust Standard Library Effort.

The `*-spec.k` files set up a proof of concept of how KMIR can be used
to prove unsafe methods according to their undefined behaviors. Proofs
were set up using the same method as described for the
`maximum-example-proof`.

All K claim files follow the same pattern (illustrated using
`unchecked_add` on `i16` as an example):

1) For a given unsafe operation, a calling wrapper function
   `unchecked_op` is written and translated to Stable MIR

```rust
 fn unchecked_op(a: i16, b: i16) -> i16 {
     let unchecked_res = unsafe { a.unchecked_add(b) };
     unchecked_res
 }
```

2) A K configuration for a Rust program that calls this function with
   symbolic `i16` arguments `A` and `B` is constructed (currently in a
   manual fashion). The `i16` arguments are represented as `Integer(A,
   16, true)`.

3) According to the [documentation of the unchecked_add function for
   the i16 primitive
   type](https://doc.rust-lang.org/std/primitive.i16.html#method.unchecked_add),

> "This results in undefined behavior when `self + rhs > i16::MAX` or
> `self + rhs < i16::MIN`, i.e. when `checked_add` would return `None`"

  This safety condition is translated into a `requires` clause in the
  K claim. In addition, the invariants for `A`'s and `B`'s
  representation as `i16` can be assumed, giving:

```
 requires // i16 invariants
            0 -Int (1 <<Int 15) <=Int A
    andBool A <Int (1 <<Int 15)
    andBool 0 -Int (1 <<Int 15) <=Int B
    andBool B <Int (1 <<Int 15)
    // invariant of the `unchecked_add` operation
    andBool A +Int B <Int (1 <<Int 15)
    andBool 0 -Int (1 <<Int 15) <=Int A +Int B
```

4) The KMIR semantics would stop the execution instantly when any
   undefined behaviour is detected (i.e., in case of an overflow or
   underflow). The K claim as a whole states that the called function
   will execute to its `Return` point, without causing any undefined
   behaviour.

Claims were set up for functions: `unchecked_add`, `unchecked_sub`,
and `unchecked_mul`, and for type `i16` but are easy to adapt for
other bit width and unsigned numbers.
