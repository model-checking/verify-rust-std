# Turning the max-with-lt program into a property proof

## Example program that we start from

```rust
fn main() {

    let a:usize = 42;
    let b:usize = 43;
    let c:usize = 0;

    let result = maximum(a, b, c);

    assert!(result >= a && result >= b && result >= c
        && (result == a || result == b || result == c ) );
}

fn maximum(a: usize, b: usize, c: usize) -> usize {
    // max(a, max(b, c))
    let max_ab = if a < b {b} else {a};
    if max_ab < c {c} else {max_ab}
}
```

We want to prove a property of `maximum`:
- When called with `a`, `b`, and `c`,
- the `result` will be greater or equal all of the arguments,
- and equal to one (or more) of them.

The `main` program above states this using some concrete values of
`a`, `b`, and `c`. We will run this program to construct a general
symbolic claim and prove it.

In a future version, we will be able to start directly with the
`maximum` function call and provide symbolic arguments to it. This
will save some manual work setting up the claim file and fits the
target of proving based on property tests.

## Extracting Stable MIR for the program

Before we can run the program using the MIR semantics, we have to
compile it with a special compiler to extract Stable MIR from it. This
step differs a bit depending on whether the program has multiple
crates, in our case it is just a simple invocation of the extraction
tool. Assuming the tool is installed as `stable-mir-json` (as in the
docker image provided):

```shell
stable-mir-json -Zno-codegen --out-dir . main-max-with-lt.rs
```

This creates `main-max-with-lt.smir.json`. The `-Zno-codegen` and
`--out-dir` options are passed through to the underlying `rustc` so no
executable is generated.

The Stable MIR for the program can also be rendered as a graph, using
`--dot` as the first option. This creates `main-max-with-lt.smir.dot`.

```shell
stable-mir-json --dot -Zno-codegen --out-dir . main-max-with-lt.rs
```
## Constructing the claim by executing `main` to certain points
Through concrete execution of the parsed K program we can interrupt
the execution after a given number of rewrite steps to inspect the
intermediate state. This will help us with writing our claim manually
until the process is automated.

1. The program (`main`) reaches the call to `maximum` after 25 steps.
   The following command runs it and displays the resulting program state.

    ```shell
    kmir run main-max-with-lt.smir.json --depth 25 | less -S
    ```
    - Arguments `a`, `b`, and `c` are initialised to `Integer`s as `locals[1]` to `locals[3]`
    - A `call` terminator calling function `ty(25)` is executed next (front of the `k` cell)
    - The function table contains `ty(25) -> ... code of "maximum"`.
    - Other state (how `main` continues, its other local variables,
      and some internal functions) is not relevant to the proof we
      want to perform.

```
<kmir>
  <k>
    #execTerminator ( terminator (... kind: terminatorKindCall (... func: operandConstant ( constOperand (... (truncated)
  </k>
  <retVal>
    noReturn
  </retVal>
  <currentFunc>
    ty ( -1 )
  </currentFunc>
  <currentFrame>
    <currentBody>
      ListItem ( basicBlock (... statements: ...(truncated)
      ... (truncated)
    </currentBody>
    <caller>
      ty ( -1 )
    </caller>
    <dest>
      place (... local: local ( -1 ) , projection: .ProjectionElems )
    </dest>
    <target>
      noBasicBlockIdx
    </target>
    <unwind>
      unwindActionUnreachable
    </unwind>
    <locals>
      ListItem ( newLocal ( ty ( 1 ) , mutabilityMut ) )
      ListItem ( typedValue ( Integer ( 42 , 64 , false ) , ty ( 26 ) , mutabilityNot ) )
      ListItem ( typedValue ( Integer ( 22 , 64 , false ) , ty ( 26 ) , mutabilityNot ) )
      ListItem ( typedValue ( Integer ( 0 , 64 , false ) , ty ( 26 ) , mutabilityNot ) )
      ListItem ( newLocal ( ty ( 26 ) , mutabilityNot ) )
      ...(truncated)
    </locals>
  </currentFrame>
  <stack>
    .List
  </stack>
  <functions>
    ty ( 13 ) |-> monoItemFn (... (truncated)
    ...
    ty ( 25 ) |-> monoItemFn (... name: symbol ( "maximum" ) , id: defId ( 7 ) , body: someBody ( body (... (truncated)
    ...
  </functions>
  ...(truncated)
```

2. The program executes for a total of 110 steps to reach the point
   where it `return`s from `maximum`. The following command runs it
   and displays the resulting program state.

    ```shell
    kmir run main-max-with-lt.smir.json --depth 110 | less -S
    ```
    - The value `locals[0]` is now set to an `Integer`. This will be the target of our assertions.
    - A `return` terminator is executed next (front of the `k` cell), it will return `locals[0]`
    - It should be an `Integer` with the desired properties as stated above

State 1. defines our start state for the claim. Irrelevant parts are
elided (replaced by variables).

* The code of the `maximum` function in the `functions` table needs to
  be kept. We also keep its identifier `ty(25)`. Other functions can
  be removed (we won't perform a return).
* The `call` terminator is kept, calling `ty(25)` with arguments from
  `locals[1,2,3]`. `target` is modified to be `noBasicBlockIdx` to
  force termination of the prover (no block to jump back to).
* The four locals `0` - `3` are required in their original order to
  provide the function arguments. The values of `a`, `b`, and `c` in
  locals `1` - `3` are replaced with symbolic variables used in the
  proof.
* We could keep all other locals but do not have to (however it is
  important that the list of locals has a known length).
* `main`s other details in `currentFrame` are irrelevant and elided.


State 2. is the end state, where all that matters is the returned value.

* The `locals` list should contain this `?RESULT` value at index `0`
* The `?RESULT` value should have the properties stated (equivalent to
  the assertion in `main`)
* Because of the modified `target`, the program should end, i.e., have
  an `#EndProgram` in the `k` cell.

The above is written as a _claim_ in K framework language into a
`maximum-spec.k` file.  Most of the syntax can be copied from the
output of the `kmir run` commands above, and irrelevant parts replaced
by `_` (LHS) or `?_` (RHS).

Alternatively, it is possible to construct a claim that the entire
rest of the program after initialising the variables will result in
the desired `?RESULT`, i.e., the assertion in `main` is executed
successfully and the program ends in `#EndProgram` after checking
it. This would require more steps.

## Running the prover on the claim and viewing the proof

Now that we have constructed claim, we can run use the KMIR verifier
to perform symbolic execution, and can view the state of proof
through the KMIR proof viewer.

```shell
kmir prove run  maximum-spec.k --proof-dir ./proof
```

The proof steps are saved in the `$PWD/proof` directory for later
inspection using `kmir prove view`. This is especially important when
the proof does _not_ succeed immediately.

```shell
kmir prove view MAXIMUM-SPEC.maximum-spec --proof-dir ./proof
```
