# GOTO-Transcoder (ESBMC)

The [goto-transcoder](https://github.com/rafaelsamenezes/goto-transcoder) is an initiative to add a compatibility layer between GOTO programs generated from CPROVER tools (e.g., CBMC and goto-instrument). Specifically, it adds a compatibility layer between Kani and [ESBMC](https://github.com/esbmc/esbmc). ESBMC has a few differences to CBMC, including:
- CBMC focuses on SAT-based encodings of unrolled programs, while ESBMC targets SMT-based encodings. The SMT support of ESBMC includes sending the full formula or using incremental-SMT.
- CBMC's concurrency support is an entirely symbolic encoding of a concurrent program in one SAT formula, while ESBMC explores each interleaving individually using context-bounded verification.
- ESBMC implements incremental-BMC and k-induction strategies.


To install the tool, you may just download the source code and build it with `cargo build`. 
For ESBMC, we recommend using [this release](https://github.com/esbmc/esbmc/releases/tag/nightly-7867f5e5595b9e181cd36eb9155d1905f87ad241).

Additionally, we also depend on Kani to generate the GOTO files. You can find more information about how to install in [the installation section of the Kani book](https://model-checking.github.io/kani/install-guide.html).

# Steps to Use the Tool

For these steps let's verify a Rust hello world, we will assume that you have Kani available in your system. We will start with
the Hello World from the [Kani tutorial](https://model-checking.github.io/kani/kani-tutorial.html):

```rust
// File: test.rs
#[kani::proof]
fn main() {
    assert!(1 == 2);
}
```

## Use Kani to generate the CBMC GOTO program

Invoke Kani and ask it to keep the intermediate files: `kani test.rs --keep-temps`. This generates a `.out` file that is in the GBF
format. We can double-check this by invoking it with CBMC: `cbmc *test4main.out --show-goto-functions`:

```
[...]
main /* _RNvCshu9GRFEWjwO_4test4main */
        // 12 file test.rs line 3 column 10 function main
        DECL _RNvCshu9GRFEWjwO_4test4main::1::var_0 : struct tag-Unit
        // 13 file /Users/runner/work/kani/kani/library/std/src/lib.rs line 44 column 9 function main
        DECL _RNvCshu9GRFEWjwO_4test4main::1::var_1 : struct tag-Unit
        // 14 file /Users/runner/work/kani/kani/library/std/src/lib.rs line 44 column 22 function main
        DECL _RNvCshu9GRFEWjwO_4test4main::1::var_2 : c_bool[8]
[...]
```

## Convert the CBMC goto into ESBMC goto

1. Clone goto-transcoder: `git clone https://github.com/rafaelsamenezes/goto-transcoder.git`
2. Convert to the ESBMC file: `cargo run cbmc2esbmc  <kani-out>.out <entrypoint> <esbmc>.goto`

```
Running: goto-transcoder file.cbmc.out  _RNvCshu9GRFEWjwO_4test4main file.esbmc.goto
[2024-10-09T13:07:20Z INFO  gototranscoder] Converting CBMC input into ESBMC
[2024-10-09T13:07:20Z INFO  gototranscoder] Done
```

This will generate the `file.esbmc.goto`, which can be used as the ESBMC input.

## Invoke ESBMC

1. Invoke ESBMC with the program: `esbmc --binary file.esbmc.goto`.

```
Solving with solver Z3 v4.13.0
Runtime decision procedure: 0.001s
Building error trace

[Counterexample]


State 1 file test.rs line 4 column 5 function main thread 0
----------------------------------------------------
Violated property:
  file test.rs line 4 column 5 function main
  KANI_CHECK_ID_test.cbacc14fa409fc10::test_0
  0


VERIFICATION FAILED
```


## Using GOTO-Transcoder to verify the Rust Standard Library

1. Follow the same procedure for Kani to add new properties.
2. Run Kani with the following extra args: `--keep-temps --only-codegen`.
3. You can then run each contract individually.
