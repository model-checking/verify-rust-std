# ESBMC

[ESBMC](https://github.com/esbmc/esbmc) is an SMT-based bounded model checker. It reads the GOTO programs that Kani generates
directly: since [v8.4](https://github.com/esbmc/esbmc/pull/5291), `esbmc --binary` accepts a CBMC GOTO binary, so no conversion
step sits between Kani and ESBMC. ESBMC has a few differences to CBMC, including:
- CBMC focuses on SAT-based encodings of unrolled programs, while ESBMC targets SMT-based encodings. The SMT support of ESBMC includes sending the full formula or using incremental-SMT.
- CBMC's concurrency support is an entirely symbolic encoding of a concurrent program in one SAT formula, while ESBMC explores each interleaving individually using context-bounded verification.
- ESBMC implements incremental-BMC and k-induction strategies.

To install ESBMC, download `esbmc-linux.zip` from the [v8.7 release](https://github.com/esbmc/esbmc/releases/tag/v8.7) and unpack it;
the binary is `release/bin/esbmc`. CI uses the same release.

ESBMC also depends on Kani to generate the GOTO files. You can find more information about how to install it in [the installation section of the Kani book](https://model-checking.github.io/kani/install-guide.html).

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

Invoke Kani and ask it to keep the intermediate files: `kani test.rs --keep-temps`. This writes one `.out` file per harness in
CBMC's GOTO binary format, here `test__RNvCsjN3sjT3oKaE_4test4main.out`. The `_RNv...` part of the file name is the harness's
entry point. Ignore the `.symtab.out` file next to it.

## Invoke ESBMC

Pass the `.out` file and its entry point to ESBMC:

```
esbmc --binary test__RNvCsjN3sjT3oKaE_4test4main.out --function _RNvCsjN3sjT3oKaE_4test4main \
    --ignore-property-class reachability_check --ignore-property-class cover
```

```
CBMC goto-binary detected: linking ESBMC additions automatically
[...]
Solving with solver Bitwuzla 0.9.0
Runtime decision procedure: 0.013s
Building error trace

[Counterexample]


State 1 file test.rs line 4 column 5 function main thread 0
----------------------------------------------------
Violated property:
  file test.rs line 4 column 5 function main
  [KANI_CHECK_ID_test.e685462a24097d9e::test_0] assertion failed: 1 == 2
  var_2 != 0

[...]
VERIFICATION FAILED
```

Kani also emits `reachability_check` and `cover` properties, which fail when the check is reachable or the condition is
satisfiable; Kani reads those results itself rather than as bugs. The two `--ignore-property-class` options keep ESBMC from
reporting them as violations.

## Using ESBMC to verify the Rust Standard Library

1. Follow the same procedure for Kani to add new properties.
2. Run Kani with the following extra args: `--keep-temps --only-codegen`.
3. You can then run ESBMC on each contract individually, as above.

In CI, [`scripts/run-esbmc.sh`](https://github.com/model-checking/verify-rust-std/blob/main/scripts/run-esbmc.sh) runs these
steps on the contracts that the [ESBMC workflow](https://github.com/model-checking/verify-rust-std/blob/main/.github/workflows/esbmc.yml) selects.
