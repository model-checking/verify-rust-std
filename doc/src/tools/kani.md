# Kani Rust Verifier

The [Kani Rust Verifier](https://github.com/model-checking/kani) is a bit-precise model checker for Rust.
Kani is designed to prove safety properties in your code as well as
the absence of some forms of undefined behavior. It uses model checking under the hood to ensure that
Rust programs adhere to user specified properties.

You can find more information about how to install in [the installation section of the Kani book](https://model-checking.github.io/kani/install-guide.html).

## Usage

Consider a Rust function that takes an integer and returns its absolute value and
a Kani proof that invokes the function that you want to verify

``` rust
fn abs_diff(a: i32, b: i32) -> i32 {
    if a > b {
        a - b
    } else {
        b - a
    }
}

#[cfg(kani)]
#[kani::proof]
fn harness() {
    let a = kani::any::<i32>();
    let b = kani::any::<i32>();
    let result = abs_diff(a, b);
    kani::assert(result >= 0, "Result should always be more than 0");
}
```

Running the command `cargo kani` in your cargo crate will give the result

```
RESULTS:
Check 1: abs_diff.assertion.1
         - Status: FAILURE
         - Description: "attempt to subtract with overflow"
         - Location: src/main.rs:5:9 in function abs_diff

... Other properties that might have failed or succeeded.

Summary:
Verification failed for - harness
Complete - 0 successfully verified harnesses, 1 failures, 1 total.
```

For a more detailed tutorial, you can refer to the [tutorial section of the Kani book](https://model-checking.github.io/kani/kani-tutorial.html).

## Using Kani to verify the Rust Standard Library

Here is a short tutorial of how to use Kani to verify proofs for the standard library.

### Step 1 - Add some proofs to your copy of the model-checking std

Create a local copy of the [model-checking fork](https://github.com/model-checking/verify-rust-std) of the Rust Standard Library. The fork comes with Kani configured, so all you'll need to do is to call Kani's building-block APIs (such as
`assert`, `assume`, `proof` and [function-contracts](https://github.com/model-checking/kani/blob/main/rfc/src/rfcs/0009-function-contracts.md) such as `modifies`, `requires` and `ensures`) directly.


For example, insert this module into an existing file in the core library, like `library/core/src/hint.rs` or `library/core/src/error.rs` in your copy of the library.
This is just for the purpose of getting started, so you can insert it in a different (existing) file in the core library instead.

``` rust
#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub mod verify {
    use crate::kani;

    #[kani::proof]
    pub fn harness_introduction() {
        kani::assert(true, "yay");
    }

    #[kani::proof_for_contract(trivial_function)]
    fn dummy_proof() {
        trivial_function(true);
    }

    #[kani::requires(x == true)]
    fn trivial_function(x: bool) -> bool {
        x
    }
}
```

### Step 2 - Run the Kani script on the std library

To aid the Rust Standard Library verification effort, Kani provides a script out of the box to help you get started.
Run the following command in your local terminal from the verify repository root:

```
./scripts/run-kani.sh --path .
```

To pass kani arguments such as `--harness`, you can run the script with `--kani-args` and continue passing in all the necessary arguments:

```
./scripts/run-kani.sh --path . --kani-args --harness alloc::layout::verify::check_array_i32 --output-format=terse
```

The script `run-kani` installs the right version of Kani for you, builds it and then finally runs the verify-std sub-command of the `kani` with some default flags.

**NOTE:** This script may crash due to linking issues. If the script fails with an error message related to linking, link the new CBMC version, delete the `./kani_build` directory and re-run.

### Step 3 - Check verification result

After running the command, you can expect an output that looks like this:

```
SUMMARY:
 ** 0 of 1 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.017101772s

Complete - 2 successfully verified harnesses, 0 failures, 2 total.
```

### Running on a specific harness

You can specify a specific harness to be verified using the `--harness` flag.

For example, in your local copy of the verify repo, run the following command.

```
./scripts/run-kani.sh --kani-args --harness harness_introduction
```

This gives you the verification result for just `harness_introduction` from the aforementioned blob.

```
RESULTS:
Check 1: verify::harness_introduction.assertion.1
         - Status: SUCCESS
         - Description: "yay"
         - Location: library/core/src/lib.rs:479:9 in function verify::harness_introduction


SUMMARY:
 ** 0 of 1 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.01885804s

Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

Now you can write proof harnesses to verify specific functions in the library.
The current convention is to keep proofs in the same module file of the verification target.

To run Kani for an individual proof, use `--harness [harness_function_name]`.
Note that Kani will batch run all proofs in the library folder if you do not supply the `--harness` flag.

If Kani returns the error `no harnesses matched the harness filter`, you can give the full name of the harness.
For example, to run the proof harness named `check_new` in `library/core/src/ptr/unique.rs`, use
`--harness ptr::unique::verify::check_new`. To run all proofs in `unique.rs`, use `--harness ptr::unique::verify`.

To find the full name of a harness, check the Kani output and find the line starting with `Checking harness [harness full name]`.

## More details

You can find more information about how to install and how you can customize your use of Kani in the
[Kani book](https://model-checking.github.io/kani/).
