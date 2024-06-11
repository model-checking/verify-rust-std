# Kani Rust Verifier

The [Kani Rust Verifier](https://github.com/model-checking/kani) is a bit-precise model checker for Rust.
Kani is designed to prove safety properties in your code as well as
the absence of some forms of undefined behavior. It uses model checking under the hood to ensure that
Rust programs adhere to user specified properties.

You can find more informations about how to install in [this section of the Kani book](https://model-checking.github.io/kani/install-guide.html).

## Usage

Consider a rust function that takes an integer and returns its absolute value and
a kani proof that invokes the function that you want to verify

``` rust
// src/main.rs
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
    kani::assert(result >= 0, "Result should always be more than 0");}
```

Running the command `cargo kani` in your cargo crate will give the result

```
...Metadata about the Kani run

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


## Using Kani to verify the rust standard library

To aid the std library verification effort, Kani provides a subcommand out of the box to help you get started.

### Step 1

Modify your local copy of the rust std library by writing proofs for the functions/methods that you want to verify.

For example, insert this short blob into your copy of the std library. This blob imports the building-block APIs such as
`assert`, `assume`, `proof` and [function-contracts](https://github.com/model-checking/kani/blob/main/rfc/src/rfcs/0009-function-contracts.md) such as `proof_for_contract` and `fake_function`.

``` rust
// src/lib/.rs
#[cfg(kani)]
kani_core::kani_lib!(core);

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub mod verify {
    use crate::kani;

    #[kani::proof]
    pub fn harness() {
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

### Step 2

Run the following command in your local terminal:

`kani verify-std -Z unstable-options "path/to/library" --target-dir "/path/to/target" -Z function-contracts -Z stubbing`.

The command `kani verify-std` is a subcommand of the `kani`. This specific subcommand is used to verify the Rust standard library with the following arguments.

- `"path/to/library"`: This argument specifies the path to the modified Rust standard library that was prepared earlier in the script.
- `--target-dir "path/to/target"`: This optional argument sets the target directory where Kani will store its output and intermediate files.

Apart from these, you can use your regular `kani-args` such as `-Z function-contracts` and `-Z stubbing` depending on your verification needs.
For more details on Kani's features, refer to [the features section in the Kani Book](https://model-checking.github.io/kani/reference/attributes.html)

### Step 3

After running the command, you can expect an output that looks like this:

```
SUMMARY:
 ** 0 of 1 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.017101772s

Complete - 2 successfully verified harnesses, 0 failures, 2 total.
```

## More details

You can find more informations about how to install and how you can customize your use of Kani in the
[Kani book](https://model-checking.github.io/kani/).
