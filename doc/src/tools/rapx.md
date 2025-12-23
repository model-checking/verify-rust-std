# RAPx
RAPx is a static analysis platform for Rust programs. It can serve as a companion to the Rust compiler in detecting semantic bugs related to unsafe code.

Using abstract interpretation, RAPx checks for undefined behavior (UB) by pre-tagging unsafe APIs. When a caller calls such a pre-tagged API, RAPx examines all program paths to verify whether the program state meets the tag's conditions—ensuring the caller remains sound under any input and does not trigger UB. Currently, RAPx can detect various types of UB, such as misaligned or dangling pointers, out-of-bounds memory access, and uninitialized memory usage.

## Safety Property Verification
This section will briefly describe several key steps of UB validation by RAPx.

RAPx has a specialized verification module for unsafe Rust code that systematically prevents undefined behavior (UB) through two core steps:

+ Audit Unit Generation: Segment code into verifiable units by analyzing unsafe code propagation patterns.

+ Safety Property Verification: Use contract-based abstract interpretation to validate safety properties.

For comprehensive methodology details and practical examples, see the [module of verification in RAPx-Book](https://artisan-lab.github.io/RAPx-Book/6.4-unsafe.html).

## Installation
See the [quick start section](https://github.com/Artisan-Lab/RAPx?tab=readme-ov-file#quick-start) to learn how to install RAPx. The version of rustc used by RAPx is continuously updated and tries to match the `verify-rust-std` project's version whenever possible.

## Usage
### Usage in verifying third-party crate
After ensuring that RAPx with the correct rustc version has been installed, you can verify the soundness of your code by doing the following steps:
+ Navigate to the root directory of the crate you wish to analyze:
```
cd /to-be-verified-crate/
```
+ Set the required environment variables. Since RAPx by default checks all unsafe calls in the standard library, __CARGO_TESTS_ONLY_SRC_ROOT must point to a pre-annotated version of std. A fully annotated std repository for RAPx linking will be released in the future.
```
export RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN_OF_RAPX
export __CARGO_TESTS_ONLY_SRC_ROOT=/path-to-pre-annotated-std-lib/library
```
+ Run the verification using the -verify subcommand. RAPx requires linking to the annotated standard library, so the -Zbuild-std argument is necessary:
```
# In Linux
cargo +$RUSTUP_TOOLCHAIN rapx -verify -- -Zbuild-std=panic_abort,core,alloc,std --target x86_64-unknown-linux-gnu
# In Mac(Arm)
cargo +$RUSTUP_TOOLCHAIN rapx -verify -- -Zbuild-std=panic_abort,core,alloc,std --target aarch64-apple-darwin
```
Upon completion, RAPx will output the analysis results regarding the contract compliance of APIs containing unsafe code:
```
|RAP|INFO|: --------In safe function "alloc::vec::into_raw_parts_with_alloc"---------
|RAP|INFO|:   Use unsafe api "core::ptr::read".
|RAP|INFO|:       Argument 1's passed Sps: {"ValidPtr", "Typed", "Align"}
```

### Usage in verifying the the Rust Standard Library
Apart from the need to set up a `dummy_crate` as the entry point for the verification command, the process is the same as validating third-party libraries. However, RAPx offers a customized command, `-verify-std`, specifically for standard library verification. When using this command, RAPx scans all APIs in the standard library and verifies those annotated with `proof` targets. For example:
```rust
#[cfg_attr(rapx, safety {proof})]
pub fn pop(&mut self) -> Option<T> {
    ...
}
```
This annotation will be conditionally expanded and verified during RAPx's compilation process.

## Caveats
RAPx provides sound detection of undefined behavior - if any path in the program contains UB, it will be reported. But this guarantee comes with inherent over-approximation of program paths, which may yield false positives where reported UB paths are infeasible in concrete execution.

Besides, RAPx is still under heavy development and can currently validate some SPs mentioned in [tag-std](https://github.com/Artisan-Lab/tag-std/blob/main/primitive-sp.md#21-summary-of-primitive-sps). Continued development and integration are needed to support the verification of the remaining ones. 

Finally, RAPx ensures the absence of undefined behavior (UB) on all paths by (i) checking the callee’s preconditions or (ii) tracking subsequent [hazard conditions](https://github.com/Artisan-Lab/tag-std/blob/main/primitive-sp.md#1-overall-idea). RAPx can not provide any proof for the logic correctness of function.

