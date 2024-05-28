# Rust std-lib verification contest

This repository is a fork of the official Rust programming language repository, created solely to verify the Rust standard library. It should not be used as an alternative to the official Rust releases.

The goal is to have a contest to help verify the [Rust standard library](https://doc.rust-lang.org/std/) and prove that it is safe. The contest will contain several challenges that can be solved by participants. These challenges can take on one of many forms such as:


1. Contributing to the core mechanism of verifying the rust standard library
2. Creating new techniques to perform scalable verification
3. Apply techniques to verify previously unverified parts of the standard library.


To help you get started in the contest, Amazon’s [Kani-rust-verifier team](https://github.com/model-checking/kani) has created mechanisms and tools to help participants verify the standard library. The Kani team has also created some initial contracts and proofs (To be filled and linked here later) to help you get started as a participant.
* * *

## Contest Details

Here are some details for the contest

1. This repository will contain templates for [Issues](http://Insert link to Issues page), [pull requests](http://Link to PR page here) etc. that will be used to create new challenges for verifying the Rust standard library.
2. This repository will contain the initial contracts and proofs that AWS creates using Kani as a tool to verify the standard library.
3. Verification of the functions will be enabled using CI pipelines and Kani tool initially.
4. Any new tool that participants want to enable will require an application using an Issue template. This tool will be analyzed by an independent committee consisting of members from the Rust open-source developers and AWS
    1. A new tool application should clearly specify the differences to existing techniques and provide sufficient background of why this is needed.
    2. Once the tool is approved, it needs to be enabled using CI pipelines.
5. Each contribution or attempt should be submitted via a pull request that will be analyzed by the committee.
6. Each contribution will be reviewed on a first come first serve basis. Acceptance will be based on a unanimous affirmative vote from the review committee. 
7. The contribution must be automated and should work in CI.
8. Once approved by the review committee, the change will be merged into the repository.


For more details, refer to the [contest book page](http://link to contest book page) here.
* * *

## Getting Started

To be filled out later.
* * *

## [Kani](https://github.com/model-checking/kani)

The Kani Rust Verifier is a bit-precise model checker for Rust.

Kani verifies:

* Memory safety (e.g., null pointer dereferences)
* User-specified assertions (i.e `assert!(...)`)
* The absence of panics (eg., `unwrap()` on `None` values)
* The absence of some types of unexpected behavior (e.g., arithmetic overflows).


You can find out more about Kani from the [Kani book](https://model-checking.github.io/kani/) or the [Kani repository on Github](https://github.com/model-checking/kani).

## Contact

For questions, suggestions or feedback, feel free to open an issue on the Kani page with the tag `stdlib-contest`  or contact us directly at [kani-developers@amazon.com](mailto:kani-developers@amazon.com).

## Security

See [SECURITY](https://github.com/model-checking/kani/security/policy) for more information.

## License

### Kani

Kani is distributed under the terms of both the MIT license and the Apache License (Version 2.0).

See [LICENSE-APACHE](link to LICENSE-APACHE) and [LICENSE-MIT](link to LICENSE-MIT) for details.


## Rust

Rust is primarily distributed under the terms of both the MIT license and the Apache License (Version 2.0), with portions covered by various BSD-like licenses.

See [the Rust repository](https://github.com/rust-lang/rust) for details.


