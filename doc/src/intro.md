# Verify Rust Standard Library Effort

The Verify Rust Standard Library effort is an ongoing investment that
targets the verification of the [Rust standard
library](https://doc.rust-lang.org/std/). The goal of this is
to provide automated verification that can be used to verify that a
given Rust standard library implementation is safe.

Verifying the Rust libraries is difficult because:
1. Lack of a specification,
2. Lack of an existing verification mechanism in the Rust ecosystem,
3. The large size of the verification problem,
4. The unknowns of scalable verification.

Given the magnitude and scope of the effort, we believe this should be a community owned effort.
For that, we are launching a contest that includes a series of challenges that focus on verifying
memory safety and a subset of undefined behaviors in the Rust standard library.

Efforts are largely classified in the following areas:

1. Contributing to the core mechanism of verifying the rust standard library
2. Creating new techniques to perform scalable verification
3. Apply techniques to verify previously unverified parts of the standard library.

There is a financial award tied to each challenge per its specification, which is awarded upon its successful completion.

We encourage everyone to watch this repository to be notified of any changes.