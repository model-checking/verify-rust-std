# Rust standard library verification

[![Rust Tests](https://github.com/model-checking/verify-rust-std/actions/workflows/rustc.yml/badge.svg)](https://github.com/model-checking/verify-rust-std/actions/workflows/rustc.yml)
[![Build Book](https://github.com/model-checking/verify-rust-std/actions/workflows/book.yml/badge.svg)](https://github.com/model-checking/verify-rust-std/actions/workflows/book.yml)


This repository is a fork of the official Rust programming
language repository, created solely to verify the Rust standard
library. It should not be used as an alternative to the official
Rust releases. The repository is tool agnostic and welcomes the addition of
new tools. The currently accepted tools are [Flux](https://model-checking.github.io/verify-rust-std/tools/flux.html), [GOTO Transcoder (ESBMC)](https://model-checking.github.io/verify-rust-std/tools/goto-transcoder.html), [Kani](https://model-checking.github.io/verify-rust-std/tools/kani.html), and [VeriFast](https://model-checking.github.io/verify-rust-std/tools/verifast.html).

The goal is to have a verified [Rust standard library](https://doc.rust-lang.org/std/) and prove that it is safe.
1. Contributing to the core mechanism of verifying the rust standard library
2. Creating new techniques to perform scalable verification
3. Apply techniques to verify previously unverified parts of the standard library.

For that we are launching a [contest supported by the Rust Foundation](https://foundation.rust-lang.org/news/rust-foundation-collaborates-with-aws-initiative-to-verify-rust-standard-libraries/)
that includes a series of challenges that focus on verifying
memory safety and a subset of undefined behaviors in the Rust standard library.
Each challenge describes the goal, the success criteria, and whether it has a financial award to be awarded upon its
successful completion.

These are the challenges:

| Challenge | Reward | Status | Proof |
| --------- | ------ | ------ | ----- |
| [1: Verify core transmuting methods](https://model-checking.github.io/verify-rust-std/challenges/0001-core-transmutation.html) | N/A | Open | |
| [2: Verify the memory safety of core intrinsics using raw pointers](https://model-checking.github.io/verify-rust-std/challenges/0002-intrinsics-memory.html) | N/A | Open | |
| [3: Verifying Raw Pointer Arithmetic Operations](https://model-checking.github.io/verify-rust-std/challenges/0003-pointer-arithmentic.html) | N/A | [Resolved](https://github.com/model-checking/verify-rust-std/pull/212) | [Kani](https://github.com/model-checking/verify-rust-std/pull/212/files) |
| [4: Memory safety of BTreeMap's `btree::node` module](https://model-checking.github.io/verify-rust-std/challenges/0004-btree-node.html) | 10,000 USD | Open | |
| [5: Verify functions iterating over inductive data type: `linked_list`](./challenges/0005-linked-list.md) | 5,000 USD | [Resolved](https://github.com/model-checking/verify-rust-std/pull/238) | [VeriFast](https://github.com/model-checking/verify-rust-std/tree/main/verifast-proofs/alloc/collections/linked_list.rs) |
| [6: Safety of `NonNull`](./challenges/0006-nonnull.md) | N/A | [Resolved](https://github.com/model-checking/verify-rust-std/pull/247) | [Kani](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/ptr/non_null.rs) |
| [7: Safety of Methods for Atomic Types & Atomic Intrinsics](./challenges/0007-atomic-types.md) | 10,000 USD | Open | |
| [8: Contracts for SmallSort](./challenges/0008-smallsort.md) | 10,000 USD | Open | |
| [9: Safe abstractions for `core::time::Duration`](./challenges/0009-duration.md) | N/A | [Resolved](https://github.com/model-checking/verify-rust-std/pull/136) | [Kani](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/time.rs) |
| [10: Memory safety of String](./challenges/0010-string.md) | N/A | Open | |
| [11: Safety of Methods for Numeric Primitive Types](./challenges/0011-floats-ints.md) | N/A | [Resolved](https://github.com/model-checking/verify-rust-std/issues/59) | [Kani](https://github.com/model-checking/verify-rust-std/tree/main/library/core/src/num) |
| [12: Safety of `NonZero`](./challenges/0012-nonzero.md) | N/A | Open | |
| [13: Safety of `CStr`](./challenges/0013-cstr.md) | N/A | Open | |
| [14: Safety of Primitive Conversions](./challenges/0014-convert-num.md) | TBD | [Resolved](https://github.com/model-checking/verify-rust-std/pull/247) | [Kani](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/convert/num.rs) |
| [15: Contracts and Tests for SIMD Intrinsics](./challenges/0015-intrinsics-simd.md) | | Open | |
| [16: Verify the safety of Iterator functions](./challenges/0016-iter.md) | 10,000 USD | Open | |
| [17: Verify the safety of slice functions](./challenges/0017-slice.md) | 10,000 USD | Open | |
| [18: Verify the safety of slice iter functions](./challenges/0018-slice-iter.md) | 10,000 USD | Open | |
| [19: Safety of `RawVec`](./challenges/0019-rawvec.md) | 10,000 USD | [Resolved](https://github.com/model-checking/verify-rust-std/pull/422) | [VeriFast](https://github.com/model-checking/verify-rust-std/tree/main/verifast-proofs/alloc/raw_vec/mod.rs) |
| [20: Verify the safety of char-related functions in str::pattern](./challenges/0020-str-pattern-pt1.md) | 25,000 USD | Open | |
| [21: Verify the safety of substring-related functions in str::pattern](./challenges/0021-str-pattern-pt2.md) | 25,000 USD | Open | |
| [22: Verify the safety of str iter functions](./challenges/0022-str-iter.md) | 10,000 USD | Open | |
| [23: Verify the safety of Vec functions part 1](./challenges/0023-vec-pt1.md) | 15,000 USD | Open | |
| [24: Verify the safety of Vec functions part 2](./challenges/0024-vec-pt2.md) | 15,000 USD | Open | |
| [25: Verify the safety of `VecDeque` functions](./challenges/0025-vecdeque.md) | 10,000 USD | Open | |
| [26: Verify reference-counted Cell implementation](./challenges/0026-rc.md) | 10,000 USD | Open | |
| [27: Verify atomically reference-counted Cell implementation](./challenges/0027-arc.md) | 10,000 USD | Open | |

See [our book](https://model-checking.github.io/verify-rust-std/intro.html) for more details on the challenge rules.

We welcome everyone to participate!

## Contact

For questions, suggestions or feedback, feel free to open an [issue here](https://github.com/model-checking/verify-rust-std/issues).

## Security

See [SECURITY](https://github.com/model-checking/kani/security/policy) for more information.

## License

### Kani
Kani is distributed under the terms of both the MIT license and the Apache License (Version 2.0).
See [LICENSE-APACHE](https://github.com/model-checking/kani/blob/main/LICENSE-APACHE) and [LICENSE-MIT](https://github.com/model-checking/kani/blob/main/LICENSE-MIT) for details.

### Rust
Rust is primarily distributed under the terms of both the MIT license and the Apache License (Version 2.0), with portions covered by various BSD-like licenses.

See [the Rust repository](https://github.com/rust-lang/rust) for details.

## Introducing a New Tool

Please use the [template available in this repository](./doc/src/tool_template.md) to introduce a new verification tool.
