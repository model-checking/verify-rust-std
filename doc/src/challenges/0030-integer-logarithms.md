# Challenge 30: Safety and Correctness of Integer Logarithms

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** [#728](https://github.com/model-checking/verify-rust-std/issues/728)
- **Start date:** *2026/11/02*
- **Reward:** *TBD*

-------------------

## Goal

Verify the safety and correctness of `ilog10`, `ilog2`, and their checked variants in `core::num`,
including `NonZero<T>::ilog2` and `NonZero<T>::ilog10` for unsigned types and the internal
`int_log10` helpers they rely on.

## Motivation

Decimal logarithms make unsafe promises about arithmetic result bounds; binary logarithms
call intrinsics that require nonzero inputs; the `usize` decimal-logarithm wrapper creates a
`NonZero` value without checking it. Violating any of these requirements is undefined
behavior, even though the public APIs are safe.

## Description

| Function | Integer Types | Location |
|---------|---------------|----------|
| `ilog10`, `checked_ilog10`, `ilog2`, `checked_ilog2` | All signed and unsigned integer types | [int_macros.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/int_macros.rs), [uint_macros.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/uint_macros.rs) |
| `NonZero<T>::ilog2`, `NonZero<T>::ilog10` | All unsigned integer types | [nonzero.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/nonzero.rs) |
| `u8_impl`, `u16_impl`, `u32_impl`, `u64_impl`, `u128_impl`, `less_than_5` | Each helper's documented input domain | [int_log10.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/imp/int_log10.rs) |
| Internal wrappers `u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128` | Corresponding integer types | [int_log10.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/num/imp/int_log10.rs) |

- **Signed:** `i8`, `i16`, `i32`, `i64`, `i128`, `isize`.
- **Unsigned:** `u8`, `u16`, `u32`, `u64`, `u128`, `usize`.

Arbitrary-base `ilog` is excluded: its general calculation contains no direct unsafe
operations, and its unsafe dependencies overlap with the implementations above.

This extends [Challenge 11](0011-floats-ints.md) to logarithm methods, which are not
in that challenge's target list. NonZero constructor verification belongs to
[Challenge 12](0012-nonzero.md) and is not repeated here.

### Assumptions

- Existing verified NonZero contracts and documented layout guarantees may be reused.
- The repository's CI runs only 64-bit targets, so proofs need only run on the 64-bit
  configuration of pointer-width-dependent code: the `usize` wrapper and the `isize` methods.
  For the 16- and 32-bit configurations, it suffices to verify the `u16`/`u32` wrappers that
  `usize` selects and the `i16`/`i32` wrappers that `isize` uses, and to argue that the
  `NonZero::new_unchecked` conversion in the `usize` wrapper is safe for each pointer width.

### Success Criteria

Cover every input to the public methods and each internal helper's documented input domain:

- Verify the safety conditions of all unsafe operations, including result-bound assertions, nonzero-input requirements, and the `NonZero::new_unchecked` conversion in the `usize` wrapper.
- For positive input `n`, prove the result is the greatest nonnegative integer `r` with `b^r <= n`, where `b` is 2 or 10 and powers are interpreted mathematically.
- Prove checked methods return `None` for zero or negative inputs, and `ilog2` and `ilog10` panic on those inputs.
- Prove the calculations do not overflow or underflow.

All proofs must automatically ensure the absence of the following
[undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

- Invoking undefined behavior through compiler intrinsics.
- Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the
[challenge book](../general-rules.md) in addition to the ones listed above.

## Kani proof implementation

The proposed Kani implementation lives in `library/core/src/num/imp/int_log10.rs`
and the verification-only module `library/core/src/num/imp/int_log2.rs`.
It does not change the runtime algorithms. The challenge remains open until the
solution is reviewed and accepted.

| Proof group | Harnesses | Coverage |
|------------|-----------|----------|
| Decimal helpers | 6 | Each helper's entire documented positive input domain |
| Decimal wrappers | 11 | Five unsigned, five signed, and `usize` wrappers |
| Supporting contracts | 1 | `hint::assert_unchecked` safety contract |
| Public decimal APIs | 18 | Checked and positive panicking APIs for 12 integer types; six unsigned `NonZero` types |
| Decimal invalid inputs | 13 | Twelve invalid-input routing proofs and the shared panic helper |
| Public binary APIs | 18 | Checked and positive panicking APIs for 12 integer types; six unsigned `NonZero` types |
| Binary invalid inputs | 12 | Invalid-input routing for all 12 integer types |

### Specifications and proof dependencies

The decimal specification compares the input with explicit powers of ten through
`10^38`; the final interval ends at `u128::MAX`. It neither calls a logarithm API
nor computes the unrepresentable value `10^39`. Helpers and wrappers have exact
result contracts. Caller harnesses use `kani::stub_verified` to check callee
preconditions and reuse independently verified postconditions. This includes
checking the condition passed to each wrapper's `assert_unchecked` call.

The binary specification requires `r < 128` and `n >> r == 1` for positive input
`n` widened to `u128`. These conditions mean exactly `2^r <= n < 2^(r+1)`,
including the interval with `r == 127`. Binary API bodies are verified directly,
including the nonzero preconditions of `ctlz_nonzero` and arithmetic safety.

Checked APIs are exercised over their entire primitive input domain. Separate
proofs check the panicking APIs on positive inputs and on nonpositive inputs.
For the latter, only the shared, no-argument panic helper is replaced by a
terminal path (`kani::assume(false)`). An assertion after the API call proves
that no invalid input returns normally; other panics, undefined behavior, or
unbounded loops remain verification failures. A separate `kani::should_panic`
harness checks the actual straight-line panic helper. This avoids using an
existential symbolic `should_panic` check as evidence for all invalid inputs.

### Pointer widths

The `usize` conversion selects `u16`, `u32`, or `u64` with exactly the same width
as the input, so casting preserves its positive value. Consequently,
`NonZero::new_unchecked` receives a nonzero value on each supported pointer width.
The selected unsigned wrappers and the `i16`/`i32` wrappers used by narrower
`isize` configurations have independent proofs. Pointer-sized APIs and the
actual `usize` conversion are run on the 64-bit CI configuration, as permitted
by this challenge; this is not a claim of local execution on 16- or 32-bit targets.

### Reproducing the proofs

From the repository root, run:

```sh
./scripts/run-kani.sh --kani-args --harness num::imp::int_log
./scripts/run-kani.sh --kani-args --harness num::imp::int_log -Z valid-value-checks
```

The filter selects all 79 challenge harnesses, including the supporting contract
and actual panic-helper proof. The existing Kani workflow discovers them without
a separate harness allowlist and verifies them across its partitions on Linux
and macOS. An additional step in partition 1 runs the complete logarithm suite
with `-Z valid-value-checks` on each OS, without partitioning, to explicitly check
for invalid values. Normal Rust regression checks remain covered by the Rust Tests workflow.
