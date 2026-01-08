# Challenge 28: Verify float to decimal conversion module

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** *Link to issue*
- **Start date:** *2026/01/01*
- **End date:** *2026/08/31*
- **Reward:** *5,000 USD*

-------------------


## Goal

The goal of this challenge is to verify the [flt2dec](https://doc.rust-lang.org/src/core/num/flt2dec/mod.rs.html) module, which provides functions for converting floating point numbers to decimals. To do this, it implements both the Dragon and Grisu families of algorithms.

## Motivation

Given that converting floats to decimals correctly is a relatively costly operation, the standard library’s flt2dec module employs unsafe code to enable performance-enhancing operations that are otherwise not allowed in safe Rust (e.g., lifetime laundering to get around borrow-checker restrictions). Functions from this module are primarily invoked whenever attempting to represent floats in a human-readable format, making this a potentially highly-used module.

## Description

All of the functions targeted in this challenge are safe functions whose bodies contain unsafe code. This challenge is thus centered around proving well-encapsulation, which here mainly means showing that calls to variants of assume_init() are only performed on fully-initialized structures, and that the lifetime laundering does not cause undefined behaviour.

### Success Criteria

The following functions contain unsafe code in their bodies but are not themselves marked unsafe. All of these should be proven unconditionally safe, or safety contracts should be added:

| Function | Defined in |
|---------|---------|
| `digits_to_dec_str` | `mod.rs` |
| `digits_to_exp_str` | `mod.rs` |
| `to_shortest_str` | `mod.rs` |
| `to_shortest_exp_str` | `mod.rs` |
| `to_exact_exp_str` | `mod.rs` |
| `to_exact_fixed_str` | `mod.rs` |
| `format_shortest_opt` | `strategy/grisu.rs` |
| `format_shortest` | `strategy/grisu.rs` |
| `format_exact_opt` | `strategy/grisu.rs` |
| `format_exact` | `strategy/grisu.rs` |
| `format_shortest` | `strategy/dragon.rs` |
| `format_exact` | `strategy/dragon.rs` |

For functions taking inputs of generic type 'T', the proofs can be limited to primitive types only.

*List of UBs*

In addition to any properties called out as SAFETY comments in the source code, all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):
* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Invoking undefined behavior via compiler intrinsics.
* Mutating immutable bytes.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
