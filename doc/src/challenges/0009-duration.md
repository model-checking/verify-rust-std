# Challenge 9: Safe abstractions for `core::time::Duration`

- **Status:** Open
- **Tracking Issue:** [#72](https://github.com/model-checking/verify-rust-std/issues/72)
- **Start date:** *2024/08/20*
- **End date:** *2025/04/10*
- **Reward:** *N/A*

-------------------


## Goal

Write function contracts for `core::time::Duration` that can be used as safe abstractions.
Even though the majority of `Duration` methods are safe, many of them are safe abstractions over unsafe code.

For instance, the `new` method is implemented as follows in v1.3.0:
```rust
pub const fn new(secs: u64, nanos: u32) -> Duration {
    if nanos < NANOS_PER_SEC {
        // SAFETY: nanos < NANOS_PER_SEC, therefore nanos is within the valid range
        Duration { secs, nanos: unsafe { Nanoseconds(nanos) } }
    } else {
        let secs = match secs.checked_add((nanos / NANOS_PER_SEC) as u64) {
            Some(secs) => secs,
            None => panic!("overflow in Duration::new"),
        };
        let nanos = nanos % NANOS_PER_SEC;
        // SAFETY: nanos % NANOS_PER_SEC < NANOS_PER_SEC, therefore nanos is within the valid range
        Duration { secs, nanos: unsafe { Nanoseconds(nanos) } }
    }
}
```

### Success Criteria

Write a [type invariant](https://model-checking.github.io/kani/crates/doc/kani/derive.Invariant.html) for the struct `Duration`. Write function contracts for the following public functions.

1. `Duration::new(secs: u64, nanos: u32) -> Duration`
2. `Duration::from_secs(secs: u64) -> Duration`
3. `Duration::from_millis(millis: u64) -> Duration`
4. `Duration::from_micros(micros: u64) -> Duration`
5. `Duration::from_nanos(nanos: u64) -> Duration`

6. `Duration::as_secs(&self) -> u64`
7. `Duration::as_millis(&self) -> u128`
8. `Duration::as_micros(&self) -> u128`
9. `Duration::as_nanos(&self) -> u128`
10. `Duration::subsec_millis(&self) -> u32`
11. `Duration::subsec_micros(&self) -> u32`
12. `Duration::subsec_nanos(&self) -> u32`

13. `Duration::checked_add(&self, rhs: Duration) -> Option<Duration>`
14. `Duration::checked_sub(&self, rhs: Duration) -> Option<Duration>`
15. `Duration::checked_mul(&self, rhs: u32) -> Option<Duration>`
16. `Duration::checked_div(&self, rhs: u32) -> Option<Duration>`

The memory safety and the contracts of the above listed functions must be verified
for all possible input values.

### List of UBs

In addition to any properties called out as `SAFETY` comments in the source
code,
all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory.
* Mutating immutable bytes.
* Producing an invalid value

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
