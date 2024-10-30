# Challenge 7: Safety of Methods for Atomic Types & Atomic Intrinsics

- **Status:** Open
- **Tracking Issue:** [#83](https://github.com/model-checking/verify-rust-std/issues/83)
- **Start date:** *2024-10-30*
- **End date:** *2024-12-10*

-------------------

## Goal

[`core::sync::atomic`](https://doc.rust-lang.org/std/sync/atomic/index.html) provides methods that operate on atomic types.
For example, `AtomicBool::store(&self, val: bool, order: Ordering)` stores `val` in the atomic boolean referenced by `self` according to the specified [atomic memory ordering](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html).

The goal of this challenge is to verify that these methods are safe.[^1]

### Success Criteria

#### Part 1: Unsafe Methods

First, verify that the unsafe `from_ptr` methods are safe, given that their safety preconditions are met.

Write safety contracts for each of the `from_ptr` methods:

- `AtomicBool::from_ptr`
- `AtomicPtr::from_ptr`
- `AtomicI8::from_ptr`
- `AtomicU8::from_ptr`
- `AtomicI16::from_ptr`
- `AtomicU16::from_ptr`
- `AtomicI32::from_ptr`
- `AtomicU32::from_ptr`
- `AtomicI64::from_ptr`
- `AtomicU64::from_ptr`
- `AtomicI128::from_ptr`
- `AtomicU128::from_ptr`

Specifically, encode the conditions about `ptr`'s alignment and validity (marked `#Safety` in the methods' documentation) as preconditions.
Then, verify that the methods are safe for all possible values for the type that `ptr` points to, given that `ptr` satisfies those preconditions.

For example, `AtomicI8::from_ptr` is defined as:
```rust
/// `ptr` must be [valid] ... (comment continues; omitted for brevity)
pub const unsafe fn from_ptr<'a>(ptr: *mut i8) -> &'a AtomicI8 {
    // SAFETY: guaranteed by the caller
    unsafe { &*ptr.cast() }
}
```

To verify this method, first encode the safety comments (e.g., about pointer validity) as preconditions, then verify the absence of undefined behavior for all possible `i8` values.

For the `AtomicPtr` case only, we do not require that you verify safety for all possible types.
Concretely, below is the type signature for `AtomicPtr::from_ptr`:

```rust
pub const unsafe fn from_ptr<'a>(ptr: *mut *mut T) -> &'a AtomicPtr<T>
```

The type pointed to is a `*mut T`.
Verify that for any arbitrary value for this `*mut T` (i.e., any arbitrary memory address), the method is safe.
However, you need not verify the method for all possible instantiations of `T`.
It suffices to verify this method for `T` of byte sizes 0, 1, 2, 4, and at least one non-power of two.

#### Part 2: Safe Abstractions

The atomic types expose safe abstractions for atomic operations.
In this part, you will work toward verifying that these abstractions are indeed safe by writing and verifying safety contracts for the unsafe code in their bodies.

For example, `AtomicBool::store` is the (public) safe method that atomically updates the boolean's value.
This method invokes the unsafe function `atomic_store`, which in turn calls `intrinsics::atomic_store_relaxed`, `intrinsics::atomic_store_release`, or `intrinsics::atomic_store_seqcst`, depending on the provided ordering.

Write and verify safety contracts for the unsafe functions:

- `atomic_store`
- `atomic_load`
- `atomic_swap`
- `atomic_add`
- `atomic_sub`
- `atomic_compare_exchange`
- `atomic_compare_exchange_weak`
- `atomic_and`
- `atomic_nand`
- `atomic_or`
- `atomic_xor`
- `atomic_max`
- `atomic_umax`
- `atomic_umin`

Then, for each of the safe abstractions that invoke the unsafe functions listed above, write contracts that ensure that they are not invoked with `order`s that would cause panics.

For example, `atomic_store` panics if invoked with `Acquire` or `AcqRel` ordering.
In this case, you would write contracts on the safe `store` methods that enforce that they are not called with either of those `order`s.

#### Part 3: Atomic Intrinsics

Write and verify safety contracts for the intrinsics invoked by the unsafe functions from Part 2 (in `core::intrinsics`):

| Operations            |  Functions |
|-----------------------|-------------|
| Store                 | `atomic_store_relaxed`, `atomic_store_release`, `atomic_store_seqcst` |
| Load                  | `atomic_load_relaxed`, `atomic_load_acquire`, `atomic_load_seqcst` |
| Swap                  | `atomic_xchg_relaxed`, `atomic_xchg_acquire`, `atomic_xchg_release`, `atomic_xchg_acqrel`, `atomic_xchg_seqcst` |
| Add                   | `atomic_xadd_relaxed`, `atomic_xadd_acquire`, `atomic_xadd_release`, `atomic_xadd_acqrel`, `atomic_xadd_seqcst` |
| Sub                   | `atomic_xsub_relaxed`, `atomic_xsub_acquire`, `atomic_xsub_release`, `atomic_xsub_acqrel`, `atomic_xsub_seqcst` |
| Compare Exchange      | `atomic_cxchg_relaxed_relaxed`, `atomic_cxchg_relaxed_acquire`, `atomic_cxchg_relaxed_seqcst`, `atomic_cxchg_acquire_relaxed`, `atomic_cxchg_acquire_acquire`, `atomic_cxchg_acquire_seqcst`, `atomic_cxchg_release_relaxed`, `atomic_cxchg_release_acquire`, `atomic_cxchg_release_seqcst`, `atomic_cxchg_acqrel_relaxed`, `atomic_cxchg_acqrel_acquire`, `atomic_cxchg_acqrel_seqcst`, `atomic_cxchg_seqcst_relaxed`, `atomic_cxchg_seqcst_acquire`, `atomic_cxchg_seqcst_seqcst` |
| Compare Exchange Weak | `atomic_cxchgweak_relaxed_relaxed`, `atomic_cxchgweak_relaxed_acquire`, `atomic_cxchgweak_relaxed_seqcst`, `atomic_cxchgweak_acquire_relaxed`, `atomic_cxchgweak_acquire_acquire`, `atomic_cxchgweak_acquire_seqcst`, `atomic_cxchgweak_release_relaxed`, `atomic_cxchgweak_release_acquire`, `atomic_cxchgweak_release_seqcst`, `atomic_cxchgweak_acqrel_relaxed`, `atomic_cxchgweak_acqrel_acquire`, `atomic_cxchgweak_acqrel_seqcst`, `atomic_cxchgweak_seqcst_relaxed`, `atomic_cxchgweak_seqcst_acquire`, `atomic_cxchgweak_seqcst_seqcst` |
| And                   | `atomic_and_relaxed`, `atomic_and_acquire`, `atomic_and_release`, `atomic_and_acqrel`, `atomic_and_seqcst` |
| Nand                  | `atomic_nand_relaxed`, `atomic_nand_acquire`, `atomic_nand_release`, `atomic_nand_acqrel`, `atomic_nand_seqcst` |
| Or                    | `atomic_or_seqcst`, `atomic_or_acquire`, `atomic_or_release`, `atomic_or_acqrel`, `atomic_or_relaxed` |
| Xor                   | `atomic_xor_seqcst`, `atomic_xor_acquire`, `atomic_xor_release`, `atomic_xor_acqrel`, `atomic_xor_relaxed` |
| Max                   | `atomic_max_relaxed`, `atomic_max_acquire`, `atomic_max_release`, `atomic_max_acqrel`, `atomic_max_seqcst` |
| Min                   | `atomic_min_relaxed`, `atomic_min_acquire`, `atomic_min_release`, `atomic_min_acqrel`, `atomic_min_seqcst` |
| Umax                  | `atomic_umax_relaxed`, `atomic_umax_acquire`, `atomic_umax_release`, `atomic_umax_acqrel`, `atomic_umax_seqcst` |
| Umin                  | `atomic_umin_relaxed`, `atomic_umin_acquire`, `atomic_umin_release`, `atomic_umin_acqrel`, `atomic_umin_seqcst` |

## List of UBs

In addition to any safety properties mentioned in the API documentation, all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Data races.
* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory.
* Invoking undefined behavior via compiler intrinsics.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md) in addition to the ones listed above.

[^1]: Throughout this challenge, when we say "safe", it is identical to saying "does not exhibit undefined behavior".