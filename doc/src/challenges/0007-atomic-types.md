# Challenge 7: Safety of Methods for Atomic Types and `ReentrantLock`

- **Status:** Open
- **Tracking Issue:** [#83](https://github.com/model-checking/verify-rust-std/issues/83)
- **Start date:** *2024-09-09*
- **End date:** *2024-12-10*

-------------------

## Goal

(Throughout this challenge, when we say "safe", it is identical to saying "does not exhibit undefined behavior").

`core::sync::atomic` provides methods that operate on atomic types.
For example, `atomic_store(dst: *mut T, val: T, order: Ordering)` stores `val` at the memory location pointed to by `dst` according to the specified [atomic memory ordering](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html).
Rust developers can use these methods to ensure that their concurrent code is thread-safe.
They can also leverage these types to implement other, more complex atomic data structures.

The goal of this challenge is first to verify that the methods for atomic types are safe, then to verify that the implementation of `ReentrantLock` (which uses atomic types) is safe.

### Success Criteria

#### Part 1: Atomic Types

First, verify that methods on atomic types (in `core::sync::atomic`) are safe.

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

Specifically, encode the conditions marked `#Safety` in the comments above the methods as preconditions.
Then, verify that the methods are safe for all possible values for the type that `ptr` points to.

For example, `AtomicI8::from_ptr` is defined as:
```rust
/// `ptr` must be [valid] ... (comment continues; omitted for brevity)
pub const unsafe fn from_ptr<'a>(ptr: *mut i8) -> &'a AtomicI8 {
    // SAFETY: guaranteed by the caller
    unsafe { &*ptr.cast() }
}
```

To verify this method, first encode the safety comments (e.g., about pointer validity) as preconditions, then verify the absence of undefined behavior for all possible `i8` values.

For the `AtomicPtr` case only, we do not require that you verify safety for all possible values for the type pointed to.
Concretely, below is the type signature for `AtomicPtr::from_ptr`:

```rust
pub const unsafe fn from_ptr<'a>(ptr: *mut *mut T) -> &'a AtomicPtr<T>
```

The type pointed to is a `*mut T`.
Verify that for any arbitrary value for this inner pointer (i.e., any arbitrary memory address), the method is safe.
However, you need not verify the method for all possible instantiations of `T`.
It suffices to verify this method for `T` of byte sizes 0, 1, 2, 4, and at least one non-power of two.

Then, write and verify safety contracts for the remaining methods that use `unsafe`:

| Method                  | Types |
| :---                    |     :---
| `from_mut`              | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `get_mut_slice`         | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `from_mut_slice`        | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `load`                  | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `store`                 | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `swap`                  | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `compare_exchange`      | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `compare_exchange_weak` | `AtomicBool`, `AtomicPtr`, `AtomicI8`,`AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_update`          | `AtomicBool`, `AtomicPtr`, `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_and`             | `AtomicBool`, `AtomicPtr`, `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_xor`             | `AtomicBool`, `AtomicPtr`, `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_nand`            | `AtomicBool`, `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128`|
| `fetch_or`              | `AtomicBool`, `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_add`             | `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_sub`             | `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_max`             | `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `fetch_min`             | `AtomicI8`, `AtomicU8`,`AtomicI16`,`AtomicU16` `AtomicI32`, `AtomicU32`, `AtomicI64`, `AtomicU64`, `AtomicI128`,`AtomicU128` |
| `get_mut`               | `AtomicBool`|
| `fetch_not`             | `AtomicBool`|
| `fetch_ptr_add`         | `AtomicPtr`|
| `fetch_ptr_sub`         | `AtomicPtr`|
| `fetch_byte_add`        | `AtomicPtr`|
| `fetch_byte_sub`        | `AtomicPtr`|
| `fetch_or`              | `AtomicPtr`|

You are not required to write correctness contracts for these functions (e.g., that `AtomicI8::fetch_sub` correctly subtracts the operands and stores the result), but it would be great to do so!

#### Part 2: Reentrant Lock

Verify that the `ReentrantLock` implementation in `std::sync::reentrant_lock` is safe. In particular, verify:

* That all uses of the methods on atomic types uphold the safety contracts you wrote in Part 1, and
* No other unsafe code in `ReentrantLock` causes undefined behavior or arithmetic overflow.

## List of UBs

In addition to any properties called out as SAFETY comments in the source code, all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Data races.
* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory.
* Invoking undefined behavior via compiler intrinsics.
* Producing an invalid value.
* Breaking the aliasing or conversion rules of `UnsafeCell` (defined [here](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html)).

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md) in addition to the ones listed above.
