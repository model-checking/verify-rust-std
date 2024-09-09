# Challenge 7: Safety of Methods for Atomic Types and `ReentrantLock`

- **Status:** Open
- **Tracking Issue:** [#83](https://github.com/model-checking/verify-rust-std/issues/83)
- **Start date:** *2024-09-09*
- **End date:** *2024-12-10*

-------------------

## Goal

Verify the safety of:
- The methods for atomic types in `core::sync::atomic` 
- The implementation of `ReentrantLock` in `std::sync::reentrant_lock`

### Success Criteria


#### Part 1: Atomic Types

First, verify the safety of methods on atomic types.

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

Specifically, encode the safety conditions marked `#Safety` in the comments above the methods.

For the integer and boolean atomics, verify that these contracts hold on all bit-valid values. For `AtomicPtr`, verify that the contracts hold for pointees of size 0, 8, 16, 32, 64, 128, and at least one non-power-of-two.

Then, write and verify safety contracts for the remaining unsafe functions:

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

These functions are wrappers around compiler intrinsics. Thus, your task is to ensure that we cannot cause undefined behavior by invoking the intrinsics on these inputs. For instance, if the intrinsic takes as input a raw pointer and reads the value at that pointer, your contracts should ensure that we would not cause UB by performing the read. For the purpose of this challenge, you may assume that any UB in the intrinsics would be a direct consequence of malformed inputs.

You are not required to write correctness contracts for these functions (e.g., that `atomic_sub` correctly subtracts the operands and stores the result), but it would be great to do so!

#### Part 2: Reentrant Lock

Verify that the `ReentrantLock` implementation in `std::sync::reentrant_lock` is safe. In particular, verify:

* That all uses of the methods on atomic types uphold the safety contracts you wrote in Part 1, and
* No other unsafe code in `ReentrantLock` causes UB or arithmetic overflow.

## List of UBs

In addition to any properties called out as SAFETY comments in the source code, all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Data races.
* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory.
* Invoking undefined behavior via compiler intrinsics.
* Producing an invalid value.
* Breaking the aliasing or conversion rules of `UnsafeCell` (defined [here](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html)).

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md) in addition to the ones listed above.


