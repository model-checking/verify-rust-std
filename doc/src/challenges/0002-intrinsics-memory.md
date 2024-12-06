# Challenge 2: Verify the memory safery of core intrinsics using raw pointers

- **Status:** Open
- **Tracking Issue:** [#16](https://github.com/model-checking/verify-rust-std/issues/16)
- **Start date:** *2024/06/12*
- **End date:** *2025/04/10*
- **Reward:** *N/A*

-------------------


## Goal

Annotate Rust core::intrinsics functions that manipulate raw pointers with their safety contract. Verify their usage in the standard library is in fact safe.

### Success Criteria

1. All the following intrinsic functions must be annotated with safety contracts.
2. Any fallback intrinsic implementation must be verified.
3. For intrinsics modeled in the tool of choice, explain how their implementation matches the intrinsics definition. This can either be done in the PR description or as an entry to the contest book as part of the “Tools” chapter.
4. For each function, contestants must state clearly the list of assumptions for each proof, how the proofs can be audited, and the list of (implicit and explicit) properties that are guaranteed.
5. The verification of each intrinsic should ensure all the documented safety conditions are met, and that meeting them is enough to guarantee safe usage.


Intrinsic functions to be annotated with safety contracts

| Function | Location |
|---------|---------|
|typed_swap | core::intrisics |
|vtable_size| core::intrisics |
|vtable_align| core::intrisics |
|copy_nonoverlapping| core::intrisics |
|copy| core::intrisics |
|write_bytes| core::intrisics |
|size_of_val| core::intrisics |
|arith_offset| core::intrisics |
|volatile_copy_nonoverlapping_memory| core::intrisics |
|volatile_copy_memory| core::intrisics |
|volatile_set_memory| core::intrisics |
|volatile_load| core::intrisics |
|volatile_store| core::intrisics |
|unaligned_volatile_load| core::intrisics |
|unaligned_volatile_store| core::intrisics |
|compare_bytes| core::intrisics |
|min_align_of_val| core::intrisics |
|ptr_offset_from| core::intrisics |
|ptr_offset_from_unsigned| core::intrisics |
|read_via_copy| core::intrisics |
|write_via_move| core::intrisics |


All the following usages of intrinsics were proven safe:

| Function | Location |
|---------|---------|
|copy_from_slice	| core::slice |
|parse_u64_into	| std::fmt |
|swap | core::mem |
|align_of_val | core::mem |
|zeroed | core::mem::maybe_uninit |



Annotate and verify all the functions that below that expose intrinsics with safety contracts

| Function | Location |
|---------|---------|
|copy_from_slice	| std::ptr |
|parse_u64_into	| std::ptr |
|swap | std::ptr |
|align_of_val | std::ptr |
|zeroed | std::ptr |



### List of UBs

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Invoking undefined behavior via compiler intrinsics.
* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory except for padding or unions.
* Mutating immutable bytes.
* Producing an invalid value


Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
