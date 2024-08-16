# Challenge 6: Safety of NonNull

- **Status:** Open
- **Tracking Issue:** [Link to issue](TODO: https://github.com/model-checking/verify-rust-std/issues/TBA)
- **Start date:** *2024-08-16*
- **End date:** *2024-12-10*

-------------------


## Goal

Verify absence of undefined behavior of the [`ptr::NonNull` module](https://github.com/rust-lang/rust/blob/master/library/core/src/ptr/non_null.rs).
Most of its functions are marked `unsafe`, yet they are used in 62 other modules
of the standard library.

### Success Criteria

Prove absence of undefined behavior of the following 48 public functions. You
may wish to do so by attaching pre- and postconditions to these, and then (if
needed by the tooling that you choose to use) adding verification harnesses.

1. `NonNull<T>::add`
1. `NonNull<T>::addr`
1. `NonNull<T>::align_offset`
1. `NonNull<T>::as_mut<'a>`
1. `NonNull<T>::as_mut_ptr`
1. `NonNull<T>::as_non_null_ptr`
1. `NonNull<T>::as_ptr`
1. `NonNull<T>::as_ref<'a>`
1. `NonNull<T>::as_uninit_mut<'a>`
1. `NonNull<T>::as_uninit_ref<'a>`
1. `NonNull<T>::as_uninit_slice<'a>`
1. `NonNull<T>::as_uninit_slice_mut<'a>`
1. `NonNull<T>::byte_add`
1. `NonNull<T>::byte_offset_from<U: ?Sized>`
1. `NonNull<T>::byte_offset`
1. `NonNull<T>::byte_sub`
1. `NonNull<T>::cast<U>`
1. `NonNull<T>::copy_from_nonoverlapping`
1. `NonNull<T>::copy_from`
1. `NonNull<T>::copy_to_nonoverlapping`
1. `NonNull<T>::copy_to`
1. `NonNull<T>::dangling`
1. `NonNull<T>::drop_in_place`
1. `NonNull<T>::from_raw_parts`
1. `NonNull<T>::get_unchecked_mut<I>`
1. `NonNull<T>::is_aligned_to`
1. `NonNull<T>::is_aligned`
1. `NonNull<T>::is_empty`
1. `NonNull<T>::len`
1. `NonNull<T>::map_addr`
1. `NonNull<T>::new_unchecked`
1. `NonNull<T>::new`
1. `NonNull<T>::offset_from`
1. `NonNull<T>::offset`
1. `NonNull<T>::read_unaligned`
1. `NonNull<T>::read_volatile`
1. `NonNull<T>::read`
1. `NonNull<T>::replace`
1. `NonNull<T>::slice_from_raw_parts`
1. `NonNull<T>::sub_ptr`
1. `NonNull<T>::sub`
1. `NonNull<T>::swap`
1. `NonNull<T>::to_raw_parts`
1. `NonNull<T>::with_addr`
1. `NonNull<T>::write_bytes`
1. `NonNull<T>::write_unaligned`
1. `NonNull<T>::write_volatile`
1. `NonNull<T>::write`

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
