# Challenge 6: Safety of NonNull

- **Status:** Open
- **Tracking Issue:** [#53](https://github.com/model-checking/verify-rust-std/issues/53)
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
2. `NonNull<T>::addr`
3. `NonNull<T>::align_offset`
4. `NonNull<T>::as_mut<'a>`
5. `NonNull<T>::as_mut_ptr`
6. `NonNull<T>::as_non_null_ptr`
7. `NonNull<T>::as_ptr`
8. `NonNull<T>::as_ref<'a>`
9. `NonNull<T>::as_uninit_mut<'a>`
10. `NonNull<T>::as_uninit_ref<'a>`
11. `NonNull<T>::as_uninit_slice<'a>`
12. `NonNull<T>::as_uninit_slice_mut<'a>`
13. `NonNull<T>::byte_add`
14. `NonNull<T>::byte_offset_from<U: ?Sized>`
15. `NonNull<T>::byte_offset`
16. `NonNull<T>::byte_sub`
17. `NonNull<T>::cast<U>`
18. `NonNull<T>::copy_from_nonoverlapping`
19. `NonNull<T>::copy_from`
20. `NonNull<T>::copy_to_nonoverlapping`
21. `NonNull<T>::copy_to`
22. `NonNull<T>::dangling`
23. `NonNull<T>::drop_in_place`
24. `NonNull<T>::from_raw_parts`
25. `NonNull<T>::get_unchecked_mut<I>`
26. `NonNull<T>::is_aligned_to`
27. `NonNull<T>::is_aligned`
28. `NonNull<T>::is_empty`
29. `NonNull<T>::len`
30. `NonNull<T>::map_addr`
31. `NonNull<T>::new_unchecked`
32. `NonNull<T>::new`
33. `NonNull<T>::offset_from`
34. `NonNull<T>::offset`
35. `NonNull<T>::read_unaligned`
36. `NonNull<T>::read_volatile`
37. `NonNull<T>::read`
38. `NonNull<T>::replace`
39. `NonNull<T>::slice_from_raw_parts`
40. `NonNull<T>::sub_ptr`
41. `NonNull<T>::sub`
42. `NonNull<T>::swap`
43. `NonNull<T>::to_raw_parts`
44. `NonNull<T>::with_addr`
45. `NonNull<T>::write_bytes`
46. `NonNull<T>::write_unaligned`
47. `NonNull<T>::write_volatile`
48. `NonNull<T>::write`

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
