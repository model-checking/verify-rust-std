# Challenge 29: Safety of Boxed

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** *Link to issue*
- **Start date:** *2026/01/01*
- **End date:** *2026/12/31*
- **Reward:** *15,000 USD*

-------------------


## Goal

The goal of this challenge is to verify the [boxed](https://doc.rust-lang.org/std/boxed/index.html) module, which implements the Box family of types (which includes Box and other related types such as ThinBox). A Box is a type of smart pointer that points to a uniquely-owned heap allocation for arbitrary types.

## Motivation

A Box allows the storage of data on the heap rather than the stack. This has several applications, a common [example](https://doc.rust-lang.org/book/ch15-01-box.html#enabling-recursive-types-with-boxes) being for using dynamically-sized types in contexts requiring an exact size (e.g., recursive types). While this type is useful and diverse in its applications, it also extensively uses unsafe code, meaning it is important to verify that this module is free of undefined behaviour.

### Success Criteria

All the following unsafe functions must be annotated with safety contracts and the contracts have been verified:

| Function | Location |
|---------|---------|
| `Box<mem::MaybeUninit<T>, A>::assume_init`  | `alloc::boxed`  |
| `Box<[mem::MaybeUninit<T>], A>::assume_init`  | `alloc::boxed`  |
| `Box<T>::from_raw`  |  `alloc::boxed`  |
| `Box<T>::from_non_null`   |  `alloc::boxed`  |
| `Box<T, A>::from_raw_in`  |  `alloc::boxed`  |
| `Box<T, A>::from_non_null_in`   | `alloc::boxed`   |
| `<dyn Error>::downcast_unchecked`  |  `alloc::boxed::convert`  |
| `<dyn Error + Send>::downcast_unchecked`  |  `alloc::boxed::convert`  |
| `<dyn Error + Send + Sync>::downcast_unchecked`  |  `alloc::boxed::convert`  |

The following functions contain unsafe code in their bodies but are not themselves marked unsafe. At least 75% of these should be proven unconditionally safe, or safety contracts should be added:

| Function | Location |
|---------|---------|
| `Box<T, A>::new_in`  |  `alloc::boxed`  |
| `Box<T, A>::try_new_in`  |  `alloc::boxed`  |
| `Box<T, A>::try_new_uninit_in`  |  `alloc::boxed`  |
| `Box<T, A>::try_new_zeroed_in` |  `alloc::boxed`  |
| `Box<T, A>::into_boxed_slice`  |  `alloc::boxed`  |
| `Box<[T]>::new_uninit_slice`  |  `alloc::boxed`  |
| `Box<[T]>::new_zeroed_slice`  |  `alloc::boxed`  |
| `Box<[T]>::try_new_uninit_slice`  |  `alloc::boxed`  |
| `Box<[T]>::try_new_zeroed_slice`  |  `alloc::boxed`  |
| `Box<[T]>::into_array` |  `alloc::boxed`  |
| `Box<T, A>::new_uninit_slice_in` |  `alloc::boxed` |
| `Box<T, A>::new_zeroed_slice_in` |  `alloc::boxed`  |
| `Box<T, A>::try_new_uninit_slice_in` |  `alloc::boxed`  |
| `Box<T, A>::try_new_zeroed_slice_in` |  `alloc::boxed`  |
| `Box<mem::MaybeUninit<T>, A>::write` |  `alloc::boxed`  |
| `Box<T>::into_non_null` |  `alloc::boxed`  |
| `Box<T, A>::into_raw_with_allocator` |  `alloc::boxed`  |
| `Box<T, A>::into_non_null_with_allocator` |  `alloc::boxed`  |
| `Box<T, A>::into_unique` |  `alloc::boxed`  |
| `Box<T, A>::leak` |  `alloc::boxed`  |
| `Box<T, A>::into_pin` |  `alloc::boxed`  |
| `<Box<T, A> as Drop>::drop` |  `alloc::boxed`  |
| `<Box<T> as Default>::default` |  `alloc::boxed`  |
| `<Box<str> as Default>::default` |  `alloc::boxed`  |
| `<Box<T, A> as Clone>::clone` |  `alloc::boxed`  |
| `<Box<str> as Clone>::clone` |  `alloc::boxed`  |
| `<Box<[T]> as BoxFromSlice<T>>::from_slice`  |  `alloc::boxed::convert`  |
| `<Box<str> as From<&str>>::from`  |  `alloc::boxed::convert`  |
| `<Box<[u8], A> as From<Box<str, A>>>::from`  |  `alloc::boxed::convert`  |
| `<Box<[T; N]> as TryFrom<Box<[T]>>>::try_from` |  `alloc::boxed::convert`  |
| `<Box<[T; N]> as TryFrom<Box<T>>>::try_from`  |  `alloc::boxed::convert`  |
| `Box<dyn Any, A>::downcast` |  `alloc::boxed::convert`  |
| `Box<dyn Any + Send, A>::downcast`  |  `alloc::boxed::convert`  |
| `Box<dyn Any + Send + Sync, A>::downcast`  |  `alloc::boxed::convert`  |
| `<dyn Error>::downcast`  |  `alloc::boxed::convert`  |
| `<dyn Error + Send>::downcast`  |  `alloc::boxed::convert`  |
| `<dyn Error + Send + Sync>::downcast`  |  `alloc::boxed::convert`  |
| `<ThinBox<T> as Deref>::deref`  | `alloc::boxed::thin`   |
| `<ThinBox<T> as DerefMut>::deref_mut`  | `alloc::boxed::thin`   |
| `<ThinBox<T> as Drop>::drop`  | `alloc::boxed::thin`   |
| `ThinBox<T>::meta`  | `alloc::boxed::thin`   |
| `ThinBox<T>::with_header`  | `alloc::boxed::thin`   |
| `WithHeader<H>::new`  | `alloc::boxed::thin`   |
| `WithHeader<H>::try_new`  | `alloc::boxed::thin`   |
| `WithHeader<H>::new_unsize_zst`  | `alloc::boxed::thin`   |
| `WithHeader<H>::header`  | `alloc::boxed::thin`   |

For functions taking inputs of generic type 'T', the proofs can be limited to primitive types only.

*List of UBs*

In addition to any properties called out as SAFETY comments in the source code, all proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):
* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Invoking undefined behavior via compiler intrinsics.
* Mutating immutable bytes.
* Producing an invalid value.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
