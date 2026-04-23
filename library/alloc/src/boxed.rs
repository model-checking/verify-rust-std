//! The `Box<T>` type for heap allocation.
//!
//! [`Box<T>`], casually referred to as a 'box', provides the simplest form of
//! heap allocation in Rust. Boxes provide ownership for this allocation, and
//! drop their contents when they go out of scope. Boxes also ensure that they
//! never allocate more than `isize::MAX` bytes.
//!
//! # Examples
//!
//! Move a value from the stack to the heap by creating a [`Box`]:
//!
//! ```
//! let val: u8 = 5;
//! let boxed: Box<u8> = Box::new(val);
//! ```
//!
//! Move a value from a [`Box`] back to the stack by [dereferencing]:
//!
//! ```
//! let boxed: Box<u8> = Box::new(5);
//! let val: u8 = *boxed;
//! ```
//!
//! Creating a recursive data structure:
//!
//! ```
//! # #[allow(dead_code)]
//! #[derive(Debug)]
//! enum List<T> {
//!     Cons(T, Box<List<T>>),
//!     Nil,
//! }
//!
//! let list: List<i32> = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
//! println!("{list:?}");
//! ```
//!
//! This will print `Cons(1, Cons(2, Nil))`.
//!
//! Recursive structures must be boxed, because if the definition of `Cons`
//! looked like this:
//!
//! ```compile_fail,E0072
//! # enum List<T> {
//! Cons(T, List<T>),
//! # }
//! ```
//!
//! It wouldn't work. This is because the size of a `List` depends on how many
//! elements are in the list, and so we don't know how much memory to allocate
//! for a `Cons`. By introducing a [`Box<T>`], which has a defined size, we know how
//! big `Cons` needs to be.
//!
//! # Memory layout
//!
//! For non-zero-sized values, a [`Box`] will use the [`Global`] allocator for its allocation. It is
//! valid to convert both ways between a [`Box`] and a raw pointer allocated with the [`Global`]
//! allocator, given that the [`Layout`] used with the allocator is correct for the type and the raw
//! pointer points to a valid value of the right type. More precisely, a `value: *mut T` that has
//! been allocated with the [`Global`] allocator with `Layout::for_value(&*value)` may be converted
//! into a box using [`Box::<T>::from_raw(value)`]. Conversely, the memory backing a `value: *mut T`
//! obtained from [`Box::<T>::into_raw`] may be deallocated using the [`Global`] allocator with
//! [`Layout::for_value(&*value)`].
//!
//! For zero-sized values, the `Box` pointer has to be non-null and sufficiently aligned. The
//! recommended way to build a Box to a ZST if `Box::new` cannot be used is to use
//! [`ptr::NonNull::dangling`].
//!
//! On top of these basic layout requirements, a `Box<T>` must point to a valid value of `T`.
//!
//! So long as `T: Sized`, a `Box<T>` is guaranteed to be represented
//! as a single pointer and is also ABI-compatible with C pointers
//! (i.e. the C type `T*`). This means that if you have extern "C"
//! Rust functions that will be called from C, you can define those
//! Rust functions using `Box<T>` types, and use `T*` as corresponding
//! type on the C side. As an example, consider this C header which
//! declares functions that create and destroy some kind of `Foo`
//! value:
//!
//! ```c
//! /* C header */
//!
//! /* Returns ownership to the caller */
//! struct Foo* foo_new(void);
//!
//! /* Takes ownership from the caller; no-op when invoked with null */
//! void foo_delete(struct Foo*);
//! ```
//!
//! These two functions might be implemented in Rust as follows. Here, the
//! `struct Foo*` type from C is translated to `Box<Foo>`, which captures
//! the ownership constraints. Note also that the nullable argument to
//! `foo_delete` is represented in Rust as `Option<Box<Foo>>`, since `Box<Foo>`
//! cannot be null.
//!
//! ```
//! #[repr(C)]
//! pub struct Foo;
//!
//! #[unsafe(no_mangle)]
//! pub extern "C" fn foo_new() -> Box<Foo> {
//!     Box::new(Foo)
//! }
//!
//! #[unsafe(no_mangle)]
//! pub extern "C" fn foo_delete(_: Option<Box<Foo>>) {}
//! ```
//!
//! Even though `Box<T>` has the same representation and C ABI as a C pointer,
//! this does not mean that you can convert an arbitrary `T*` into a `Box<T>`
//! and expect things to work. `Box<T>` values will always be fully aligned,
//! non-null pointers. Moreover, the destructor for `Box<T>` will attempt to
//! free the value with the global allocator. In general, the best practice
//! is to only use `Box<T>` for pointers that originated from the global
//! allocator.
//!
//! **Important.** At least at present, you should avoid using
//! `Box<T>` types for functions that are defined in C but invoked
//! from Rust. In those cases, you should directly mirror the C types
//! as closely as possible. Using types like `Box<T>` where the C
//! definition is just using `T*` can lead to undefined behavior, as
//! described in [rust-lang/unsafe-code-guidelines#198][ucg#198].
//!
//! # Considerations for unsafe code
//!
//! **Warning: This section is not normative and is subject to change, possibly
//! being relaxed in the future! It is a simplified summary of the rules
//! currently implemented in the compiler.**
//!
//! The aliasing rules for `Box<T>` are the same as for `&mut T`. `Box<T>`
//! asserts uniqueness over its content. Using raw pointers derived from a box
//! after that box has been mutated through, moved or borrowed as `&mut T`
//! is not allowed. For more guidance on working with box from unsafe code, see
//! [rust-lang/unsafe-code-guidelines#326][ucg#326].
//!
//! # Editions
//!
//! A special case exists for the implementation of `IntoIterator` for arrays on the Rust 2021
//! edition, as documented [here][array]. Unfortunately, it was later found that a similar
//! workaround should be added for boxed slices, and this was applied in the 2024 edition.
//!
//! Specifically, `IntoIterator` is implemented for `Box<[T]>` on all editions, but specific calls
//! to `into_iter()` for boxed slices will defer to the slice implementation on editions before
//! 2024:
//!
//! ```rust,edition2021
//! // Rust 2015, 2018, and 2021:
//!
//! # #![allow(boxed_slice_into_iter)] // override our `deny(warnings)`
//! let boxed_slice: Box<[i32]> = vec![0; 3].into_boxed_slice();
//!
//! // This creates a slice iterator, producing references to each value.
//! for item in boxed_slice.into_iter().enumerate() {
//!     let (i, x): (usize, &i32) = item;
//!     println!("boxed_slice[{i}] = {x}");
//! }
//!
//! // The `boxed_slice_into_iter` lint suggests this change for future compatibility:
//! for item in boxed_slice.iter().enumerate() {
//!     let (i, x): (usize, &i32) = item;
//!     println!("boxed_slice[{i}] = {x}");
//! }
//!
//! // You can explicitly iterate a boxed slice by value using `IntoIterator::into_iter`
//! for item in IntoIterator::into_iter(boxed_slice).enumerate() {
//!     let (i, x): (usize, i32) = item;
//!     println!("boxed_slice[{i}] = {x}");
//! }
//! ```
//!
//! Similar to the array implementation, this may be modified in the future to remove this override,
//! and it's best to avoid relying on this edition-dependent behavior if you wish to preserve
//! compatibility with future versions of the compiler.
//!
//! [ucg#198]: https://github.com/rust-lang/unsafe-code-guidelines/issues/198
//! [ucg#326]: https://github.com/rust-lang/unsafe-code-guidelines/issues/326
//! [dereferencing]: core::ops::Deref
//! [`Box::<T>::from_raw(value)`]: Box::from_raw
//! [`Global`]: crate::alloc::Global
//! [`Layout`]: crate::alloc::Layout
//! [`Layout::for_value(&*value)`]: crate::alloc::Layout::for_value
//! [valid]: ptr#safety

#![stable(feature = "rust1", since = "1.0.0")]

use core::borrow::{Borrow, BorrowMut};
#[cfg(not(no_global_oom_handling))]
use core::clone::CloneToUninit;
use core::cmp::Ordering;
use core::error::{self, Error};
use core::fmt;
use core::future::Future;
use core::hash::{Hash, Hasher};
use core::marker::{Tuple, Unsize};
use core::mem::{self, SizedTypeProperties};
use core::ops::{
    AsyncFn, AsyncFnMut, AsyncFnOnce, CoerceUnsized, Coroutine, CoroutineState, Deref, DerefMut,
    DerefPure, DispatchFromDyn, LegacyReceiver,
};
use core::pin::{Pin, PinCoerceUnsized};
use core::ptr::{self, NonNull, Unique};
use core::task::{Context, Poll};

#[cfg(kani)]
use {crate::vec::Vec, core::kani};

#[cfg(not(no_global_oom_handling))]
use crate::alloc::handle_alloc_error;
use crate::alloc::{AllocError, Allocator, Global, Layout};
use crate::raw_vec::RawVec;
#[cfg(not(no_global_oom_handling))]
use crate::str::from_boxed_utf8_unchecked;

/// Conversion related impls for `Box<_>` (`From`, `downcast`, etc)
mod convert;
/// Iterator related impls for `Box<_>`.
mod iter;
/// [`ThinBox`] implementation.
mod thin;

#[unstable(feature = "thin_box", issue = "92791")]
pub use thin::ThinBox;

/// A pointer type that uniquely owns a heap allocation of type `T`.
///
/// See the [module-level documentation](../../std/boxed/index.html) for more.
#[lang = "owned_box"]
#[fundamental]
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_insignificant_dtor]
#[doc(search_unbox)]
// The declaration of the `Box` struct must be kept in sync with the
// compiler or ICEs will happen.
pub struct Box<
    T: ?Sized,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
>(Unique<T>, A);

/// Constructs a `Box<T>` by calling the `exchange_malloc` lang item and moving the argument into
/// the newly allocated memory. This is an intrinsic to avoid unnecessary copies.
///
/// This is the surface syntax for `box <expr>` expressions.
#[rustc_intrinsic]
#[unstable(feature = "liballoc_internals", issue = "none")]
pub fn box_new<T>(x: T) -> Box<T>;

impl<T> Box<T> {
    /// Allocates memory on the heap and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Examples
    ///
    /// ```
    /// let five = Box::new(5);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline(always)]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    #[rustc_diagnostic_item = "box_new"]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub fn new(x: T) -> Self {
        return box_new(x);
    }

    /// Constructs a new box with uninitialized contents.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut five = Box::<u32>::new_uninit();
    /// // Deferred initialization:
    /// five.write(5);
    /// let five = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "new_uninit", since = "1.82.0")]
    #[must_use]
    #[inline]
    pub fn new_uninit() -> Box<mem::MaybeUninit<T>> {
        Self::new_uninit_in(Global)
    }

    /// Constructs a new `Box` with uninitialized contents, with the memory
    /// being filled with `0` bytes.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// let zero = Box::<u32>::new_zeroed();
    /// let zero = unsafe { zero.assume_init() };
    ///
    /// assert_eq!(*zero, 0)
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "new_zeroed_alloc", since = "CURRENT_RUSTC_VERSION")]
    #[must_use]
    pub fn new_zeroed() -> Box<mem::MaybeUninit<T>> {
        Self::new_zeroed_in(Global)
    }

    /// Constructs a new `Pin<Box<T>>`. If `T` does not implement [`Unpin`], then
    /// `x` will be pinned in memory and unable to be moved.
    ///
    /// Constructing and pinning of the `Box` can also be done in two steps: `Box::pin(x)`
    /// does the same as <code>[Box::into_pin]\([Box::new]\(x))</code>. Consider using
    /// [`into_pin`](Box::into_pin) if you already have a `Box<T>`, or if you want to
    /// construct a (pinned) `Box` in a different way than with [`Box::new`].
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "pin", since = "1.33.0")]
    #[must_use]
    #[inline(always)]
    pub fn pin(x: T) -> Pin<Box<T>> {
        Box::new(x).into()
    }

    /// Allocates memory on the heap then places `x` into it,
    /// returning an error if the allocation fails
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// let five = Box::try_new(5)?;
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new(x: T) -> Result<Self, AllocError> {
        Self::try_new_in(x, Global)
    }

    /// Constructs a new box with uninitialized contents on the heap,
    /// returning an error if the allocation fails
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// let mut five = Box::<u32>::try_new_uninit()?;
    /// // Deferred initialization:
    /// five.write(5);
    /// let five = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new_uninit() -> Result<Box<mem::MaybeUninit<T>>, AllocError> {
        Box::try_new_uninit_in(Global)
    }

    /// Constructs a new `Box` with uninitialized contents, with the memory
    /// being filled with `0` bytes on the heap
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// let zero = Box::<u32>::try_new_zeroed()?;
    /// let zero = unsafe { zero.assume_init() };
    ///
    /// assert_eq!(*zero, 0);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new_zeroed() -> Result<Box<mem::MaybeUninit<T>>, AllocError> {
        Box::try_new_zeroed_in(Global)
    }
}

impl<T, A: Allocator> Box<T, A> {
    /// Allocates memory in the given allocator then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let five = Box::new_in(5, System);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[must_use]
    #[inline]
    pub fn new_in(x: T, alloc: A) -> Self
    where
        A: Allocator,
    {
        let mut boxed = Self::new_uninit_in(alloc);
        boxed.write(x);
        unsafe { boxed.assume_init() }
    }

    /// Allocates memory in the given allocator then places `x` into it,
    /// returning an error if the allocation fails
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let five = Box::try_new_in(5, System)?;
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new_in(x: T, alloc: A) -> Result<Self, AllocError>
    where
        A: Allocator,
    {
        let mut boxed = Self::try_new_uninit_in(alloc)?;
        boxed.write(x);
        unsafe { Ok(boxed.assume_init()) }
    }

    /// Constructs a new box with uninitialized contents in the provided allocator.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut five = Box::<u32, _>::new_uninit_in(System);
    /// // Deferred initialization:
    /// five.write(5);
    /// let five = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    pub fn new_uninit_in(alloc: A) -> Box<mem::MaybeUninit<T>, A>
    where
        A: Allocator,
    {
        let layout = Layout::new::<mem::MaybeUninit<T>>();
        // NOTE: Prefer match over unwrap_or_else since closure sometimes not inlineable.
        // That would make code size bigger.
        match Box::try_new_uninit_in(alloc) {
            Ok(m) => m,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Constructs a new box with uninitialized contents in the provided allocator,
    /// returning an error if the allocation fails
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut five = Box::<u32, _>::try_new_uninit_in(System)?;
    /// // Deferred initialization:
    /// five.write(5);
    /// let five = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub fn try_new_uninit_in(alloc: A) -> Result<Box<mem::MaybeUninit<T>, A>, AllocError>
    where
        A: Allocator,
    {
        let ptr = if T::IS_ZST {
            NonNull::dangling()
        } else {
            let layout = Layout::new::<mem::MaybeUninit<T>>();
            alloc.allocate(layout)?.cast()
        };
        unsafe { Ok(Box::from_raw_in(ptr.as_ptr(), alloc)) }
    }

    /// Constructs a new `Box` with uninitialized contents, with the memory
    /// being filled with `0` bytes in the provided allocator.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let zero = Box::<u32, _>::new_zeroed_in(System);
    /// let zero = unsafe { zero.assume_init() };
    ///
    /// assert_eq!(*zero, 0)
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    pub fn new_zeroed_in(alloc: A) -> Box<mem::MaybeUninit<T>, A>
    where
        A: Allocator,
    {
        let layout = Layout::new::<mem::MaybeUninit<T>>();
        // NOTE: Prefer match over unwrap_or_else since closure sometimes not inlineable.
        // That would make code size bigger.
        match Box::try_new_zeroed_in(alloc) {
            Ok(m) => m,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Constructs a new `Box` with uninitialized contents, with the memory
    /// being filled with `0` bytes in the provided allocator,
    /// returning an error if the allocation fails,
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let zero = Box::<u32, _>::try_new_zeroed_in(System)?;
    /// let zero = unsafe { zero.assume_init() };
    ///
    /// assert_eq!(*zero, 0);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub fn try_new_zeroed_in(alloc: A) -> Result<Box<mem::MaybeUninit<T>, A>, AllocError>
    where
        A: Allocator,
    {
        let ptr = if T::IS_ZST {
            NonNull::dangling()
        } else {
            let layout = Layout::new::<mem::MaybeUninit<T>>();
            alloc.allocate_zeroed(layout)?.cast()
        };
        unsafe { Ok(Box::from_raw_in(ptr.as_ptr(), alloc)) }
    }

    /// Constructs a new `Pin<Box<T, A>>`. If `T` does not implement [`Unpin`], then
    /// `x` will be pinned in memory and unable to be moved.
    ///
    /// Constructing and pinning of the `Box` can also be done in two steps: `Box::pin_in(x, alloc)`
    /// does the same as <code>[Box::into_pin]\([Box::new_in]\(x, alloc))</code>. Consider using
    /// [`into_pin`](Box::into_pin) if you already have a `Box<T, A>`, or if you want to
    /// construct a (pinned) `Box` in a different way than with [`Box::new_in`].
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[must_use]
    #[inline(always)]
    pub fn pin_in(x: T, alloc: A) -> Pin<Self>
    where
        A: 'static + Allocator,
    {
        Self::into_pin(Self::new_in(x, alloc))
    }

    /// Converts a `Box<T>` into a `Box<[T]>`
    ///
    /// This conversion does not allocate on the heap and happens in place.
    #[unstable(feature = "box_into_boxed_slice", issue = "71582")]
    pub fn into_boxed_slice(boxed: Self) -> Box<[T], A> {
        let (raw, alloc) = Box::into_raw_with_allocator(boxed);
        unsafe { Box::from_raw_in(raw as *mut [T; 1], alloc) }
    }

    /// Consumes the `Box`, returning the wrapped value.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(box_into_inner)]
    ///
    /// let c = Box::new(5);
    ///
    /// assert_eq!(Box::into_inner(c), 5);
    /// ```
    #[unstable(feature = "box_into_inner", issue = "80437")]
    #[inline]
    pub fn into_inner(boxed: Self) -> T {
        *boxed
    }

    /// Consumes the `Box` without consuming its allocation, returning the wrapped value and a `Box`
    /// to the uninitialized memory where the wrapped value used to live.
    ///
    /// This can be used together with [`write`](Box::write) to reuse the allocation for multiple
    /// boxed values.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(box_take)]
    ///
    /// let c = Box::new(5);
    ///
    /// // take the value out of the box
    /// let (value, uninit) = Box::take(c);
    /// assert_eq!(value, 5);
    ///
    /// // reuse the box for a second value
    /// let c = Box::write(uninit, 6);
    /// assert_eq!(*c, 6);
    /// ```
    #[unstable(feature = "box_take", issue = "147212")]
    pub fn take(boxed: Self) -> (T, Box<mem::MaybeUninit<T>, A>) {
        unsafe {
            let (raw, alloc) = Box::into_raw_with_allocator(boxed);
            let value = raw.read();
            let uninit = Box::from_raw_in(raw.cast::<mem::MaybeUninit<T>>(), alloc);
            (value, uninit)
        }
    }
}

impl<T> Box<[T]> {
    /// Constructs a new boxed slice with uninitialized contents.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut values = Box::<[u32]>::new_uninit_slice(3);
    /// // Deferred initialization:
    /// values[0].write(1);
    /// values[1].write(2);
    /// values[2].write(3);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [1, 2, 3])
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "new_uninit", since = "1.82.0")]
    #[must_use]
    pub fn new_uninit_slice(len: usize) -> Box<[mem::MaybeUninit<T>]> {
        unsafe { RawVec::with_capacity(len).into_box(len) }
    }

    /// Constructs a new boxed slice with uninitialized contents, with the memory
    /// being filled with `0` bytes.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// let values = Box::<[u32]>::new_zeroed_slice(3);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [0, 0, 0])
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "new_zeroed_alloc", since = "CURRENT_RUSTC_VERSION")]
    #[must_use]
    pub fn new_zeroed_slice(len: usize) -> Box<[mem::MaybeUninit<T>]> {
        unsafe { RawVec::with_capacity_zeroed(len).into_box(len) }
    }

    /// Constructs a new boxed slice with uninitialized contents. Returns an error if
    /// the allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// let mut values = Box::<[u32]>::try_new_uninit_slice(3)?;
    /// // Deferred initialization:
    /// values[0].write(1);
    /// values[1].write(2);
    /// values[2].write(3);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [1, 2, 3]);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new_uninit_slice(len: usize) -> Result<Box<[mem::MaybeUninit<T>]>, AllocError> {
        let ptr = if T::IS_ZST || len == 0 {
            NonNull::dangling()
        } else {
            let layout = match Layout::array::<mem::MaybeUninit<T>>(len) {
                Ok(l) => l,
                Err(_) => return Err(AllocError),
            };
            Global.allocate(layout)?.cast()
        };
        unsafe { Ok(RawVec::from_raw_parts_in(ptr.as_ptr(), len, Global).into_box(len)) }
    }

    /// Constructs a new boxed slice with uninitialized contents, with the memory
    /// being filled with `0` bytes. Returns an error if the allocation fails.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// let values = Box::<[u32]>::try_new_zeroed_slice(3)?;
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [0, 0, 0]);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new_zeroed_slice(len: usize) -> Result<Box<[mem::MaybeUninit<T>]>, AllocError> {
        let ptr = if T::IS_ZST || len == 0 {
            NonNull::dangling()
        } else {
            let layout = match Layout::array::<mem::MaybeUninit<T>>(len) {
                Ok(l) => l,
                Err(_) => return Err(AllocError),
            };
            Global.allocate_zeroed(layout)?.cast()
        };
        unsafe { Ok(RawVec::from_raw_parts_in(ptr.as_ptr(), len, Global).into_box(len)) }
    }

    /// Converts the boxed slice into a boxed array.
    ///
    /// This operation does not reallocate; the underlying array of the slice is simply reinterpreted as an array type.
    ///
    /// If `N` is not exactly equal to the length of `self`, then this method returns `None`.
    #[unstable(feature = "slice_as_array", issue = "133508")]
    #[inline]
    #[must_use]
    pub fn into_array<const N: usize>(self) -> Option<Box<[T; N]>> {
        if self.len() == N {
            let ptr = Self::into_raw(self) as *mut [T; N];

            // SAFETY: The underlying array of a slice has the exact same layout as an actual array `[T; N]` if `N` is equal to the slice's length.
            let me = unsafe { Box::from_raw(ptr) };
            Some(me)
        } else {
            None
        }
    }
}

impl<T, A: Allocator> Box<[T], A> {
    /// Constructs a new boxed slice with uninitialized contents in the provided allocator.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut values = Box::<[u32], _>::new_uninit_slice_in(3, System);
    /// // Deferred initialization:
    /// values[0].write(1);
    /// values[1].write(2);
    /// values[2].write(3);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [1, 2, 3])
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[must_use]
    pub fn new_uninit_slice_in(len: usize, alloc: A) -> Box<[mem::MaybeUninit<T>], A> {
        unsafe { RawVec::with_capacity_in(len, alloc).into_box(len) }
    }

    /// Constructs a new boxed slice with uninitialized contents in the provided allocator,
    /// with the memory being filled with `0` bytes.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let values = Box::<[u32], _>::new_zeroed_slice_in(3, System);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [0, 0, 0])
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[must_use]
    pub fn new_zeroed_slice_in(len: usize, alloc: A) -> Box<[mem::MaybeUninit<T>], A> {
        unsafe { RawVec::with_capacity_zeroed_in(len, alloc).into_box(len) }
    }

    /// Constructs a new boxed slice with uninitialized contents in the provided allocator. Returns an error if
    /// the allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut values = Box::<[u32], _>::try_new_uninit_slice_in(3, System)?;
    /// // Deferred initialization:
    /// values[0].write(1);
    /// values[1].write(2);
    /// values[2].write(3);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [1, 2, 3]);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new_uninit_slice_in(
        len: usize,
        alloc: A,
    ) -> Result<Box<[mem::MaybeUninit<T>], A>, AllocError> {
        let ptr = if T::IS_ZST || len == 0 {
            NonNull::dangling()
        } else {
            let layout = match Layout::array::<mem::MaybeUninit<T>>(len) {
                Ok(l) => l,
                Err(_) => return Err(AllocError),
            };
            alloc.allocate(layout)?.cast()
        };
        unsafe { Ok(RawVec::from_raw_parts_in(ptr.as_ptr(), len, alloc).into_box(len)) }
    }

    /// Constructs a new boxed slice with uninitialized contents in the provided allocator, with the memory
    /// being filled with `0` bytes. Returns an error if the allocation fails.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let values = Box::<[u32], _>::try_new_zeroed_slice_in(3, System)?;
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [0, 0, 0]);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [zeroed]: mem::MaybeUninit::zeroed
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn try_new_zeroed_slice_in(
        len: usize,
        alloc: A,
    ) -> Result<Box<[mem::MaybeUninit<T>], A>, AllocError> {
        let ptr = if T::IS_ZST || len == 0 {
            NonNull::dangling()
        } else {
            let layout = match Layout::array::<mem::MaybeUninit<T>>(len) {
                Ok(l) => l,
                Err(_) => return Err(AllocError),
            };
            alloc.allocate_zeroed(layout)?.cast()
        };
        unsafe { Ok(RawVec::from_raw_parts_in(ptr.as_ptr(), len, alloc).into_box(len)) }
    }
}

impl<T, A: Allocator> Box<mem::MaybeUninit<T>, A> {
    /// Converts to `Box<T, A>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the value
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    ///
    /// # Examples
    ///
    /// ```
    /// let mut five = Box::<u32>::new_uninit();
    /// // Deferred initialization:
    /// five.write(5);
    /// let five: Box<u32> = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    #[stable(feature = "new_uninit", since = "1.82.0")]
    #[inline]
    #[cfg_attr(
        kani,
        kani::requires({
            let ptr = (&*self) as *const mem::MaybeUninit<T> as *const T;
            kani::mem::can_dereference(ptr)
        })
    )]
    pub unsafe fn assume_init(self) -> Box<T, A> {
        let (raw, alloc) = Box::into_raw_with_allocator(self);
        unsafe { Box::from_raw_in(raw as *mut T, alloc) }
    }

    /// Writes the value and converts to `Box<T, A>`.
    ///
    /// This method converts the box similarly to [`Box::assume_init`] but
    /// writes `value` into it before conversion thus guaranteeing safety.
    /// In some scenarios use of this method may improve performance because
    /// the compiler may be able to optimize copying from stack.
    ///
    /// # Examples
    ///
    /// ```
    /// let big_box = Box::<[usize; 1024]>::new_uninit();
    ///
    /// let mut array = [0; 1024];
    /// for (i, place) in array.iter_mut().enumerate() {
    ///     *place = i;
    /// }
    ///
    /// // The optimizer may be able to elide this copy, so previous code writes
    /// // to heap directly.
    /// let big_box = Box::write(big_box, array);
    ///
    /// for (i, x) in big_box.iter().enumerate() {
    ///     assert_eq!(*x, i);
    /// }
    /// ```
    #[stable(feature = "box_uninit_write", since = "1.87.0")]
    #[inline]
    pub fn write(mut boxed: Self, value: T) -> Box<T, A> {
        unsafe {
            (*boxed).write(value);
            boxed.assume_init()
        }
    }
}

impl<T, A: Allocator> Box<[mem::MaybeUninit<T>], A> {
    /// Converts to `Box<[T], A>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the values
    /// really are in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    ///
    /// # Examples
    ///
    /// ```
    /// let mut values = Box::<[u32]>::new_uninit_slice(3);
    /// // Deferred initialization:
    /// values[0].write(1);
    /// values[1].write(2);
    /// values[2].write(3);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [1, 2, 3])
    /// ```
    #[stable(feature = "new_uninit", since = "1.82.0")]
    #[inline]
    #[cfg_attr(
        kani,
        kani::requires({
            let ptr = (&*self) as *const [mem::MaybeUninit<T>] as *const [T];
            kani::mem::can_dereference(ptr)
        })
    )]
    pub unsafe fn assume_init(self) -> Box<[T], A> {
        let (raw, alloc) = Box::into_raw_with_allocator(self);
        unsafe { Box::from_raw_in(raw as *mut [T], alloc) }
    }
}

impl<T: ?Sized> Box<T> {
    /// Constructs a box from a raw pointer.
    ///
    /// After calling this function, the raw pointer is owned by the
    /// resulting `Box`. Specifically, the `Box` destructor will call
    /// the destructor of `T` and free the allocated memory. For this
    /// to be safe, the memory must have been allocated in accordance
    /// with the [memory layout] used by `Box` .
    ///
    /// # Safety
    ///
    /// This function is unsafe because improper use may lead to
    /// memory problems. For example, a double-free may occur if the
    /// function is called twice on the same raw pointer.
    ///
    /// The raw pointer must point to a block of memory allocated by the global allocator.
    ///
    /// The safety conditions are described in the [memory layout] section.
    ///
    /// # Examples
    ///
    /// Recreate a `Box` which was previously converted to a raw pointer
    /// using [`Box::into_raw`]:
    /// ```
    /// let x = Box::new(5);
    /// let ptr = Box::into_raw(x);
    /// let x = unsafe { Box::from_raw(ptr) };
    /// ```
    /// Manually create a `Box` from scratch by using the global allocator:
    /// ```
    /// use std::alloc::{alloc, Layout};
    ///
    /// unsafe {
    ///     let ptr = alloc(Layout::new::<i32>()) as *mut i32;
    ///     // In general .write is required to avoid attempting to destruct
    ///     // the (uninitialized) previous contents of `ptr`, though for this
    ///     // simple example `*ptr = 5` would have worked as well.
    ///     ptr.write(5);
    ///     let x = Box::from_raw(ptr);
    /// }
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[stable(feature = "box_raw", since = "1.4.0")]
    #[inline]
    #[must_use = "call `drop(Box::from_raw(ptr))` if you intend to drop the `Box`"]
    #[cfg_attr(
        kani,
        kani::requires({
            let align = kani::mem::checked_align_of_raw(raw);
            let size = kani::mem::checked_size_of_raw(raw);

            !raw.is_null()
                && align.is_some()
                && size.map_or(false, |size| size <= isize::MAX as usize)
                && kani::mem::can_dereference(raw)
        })
    )]
    pub unsafe fn from_raw(raw: *mut T) -> Self {
        unsafe { Self::from_raw_in(raw, Global) }
    }

    /// Constructs a box from a `NonNull` pointer.
    ///
    /// After calling this function, the `NonNull` pointer is owned by
    /// the resulting `Box`. Specifically, the `Box` destructor will call
    /// the destructor of `T` and free the allocated memory. For this
    /// to be safe, the memory must have been allocated in accordance
    /// with the [memory layout] used by `Box` .
    ///
    /// # Safety
    ///
    /// This function is unsafe because improper use may lead to
    /// memory problems. For example, a double-free may occur if the
    /// function is called twice on the same `NonNull` pointer.
    ///
    /// The non-null pointer must point to a block of memory allocated by the global allocator.
    ///
    /// The safety conditions are described in the [memory layout] section.
    ///
    /// # Examples
    ///
    /// Recreate a `Box` which was previously converted to a `NonNull`
    /// pointer using [`Box::into_non_null`]:
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// let x = Box::new(5);
    /// let non_null = Box::into_non_null(x);
    /// let x = unsafe { Box::from_non_null(non_null) };
    /// ```
    /// Manually create a `Box` from scratch by using the global allocator:
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// use std::alloc::{alloc, Layout};
    /// use std::ptr::NonNull;
    ///
    /// unsafe {
    ///     let non_null = NonNull::new(alloc(Layout::new::<i32>()).cast::<i32>())
    ///         .expect("allocation failed");
    ///     // In general .write is required to avoid attempting to destruct
    ///     // the (uninitialized) previous contents of `non_null`.
    ///     non_null.write(5);
    ///     let x = Box::from_non_null(non_null);
    /// }
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[unstable(feature = "box_vec_non_null", reason = "new API", issue = "130364")]
    #[inline]
    #[must_use = "call `drop(Box::from_non_null(ptr))` if you intend to drop the `Box`"]
    #[cfg_attr(
        kani,
        kani::requires({
            let raw = ptr.as_ptr();
            let align = kani::mem::checked_align_of_raw(raw);
            let size = kani::mem::checked_size_of_raw(raw);

            align.is_some()
                && size.map_or(false, |size| size <= isize::MAX as usize)
                && kani::mem::can_dereference(raw)
        })
    )]
    #[cfg_attr(
        kani,
        kani::ensures(|result: &Self| {
            let raw = ptr.as_ptr();
            (&**result) as *const T == raw
        })
    )]
    pub unsafe fn from_non_null(ptr: NonNull<T>) -> Self {
        unsafe { Self::from_raw(ptr.as_ptr()) }
    }

    /// Consumes the `Box`, returning a wrapped raw pointer.
    ///
    /// The pointer will be properly aligned and non-null.
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Box`. In particular, the
    /// caller should properly destroy `T` and release the memory, taking
    /// into account the [memory layout] used by `Box`. The easiest way to
    /// do this is to convert the raw pointer back into a `Box` with the
    /// [`Box::from_raw`] function, allowing the `Box` destructor to perform
    /// the cleanup.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::into_raw(b)` instead of `b.into_raw()`. This
    /// is so that there is no conflict with a method on the inner type.
    ///
    /// # Examples
    /// Converting the raw pointer back into a `Box` with [`Box::from_raw`]
    /// for automatic cleanup:
    /// ```
    /// let x = Box::new(String::from("Hello"));
    /// let ptr = Box::into_raw(x);
    /// let x = unsafe { Box::from_raw(ptr) };
    /// ```
    /// Manual cleanup by explicitly running the destructor and deallocating
    /// the memory:
    /// ```
    /// use std::alloc::{dealloc, Layout};
    /// use std::ptr;
    ///
    /// let x = Box::new(String::from("Hello"));
    /// let ptr = Box::into_raw(x);
    /// unsafe {
    ///     ptr::drop_in_place(ptr);
    ///     dealloc(ptr as *mut u8, Layout::new::<String>());
    /// }
    /// ```
    /// Note: This is equivalent to the following:
    /// ```
    /// let x = Box::new(String::from("Hello"));
    /// let ptr = Box::into_raw(x);
    /// unsafe {
    ///     drop(Box::from_raw(ptr));
    /// }
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[must_use = "losing the pointer will leak memory"]
    #[stable(feature = "box_raw", since = "1.4.0")]
    #[inline]
    pub fn into_raw(b: Self) -> *mut T {
        // Avoid `into_raw_with_allocator` as that interacts poorly with Miri's Stacked Borrows.
        let mut b = mem::ManuallyDrop::new(b);
        // We go through the built-in deref for `Box`, which is crucial for Miri to recognize this
        // operation for it's alias tracking.
        &raw mut **b
    }

    /// Consumes the `Box`, returning a wrapped `NonNull` pointer.
    ///
    /// The pointer will be properly aligned.
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Box`. In particular, the
    /// caller should properly destroy `T` and release the memory, taking
    /// into account the [memory layout] used by `Box`. The easiest way to
    /// do this is to convert the `NonNull` pointer back into a `Box` with the
    /// [`Box::from_non_null`] function, allowing the `Box` destructor to
    /// perform the cleanup.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::into_non_null(b)` instead of `b.into_non_null()`.
    /// This is so that there is no conflict with a method on the inner type.
    ///
    /// # Examples
    /// Converting the `NonNull` pointer back into a `Box` with [`Box::from_non_null`]
    /// for automatic cleanup:
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// let x = Box::new(String::from("Hello"));
    /// let non_null = Box::into_non_null(x);
    /// let x = unsafe { Box::from_non_null(non_null) };
    /// ```
    /// Manual cleanup by explicitly running the destructor and deallocating
    /// the memory:
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// use std::alloc::{dealloc, Layout};
    ///
    /// let x = Box::new(String::from("Hello"));
    /// let non_null = Box::into_non_null(x);
    /// unsafe {
    ///     non_null.drop_in_place();
    ///     dealloc(non_null.as_ptr().cast::<u8>(), Layout::new::<String>());
    /// }
    /// ```
    /// Note: This is equivalent to the following:
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// let x = Box::new(String::from("Hello"));
    /// let non_null = Box::into_non_null(x);
    /// unsafe {
    ///     drop(Box::from_non_null(non_null));
    /// }
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[must_use = "losing the pointer will leak memory"]
    #[unstable(feature = "box_vec_non_null", reason = "new API", issue = "130364")]
    #[inline]
    pub fn into_non_null(b: Self) -> NonNull<T> {
        // SAFETY: `Box` is guaranteed to be non-null.
        unsafe { NonNull::new_unchecked(Self::into_raw(b)) }
    }
}

impl<T: ?Sized, A: Allocator> Box<T, A> {
    /// Constructs a box from a raw pointer in the given allocator.
    ///
    /// After calling this function, the raw pointer is owned by the
    /// resulting `Box`. Specifically, the `Box` destructor will call
    /// the destructor of `T` and free the allocated memory. For this
    /// to be safe, the memory must have been allocated in accordance
    /// with the [memory layout] used by `Box` .
    ///
    /// # Safety
    ///
    /// This function is unsafe because improper use may lead to
    /// memory problems. For example, a double-free may occur if the
    /// function is called twice on the same raw pointer.
    ///
    /// The raw pointer must point to a block of memory allocated by `alloc`.
    ///
    /// # Examples
    ///
    /// Recreate a `Box` which was previously converted to a raw pointer
    /// using [`Box::into_raw_with_allocator`]:
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let x = Box::new_in(5, System);
    /// let (ptr, alloc) = Box::into_raw_with_allocator(x);
    /// let x = unsafe { Box::from_raw_in(ptr, alloc) };
    /// ```
    /// Manually create a `Box` from scratch by using the system allocator:
    /// ```
    /// #![feature(allocator_api, slice_ptr_get)]
    ///
    /// use std::alloc::{Allocator, Layout, System};
    ///
    /// unsafe {
    ///     let ptr = System.allocate(Layout::new::<i32>())?.as_mut_ptr() as *mut i32;
    ///     // In general .write is required to avoid attempting to destruct
    ///     // the (uninitialized) previous contents of `ptr`, though for this
    ///     // simple example `*ptr = 5` would have worked as well.
    ///     ptr.write(5);
    ///     let x = Box::from_raw_in(ptr, System);
    /// }
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    #[cfg_attr(
        kani,
        kani::requires({
            let align = kani::mem::checked_align_of_raw(raw);
            let size = kani::mem::checked_size_of_raw(raw);

            !raw.is_null()
                && align.is_some()
                && size.map_or(false, |size| size <= isize::MAX as usize)
                && kani::mem::can_dereference(raw)
        })
    )]
    #[cfg_attr(kani, kani::ensures(|result: &Self| (&**result) as *const T == raw))]
    pub unsafe fn from_raw_in(raw: *mut T, alloc: A) -> Self {
        Box(unsafe { Unique::new_unchecked(raw) }, alloc)
    }

    /// Constructs a box from a `NonNull` pointer in the given allocator.
    ///
    /// After calling this function, the `NonNull` pointer is owned by
    /// the resulting `Box`. Specifically, the `Box` destructor will call
    /// the destructor of `T` and free the allocated memory. For this
    /// to be safe, the memory must have been allocated in accordance
    /// with the [memory layout] used by `Box` .
    ///
    /// # Safety
    ///
    /// This function is unsafe because improper use may lead to
    /// memory problems. For example, a double-free may occur if the
    /// function is called twice on the same raw pointer.
    ///
    /// The non-null pointer must point to a block of memory allocated by `alloc`.
    ///
    /// # Examples
    ///
    /// Recreate a `Box` which was previously converted to a `NonNull` pointer
    /// using [`Box::into_non_null_with_allocator`]:
    /// ```
    /// #![feature(allocator_api, box_vec_non_null)]
    ///
    /// use std::alloc::System;
    ///
    /// let x = Box::new_in(5, System);
    /// let (non_null, alloc) = Box::into_non_null_with_allocator(x);
    /// let x = unsafe { Box::from_non_null_in(non_null, alloc) };
    /// ```
    /// Manually create a `Box` from scratch by using the system allocator:
    /// ```
    /// #![feature(allocator_api, box_vec_non_null, slice_ptr_get)]
    ///
    /// use std::alloc::{Allocator, Layout, System};
    ///
    /// unsafe {
    ///     let non_null = System.allocate(Layout::new::<i32>())?.cast::<i32>();
    ///     // In general .write is required to avoid attempting to destruct
    ///     // the (uninitialized) previous contents of `non_null`.
    ///     non_null.write(5);
    ///     let x = Box::from_non_null_in(non_null, System);
    /// }
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[unstable(feature = "allocator_api", issue = "32838")]
    // #[unstable(feature = "box_vec_non_null", reason = "new API", issue = "130364")]
    #[inline]
    #[cfg_attr(
        kani,
        kani::requires({
            let ptr = raw.as_ptr();
            let align = kani::mem::checked_align_of_raw(ptr);
            let size = kani::mem::checked_size_of_raw(ptr);

            align.is_some()
                && size.map_or(false, |size| size <= isize::MAX as usize)
                && kani::mem::can_dereference(ptr)
        })
    )]
    #[cfg_attr(kani, kani::ensures(|result: &Self| (&**result) as *const T == raw.as_ptr()))]
    pub unsafe fn from_non_null_in(raw: NonNull<T>, alloc: A) -> Self {
        // SAFETY: guaranteed by the caller.
        unsafe { Box::from_raw_in(raw.as_ptr(), alloc) }
    }

    /// Consumes the `Box`, returning a wrapped raw pointer and the allocator.
    ///
    /// The pointer will be properly aligned and non-null.
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Box`. In particular, the
    /// caller should properly destroy `T` and release the memory, taking
    /// into account the [memory layout] used by `Box`. The easiest way to
    /// do this is to convert the raw pointer back into a `Box` with the
    /// [`Box::from_raw_in`] function, allowing the `Box` destructor to perform
    /// the cleanup.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::into_raw_with_allocator(b)` instead of `b.into_raw_with_allocator()`. This
    /// is so that there is no conflict with a method on the inner type.
    ///
    /// # Examples
    /// Converting the raw pointer back into a `Box` with [`Box::from_raw_in`]
    /// for automatic cleanup:
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let x = Box::new_in(String::from("Hello"), System);
    /// let (ptr, alloc) = Box::into_raw_with_allocator(x);
    /// let x = unsafe { Box::from_raw_in(ptr, alloc) };
    /// ```
    /// Manual cleanup by explicitly running the destructor and deallocating
    /// the memory:
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::{Allocator, Layout, System};
    /// use std::ptr::{self, NonNull};
    ///
    /// let x = Box::new_in(String::from("Hello"), System);
    /// let (ptr, alloc) = Box::into_raw_with_allocator(x);
    /// unsafe {
    ///     ptr::drop_in_place(ptr);
    ///     let non_null = NonNull::new_unchecked(ptr);
    ///     alloc.deallocate(non_null.cast(), Layout::new::<String>());
    /// }
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[must_use = "losing the pointer will leak memory"]
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn into_raw_with_allocator(b: Self) -> (*mut T, A) {
        let mut b = mem::ManuallyDrop::new(b);
        // We carefully get the raw pointer out in a way that Miri's aliasing model understands what
        // is happening: using the primitive "deref" of `Box`. In case `A` is *not* `Global`, we
        // want *no* aliasing requirements here!
        // In case `A` *is* `Global`, this does not quite have the right behavior; `into_raw`
        // works around that.
        let ptr = &raw mut **b;
        let alloc = unsafe { ptr::read(&b.1) };
        (ptr, alloc)
    }

    /// Consumes the `Box`, returning a wrapped `NonNull` pointer and the allocator.
    ///
    /// The pointer will be properly aligned.
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Box`. In particular, the
    /// caller should properly destroy `T` and release the memory, taking
    /// into account the [memory layout] used by `Box`. The easiest way to
    /// do this is to convert the `NonNull` pointer back into a `Box` with the
    /// [`Box::from_non_null_in`] function, allowing the `Box` destructor to
    /// perform the cleanup.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::into_non_null_with_allocator(b)` instead of
    /// `b.into_non_null_with_allocator()`. This is so that there is no
    /// conflict with a method on the inner type.
    ///
    /// # Examples
    /// Converting the `NonNull` pointer back into a `Box` with
    /// [`Box::from_non_null_in`] for automatic cleanup:
    /// ```
    /// #![feature(allocator_api, box_vec_non_null)]
    ///
    /// use std::alloc::System;
    ///
    /// let x = Box::new_in(String::from("Hello"), System);
    /// let (non_null, alloc) = Box::into_non_null_with_allocator(x);
    /// let x = unsafe { Box::from_non_null_in(non_null, alloc) };
    /// ```
    /// Manual cleanup by explicitly running the destructor and deallocating
    /// the memory:
    /// ```
    /// #![feature(allocator_api, box_vec_non_null)]
    ///
    /// use std::alloc::{Allocator, Layout, System};
    ///
    /// let x = Box::new_in(String::from("Hello"), System);
    /// let (non_null, alloc) = Box::into_non_null_with_allocator(x);
    /// unsafe {
    ///     non_null.drop_in_place();
    ///     alloc.deallocate(non_null.cast::<u8>(), Layout::new::<String>());
    /// }
    /// ```
    ///
    /// [memory layout]: self#memory-layout
    #[must_use = "losing the pointer will leak memory"]
    #[unstable(feature = "allocator_api", issue = "32838")]
    // #[unstable(feature = "box_vec_non_null", reason = "new API", issue = "130364")]
    #[inline]
    pub fn into_non_null_with_allocator(b: Self) -> (NonNull<T>, A) {
        let (ptr, alloc) = Box::into_raw_with_allocator(b);
        // SAFETY: `Box` is guaranteed to be non-null.
        unsafe { (NonNull::new_unchecked(ptr), alloc) }
    }

    #[unstable(
        feature = "ptr_internals",
        issue = "none",
        reason = "use `Box::leak(b).into()` or `Unique::from(Box::leak(b))` instead"
    )]
    #[inline]
    #[doc(hidden)]
    pub fn into_unique(b: Self) -> (Unique<T>, A) {
        let (ptr, alloc) = Box::into_raw_with_allocator(b);
        unsafe { (Unique::from(&mut *ptr), alloc) }
    }

    /// Returns a raw mutable pointer to the `Box`'s contents.
    ///
    /// The caller must ensure that the `Box` outlives the pointer this
    /// function returns, or else it will end up dangling.
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying memory, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`] and [`as_mut_ptr`].
    /// Note that calling other methods that materialize references to the memory
    /// may still invalidate this pointer.
    /// See the example below for how this guarantee can be used.
    ///
    /// # Examples
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    /// #![feature(box_as_ptr)]
    ///
    /// unsafe {
    ///     let mut b = Box::new(0);
    ///     let ptr1 = Box::as_mut_ptr(&mut b);
    ///     ptr1.write(1);
    ///     let ptr2 = Box::as_mut_ptr(&mut b);
    ///     ptr2.write(2);
    ///     // Notably, the write to `ptr2` did *not* invalidate `ptr1`:
    ///     ptr1.write(3);
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    /// [`as_ptr`]: Self::as_ptr
    #[unstable(feature = "box_as_ptr", issue = "129090")]
    #[rustc_never_returns_null_ptr]
    #[rustc_as_ptr]
    #[inline]
    pub fn as_mut_ptr(b: &mut Self) -> *mut T {
        // This is a primitive deref, not going through `DerefMut`, and therefore not materializing
        // any references.
        &raw mut **b
    }

    /// Returns a raw pointer to the `Box`'s contents.
    ///
    /// The caller must ensure that the `Box` outlives the pointer this
    /// function returns, or else it will end up dangling.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to
    /// is never written to (except inside an `UnsafeCell`) using this pointer or any pointer
    /// derived from it. If you need to mutate the contents of the `Box`, use [`as_mut_ptr`].
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying memory, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`] and [`as_mut_ptr`].
    /// Note that calling other methods that materialize mutable references to the memory,
    /// as well as writing to this memory, may still invalidate this pointer.
    /// See the example below for how this guarantee can be used.
    ///
    /// # Examples
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    /// #![feature(box_as_ptr)]
    ///
    /// unsafe {
    ///     let mut v = Box::new(0);
    ///     let ptr1 = Box::as_ptr(&v);
    ///     let ptr2 = Box::as_mut_ptr(&mut v);
    ///     let _val = ptr2.read();
    ///     // No write to this memory has happened yet, so `ptr1` is still valid.
    ///     let _val = ptr1.read();
    ///     // However, once we do a write...
    ///     ptr2.write(1);
    ///     // ... `ptr1` is no longer valid.
    ///     // This would be UB: let _val = ptr1.read();
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    /// [`as_ptr`]: Self::as_ptr
    #[unstable(feature = "box_as_ptr", issue = "129090")]
    #[rustc_never_returns_null_ptr]
    #[rustc_as_ptr]
    #[inline]
    pub fn as_ptr(b: &Self) -> *const T {
        // This is a primitive deref, not going through `DerefMut`, and therefore not materializing
        // any references.
        &raw const **b
    }

    /// Returns a reference to the underlying allocator.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::allocator(&b)` instead of `b.allocator()`. This
    /// is so that there is no conflict with a method on the inner type.
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn allocator(b: &Self) -> &A {
        &b.1
    }

    /// Consumes and leaks the `Box`, returning a mutable reference,
    /// `&'a mut T`.
    ///
    /// Note that the type `T` must outlive the chosen lifetime `'a`. If the type
    /// has only static references, or none at all, then this may be chosen to be
    /// `'static`.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak. If this is not acceptable, the reference should first be wrapped
    /// with the [`Box::from_raw`] function producing a `Box`. This `Box` can
    /// then be dropped which will properly destroy `T` and release the
    /// allocated memory.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::leak(b)` instead of `b.leak()`. This
    /// is so that there is no conflict with a method on the inner type.
    ///
    /// # Examples
    ///
    /// Simple usage:
    ///
    /// ```
    /// let x = Box::new(41);
    /// let static_ref: &'static mut usize = Box::leak(x);
    /// *static_ref += 1;
    /// assert_eq!(*static_ref, 42);
    /// # // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// # // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// # drop(unsafe { Box::from_raw(static_ref) });
    /// ```
    ///
    /// Unsized data:
    ///
    /// ```
    /// let x = vec![1, 2, 3].into_boxed_slice();
    /// let static_ref = Box::leak(x);
    /// static_ref[0] = 4;
    /// assert_eq!(*static_ref, [4, 2, 3]);
    /// # // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// # // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// # drop(unsafe { Box::from_raw(static_ref) });
    /// ```
    #[stable(feature = "box_leak", since = "1.26.0")]
    #[inline]
    pub fn leak<'a>(b: Self) -> &'a mut T
    where
        A: 'a,
    {
        let (ptr, alloc) = Box::into_raw_with_allocator(b);
        mem::forget(alloc);
        unsafe { &mut *ptr }
    }

    /// Converts a `Box<T>` into a `Pin<Box<T>>`. If `T` does not implement [`Unpin`], then
    /// `*boxed` will be pinned in memory and unable to be moved.
    ///
    /// This conversion does not allocate on the heap and happens in place.
    ///
    /// This is also available via [`From`].
    ///
    /// Constructing and pinning a `Box` with <code>Box::into_pin([Box::new]\(x))</code>
    /// can also be written more concisely using <code>[Box::pin]\(x)</code>.
    /// This `into_pin` method is useful if you already have a `Box<T>`, or you are
    /// constructing a (pinned) `Box` in a different way than with [`Box::new`].
    ///
    /// # Notes
    ///
    /// It's not recommended that crates add an impl like `From<Box<T>> for Pin<T>`,
    /// as it'll introduce an ambiguity when calling `Pin::from`.
    /// A demonstration of such a poor impl is shown below.
    ///
    /// ```compile_fail
    /// # use std::pin::Pin;
    /// struct Foo; // A type defined in this crate.
    /// impl From<Box<()>> for Pin<Foo> {
    ///     fn from(_: Box<()>) -> Pin<Foo> {
    ///         Pin::new(Foo)
    ///     }
    /// }
    ///
    /// let foo = Box::new(());
    /// let bar = Pin::from(foo);
    /// ```
    #[stable(feature = "box_into_pin", since = "1.63.0")]
    pub fn into_pin(boxed: Self) -> Pin<Self>
    where
        A: 'static,
    {
        // It's not possible to move or replace the insides of a `Pin<Box<T>>`
        // when `T: !Unpin`, so it's safe to pin it directly without any
        // additional requirements.
        unsafe { Pin::new_unchecked(boxed) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<#[may_dangle] T: ?Sized, A: Allocator> Drop for Box<T, A> {
    #[inline]
    fn drop(&mut self) {
        // the T in the Box is dropped by the compiler before the destructor is run

        let ptr = self.0;

        unsafe {
            let layout = Layout::for_value_raw(ptr.as_ptr());
            if layout.size() != 0 {
                self.1.deallocate(From::from(ptr.cast()), layout);
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Default> Default for Box<T> {
    /// Creates a `Box<T>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        let mut x: Box<mem::MaybeUninit<T>> = Box::new_uninit();
        unsafe {
            // SAFETY: `x` is valid for writing and has the same layout as `T`.
            // If `T::default()` panics, dropping `x` will just deallocate the Box as `MaybeUninit<T>`
            // does not have a destructor.
            //
            // We use `ptr::write` as `MaybeUninit::write` creates
            // extra stack copies of `T` in debug mode.
            //
            // See https://github.com/rust-lang/rust/issues/136043 for more context.
            ptr::write(&raw mut *x as *mut T, T::default());
            // SAFETY: `x` was just initialized above.
            x.assume_init()
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Default for Box<[T]> {
    /// Creates an empty `[T]` inside a `Box`.
    #[inline]
    fn default() -> Self {
        let ptr: Unique<[T]> = Unique::<[T; 0]>::dangling();
        Box(ptr, Global)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "default_box_extra", since = "1.17.0")]
impl Default for Box<str> {
    #[inline]
    fn default() -> Self {
        // SAFETY: This is the same as `Unique::cast<U>` but with an unsized `U = str`.
        let ptr: Unique<str> = unsafe {
            let bytes: Unique<[u8]> = Unique::<[u8; 0]>::dangling();
            Unique::new_unchecked(bytes.as_ptr() as *mut str)
        };
        Box(ptr, Global)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "pin_default_impls", since = "1.91.0")]
impl<T> Default for Pin<Box<T>>
where
    T: ?Sized,
    Box<T>: Default,
{
    #[inline]
    fn default() -> Self {
        Box::into_pin(Box::<T>::default())
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone, A: Allocator + Clone> Clone for Box<T, A> {
    /// Returns a new box with a `clone()` of this box's contents.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = Box::new(5);
    /// let y = x.clone();
    ///
    /// // The value is the same
    /// assert_eq!(x, y);
    ///
    /// // But they are unique objects
    /// assert_ne!(&*x as *const i32, &*y as *const i32);
    /// ```
    #[inline]
    fn clone(&self) -> Self {
        // Pre-allocate memory to allow writing the cloned value directly.
        let mut boxed = Self::new_uninit_in(self.1.clone());
        unsafe {
            (**self).clone_to_uninit(boxed.as_mut_ptr().cast());
            boxed.assume_init()
        }
    }

    /// Copies `source`'s contents into `self` without creating a new allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = Box::new(5);
    /// let mut y = Box::new(10);
    /// let yp: *const i32 = &*y;
    ///
    /// y.clone_from(&x);
    ///
    /// // The value is the same
    /// assert_eq!(x, y);
    ///
    /// // And no allocation occurred
    /// assert_eq!(yp, &*y);
    /// ```
    #[inline]
    fn clone_from(&mut self, source: &Self) {
        (**self).clone_from(&(**source));
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_slice_clone", since = "1.3.0")]
impl<T: Clone, A: Allocator + Clone> Clone for Box<[T], A> {
    fn clone(&self) -> Self {
        let alloc = Box::allocator(self).clone();
        self.to_vec_in(alloc).into_boxed_slice()
    }

    /// Copies `source`'s contents into `self` without creating a new allocation,
    /// so long as the two are of the same length.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = Box::new([5, 6, 7]);
    /// let mut y = Box::new([8, 9, 10]);
    /// let yp: *const [i32] = &*y;
    ///
    /// y.clone_from(&x);
    ///
    /// // The value is the same
    /// assert_eq!(x, y);
    ///
    /// // And no allocation occurred
    /// assert_eq!(yp, &*y);
    /// ```
    fn clone_from(&mut self, source: &Self) {
        if self.len() == source.len() {
            self.clone_from_slice(&source);
        } else {
            *self = source.clone();
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_slice_clone", since = "1.3.0")]
impl Clone for Box<str> {
    fn clone(&self) -> Self {
        // this makes a copy of the data
        let buf: Box<[u8]> = self.as_bytes().into();
        unsafe { from_boxed_utf8_unchecked(buf) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + PartialEq, A: Allocator> PartialEq for Box<T, A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&**self, &**other)
    }
    #[inline]
    fn ne(&self, other: &Self) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + PartialOrd, A: Allocator> PartialOrd for Box<T, A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
    #[inline]
    fn lt(&self, other: &Self) -> bool {
        PartialOrd::lt(&**self, &**other)
    }
    #[inline]
    fn le(&self, other: &Self) -> bool {
        PartialOrd::le(&**self, &**other)
    }
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        PartialOrd::ge(&**self, &**other)
    }
    #[inline]
    fn gt(&self, other: &Self) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Ord, A: Allocator> Ord for Box<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Eq, A: Allocator> Eq for Box<T, A> {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Hash, A: Allocator> Hash for Box<T, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

#[stable(feature = "indirect_hasher_impl", since = "1.22.0")]
impl<T: ?Sized + Hasher, A: Allocator> Hasher for Box<T, A> {
    fn finish(&self) -> u64 {
        (**self).finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes)
    }
    fn write_u8(&mut self, i: u8) {
        (**self).write_u8(i)
    }
    fn write_u16(&mut self, i: u16) {
        (**self).write_u16(i)
    }
    fn write_u32(&mut self, i: u32) {
        (**self).write_u32(i)
    }
    fn write_u64(&mut self, i: u64) {
        (**self).write_u64(i)
    }
    fn write_u128(&mut self, i: u128) {
        (**self).write_u128(i)
    }
    fn write_usize(&mut self, i: usize) {
        (**self).write_usize(i)
    }
    fn write_i8(&mut self, i: i8) {
        (**self).write_i8(i)
    }
    fn write_i16(&mut self, i: i16) {
        (**self).write_i16(i)
    }
    fn write_i32(&mut self, i: i32) {
        (**self).write_i32(i)
    }
    fn write_i64(&mut self, i: i64) {
        (**self).write_i64(i)
    }
    fn write_i128(&mut self, i: i128) {
        (**self).write_i128(i)
    }
    fn write_isize(&mut self, i: isize) {
        (**self).write_isize(i)
    }
    fn write_length_prefix(&mut self, len: usize) {
        (**self).write_length_prefix(len)
    }
    fn write_str(&mut self, s: &str) {
        (**self).write_str(s)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Display + ?Sized, A: Allocator> fmt::Display for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Debug + ?Sized, A: Allocator> fmt::Debug for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized, A: Allocator> fmt::Pointer for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // It's not possible to extract the inner Uniq directly from the Box,
        // instead we cast it to a *const which aliases the Unique
        let ptr: *const T = &**self;
        fmt::Pointer::fmt(&ptr, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized, A: Allocator> Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T {
        &**self
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized, A: Allocator> DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T {
        &mut **self
    }
}

#[unstable(feature = "deref_pure_trait", issue = "87121")]
unsafe impl<T: ?Sized, A: Allocator> DerefPure for Box<T, A> {}

#[unstable(feature = "legacy_receiver_trait", issue = "none")]
impl<T: ?Sized, A: Allocator> LegacyReceiver for Box<T, A> {}

#[stable(feature = "boxed_closure_impls", since = "1.35.0")]
impl<Args: Tuple, F: FnOnce<Args> + ?Sized, A: Allocator> FnOnce<Args> for Box<F, A> {
    type Output = <F as FnOnce<Args>>::Output;

    extern "rust-call" fn call_once(self, args: Args) -> Self::Output {
        <F as FnOnce<Args>>::call_once(*self, args)
    }
}

#[stable(feature = "boxed_closure_impls", since = "1.35.0")]
impl<Args: Tuple, F: FnMut<Args> + ?Sized, A: Allocator> FnMut<Args> for Box<F, A> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output {
        <F as FnMut<Args>>::call_mut(self, args)
    }
}

#[stable(feature = "boxed_closure_impls", since = "1.35.0")]
impl<Args: Tuple, F: Fn<Args> + ?Sized, A: Allocator> Fn<Args> for Box<F, A> {
    extern "rust-call" fn call(&self, args: Args) -> Self::Output {
        <F as Fn<Args>>::call(self, args)
    }
}

#[stable(feature = "async_closure", since = "1.85.0")]
impl<Args: Tuple, F: AsyncFnOnce<Args> + ?Sized, A: Allocator> AsyncFnOnce<Args> for Box<F, A> {
    type Output = F::Output;
    type CallOnceFuture = F::CallOnceFuture;

    extern "rust-call" fn async_call_once(self, args: Args) -> Self::CallOnceFuture {
        F::async_call_once(*self, args)
    }
}

#[stable(feature = "async_closure", since = "1.85.0")]
impl<Args: Tuple, F: AsyncFnMut<Args> + ?Sized, A: Allocator> AsyncFnMut<Args> for Box<F, A> {
    type CallRefFuture<'a>
        = F::CallRefFuture<'a>
    where
        Self: 'a;

    extern "rust-call" fn async_call_mut(&mut self, args: Args) -> Self::CallRefFuture<'_> {
        F::async_call_mut(self, args)
    }
}

#[stable(feature = "async_closure", since = "1.85.0")]
impl<Args: Tuple, F: AsyncFn<Args> + ?Sized, A: Allocator> AsyncFn<Args> for Box<F, A> {
    extern "rust-call" fn async_call(&self, args: Args) -> Self::CallRefFuture<'_> {
        F::async_call(self, args)
    }
}

#[unstable(feature = "coerce_unsized", issue = "18598")]
impl<T: ?Sized + Unsize<U>, U: ?Sized, A: Allocator> CoerceUnsized<Box<U, A>> for Box<T, A> {}

#[unstable(feature = "pin_coerce_unsized_trait", issue = "123430")]
unsafe impl<T: ?Sized, A: Allocator> PinCoerceUnsized for Box<T, A> {}

// It is quite crucial that we only allow the `Global` allocator here.
// Handling arbitrary custom allocators (which can affect the `Box` layout heavily!)
// would need a lot of codegen and interpreter adjustments.
#[unstable(feature = "dispatch_from_dyn", issue = "none")]
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<Box<U>> for Box<T, Global> {}

#[stable(feature = "box_borrow", since = "1.1.0")]
impl<T: ?Sized, A: Allocator> Borrow<T> for Box<T, A> {
    fn borrow(&self) -> &T {
        &**self
    }
}

#[stable(feature = "box_borrow", since = "1.1.0")]
impl<T: ?Sized, A: Allocator> BorrowMut<T> for Box<T, A> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}

#[stable(since = "1.5.0", feature = "smart_ptr_as_ref")]
impl<T: ?Sized, A: Allocator> AsRef<T> for Box<T, A> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

#[stable(since = "1.5.0", feature = "smart_ptr_as_ref")]
impl<T: ?Sized, A: Allocator> AsMut<T> for Box<T, A> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}

/* Nota bene
 *
 *  We could have chosen not to add this impl, and instead have written a
 *  function of Pin<Box<T>> to Pin<T>. Such a function would not be sound,
 *  because Box<T> implements Unpin even when T does not, as a result of
 *  this impl.
 *
 *  We chose this API instead of the alternative for a few reasons:
 *      - Logically, it is helpful to understand pinning in regard to the
 *        memory region being pointed to. For this reason none of the
 *        standard library pointer types support projecting through a pin
 *        (Box<T> is the only pointer type in std for which this would be
 *        safe.)
 *      - It is in practice very useful to have Box<T> be unconditionally
 *        Unpin because of trait objects, for which the structural auto
 *        trait functionality does not apply (e.g., Box<dyn Foo> would
 *        otherwise not be Unpin).
 *
 *  Another type with the same semantics as Box but only a conditional
 *  implementation of `Unpin` (where `T: Unpin`) would be valid/safe, and
 *  could have a method to project a Pin<T> from it.
 */
#[stable(feature = "pin", since = "1.33.0")]
impl<T: ?Sized, A: Allocator> Unpin for Box<T, A> {}

#[unstable(feature = "coroutine_trait", issue = "43122")]
impl<G: ?Sized + Coroutine<R> + Unpin, R, A: Allocator> Coroutine<R> for Box<G, A> {
    type Yield = G::Yield;
    type Return = G::Return;

    fn resume(mut self: Pin<&mut Self>, arg: R) -> CoroutineState<Self::Yield, Self::Return> {
        G::resume(Pin::new(&mut *self), arg)
    }
}

#[unstable(feature = "coroutine_trait", issue = "43122")]
impl<G: ?Sized + Coroutine<R>, R, A: Allocator> Coroutine<R> for Pin<Box<G, A>>
where
    A: 'static,
{
    type Yield = G::Yield;
    type Return = G::Return;

    fn resume(mut self: Pin<&mut Self>, arg: R) -> CoroutineState<Self::Yield, Self::Return> {
        G::resume((*self).as_mut(), arg)
    }
}

#[stable(feature = "futures_api", since = "1.36.0")]
impl<F: ?Sized + Future + Unpin, A: Allocator> Future for Box<F, A> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        F::poll(Pin::new(&mut *self), cx)
    }
}

#[stable(feature = "box_error", since = "1.8.0")]
impl<E: Error> Error for Box<E> {
    #[allow(deprecated)]
    fn cause(&self) -> Option<&dyn Error> {
        Error::cause(&**self)
    }

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Error::source(&**self)
    }

    fn provide<'b>(&'b self, request: &mut error::Request<'b>) {
        Error::provide(&**self, request);
    }
}

// ==============================================================
// Challenge 29: Verify safety of Boxed functions harnesses
// ==============================================================

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod kani_box_harness_helpers {
    use super::*;

    pub(super) fn verifier_nondet_vec<T>() -> Vec<T> {
        let cap: usize = kani::any();
        let elem_layout = Layout::new::<T>();
        kani::assume(elem_layout.repeat(cap).is_ok());
        let mut v = Vec::<T>::with_capacity(cap);
        unsafe {
            let sz: usize = kani::any();
            kani::assume(sz <= cap);
            v.set_len(sz);
            ptr::write_bytes(
                v.as_mut_ptr().cast::<u8>(),
                kani::any::<u8>(),
                mem::size_of::<T>() * sz,
            );
        }
        v
    }

    pub(super) fn box_slice_layout_ok<T>(len: usize) -> bool {
        Layout::array::<T>(len).is_ok()
    }

    pub(super) fn nondet_box_slice<T>(vec: &Vec<T>) -> &[T] {
        let len = vec.len();
        kani::assume(box_slice_layout_ok::<T>(len));
        vec.as_slice()
    }

    pub(super) fn verifier_nondet_vec_box<T>() -> Vec<T> {
        let vec = verifier_nondet_vec();
        kani::assume(box_slice_layout_ok::<T>(vec.len()));
        vec
    }

    pub(super) fn verifier_nondet_box_uninit_slice<T>() -> Box<[mem::MaybeUninit<T>], Global> {
        let len = kani::any_where(|l: &usize| box_slice_layout_ok::<T>(*l));
        let mut boxed = Box::<[T]>::new_uninit_slice(len);
        unsafe {
            ptr::write_bytes(
                boxed.as_mut_ptr().cast::<u8>(),
                kani::any::<u8>(),
                mem::size_of::<T>() * len,
            );
        }
        boxed
    }
}

// === UNSAFE FUNCTIONS ===

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_944 {
    use super::*;

    // Kani limitation: proof_for_contract is not reliable for this
    // MaybeUninit-based generic impl in boxed.rs, so these harnesses use
    // #[kani::proof] and exercise the caller-side safety requirement directly.
    //
    // Kani cannot express the full generic "value is initialized" predicate
    // for arbitrary `T`. The harness models the Safety contract by explicitly
    // writing a valid `T` into the boxed MaybeUninit slot before calling
    // `assume_init`.
    macro_rules! gen_assume_init_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic initialized value of the target type.
                let value: $ty = kani::any::<$ty>();

                // Keep a copy so the initialized result can be compared after conversion.
                let expected = value.clone();

                // Allocate boxed storage for an uninitialized value of the same type.
                let mut uninit: Box<mem::MaybeUninit<$ty>, Global> =
                    Box::<$ty, Global>::new_uninit_in(Global);

                // Write a valid `$ty` into the boxed `MaybeUninit` slot.
                (*uninit).write(value);

                // Convert the boxed `MaybeUninit` into a boxed initialized value.
                let init: Box<$ty, Global> = unsafe { uninit.assume_init() };

                // Check that the recovered value matches the one written into the slot.
                assert_eq!(&*init, &expected);
            }
        };
    }

    gen_assume_init_harness!(harness_box_assume_init_i8, i8);
    gen_assume_init_harness!(harness_box_assume_init_i16, i16);
    gen_assume_init_harness!(harness_box_assume_init_i32, i32);
    gen_assume_init_harness!(harness_box_assume_init_i64, i64);
    gen_assume_init_harness!(harness_box_assume_init_i128, i128);
    gen_assume_init_harness!(harness_box_assume_init_u8, u8);
    gen_assume_init_harness!(harness_box_assume_init_u16, u16);
    gen_assume_init_harness!(harness_box_assume_init_u32, u32);
    gen_assume_init_harness!(harness_box_assume_init_u64, u64);
    gen_assume_init_harness!(harness_box_assume_init_u128, u128);
    gen_assume_init_harness!(harness_box_assume_init_unit, ());
    gen_assume_init_harness!(harness_box_assume_init_array, [u8; 4]);
    gen_assume_init_harness!(harness_box_assume_init_bool, bool);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1011 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    // Kani limitation: proof_for_contract is not reliable for this
    // MaybeUninit-based slice impl in boxed.rs, so these harnesses use
    // #[kani::proof] and exercise the caller-side safety requirement directly.
    //
    // For byte-valid element types, the harness can model the caller-side
    // safety requirement with an unbounded byte-level witness: it constructs a
    // boxed `[MaybeUninit<T>]` slice using Box's own uninitialized slice API,
    // fills the backing bytes nondeterministically, and then converts it to
    // `Box<[T]>`.
    macro_rules! gen_assume_init_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a symbolic boxed slice of `MaybeUninit` elements.
                let uninit: Box<[mem::MaybeUninit<$elem>], Global> =
                    verifier_nondet_box_uninit_slice::<$elem>();

                // Record the original data pointer before the conversion.
                let expected_data = (&*uninit).as_ptr() as *const $elem;

                // Record the original slice length before the conversion.
                let expected_len = uninit.len();

                // Convert the boxed `MaybeUninit` slice into a boxed initialized slice.
                let result: Box<[$elem], Global> = unsafe { uninit.assume_init() };

                // Check that the conversion preserves the backing data pointer.
                assert_eq!((&*result).as_ptr(), expected_data);

                // Check that the conversion preserves the slice length.
                assert_eq!(result.len(), expected_len);
            }
        };
    }

    gen_assume_init_slice_harness!(harness_box_assume_init_slice_i8, i8);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_i16, i16);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_i32, i32);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_i64, i64);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_i128, i128);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_u8, u8);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_u16, u16);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_u32, u32);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_u64, u64);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_u128, u128);
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_unit, ());
    gen_assume_init_slice_harness!(harness_box_assume_init_slice_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1079 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_from_raw_sized_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Box::<$ty>::from_raw)]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build a boxed value whose allocation will become the raw witness.
                let boxed: Box<$ty> = Box::new(value);

                // Consume the box and extract the raw pointer expected by `from_raw`.
                let ptr: *mut $ty = Box::into_raw(boxed);

                // Rebuild ownership from the raw pointer.
                let _recovered: Box<$ty> = unsafe { Box::from_raw(ptr) };
            }
        };
    }

    macro_rules! gen_from_raw_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof_for_contract(Box::<[$elem]>::from_raw)]
            pub fn $name() {
                // Build a symbolic boxed slice of the target element type.
                let boxed: Box<[$elem]> = verifier_nondet_vec_box::<$elem>().into_boxed_slice();

                // Consume the boxed slice and extract the raw fat pointer.
                let ptr: *mut [$elem] = Box::into_raw(boxed);

                // Rebuild ownership from the raw slice pointer.
                let _recovered: Box<[$elem]> = unsafe { Box::from_raw(ptr) };
            }
        };
    }

    gen_from_raw_sized_harness!(harness_box_from_raw_i8, i8);
    gen_from_raw_sized_harness!(harness_box_from_raw_i16, i16);
    gen_from_raw_sized_harness!(harness_box_from_raw_i32, i32);
    gen_from_raw_sized_harness!(harness_box_from_raw_i64, i64);
    gen_from_raw_sized_harness!(harness_box_from_raw_i128, i128);
    gen_from_raw_sized_harness!(harness_box_from_raw_u8, u8);
    gen_from_raw_sized_harness!(harness_box_from_raw_u16, u16);
    gen_from_raw_sized_harness!(harness_box_from_raw_u32, u32);
    gen_from_raw_sized_harness!(harness_box_from_raw_u64, u64);
    gen_from_raw_sized_harness!(harness_box_from_raw_u128, u128);
    gen_from_raw_sized_harness!(harness_box_from_raw_bool, bool);
    gen_from_raw_sized_harness!(harness_box_from_raw_unit, ());
    gen_from_raw_sized_harness!(harness_box_from_raw_array, [u8; 4]);

    gen_from_raw_unsized_harness!(harness_box_from_raw_vec_u8, u8);
    gen_from_raw_unsized_harness!(harness_box_from_raw_vec_u16, u16);
    gen_from_raw_unsized_harness!(harness_box_from_raw_vec_u32, u32);
    gen_from_raw_unsized_harness!(harness_box_from_raw_vec_u64, u64);
    gen_from_raw_unsized_harness!(harness_box_from_raw_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1147 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_from_non_null_sized_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Box::<$ty>::from_non_null)]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build a boxed value whose allocation will become the non-null witness.
                let boxed: Box<$ty> = Box::new(value);

                // Consume the box and extract the non-null pointer expected by `from_non_null`.
                let ptr: NonNull<$ty> = Box::into_non_null(boxed);

                // Rebuild ownership from the non-null pointer.
                let _recovered: Box<$ty> = unsafe { Box::from_non_null(ptr) };
            }
        };
    }

    macro_rules! gen_from_non_null_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof_for_contract(Box::<[$elem]>::from_non_null)]
            pub fn $name() {
                // Build a symbolic boxed slice of the target element type.
                let boxed: Box<[$elem]> = verifier_nondet_vec_box::<$elem>().into_boxed_slice();

                // Consume the boxed slice and extract the non-null fat pointer.
                let ptr: NonNull<[$elem]> = Box::into_non_null(boxed);

                // Rebuild ownership from the non-null slice pointer.
                let _recovered: Box<[$elem]> = unsafe { Box::from_non_null(ptr) };
            }
        };
    }

    gen_from_non_null_sized_harness!(harness_box_from_non_null_i8, i8);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_i16, i16);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_i32, i32);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_i64, i64);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_i128, i128);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_u8, u8);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_u16, u16);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_u32, u32);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_u64, u64);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_u128, u128);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_bool, bool);
    gen_from_non_null_sized_harness!(harness_box_from_non_null_unit, ());
    gen_from_non_null_sized_harness!(harness_box_from_non_null_array, [u8; 4]);

    gen_from_non_null_unsized_harness!(harness_box_from_non_null_vec_u8, u8);
    gen_from_non_null_unsized_harness!(harness_box_from_non_null_vec_u16, u16);
    gen_from_non_null_unsized_harness!(harness_box_from_non_null_vec_u32, u32);
    gen_from_non_null_unsized_harness!(harness_box_from_non_null_vec_u64, u64);
    gen_from_non_null_unsized_harness!(harness_box_from_non_null_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1306 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    // These harnesses allocate raw memory directly instead of using higher-level
    // Box constructors. `proof_for_contract` requires a single top-level call to
    // `Box::from_raw_in`, while helpers such as `Box::new_in`,
    // `Box::new_uninit_slice_in`, and `Vec::into_boxed_slice` eventually route
    // through `Box::from_raw_in` during setup.

    macro_rules! gen_from_raw_in_sized_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Box::<$ty, Global>::from_raw_in)]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build a raw pointer that satisfies the contract without using
                // `Box::new_in`, which would internally call `Box::from_raw_in`.
                let ptr: *mut $ty = if mem::size_of::<$ty>() == 0 {
                    // ZST boxes use a non-null dangling pointer and never allocate.
                    mem::forget(value);
                    NonNull::<$ty>::dangling().as_ptr()
                } else {
                    let layout = Layout::new::<$ty>();
                    // Allocate backing memory with the same allocator passed to
                    // the function under test, then initialize it with a valid `$ty`.
                    let ptr = match Global.allocate(layout) {
                        Ok(memory) => memory.cast::<$ty>().as_ptr(),
                        Err(_) => handle_alloc_error(layout),
                    };
                    unsafe { ptr.write(value) };
                    ptr
                };

                // Use the same allocator witness that was used to produce the raw pointer.
                let alloc = Global;

                // Rebuild ownership from the raw pointer and allocator pair.
                let _recovered: Box<$ty, Global> = unsafe { Box::from_raw_in(ptr, alloc) };
            }
        };
    }

    macro_rules! gen_from_raw_in_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof_for_contract(Box::<[$elem], Global>::from_raw_in)]
            pub fn $name() {
                // Keep the slice length symbolic so this remains an unbound
                // unsized harness, while still ruling out impossible layouts.
                let len: usize = kani::any_where(|len: &usize| box_slice_layout_ok::<$elem>(*len));

                let data: *mut $elem = if len == 0 {
                    // Empty slices use a non-null dangling data pointer.
                    NonNull::<$elem>::dangling().as_ptr()
                } else {
                    let layout = Layout::array::<$elem>(len).unwrap();
                    // Allocate raw backing storage for `len` elements with the
                    // allocator that will later be given to `from_raw_in`.
                    let ptr = match Global.allocate(layout) {
                        Ok(memory) => memory.cast::<$elem>().as_ptr(),
                        Err(_) => handle_alloc_error(layout),
                    };
                    unsafe {
                        // Fill the allocation with unconstrained bytes before
                        // packaging it as a raw slice pointer.
                        ptr::write_bytes(
                            ptr.cast::<u8>(),
                            kani::any::<u8>(),
                            mem::size_of::<$elem>() * len,
                        );
                    }
                    ptr
                };

                // Rebuild the fat pointer expected by `Box<[T]>::from_raw_in`
                // from the data pointer plus symbolic slice length.
                let ptr: *mut [$elem] = ptr::slice_from_raw_parts_mut(data, len);

                // Use the same allocator witness that was used to produce the backing storage.
                let alloc = Global;

                // Rebuild ownership from the raw slice pointer and allocator pair.
                let _recovered: Box<[$elem], Global> = unsafe { Box::from_raw_in(ptr, alloc) };
            }
        };
    }

    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_i8, i8);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_i16, i16);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_i32, i32);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_i64, i64);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_i128, i128);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_u8, u8);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_u16, u16);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_u32, u32);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_u64, u64);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_u128, u128);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_bool, bool);
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_unit, ());
    gen_from_raw_in_sized_harness!(harness_box_from_raw_in_array, [u8; 4]);

    gen_from_raw_in_unsized_harness!(harness_box_from_raw_in_vec_u8, u8);
    gen_from_raw_in_unsized_harness!(harness_box_from_raw_in_vec_u16, u16);
    gen_from_raw_in_unsized_harness!(harness_box_from_raw_in_vec_u32, u32);
    gen_from_raw_in_unsized_harness!(harness_box_from_raw_in_vec_u64, u64);
    gen_from_raw_in_unsized_harness!(harness_box_from_raw_in_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1405 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_from_non_null_in_sized_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Box::<$ty, Global>::from_non_null_in)]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value whose allocation will become the non-null witness.
                let boxed: Box<$ty, Global> = Box::new_in(value, Global);

                // Consume the box and extract the non-null pointer together with its allocator.
                let (ptr, alloc): (NonNull<$ty>, Global) = Box::into_non_null_with_allocator(boxed);

                // Rebuild ownership from the non-null pointer and allocator pair.
                let _recovered: Box<$ty, Global> = unsafe { Box::from_non_null_in(ptr, alloc) };
            }
        };
    }

    macro_rules! gen_from_non_null_in_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof_for_contract(Box::<[$elem], Global>::from_non_null_in)]
            pub fn $name() {
                // Build a symbolic boxed slice of the target element type.
                let boxed: Box<[$elem], Global> =
                    verifier_nondet_vec_box::<$elem>().into_boxed_slice();

                // Consume the boxed slice and extract the non-null fat pointer together with its allocator.
                let (ptr, alloc): (NonNull<[$elem]>, Global) =
                    Box::into_non_null_with_allocator(boxed);

                // Rebuild ownership from the non-null slice pointer and allocator pair.
                let _recovered: Box<[$elem], Global> = unsafe { Box::from_non_null_in(ptr, alloc) };
            }
        };
    }

    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_i8, i8);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_i16, i16);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_i32, i32);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_i64, i64);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_i128, i128);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_u8, u8);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_u16, u16);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_u32, u32);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_u64, u64);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_u128, u128);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_bool, bool);
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_unit, ());
    gen_from_non_null_in_sized_harness!(harness_box_from_non_null_in_array, [u8; 4]);

    gen_from_non_null_in_unsized_harness!(harness_box_from_non_null_in_vec_u8, u8);
    gen_from_non_null_in_unsized_harness!(harness_box_from_non_null_in_vec_u16, u16);
    gen_from_non_null_in_unsized_harness!(harness_box_from_non_null_in_vec_u32, u32);
    gen_from_non_null_in_unsized_harness!(harness_box_from_non_null_in_vec_u64, u64);
    gen_from_non_null_in_unsized_harness!(harness_box_from_non_null_in_vec_u128, u128);
}

// === SAFE FUNCTIONS ===

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_410 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_new_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic input value of the target element type.
                let value: $ty = kani::any();

                // Call the safe constructor with the global allocator.
                let _boxed: Box<$ty, Global> = Box::<$ty, Global>::new_in(value, Global);
            }
        };
    }

    macro_rules! gen_box_new_in_vec_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector payload for the boxed value.
                let vec: Vec<$elem> = verifier_nondet_vec::<$elem>();

                // Call the safe constructor with the global allocator.
                let _boxed: Box<Vec<$elem>, Global> =
                    Box::<Vec<$elem>, Global>::new_in(vec, Global);
            }
        };
    }

    gen_box_new_in_harness!(harness_box_new_in_i8, i8);
    gen_box_new_in_harness!(harness_box_new_in_i16, i16);
    gen_box_new_in_harness!(harness_box_new_in_i32, i32);
    gen_box_new_in_harness!(harness_box_new_in_i64, i64);
    gen_box_new_in_harness!(harness_box_new_in_i128, i128);
    gen_box_new_in_harness!(harness_box_new_in_u8, u8);
    gen_box_new_in_harness!(harness_box_new_in_u16, u16);
    gen_box_new_in_harness!(harness_box_new_in_u32, u32);
    gen_box_new_in_harness!(harness_box_new_in_u64, u64);
    gen_box_new_in_harness!(harness_box_new_in_u128, u128);
    gen_box_new_in_harness!(harness_box_new_in_unit, ());
    gen_box_new_in_harness!(harness_box_new_in_array, [u8; 4]);
    gen_box_new_in_harness!(harness_box_new_in_bool, bool);

    gen_box_new_in_vec_harness!(harness_box_new_in_vec_u8, u8);
    gen_box_new_in_vec_harness!(harness_box_new_in_vec_u16, u16);
    gen_box_new_in_vec_harness!(harness_box_new_in_vec_u32, u32);
    gen_box_new_in_vec_harness!(harness_box_new_in_vec_u64, u64);
    gen_box_new_in_vec_harness!(harness_box_new_in_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_436 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_try_new_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic input value of the target element type.
                let value: $ty = kani::any();

                // Call the fallible safe constructor with the global allocator.
                let _result = Box::<$ty, Global>::try_new_in(value, Global);
            }
        };
    }

    macro_rules! gen_box_try_new_in_vec_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector payload for the boxed value.
                let vec: Vec<$elem> = verifier_nondet_vec::<$elem>();

                // Call the fallible safe constructor with the global allocator.
                let _result = Box::<Vec<$elem>, Global>::try_new_in(vec, Global);
            }
        };
    }

    gen_box_try_new_in_harness!(harness_box_try_new_in_i8, i8);
    gen_box_try_new_in_harness!(harness_box_try_new_in_i16, i16);
    gen_box_try_new_in_harness!(harness_box_try_new_in_i32, i32);
    gen_box_try_new_in_harness!(harness_box_try_new_in_i64, i64);
    gen_box_try_new_in_harness!(harness_box_try_new_in_i128, i128);
    gen_box_try_new_in_harness!(harness_box_try_new_in_u8, u8);
    gen_box_try_new_in_harness!(harness_box_try_new_in_u16, u16);
    gen_box_try_new_in_harness!(harness_box_try_new_in_u32, u32);
    gen_box_try_new_in_harness!(harness_box_try_new_in_u64, u64);
    gen_box_try_new_in_harness!(harness_box_try_new_in_u128, u128);
    gen_box_try_new_in_harness!(harness_box_try_new_in_unit, ());
    gen_box_try_new_in_harness!(harness_box_try_new_in_array, [u8; 4]);
    gen_box_try_new_in_harness!(harness_box_try_new_in_bool, bool);

    gen_box_try_new_in_vec_harness!(harness_box_try_new_in_vec_u8, u8);
    gen_box_try_new_in_vec_harness!(harness_box_try_new_in_vec_u16, u16);
    gen_box_try_new_in_vec_harness!(harness_box_try_new_in_vec_u32, u32);
    gen_box_try_new_in_vec_harness!(harness_box_try_new_in_vec_u64, u64);
    gen_box_try_new_in_vec_harness!(harness_box_try_new_in_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_496 {
    use super::*;

    macro_rules! gen_box_try_new_uninit_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Call the fallible uninitialized constructor with the global allocator.
                let _result = Box::<$ty, Global>::try_new_uninit_in(Global);
            }
        };
    }

    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_i8, i8);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_i16, i16);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_i32, i32);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_i64, i64);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_i128, i128);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_u8, u8);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_u16, u16);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_u32, u32);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_u64, u64);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_u128, u128);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_unit, ());
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_array, [u8; 4]);
    gen_box_try_new_uninit_in_harness!(harness_box_try_new_uninit_in_bool, bool);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_568 {
    use super::*;

    macro_rules! gen_box_try_new_zeroed_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Call the fallible zeroed constructor with the global allocator.
                let _result = Box::<$ty, Global>::try_new_zeroed_in(Global);
            }
        };
    }

    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_i8, i8);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_i16, i16);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_i32, i32);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_i64, i64);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_i128, i128);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_u8, u8);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_u16, u16);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_u32, u32);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_u64, u64);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_u128, u128);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_unit, ());
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_array, [u8; 4]);
    gen_box_try_new_zeroed_in_harness!(harness_box_try_new_zeroed_in_bool, bool);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_603 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_into_boxed_slice_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic input value of the target element type.
                let value: $ty = kani::any();

                // Build the boxed scalar value that will be reinterpreted as a slice.
                let boxed: Box<$ty, Global> = Box::<$ty, Global>::new_in(value, Global);

                // Convert the boxed scalar into a boxed single-element slice.
                let _slice: Box<[$ty], Global> = Box::<$ty, Global>::into_boxed_slice(boxed);
            }
        };
    }

    macro_rules! gen_box_into_boxed_slice_vec_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector payload for the boxed value.
                let value: Vec<$elem> = verifier_nondet_vec::<$elem>();

                // Build the boxed vector value that will be reinterpreted as a slice.
                let boxed: Box<Vec<$elem>, Global> =
                    Box::<Vec<$elem>, Global>::new_in(value, Global);

                // Convert the boxed vector into a boxed single-element slice.
                let _slice: Box<[Vec<$elem>], Global> =
                    Box::<Vec<$elem>, Global>::into_boxed_slice(boxed);
            }
        };
    }

    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_i8, i8);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_i16, i16);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_i32, i32);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_i64, i64);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_i128, i128);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_u8, u8);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_u16, u16);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_u32, u32);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_u64, u64);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_u128, u128);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_unit, ());
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_array, [u8; 4]);
    gen_box_into_boxed_slice_harness!(harness_box_into_boxed_slice_bool, bool);

    gen_box_into_boxed_slice_vec_harness!(harness_box_into_boxed_slice_vec_u8, u8);
    gen_box_into_boxed_slice_vec_harness!(harness_box_into_boxed_slice_vec_u16, u16);
    gen_box_into_boxed_slice_vec_harness!(harness_box_into_boxed_slice_vec_u32, u32);
    gen_box_into_boxed_slice_vec_harness!(harness_box_into_boxed_slice_vec_u64, u64);
    gen_box_into_boxed_slice_vec_harness!(harness_box_into_boxed_slice_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_675 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_new_uninit_slice_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic slice length that stays within the box slice layout limits.
                let len: usize = kani::any_where(|l: &usize| box_slice_layout_ok::<$ty>(*l));

                // Construct an uninitialized boxed slice for that symbolic length.
                let _boxed: Box<[mem::MaybeUninit<$ty>]> = Box::<[$ty]>::new_uninit_slice(len);
            }
        };
    }

    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_i8, i8);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_i16, i16);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_i32, i32);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_i64, i64);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_i128, i128);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_u8, u8);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_u16, u16);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_u32, u32);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_u64, u64);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_u128, u128);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_unit, ());
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_bool, bool);
    gen_box_new_uninit_slice_harness!(harness_box_new_uninit_slice_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_698 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_new_zeroed_slice_harness {
        ($name:ident, $elem_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic slice length that stays within the box slice layout limits.
                let len: usize = kani::any_where(|l: &usize| box_slice_layout_ok::<$elem_ty>(*l));

                // Construct a zeroed boxed slice for that symbolic length.
                let _boxed: Box<[mem::MaybeUninit<$elem_ty>]> =
                    Box::<[$elem_ty]>::new_zeroed_slice(len);
            }
        };
    }

    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_i8, i8);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_i16, i16);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_i32, i32);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_i64, i64);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_i128, i128);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_u8, u8);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_u16, u16);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_u32, u32);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_u64, u64);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_u128, u128);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_unit, ());
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_bool, bool);
    gen_box_new_zeroed_slice_harness!(harness_box_new_zeroed_slice_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_722 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_try_new_uninit_slice_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic slice length for the fallible constructor call.
                let len: usize = kani::any();

                // Call the fallible uninitialized slice constructor with that length.
                let _result: Result<Box<[mem::MaybeUninit<$ty>]>, AllocError> =
                    Box::<[$ty]>::try_new_uninit_slice(len);
            }
        };
    }

    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_i8, i8);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_i16, i16);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_i32, i32);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_i64, i64);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_i128, i128);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_u8, u8);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_u16, u16);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_u32, u32);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_u64, u64);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_u128, u128);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_unit, ());
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_bool, bool);
    gen_box_try_new_uninit_slice_harness!(harness_box_try_new_uninit_slice_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_756 {
    use super::*;

    macro_rules! gen_box_try_new_zeroed_slice_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic slice length for the fallible constructor call.
                let len: usize = kani::any();

                // Call the fallible zeroed slice constructor with that length.
                let _result: Result<Box<[mem::MaybeUninit<$ty>]>, AllocError> =
                    Box::<[$ty]>::try_new_zeroed_slice(len);
            }
        };
    }

    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_i8, i8);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_i16, i16);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_i32, i32);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_i64, i64);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_i128, i128);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_u8, u8);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_u16, u16);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_u32, u32);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_u64, u64);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_u128, u128);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_unit, ());
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_bool, bool);
    gen_box_try_new_zeroed_slice_harness!(harness_box_try_new_zeroed_slice_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_777 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    // `Box<[T]>::into_array::<N>` branches only on `self.len() == N`.
    //
    // The harness builds `self` from a nondeterministic `Vec<T>`, so the slice
    // length is symbolic. With `N` fixed to 100, Kani explores:
    // - `vec.len() == 100`: `into_array` calls `Box::into_raw(self)`, casts the
    //   slice pointer to `*mut [T; 100]`, rebuilds it with `Box::from_raw`, and
    //   returns `Some(Box<[T; 100]>)`.
    // - `vec.len() != 100`: the length check fails, so `into_array` returns
    //   `None` without reinterpreting the slice pointer as an array.
    macro_rules! gen_box_into_array_slice_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector that determines the slice length at runtime.
                let vec: Vec<$ty> = verifier_nondet_vec_box::<$ty>();

                // Turn the vector into the boxed slice consumed by `into_array`.
                let boxed: Box<[$ty]> = vec.into_boxed_slice();

                // Fix the target array length used by the conversion attempt.
                const N: usize = 100;

                // Attempt the safe conversion from a boxed slice into a boxed array.
                let _: Option<Box<[$ty; N]>> = boxed.into_array::<N>();
            }
        };
    }

    gen_box_into_array_slice_harness!(harness_box_into_array_slice_i8, i8);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_i16, i16);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_i32, i32);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_i64, i64);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_i128, i128);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_u8, u8);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_u16, u16);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_u32, u32);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_u64, u64);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_u128, u128);
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_unit, ());
    gen_box_into_array_slice_harness!(harness_box_into_array_slice_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_812 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_new_uninit_slice_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic slice length that stays within the box slice layout limits.
                let len: usize = kani::any_where(|l: &usize| box_slice_layout_ok::<$ty>(*l));

                // Construct an allocator-aware uninitialized boxed slice with the global allocator.
                let _boxed: Box<[mem::MaybeUninit<$ty>], Global> =
                    Box::<[$ty], Global>::new_uninit_slice_in(len, Global);
            }
        };
    }

    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_i8, i8);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_i16, i16);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_i32, i32);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_i64, i64);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_i128, i128);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_u8, u8);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_u16, u16);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_u32, u32);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_u64, u64);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_u128, u128);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_unit, ());
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_bool, bool);
    gen_box_new_uninit_slice_in_harness!(harness_box_new_uninit_slice_in_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_839 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_new_zeroed_slice_in_harness {
        ($name:ident, $elem_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Name the element type once so the layout helper and the target call stay aligned.
                type T = $elem_ty;

                // Create a symbolic slice length that stays within the box slice layout limits.
                let len: usize = kani::any_where(|l: &usize| box_slice_layout_ok::<T>(*l));

                // Construct an allocator-aware zeroed boxed slice with the global allocator.
                let _boxed: Box<[mem::MaybeUninit<T>], Global> =
                    Box::<[T], Global>::new_zeroed_slice_in(len, Global);
            }
        };
    }

    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_i8, i8);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_i16, i16);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_i32, i32);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_i64, i64);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_i128, i128);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_u8, u8);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_u16, u16);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_u32, u32);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_u64, u64);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_u128, u128);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_unit, ());
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_bool, bool);
    gen_box_new_zeroed_slice_in_harness!(harness_box_new_zeroed_slice_in_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_865 {
    use super::*;

    macro_rules! gen_box_try_new_uninit_slice_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic slice length for the target call.
                let len: usize = kani::any();

                // Call the allocator-aware fallible uninitialized slice constructor.
                let _result: Result<Box<[mem::MaybeUninit<$ty>], Global>, AllocError> =
                    Box::<[$ty], Global>::try_new_uninit_slice_in(len, Global);
            }
        };
    }

    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_i8, i8);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_i16, i16);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_i32, i32);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_i64, i64);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_i128, i128);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_u8, u8);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_u16, u16);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_u32, u32);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_u64, u64);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_u128, u128);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_unit, ());
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_bool, bool);
    gen_box_try_new_uninit_slice_in_harness!(harness_box_try_new_uninit_slice_in_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_904 {
    use super::*;

    macro_rules! gen_box_try_new_zeroed_slice_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic slice length for the target call.
                let len: usize = kani::any();

                // Call the safe constructor with the global allocator and keep
                // the result typed as the exact return shape of the function.
                let _result: Result<Box<[mem::MaybeUninit<$ty>], Global>, AllocError> =
                    Box::<[$ty], Global>::try_new_zeroed_slice_in(len, Global);
            }
        };
    }

    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_i8, i8);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_i16, i16);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_i32, i32);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_i64, i64);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_i128, i128);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_u8, u8);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_u16, u16);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_u32, u32);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_u64, u64);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_u128, u128);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_unit, ());
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_bool, bool);
    gen_box_try_new_zeroed_slice_in_harness!(harness_box_try_new_zeroed_slice_in_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_985 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_write_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic initialized value of the target type.
                let value: $ty = kani::any();

                // Allocate boxed storage for an uninitialized value of the same type.
                let boxed: Box<mem::MaybeUninit<$ty>, Global> =
                    Box::<$ty, Global>::new_uninit_in(Global);

                // Write the initialized value into the boxed `MaybeUninit` slot.
                let _written: Box<$ty, Global> = Box::write(boxed, value);
            }
        };
    }

    macro_rules! gen_box_write_vec_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector payload that owns heap-backed contents.
                let value: Vec<$elem> = verifier_nondet_vec::<$elem>();

                // Allocate boxed storage for an uninitialized vector value.
                let boxed: Box<mem::MaybeUninit<Vec<$elem>>, Global> =
                    Box::<Vec<$elem>, Global>::new_uninit_in(Global);

                // Write the initialized vector into the boxed `MaybeUninit` slot.
                let _written: Box<Vec<$elem>, Global> = Box::write(boxed, value);
            }
        };
    }

    gen_box_write_harness!(harness_box_write_i8, i8);
    gen_box_write_harness!(harness_box_write_i16, i16);
    gen_box_write_harness!(harness_box_write_i32, i32);
    gen_box_write_harness!(harness_box_write_i64, i64);
    gen_box_write_harness!(harness_box_write_i128, i128);
    gen_box_write_harness!(harness_box_write_u8, u8);
    gen_box_write_harness!(harness_box_write_u16, u16);
    gen_box_write_harness!(harness_box_write_u32, u32);
    gen_box_write_harness!(harness_box_write_u64, u64);
    gen_box_write_harness!(harness_box_write_u128, u128);
    gen_box_write_harness!(harness_box_write_unit, ());
    gen_box_write_harness!(harness_box_write_bool, bool);
    gen_box_write_harness!(harness_box_write_array, [u8; 4]);

    gen_box_write_vec_harness!(harness_box_write_vec_u8, u8);
    gen_box_write_vec_harness!(harness_box_write_vec_u16, u16);
    gen_box_write_vec_harness!(harness_box_write_vec_u32, u32);
    gen_box_write_vec_harness!(harness_box_write_vec_u64, u64);
    gen_box_write_vec_harness!(harness_box_write_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1281 {
    use core::any::Any;

    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_into_non_null_sized_harness {
        ($name:ident, dyn Any) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that can be coerced into `dyn Any`.
                let value: i32 = kani::any();

                // Build the concrete boxed value that will be erased behind the trait object.
                let boxed_i32: Box<i32> = Box::new(value);

                // Erase the concrete type behind a boxed `dyn Any`.
                let boxed: Box<dyn Any> = boxed_i32;

                // Consume the box and extract the non-null trait-object pointer.
                let ptr: NonNull<dyn Any> = Box::<dyn Any>::into_non_null(boxed);

                // Rebuild ownership from the non-null trait-object pointer.
                let _recovered: Box<dyn Any> = unsafe { Box::<dyn Any>::from_non_null(ptr) };
            }
        };
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value whose allocation will become the non-null witness.
                let boxed: Box<$ty> = Box::new(value);

                // Consume the box and extract the non-null pointer.
                let ptr: NonNull<$ty> = Box::<$ty>::into_non_null(boxed);

                // Rebuild ownership from the non-null pointer.
                let _recovered: Box<$ty> = unsafe { Box::<$ty>::from_non_null(ptr) };
            }
        };
    }

    macro_rules! gen_box_into_non_null_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$elem> = verifier_nondet_vec_box::<$elem>();

                // Convert the vector into the boxed slice consumed by `into_non_null`.
                let boxed: Box<[$elem]> = vec.into_boxed_slice();

                // Consume the boxed slice and extract the non-null fat pointer.
                let ptr: NonNull<[$elem]> = Box::<[$elem]>::into_non_null(boxed);

                // Rebuild ownership from the non-null slice pointer.
                let _recovered: Box<[$elem]> = unsafe { Box::<[$elem]>::from_non_null(ptr) };
            }
        };
    }

    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_i8, i8);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_i16, i16);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_i32, i32);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_i64, i64);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_i128, i128);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_u8, u8);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_u16, u16);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_u32, u32);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_u64, u64);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_u128, u128);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_unit, ());
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_bool, bool);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_array, [u8; 4]);
    gen_box_into_non_null_sized_harness!(harness_box_into_non_null_dyn_any, dyn Any);

    gen_box_into_non_null_unsized_harness!(harness_box_into_non_null_vec_u8, u8);
    gen_box_into_non_null_unsized_harness!(harness_box_into_non_null_vec_u16, u16);
    gen_box_into_non_null_unsized_harness!(harness_box_into_non_null_vec_u32, u32);
    gen_box_into_non_null_unsized_harness!(harness_box_into_non_null_vec_u64, u64);
    gen_box_into_non_null_unsized_harness!(harness_box_into_non_null_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1470 {
    use core::any::Any;

    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_into_raw_with_allocator_sized_harness {
        ($name:ident, dyn Any) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that can be coerced into `dyn Any`.
                let value: i32 = kani::any();

                // Build the concrete boxed value that will be erased behind the trait object.
                let boxed_i32: Box<i32, Global> = Box::new_in(value, Global);

                // Erase the concrete type behind a boxed `dyn Any`.
                let boxed: Box<dyn Any, Global> = boxed_i32;

                // Consume the box and extract the raw trait-object pointer together with its allocator.
                let (ptr, alloc): (*mut dyn Any, Global) =
                    Box::<dyn Any, Global>::into_raw_with_allocator(boxed);

                // Rebuild ownership from the raw pointer and allocator pair.
                let _recovered: Box<dyn Any, Global> =
                    unsafe { Box::<dyn Any, Global>::from_raw_in(ptr, alloc) };
            }
        };
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value whose allocation will become the raw-pointer witness.
                let boxed: Box<$ty, Global> = Box::new_in(value, Global);

                // Consume the box and extract the raw pointer together with its allocator.
                let (ptr, alloc): (*mut $ty, Global) =
                    Box::<$ty, Global>::into_raw_with_allocator(boxed);

                // Rebuild ownership from the raw pointer and allocator pair.
                let _recovered: Box<$ty, Global> =
                    unsafe { Box::<$ty, Global>::from_raw_in(ptr, alloc) };
            }
        };
    }

    macro_rules! gen_box_into_raw_with_allocator_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$elem> = verifier_nondet_vec_box::<$elem>();

                // Convert the vector into the boxed slice consumed by `into_raw_with_allocator`.
                let boxed: Box<[$elem], Global> = vec.into_boxed_slice();

                // Consume the boxed slice and extract the raw fat pointer together with its allocator.
                let (ptr, alloc): (*mut [$elem], Global) =
                    Box::<[$elem], Global>::into_raw_with_allocator(boxed);

                // Rebuild ownership from the raw slice pointer and allocator pair.
                let _recovered: Box<[$elem], Global> =
                    unsafe { Box::<[$elem], Global>::from_raw_in(ptr, alloc) };
            }
        };
    }

    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_i8, i8);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_i16, i16);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_i32, i32);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_i64, i64);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_i128, i128);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_u8, u8);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_u16, u16);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_u32, u32);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_u64, u64);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_u128, u128);
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_unit, ());
    gen_box_into_raw_with_allocator_sized_harness!(harness_box_into_raw_with_allocator_bool, bool);
    gen_box_into_raw_with_allocator_sized_harness!(
        harness_box_into_raw_with_allocator_array,
        [u8; 4]
    );
    gen_box_into_raw_with_allocator_sized_harness!(
        harness_box_into_raw_with_allocator_dyn_any,
        dyn Any
    );

    gen_box_into_raw_with_allocator_unsized_harness!(
        harness_box_into_raw_with_allocator_vec_u8,
        u8
    );
    gen_box_into_raw_with_allocator_unsized_harness!(
        harness_box_into_raw_with_allocator_vec_u16,
        u16
    );
    gen_box_into_raw_with_allocator_unsized_harness!(
        harness_box_into_raw_with_allocator_vec_u32,
        u32
    );
    gen_box_into_raw_with_allocator_unsized_harness!(
        harness_box_into_raw_with_allocator_vec_u64,
        u64
    );
    gen_box_into_raw_with_allocator_unsized_harness!(
        harness_box_into_raw_with_allocator_vec_u128,
        u128
    );
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1531 {
    use core::any::Any;

    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_into_non_null_with_allocator_sized_harness {
        ($name:ident, dyn Any) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that can be coerced into `dyn Any`.
                let value: i32 = kani::any();

                // Build the concrete boxed value that will be erased behind the trait object.
                let boxed_i32: Box<i32, Global> = Box::new_in(value, Global);

                // Erase the concrete type behind a boxed `dyn Any`.
                let boxed: Box<dyn Any, Global> = boxed_i32;

                // Consume the box and extract the non-null trait-object pointer together with its allocator.
                let (ptr, alloc): (NonNull<dyn Any>, Global) =
                    Box::<dyn Any, Global>::into_non_null_with_allocator(boxed);

                // Rebuild ownership from the non-null pointer and allocator pair.
                let _recovered: Box<dyn Any, Global> =
                    unsafe { Box::<dyn Any, Global>::from_non_null_in(ptr, alloc) };
            }
        };
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value whose allocation will become the non-null witness.
                let boxed: Box<$ty, Global> = Box::new_in(value, Global);

                // Consume the box and extract the non-null pointer together with its allocator.
                let (ptr, alloc): (NonNull<$ty>, Global) =
                    Box::<$ty, Global>::into_non_null_with_allocator(boxed);

                // Rebuild ownership from the non-null pointer and allocator pair.
                let _recovered: Box<$ty, Global> =
                    unsafe { Box::<$ty, Global>::from_non_null_in(ptr, alloc) };
            }
        };
    }

    macro_rules! gen_box_into_non_null_with_allocator_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$elem> = verifier_nondet_vec_box::<$elem>();

                // Convert the vector into the boxed slice consumed by `into_non_null_with_allocator`.
                let boxed: Box<[$elem], Global> = vec.into_boxed_slice();

                // Consume the boxed slice and extract the non-null fat pointer together with its allocator.
                let (ptr, alloc): (NonNull<[$elem]>, Global) =
                    Box::<[$elem], Global>::into_non_null_with_allocator(boxed);

                // Rebuild ownership from the non-null slice pointer and allocator pair.
                let _recovered: Box<[$elem], Global> =
                    unsafe { Box::<[$elem], Global>::from_non_null_in(ptr, alloc) };
            }
        };
    }

    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_i8,
        i8
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_i16,
        i16
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_i32,
        i32
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_i64,
        i64
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_i128,
        i128
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_u8,
        u8
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_u16,
        u16
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_u32,
        u32
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_u64,
        u64
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_u128,
        u128
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_unit,
        ()
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_bool,
        bool
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_array,
        [u8; 4]
    );
    gen_box_into_non_null_with_allocator_sized_harness!(
        harness_box_into_non_null_with_allocator_dyn_any,
        dyn Any
    );

    gen_box_into_non_null_with_allocator_unsized_harness!(
        harness_box_into_non_null_with_allocator_vec_u8,
        u8
    );
    gen_box_into_non_null_with_allocator_unsized_harness!(
        harness_box_into_non_null_with_allocator_vec_u16,
        u16
    );
    gen_box_into_non_null_with_allocator_unsized_harness!(
        harness_box_into_non_null_with_allocator_vec_u32,
        u32
    );
    gen_box_into_non_null_with_allocator_unsized_harness!(
        harness_box_into_non_null_with_allocator_vec_u64,
        u64
    );
    gen_box_into_non_null_with_allocator_unsized_harness!(
        harness_box_into_non_null_with_allocator_vec_u128,
        u128
    );
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1544 {
    use core::any::Any;

    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_into_unique_sized_harness {
        ($name:ident, dyn Any) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that can be coerced into `dyn Any`.
                let value: i32 = kani::any();

                // Build the concrete boxed value that will be erased behind the trait object.
                let boxed_i32: Box<i32, Global> = Box::new_in(value, Global);

                // Erase the concrete type behind a boxed `dyn Any`.
                let boxed: Box<dyn Any, Global> = boxed_i32;

                // Consume the box and extract the unique pointer together with its allocator.
                let (ptr, alloc): (Unique<dyn Any>, Global) =
                    Box::<dyn Any, Global>::into_unique(boxed);

                // Recover the raw pointer from the unique wrapper.
                let raw: *mut dyn Any = ptr.as_ptr();

                // Rebuild ownership from the raw pointer and allocator pair.
                let _recovered: Box<dyn Any, Global> =
                    unsafe { Box::<dyn Any, Global>::from_raw_in(raw, alloc) };
            }
        };
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value whose allocation will become the unique-pointer witness.
                let boxed: Box<$ty, Global> = Box::new_in(value, Global);

                // Consume the box and extract the unique pointer together with its allocator.
                let (ptr, alloc): (Unique<$ty>, Global) = Box::<$ty, Global>::into_unique(boxed);

                // Recover the raw pointer from the unique wrapper.
                let raw: *mut $ty = ptr.as_ptr();

                // Rebuild ownership from the raw pointer and allocator pair.
                let _recovered: Box<$ty, Global> =
                    unsafe { Box::<$ty, Global>::from_raw_in(raw, alloc) };
            }
        };
    }

    macro_rules! gen_box_into_unique_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$elem> = verifier_nondet_vec_box::<$elem>();

                // Convert the vector into the boxed slice consumed by `into_unique`.
                let boxed: Box<[$elem], Global> = vec.into_boxed_slice();

                // Consume the boxed slice and extract the unique fat pointer together with its allocator.
                let (ptr, alloc): (Unique<[$elem]>, Global) =
                    Box::<[$elem], Global>::into_unique(boxed);

                // Recover the raw slice pointer from the unique wrapper.
                let raw: *mut [$elem] = ptr.as_ptr();

                // Rebuild ownership from the raw slice pointer and allocator pair.
                let _recovered: Box<[$elem], Global> =
                    unsafe { Box::<[$elem], Global>::from_raw_in(raw, alloc) };
            }
        };
    }

    gen_box_into_unique_sized_harness!(harness_box_into_unique_i8, i8);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_i16, i16);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_i32, i32);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_i64, i64);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_i128, i128);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_u8, u8);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_u16, u16);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_u32, u32);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_u64, u64);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_u128, u128);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_unit, ());
    gen_box_into_unique_sized_harness!(harness_box_into_unique_bool, bool);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_array, [u8; 4]);
    gen_box_into_unique_sized_harness!(harness_box_into_unique_dyn_any, dyn Any);

    gen_box_into_unique_unsized_harness!(harness_box_into_unique_vec_u8, u8);
    gen_box_into_unique_unsized_harness!(harness_box_into_unique_vec_u16, u16);
    gen_box_into_unique_unsized_harness!(harness_box_into_unique_vec_u32, u32);
    gen_box_into_unique_unsized_harness!(harness_box_into_unique_vec_u64, u64);
    gen_box_into_unique_unsized_harness!(harness_box_into_unique_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1696 {
    use core::any::Any;

    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_leak_sized_harness {
        ($name:ident, dyn Any) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that can be coerced into `dyn Any`.
                let value: i32 = kani::any();

                // Build the concrete boxed value that will be erased behind the trait object.
                let boxed_i32: Box<i32> = Box::new(value);

                // Erase the concrete type behind a boxed `dyn Any`.
                let boxed: Box<dyn Any> = boxed_i32;

                // Leak the box and obtain a mutable trait-object reference to its contents.
                let leaked: &mut dyn Any = Box::<dyn Any>::leak(boxed);

                // Recover the raw trait-object pointer from the leaked reference.
                let ptr: *mut dyn Any = leaked;

                // Rebuild the box so the harness itself does not leave a permanent leak behind.
                let _recovered: Box<dyn Any> = unsafe { Box::<dyn Any>::from_raw(ptr) };
            }
        };
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value that will be consumed by `leak`.
                let boxed: Box<$ty> = Box::new(value);

                // Leak the box and obtain a mutable reference to its contents.
                let leaked: &mut $ty = Box::<$ty>::leak(boxed);

                // Recover the raw pointer from the leaked mutable reference.
                let ptr: *mut $ty = leaked;

                // Rebuild the box so the harness itself does not leave a permanent leak behind.
                let _recovered: Box<$ty> = unsafe { Box::<$ty>::from_raw(ptr) };
            }
        };
    }

    macro_rules! gen_box_leak_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$elem> = verifier_nondet_vec_box::<$elem>();

                // Convert the vector into the boxed slice consumed by `leak`.
                let boxed: Box<[$elem]> = vec.into_boxed_slice();

                // Leak the box and obtain a mutable slice reference to its contents.
                let leaked: &mut [$elem] = Box::<[$elem]>::leak(boxed);

                // Recover the raw slice pointer from the leaked mutable reference.
                let ptr: *mut [$elem] = leaked;

                // Rebuild the box so the harness itself does not leave a permanent leak behind.
                let _recovered: Box<[$elem]> = unsafe { Box::<[$elem]>::from_raw(ptr) };
            }
        };
    }

    gen_box_leak_sized_harness!(harness_box_leak_i8, i8);
    gen_box_leak_sized_harness!(harness_box_leak_i16, i16);
    gen_box_leak_sized_harness!(harness_box_leak_i32, i32);
    gen_box_leak_sized_harness!(harness_box_leak_i64, i64);
    gen_box_leak_sized_harness!(harness_box_leak_i128, i128);
    gen_box_leak_sized_harness!(harness_box_leak_u8, u8);
    gen_box_leak_sized_harness!(harness_box_leak_u16, u16);
    gen_box_leak_sized_harness!(harness_box_leak_u32, u32);
    gen_box_leak_sized_harness!(harness_box_leak_u64, u64);
    gen_box_leak_sized_harness!(harness_box_leak_u128, u128);
    gen_box_leak_sized_harness!(harness_box_leak_unit, ());
    gen_box_leak_sized_harness!(harness_box_leak_bool, bool);
    gen_box_leak_sized_harness!(harness_box_leak_array, [u8; 4]);
    gen_box_leak_sized_harness!(harness_box_leak_dyn_any, dyn Any);

    gen_box_leak_unsized_harness!(harness_box_leak_vec_u8, u8);
    gen_box_leak_unsized_harness!(harness_box_leak_vec_u16, u16);
    gen_box_leak_unsized_harness!(harness_box_leak_vec_u32, u32);
    gen_box_leak_unsized_harness!(harness_box_leak_vec_u64, u64);
    gen_box_leak_unsized_harness!(harness_box_leak_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1736 {
    use core::any::Any;
    use core::marker::PhantomPinned;

    use super::kani_box_harness_helpers::*;
    use super::*;

    struct NotUnpinSentinel(u8, PhantomPinned);

    macro_rules! gen_box_into_pin_harness {
        ($name:ident, dyn Any) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that can be coerced into `dyn Any`.
                let value: i32 = kani::any();

                // Build the concrete boxed value that will be erased behind the trait object.
                let boxed_i32: Box<i32, Global> = Box::new_in(value, Global);

                // Erase the concrete type behind a boxed `dyn Any`.
                let boxed: Box<dyn Any, Global> = boxed_i32;

                // Convert the box into a pinned box without moving its contents.
                let _pinned: Pin<Box<dyn Any, Global>> = Box::<dyn Any, Global>::into_pin(boxed);
            }
        };
        ($name:ident, NotUnpinSentinel) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic `!Unpin` value to exercise the safety note in `into_pin`.
                let value = NotUnpinSentinel(kani::any(), PhantomPinned);

                // Build the boxed value that will be pinned in place.
                let boxed: Box<NotUnpinSentinel, Global> = Box::new_in(value, Global);

                // Convert the box into a pinned box without moving its contents.
                let _pinned: Pin<Box<NotUnpinSentinel, Global>> =
                    Box::<NotUnpinSentinel, Global>::into_pin(boxed);
            }
        };
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value that will be pinned in place.
                let boxed: Box<$ty, Global> = Box::new_in(value, Global);

                // Convert the box into a pinned box without moving its contents.
                let _pinned: Pin<Box<$ty, Global>> = Box::<$ty, Global>::into_pin(boxed);
            }
        };
    }

    macro_rules! gen_box_into_pin_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$elem> = verifier_nondet_vec_box::<$elem>();

                // Convert the vector into the boxed slice consumed by `into_pin`.
                let boxed: Box<[$elem], Global> = vec.into_boxed_slice();

                // Convert the box into a pinned box without moving its contents.
                let _pinned: Pin<Box<[$elem], Global>> = Box::<[$elem], Global>::into_pin(boxed);
            }
        };
    }

    gen_box_into_pin_harness!(harness_box_into_pin_i8, i8);
    gen_box_into_pin_harness!(harness_box_into_pin_i16, i16);
    gen_box_into_pin_harness!(harness_box_into_pin_i32, i32);
    gen_box_into_pin_harness!(harness_box_into_pin_i64, i64);
    gen_box_into_pin_harness!(harness_box_into_pin_i128, i128);
    gen_box_into_pin_harness!(harness_box_into_pin_u8, u8);
    gen_box_into_pin_harness!(harness_box_into_pin_u16, u16);
    gen_box_into_pin_harness!(harness_box_into_pin_u32, u32);
    gen_box_into_pin_harness!(harness_box_into_pin_u64, u64);
    gen_box_into_pin_harness!(harness_box_into_pin_u128, u128);
    gen_box_into_pin_harness!(harness_box_into_pin_unit, ());
    gen_box_into_pin_harness!(harness_box_into_pin_bool, bool);
    gen_box_into_pin_harness!(harness_box_into_pin_array, [u8; 4]);
    gen_box_into_pin_harness!(harness_box_into_pin_dyn_any, dyn Any);
    gen_box_into_pin_harness!(harness_box_into_pin_not_unpin, NotUnpinSentinel);

    gen_box_into_pin_unsized_harness!(harness_box_into_pin_vec_u8, u8);
    gen_box_into_pin_unsized_harness!(harness_box_into_pin_vec_u16, u16);
    gen_box_into_pin_unsized_harness!(harness_box_into_pin_vec_u32, u32);
    gen_box_into_pin_unsized_harness!(harness_box_into_pin_vec_u64, u64);
    gen_box_into_pin_unsized_harness!(harness_box_into_pin_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1750 {
    use core::any::Any;

    use super::kani_box_harness_helpers::*;
    use super::*;

    // `Drop for Box<T, A>` has one explicit control-flow split:
    // - `layout.size() != 0`: after the compiler has already dropped `T`, the
    //   destructor computes the layout of the pointee and calls
    //   `self.1.deallocate(...)`.
    // - `layout.size() == 0`: the destructor skips deallocation entirely.
    //
    // The harnesses cover that branch in three representative families:
    // - sized values: `()` covers the zero-sized path, while the other scalar
    //   types cover the deallocation path;
    // - trait objects: `dyn Any` exercises the `T: ?Sized` object case;
    // - slices: `[$elem]` exercises the `T: ?Sized` slice case, and `[$elem]`
    //   with `$elem = ()` covers a zero-sized unsized pointee.
    //
    // Each harness simply constructs a `Box` and then calls `drop(boxed)`,
    // which is the actual safe surface that triggers `<Box<T, A> as Drop>::drop`.
    macro_rules! gen_box_drop_harness {
        ($name:ident, dyn Any) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that can be coerced into `dyn Any`.
                let value: i32 = kani::any();

                // Build the concrete boxed value that will be erased behind the trait object.
                let boxed_i32: Box<i32, Global> = Box::new_in(value, Global);

                // Erase the concrete type behind a boxed `dyn Any`.
                let boxed: Box<dyn Any, Global> = boxed_i32;

                // Trigger `<Box<dyn Any, Global> as Drop>::drop` through the safe surface.
                drop(boxed);
            }
        };
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target type.
                let value: $ty = kani::any();

                // Build the boxed value whose destructor will be exercised.
                let boxed: Box<$ty, Global> = Box::new_in(value, Global);

                // Trigger `<Box<$ty, Global> as Drop>::drop` through the safe surface.
                drop(boxed);
            }
        };
    }

    macro_rules! gen_box_drop_unsized_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$elem> = verifier_nondet_vec_box::<$elem>();

                // Convert the vector into the boxed slice whose destructor will be exercised.
                let boxed: Box<[$elem], Global> = vec.into_boxed_slice();

                // Trigger `<Box<[$elem], Global> as Drop>::drop` through the safe surface.
                drop(boxed);
            }
        };
    }

    gen_box_drop_harness!(harness_box_drop_i8, i8);
    gen_box_drop_harness!(harness_box_drop_i16, i16);
    gen_box_drop_harness!(harness_box_drop_i32, i32);
    gen_box_drop_harness!(harness_box_drop_i64, i64);
    gen_box_drop_harness!(harness_box_drop_i128, i128);
    gen_box_drop_harness!(harness_box_drop_u8, u8);
    gen_box_drop_harness!(harness_box_drop_u16, u16);
    gen_box_drop_harness!(harness_box_drop_u32, u32);
    gen_box_drop_harness!(harness_box_drop_u64, u64);
    gen_box_drop_harness!(harness_box_drop_u128, u128);
    gen_box_drop_harness!(harness_box_drop_unit, ());
    gen_box_drop_harness!(harness_box_drop_bool, bool);
    gen_box_drop_harness!(harness_box_drop_array, [u8; 4]);
    gen_box_drop_harness!(harness_box_drop_dyn_any, dyn Any);

    gen_box_drop_unsized_harness!(harness_box_drop_vec_u8, u8);
    gen_box_drop_unsized_harness!(harness_box_drop_vec_u16, u16);
    gen_box_drop_unsized_harness!(harness_box_drop_vec_u32, u32);
    gen_box_drop_unsized_harness!(harness_box_drop_vec_u64, u64);
    gen_box_drop_unsized_harness!(harness_box_drop_vec_u128, u128);
    gen_box_drop_unsized_harness!(harness_box_drop_vec_unit, ());
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1769 {
    use super::*;

    macro_rules! gen_box_default_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Construct a boxed value through the `Default for Box<T>` implementation.
                let _boxed: Box<$ty> = Box::<$ty>::default();
            }
        };
    }

    gen_box_default_harness!(harness_box_default_i8, i8);
    gen_box_default_harness!(harness_box_default_i16, i16);
    gen_box_default_harness!(harness_box_default_i32, i32);
    gen_box_default_harness!(harness_box_default_i64, i64);
    gen_box_default_harness!(harness_box_default_i128, i128);
    gen_box_default_harness!(harness_box_default_u8, u8);
    gen_box_default_harness!(harness_box_default_u16, u16);
    gen_box_default_harness!(harness_box_default_u32, u32);
    gen_box_default_harness!(harness_box_default_u64, u64);
    gen_box_default_harness!(harness_box_default_u128, u128);
    gen_box_default_harness!(harness_box_default_unit, ());
    gen_box_default_harness!(harness_box_default_array, [u8; 4]);
    gen_box_default_harness!(harness_box_default_bool, bool);
    gen_box_default_harness!(harness_box_default_vec_u8, Vec<u8>);
    gen_box_default_harness!(harness_box_default_vec_u16, Vec<u16>);
    gen_box_default_harness!(harness_box_default_vec_u32, Vec<u32>);
    gen_box_default_harness!(harness_box_default_vec_u64, Vec<u64>);
    gen_box_default_harness!(harness_box_default_vec_u128, Vec<u128>);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1802 {
    use super::*;

    macro_rules! gen_box_str_default_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Construct the boxed string through the dedicated `Default for Box<str>` implementation.
                let _boxed: Box<$ty> = Box::<$ty>::default();
            }
        };
    }

    gen_box_str_default_harness!(harness_box_default_str, str);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1843 {
    use super::kani_box_harness_helpers::*;
    use super::*;

    macro_rules! gen_box_clone_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic value of the target cloneable type.
                let value: $ty = kani::any();

                // Build the original boxed value whose clone path will be exercised.
                let boxed: Box<$ty, Global> = Box::new_in(value, Global);

                // Clone the box through `<Box<T, A> as Clone>::clone`.
                let _clone: Box<$ty, Global> = Clone::clone(&boxed);
            }
        };
    }

    macro_rules! gen_box_clone_vec_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector payload whose own `Clone` implementation will be exercised.
                let value: Vec<$elem> = verifier_nondet_vec::<$elem>();

                // Build the original boxed vector whose clone path will be exercised.
                let boxed: Box<Vec<$elem>, Global> = Box::new_in(value, Global);

                // Clone the box through `<Box<T, A> as Clone>::clone`.
                let _clone: Box<Vec<$elem>, Global> = Clone::clone(&boxed);
            }
        };
    }

    gen_box_clone_harness!(harness_box_clone_i8, i8);
    gen_box_clone_harness!(harness_box_clone_i16, i16);
    gen_box_clone_harness!(harness_box_clone_i32, i32);
    gen_box_clone_harness!(harness_box_clone_i64, i64);
    gen_box_clone_harness!(harness_box_clone_i128, i128);
    gen_box_clone_harness!(harness_box_clone_u8, u8);
    gen_box_clone_harness!(harness_box_clone_u16, u16);
    gen_box_clone_harness!(harness_box_clone_u32, u32);
    gen_box_clone_harness!(harness_box_clone_u64, u64);
    gen_box_clone_harness!(harness_box_clone_u128, u128);
    gen_box_clone_harness!(harness_box_clone_unit, ());
    gen_box_clone_harness!(harness_box_clone_array, [u8; 4]);
    gen_box_clone_harness!(harness_box_clone_bool, bool);

    gen_box_clone_vec_harness!(harness_box_clone_vec_u8, u8);
    gen_box_clone_vec_harness!(harness_box_clone_vec_u16, u16);
    gen_box_clone_vec_harness!(harness_box_clone_vec_u32, u32);
    gen_box_clone_vec_harness!(harness_box_clone_vec_u64, u64);
    gen_box_clone_vec_harness!(harness_box_clone_vec_u128, u128);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_1913 {
    use super::*;

    macro_rules! gen_box_str_clone_harness {
        ($name:ident, $value:expr) => {
            #[kani::proof]
            pub fn $name() {
                // Build the original boxed string whose clone path will be exercised.
                let boxed: Box<str> = Box::<str>::from($value);

                // Clone the boxed string through `<Box<str> as Clone>::clone`.
                let _clone: Box<str> = Clone::clone(&boxed);
            }
        };
    }

    gen_box_str_clone_harness!(harness_box_clone_str_empty, "");
    gen_box_str_clone_harness!(harness_box_clone_str_nonempty, "test");
}
