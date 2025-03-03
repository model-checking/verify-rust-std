use safety::{ensures, requires};

use crate::cmp::Ordering;
#[cfg(kani)]
use crate::kani;
use crate::marker::Unsize;
use crate::mem::{MaybeUninit, SizedTypeProperties};
use crate::num::NonZero;
use crate::ops::{CoerceUnsized, DispatchFromDyn};
use crate::pin::PinCoerceUnsized;
use crate::ptr::Unique;
use crate::slice::{self, SliceIndex};
#[cfg(kani)]
use crate::ub_checks;
use crate::ub_checks::assert_unsafe_precondition;
use crate::{fmt, hash, intrinsics, mem, ptr};

/// `*mut T` but non-zero and [covariant].
///
/// This is often the correct thing to use when building data structures using
/// raw pointers, but is ultimately more dangerous to use because of its additional
/// properties. If you're not sure if you should use `NonNull<T>`, just use `*mut T`!
///
/// Unlike `*mut T`, the pointer must always be non-null, even if the pointer
/// is never dereferenced. This is so that enums may use this forbidden value
/// as a discriminant -- `Option<NonNull<T>>` has the same size as `*mut T`.
/// However the pointer may still dangle if it isn't dereferenced.
///
/// Unlike `*mut T`, `NonNull<T>` was chosen to be covariant over `T`. This makes it
/// possible to use `NonNull<T>` when building covariant types, but introduces the
/// risk of unsoundness if used in a type that shouldn't actually be covariant.
/// (The opposite choice was made for `*mut T` even though technically the unsoundness
/// could only be caused by calling unsafe functions.)
///
/// Covariance is correct for most safe abstractions, such as `Box`, `Rc`, `Arc`, `Vec`,
/// and `LinkedList`. This is the case because they provide a public API that follows the
/// normal shared XOR mutable rules of Rust.
///
/// If your type cannot safely be covariant, you must ensure it contains some
/// additional field to provide invariance. Often this field will be a [`PhantomData`]
/// type like `PhantomData<Cell<T>>` or `PhantomData<&'a mut T>`.
///
/// Notice that `NonNull<T>` has a `From` instance for `&T`. However, this does
/// not change the fact that mutating through a (pointer derived from a) shared
/// reference is undefined behavior unless the mutation happens inside an
/// [`UnsafeCell<T>`]. The same goes for creating a mutable reference from a shared
/// reference. When using this `From` instance without an `UnsafeCell<T>`,
/// it is your responsibility to ensure that `as_mut` is never called, and `as_ptr`
/// is never used for mutation.
///
/// # Representation
///
/// Thanks to the [null pointer optimization],
/// `NonNull<T>` and `Option<NonNull<T>>`
/// are guaranteed to have the same size and alignment:
///
/// ```
/// # use std::mem::{size_of, align_of};
/// use std::ptr::NonNull;
///
/// assert_eq!(size_of::<NonNull<i16>>(), size_of::<Option<NonNull<i16>>>());
/// assert_eq!(align_of::<NonNull<i16>>(), align_of::<Option<NonNull<i16>>>());
///
/// assert_eq!(size_of::<NonNull<str>>(), size_of::<Option<NonNull<str>>>());
/// assert_eq!(align_of::<NonNull<str>>(), align_of::<Option<NonNull<str>>>());
/// ```
///
/// [covariant]: https://doc.rust-lang.org/reference/subtyping.html
/// [`PhantomData`]: crate::marker::PhantomData
/// [`UnsafeCell<T>`]: crate::cell::UnsafeCell
/// [null pointer optimization]: crate::option#representation
#[stable(feature = "nonnull", since = "1.25.0")]
#[repr(transparent)]
#[rustc_layout_scalar_valid_range_start(1)]
#[rustc_nonnull_optimization_guaranteed]
#[rustc_diagnostic_item = "NonNull"]
pub struct NonNull<T: ?Sized> {
    // Remember to use `.as_ptr()` instead of `.pointer`, as field projecting to
    // this is banned by <https://github.com/rust-lang/compiler-team/issues/807>.
    pointer: *const T,
}

/// `NonNull` pointers are not `Send` because the data they reference may be aliased.
// N.B., this impl is unnecessary, but should provide better error messages.
#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> !Send for NonNull<T> {}

/// `NonNull` pointers are not `Sync` because the data they reference may be aliased.
// N.B., this impl is unnecessary, but should provide better error messages.
#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> !Sync for NonNull<T> {}

impl<T: Sized> NonNull<T> {
    /// Creates a pointer with the given address and no [provenance][crate::ptr#provenance].
    ///
    /// For more details, see the equivalent method on a raw pointer, [`ptr::without_provenance_mut`].
    ///
    /// This is a [Strict Provenance][crate::ptr#strict-provenance] API.
    #[unstable(feature = "nonnull_provenance", issue = "135243")]
    #[must_use]
    #[inline]
    pub const fn without_provenance(addr: NonZero<usize>) -> Self {
        let pointer = crate::ptr::without_provenance(addr.get());
        // SAFETY: we know `addr` is non-zero.
        unsafe { NonNull { pointer } }
    }

    /// Creates a new `NonNull` that is dangling, but well-aligned.
    ///
    /// This is useful for initializing types which lazily allocate, like
    /// `Vec::new` does.
    ///
    /// Note that the pointer value may potentially represent a valid pointer to
    /// a `T`, which means this must not be used as a "not yet initialized"
    /// sentinel value. Types that lazily allocate must track initialization by
    /// some other means.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let ptr = NonNull::<u32>::dangling();
    /// // Important: don't try to access the value of `ptr` without
    /// // initializing it first! The pointer is not null but isn't valid either!
    /// ```
    #[stable(feature = "nonnull", since = "1.25.0")]
    #[rustc_const_stable(feature = "const_nonnull_dangling", since = "1.36.0")]
    #[must_use]
    #[inline]
    #[ensures(|result| !result.pointer.is_null() && result.pointer.is_aligned())]
    pub const fn dangling() -> Self {
        let align = crate::ptr::Alignment::of::<T>();
        NonNull::without_provenance(align.as_nonzero())
    }

    /// Converts an address back to a mutable pointer, picking up some previously 'exposed'
    /// [provenance][crate::ptr#provenance].
    ///
    /// For more details, see the equivalent method on a raw pointer, [`ptr::with_exposed_provenance_mut`].
    ///
    /// This is an [Exposed Provenance][crate::ptr#exposed-provenance] API.
    #[unstable(feature = "nonnull_provenance", issue = "135243")]
    #[inline]
    pub fn with_exposed_provenance(addr: NonZero<usize>) -> Self {
        // SAFETY: we know `addr` is non-zero.
        unsafe {
            let ptr = crate::ptr::with_exposed_provenance_mut(addr.get());
            NonNull::new_unchecked(ptr)
        }
    }

    /// Returns a shared references to the value. In contrast to [`as_ref`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the mutable counterpart see [`as_uninit_mut`].
    ///
    /// [`as_ref`]: NonNull::as_ref
    /// [`as_uninit_mut`]: NonNull::as_uninit_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    /// Note that because the created reference is to `MaybeUninit<T>`, the
    /// source pointer can point to uninitialized memory.
    #[inline]
    #[must_use]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    #[requires(ub_checks::can_dereference(self.as_ptr()))] // Ensure the pointer is valid to create a reference.
    #[ensures(|result: &&MaybeUninit<T>| core::ptr::eq(*result, self.cast().as_ptr()))] // Ensure returned reference points to the correct memory location.
    pub const unsafe fn as_uninit_ref<'a>(self) -> &'a MaybeUninit<T> {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &*self.cast().as_ptr() }
    }

    /// Returns a unique references to the value. In contrast to [`as_mut`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the shared counterpart see [`as_uninit_ref`].
    ///
    /// [`as_mut`]: NonNull::as_mut
    /// [`as_uninit_ref`]: NonNull::as_uninit_ref
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    /// Note that because the created reference is to `MaybeUninit<T>`, the
    /// source pointer can point to uninitialized memory.
    #[inline]
    #[must_use]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    #[requires(ub_checks::can_dereference(self.as_ptr()))] // Ensure pointer is valid to create a mutable reference.
    #[ensures(|result: &&mut MaybeUninit<T>| core::ptr::eq(*result, self.cast().as_ptr()))] // Ensure the returned reference points to the correct memory.
    pub const unsafe fn as_uninit_mut<'a>(self) -> &'a mut MaybeUninit<T> {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &mut *self.cast().as_ptr() }
    }
}

impl<T: ?Sized> NonNull<T> {
    /// Creates a new `NonNull`.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let mut x = 0u32;
    /// let ptr = unsafe { NonNull::new_unchecked(&mut x as *mut _) };
    /// ```
    ///
    /// *Incorrect* usage of this function:
    ///
    /// ```rust,no_run
    /// use std::ptr::NonNull;
    ///
    /// // NEVER DO THAT!!! This is undefined behavior. ⚠️
    /// let ptr = unsafe { NonNull::<u32>::new_unchecked(std::ptr::null_mut()) };
    /// ```
    #[stable(feature = "nonnull", since = "1.25.0")]
    #[rustc_const_stable(feature = "const_nonnull_new_unchecked", since = "1.25.0")]
    #[inline]
    #[requires(!ptr.is_null())]
    #[ensures(|result| result.as_ptr() == ptr)]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        // SAFETY: the caller must guarantee that `ptr` is non-null.
        unsafe {
            assert_unsafe_precondition!(
                check_language_ub,
                "NonNull::new_unchecked requires that the pointer is non-null",
                (ptr: *mut () = ptr as *mut ()) => !ptr.is_null()
            );
            NonNull { pointer: ptr as _ }
        }
    }

    /// Creates a new `NonNull` if `ptr` is non-null.
    ///
    /// # Panics during const evaluation
    ///
    /// This method will panic during const evaluation if the pointer cannot be
    /// determined to be null or not. See [`is_null`] for more information.
    ///
    /// [`is_null`]: ../primitive.pointer.html#method.is_null-1
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNull::<u32>::new(&mut x as *mut _).expect("ptr is null!");
    ///
    /// if let Some(ptr) = NonNull::<u32>::new(std::ptr::null_mut()) {
    ///     unreachable!();
    /// }
    /// ```
    #[stable(feature = "nonnull", since = "1.25.0")]
    #[rustc_const_stable(feature = "const_nonnull_new", since = "1.85.0")]
    #[inline]
    #[ensures(|result| result.is_some() == !ptr.is_null())]
    #[ensures(|result| result.is_none() || result.expect("ptr is null!").as_ptr() == ptr)]
    pub const fn new(ptr: *mut T) -> Option<Self> {
        if !ptr.is_null() {
            // SAFETY: The pointer is already checked and is not null
            Some(unsafe { Self::new_unchecked(ptr) })
        } else {
            None
        }
    }

    /// Converts a reference to a `NonNull` pointer.
    #[unstable(feature = "non_null_from_ref", issue = "130823")]
    #[inline]
    pub const fn from_ref(r: &T) -> Self {
        // SAFETY: A reference cannot be null.
        unsafe { NonNull { pointer: r as *const T } }
    }

    /// Converts a mutable reference to a `NonNull` pointer.
    #[unstable(feature = "non_null_from_ref", issue = "130823")]
    #[inline]
    pub const fn from_mut(r: &mut T) -> Self {
        // SAFETY: A mutable reference cannot be null.
        unsafe { NonNull { pointer: r as *mut T } }
    }

    /// Performs the same functionality as [`std::ptr::from_raw_parts`], except that a
    /// `NonNull` pointer is returned, as opposed to a raw `*const` pointer.
    ///
    /// See the documentation of [`std::ptr::from_raw_parts`] for more details.
    ///
    /// [`std::ptr::from_raw_parts`]: crate::ptr::from_raw_parts
    #[unstable(feature = "ptr_metadata", issue = "81513")]
    #[inline]
    #[ensures(|result| !result.pointer.is_null())]
    pub const fn from_raw_parts(
        data_pointer: NonNull<impl super::Thin>,
        metadata: <T as super::Pointee>::Metadata,
    ) -> NonNull<T> {
        // SAFETY: The result of `ptr::from::raw_parts_mut` is non-null because `data_pointer` is.
        unsafe {
            NonNull::new_unchecked(super::from_raw_parts_mut(data_pointer.as_ptr(), metadata))
        }
    }

    /// Decompose a (possibly wide) pointer into its data pointer and metadata components.
    ///
    /// The pointer can be later reconstructed with [`NonNull::from_raw_parts`].
    #[unstable(feature = "ptr_metadata", issue = "81513")]
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[inline]
    #[ensures(|(data_ptr, metadata)| !data_ptr.as_ptr().is_null())]
    #[ensures(|(data_ptr, metadata)| self.as_ptr() as *const () == data_ptr.as_ptr() as *const ())]
    pub const fn to_raw_parts(self) -> (NonNull<()>, <T as super::Pointee>::Metadata) {
        (self.cast(), super::metadata(self.as_ptr()))
    }

    /// Gets the "address" portion of the pointer.
    ///
    /// For more details, see the equivalent method on a raw pointer, [`pointer::addr`].
    ///
    /// This is a [Strict Provenance][crate::ptr#strict-provenance] API.
    #[must_use]
    #[inline]
    #[stable(feature = "strict_provenance", since = "1.84.0")]
    #[ensures(|result| result.get() == self.as_ptr() as *const() as usize)]
    pub fn addr(self) -> NonZero<usize> {
        // SAFETY: The pointer is guaranteed by the type to be non-null,
        // meaning that the address will be non-zero.
        unsafe { NonZero::new_unchecked(self.as_ptr().addr()) }
    }

    /// Exposes the ["provenance"][crate::ptr#provenance] part of the pointer for future use in
    /// [`with_exposed_provenance`][NonNull::with_exposed_provenance] and returns the "address" portion.
    ///
    /// For more details, see the equivalent method on a raw pointer, [`pointer::expose_provenance`].
    ///
    /// This is an [Exposed Provenance][crate::ptr#exposed-provenance] API.
    #[unstable(feature = "nonnull_provenance", issue = "135243")]
    pub fn expose_provenance(self) -> NonZero<usize> {
        // SAFETY: The pointer is guaranteed by the type to be non-null,
        // meaning that the address will be non-zero.
        unsafe { NonZero::new_unchecked(self.as_ptr().expose_provenance()) }
    }

    /// Creates a new pointer with the given address and the [provenance][crate::ptr#provenance] of
    /// `self`.
    ///
    /// For more details, see the equivalent method on a raw pointer, [`pointer::with_addr`].
    ///
    /// This is a [Strict Provenance][crate::ptr#strict-provenance] API.
    #[must_use]
    #[inline]
    #[stable(feature = "strict_provenance", since = "1.84.0")]
    #[ensures(|result: &Self| !result.as_ptr().is_null() && result.addr() == addr)]
    pub fn with_addr(self, addr: NonZero<usize>) -> Self {
        // SAFETY: The result of `ptr::from::with_addr` is non-null because `addr` is guaranteed to be non-zero.
        unsafe { NonNull::new_unchecked(self.as_ptr().with_addr(addr.get()) as *mut _) }
    }

    /// Creates a new pointer by mapping `self`'s address to a new one, preserving the
    /// [provenance][crate::ptr#provenance] of `self`.
    ///
    /// For more details, see the equivalent method on a raw pointer, [`pointer::map_addr`].
    ///
    /// This is a [Strict Provenance][crate::ptr#strict-provenance] API.
    #[must_use]
    #[inline]
    #[stable(feature = "strict_provenance", since = "1.84.0")]
    #[ensures(|result: &Self| !result.as_ptr().is_null())]
    pub fn map_addr(self, f: impl FnOnce(NonZero<usize>) -> NonZero<usize>) -> Self {
        self.with_addr(f(self.addr()))
    }

    /// Acquires the underlying `*mut` pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNull::new(&mut x).expect("ptr is null!");
    ///
    /// let x_value = unsafe { *ptr.as_ptr() };
    /// assert_eq!(x_value, 0);
    ///
    /// unsafe { *ptr.as_ptr() += 2; }
    /// let x_value = unsafe { *ptr.as_ptr() };
    /// assert_eq!(x_value, 2);
    /// ```
    #[stable(feature = "nonnull", since = "1.25.0")]
    #[rustc_const_stable(feature = "const_nonnull_as_ptr", since = "1.32.0")]
    #[rustc_never_returns_null_ptr]
    #[must_use]
    #[inline(always)]
    //Ensures address of resulting pointer is same as original
    #[ensures(|result: &*mut T| *result == self.pointer as *mut T)]
    pub const fn as_ptr(self) -> *mut T {
        // This is a transmute for the same reasons as `NonZero::get`.

        // SAFETY: `NonNull` is `transparent` over a `*const T`, and `*const T`
        // and `*mut T` have the same layout, so transitively we can transmute
        // our `NonNull` to a `*mut T` directly.
        unsafe { mem::transmute::<Self, *mut T>(self) }
    }

    /// Returns a shared reference to the value. If the value may be uninitialized, [`as_uninit_ref`]
    /// must be used instead.
    ///
    /// For the mutable counterpart see [`as_mut`].
    ///
    /// [`as_uninit_ref`]: NonNull::as_uninit_ref
    /// [`as_mut`]: NonNull::as_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNull::new(&mut x as *mut _).expect("ptr is null!");
    ///
    /// let ref_x = unsafe { ptr.as_ref() };
    /// println!("{ref_x}");
    /// ```
    ///
    /// [the module documentation]: crate::ptr#safety
    #[stable(feature = "nonnull", since = "1.25.0")]
    #[rustc_const_stable(feature = "const_nonnull_as_ref", since = "1.73.0")]
    #[must_use]
    #[inline(always)]
    #[requires(ub_checks::can_dereference(self.as_ptr() as *const()))] // Ensure input is convertible to a reference
    #[ensures(|result: &&T| core::ptr::eq(*result, self.as_ptr()))] // Ensure returned reference matches pointer
    pub const unsafe fn as_ref<'a>(&self) -> &'a T {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        // `cast_const` avoids a mutable raw pointer deref.
        unsafe { &*self.as_ptr().cast_const() }
    }

    /// Returns a unique reference to the value. If the value may be uninitialized, [`as_uninit_mut`]
    /// must be used instead.
    ///
    /// For the shared counterpart see [`as_ref`].
    ///
    /// [`as_uninit_mut`]: NonNull::as_uninit_mut
    /// [`as_ref`]: NonNull::as_ref
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let mut x = 0u32;
    /// let mut ptr = NonNull::new(&mut x).expect("null pointer");
    ///
    /// let x_ref = unsafe { ptr.as_mut() };
    /// assert_eq!(*x_ref, 0);
    /// *x_ref += 2;
    /// assert_eq!(*x_ref, 2);
    /// ```
    ///
    /// [the module documentation]: crate::ptr#safety
    #[stable(feature = "nonnull", since = "1.25.0")]
    #[rustc_const_stable(feature = "const_ptr_as_ref", since = "1.83.0")]
    #[must_use]
    #[inline(always)]
    #[requires(ub_checks::can_dereference(self.as_ptr() as *const()))]
    // verify result (a mutable reference) is still associated with the same memory address as the raw pointer stored in self
    #[ensures(|result: &&mut T| core::ptr::eq(*result, self.as_ptr()))]
    pub const unsafe fn as_mut<'a>(&mut self) -> &'a mut T {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a mutable reference.
        unsafe { &mut *self.as_ptr() }
    }

    /// Casts to a pointer of another type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNull::new(&mut x as *mut _).expect("null pointer");
    ///
    /// let casted_ptr = ptr.cast::<i8>();
    /// let raw_ptr: *mut i8 = casted_ptr.as_ptr();
    /// ```
    #[stable(feature = "nonnull_cast", since = "1.27.0")]
    #[rustc_const_stable(feature = "const_nonnull_cast", since = "1.36.0")]
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[inline]
    // Address preservation
    #[ensures(|result: &NonNull<U>| result.as_ptr().addr() == self.as_ptr().addr())]
    pub const fn cast<U>(self) -> NonNull<U> {
        // SAFETY: `self` is a `NonNull` pointer which is necessarily non-null
        unsafe { NonNull { pointer: self.as_ptr() as *mut U } }
    }

    /// Adds an offset to a pointer.
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * The computed offset, `count * size_of::<T>()` bytes, must not overflow `isize`.
    ///
    /// * If the computed offset is non-zero, then `self` must be derived from a pointer to some
    ///   [allocated object], and the entire memory range between `self` and the result must be in
    ///   bounds of that allocated object. In particular, this range must not "wrap around" the edge
    ///   of the address space.
    ///
    /// Allocated objects can never be larger than `isize::MAX` bytes, so if the computed offset
    /// stays in bounds of the allocated object, it is guaranteed to satisfy the first requirement.
    /// This implies, for instance, that `vec.as_ptr().add(vec.len())` (for `vec: Vec<T>`) is always
    /// safe.
    ///
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let mut s = [1, 2, 3];
    /// let ptr: NonNull<u32> = NonNull::new(s.as_mut_ptr()).unwrap();
    ///
    /// unsafe {
    ///     println!("{}", ptr.offset(1).read());
    ///     println!("{}", ptr.offset(2).read());
    /// }
    /// ```
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(
        count.checked_mul(core::mem::size_of::<T>() as isize).is_some() &&
       (self.as_ptr() as isize).checked_add(count.wrapping_mul(core::mem::size_of::<T>() as isize)).is_some() &&
        (count == 0 || core::ub_checks::same_allocation(self.as_ptr() as *const (), self.as_ptr().wrapping_offset(count) as *const ()))
    )]
    #[ensures(|result: &Self| result.as_ptr() == self.as_ptr().wrapping_offset(count))]
    pub const unsafe fn offset(self, count: isize) -> Self
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `offset`.
        // Additionally safety contract of `offset` guarantees that the resulting pointer is
        // pointing to an allocation, there can't be an allocation at null, thus it's safe to
        // construct `NonNull`.
        unsafe { NonNull { pointer: intrinsics::offset(self.as_ptr(), count) } }
    }

    /// Calculates the offset from a pointer in bytes.
    ///
    /// `count` is in units of **bytes**.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [offset][pointer::offset] on it. See that method for documentation
    /// and safety requirements.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(
        (self.as_ptr().addr() as isize).checked_add(count).is_some() &&
        core::ub_checks::same_allocation(self.as_ptr(), self.as_ptr().wrapping_byte_offset(count))
    )]
    #[ensures(|result: &Self| result.as_ptr() == self.as_ptr().wrapping_byte_offset(count))]
    pub const unsafe fn byte_offset(self, count: isize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `offset` and `byte_offset` has
        // the same safety contract.
        // Additionally safety contract of `offset` guarantees that the resulting pointer is
        // pointing to an allocation, there can't be an allocation at null, thus it's safe to
        // construct `NonNull`.
        unsafe { NonNull { pointer: self.as_ptr().byte_offset(count) } }
    }

    /// Adds an offset to a pointer (convenience for `.offset(count as isize)`).
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * The computed offset, `count * size_of::<T>()` bytes, must not overflow `isize`.
    ///
    /// * If the computed offset is non-zero, then `self` must be derived from a pointer to some
    ///   [allocated object], and the entire memory range between `self` and the result must be in
    ///   bounds of that allocated object. In particular, this range must not "wrap around" the edge
    ///   of the address space.
    ///
    /// Allocated objects can never be larger than `isize::MAX` bytes, so if the computed offset
    /// stays in bounds of the allocated object, it is guaranteed to satisfy the first requirement.
    /// This implies, for instance, that `vec.as_ptr().add(vec.len())` (for `vec: Vec<T>`) is always
    /// safe.
    ///
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let s: &str = "123";
    /// let ptr: NonNull<u8> = NonNull::new(s.as_ptr().cast_mut()).unwrap();
    ///
    /// unsafe {
    ///     println!("{}", ptr.add(1).read() as char);
    ///     println!("{}", ptr.add(2).read() as char);
    /// }
    /// ```
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(count.checked_mul(core::mem::size_of::<T>()).is_some()
        && count * core::mem::size_of::<T>() <= isize::MAX as usize
        && (self.pointer as isize).checked_add(count as isize * core::mem::size_of::<T>() as isize).is_some() // check wrapping add
        && core::ub_checks::same_allocation(self.pointer, self.pointer.wrapping_offset(count as isize)))]
    #[ensures(|result: &NonNull<T>| result.as_ptr() == self.as_ptr().offset(count as isize))]
    pub const unsafe fn add(self, count: usize) -> Self
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `offset`.
        // Additionally safety contract of `offset` guarantees that the resulting pointer is
        // pointing to an allocation, there can't be an allocation at null, thus it's safe to
        // construct `NonNull`.
        unsafe { NonNull { pointer: intrinsics::offset(self.as_ptr(), count) } }
    }

    /// Calculates the offset from a pointer in bytes (convenience for `.byte_offset(count as isize)`).
    ///
    /// `count` is in units of bytes.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [`add`][NonNull::add] on it. See that method for documentation
    /// and safety requirements.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(
        count == 0 || (
            (core::mem::size_of_val_raw(self.as_ptr() as * const _) > 0) &&
            (count <= (isize::MAX as usize)) &&
            (self.as_ptr().addr().checked_add(count).is_some()) &&
            (core::ub_checks::same_allocation(self.as_ptr(), self.as_ptr().wrapping_byte_add(count)))
        )
    )]
    pub const unsafe fn byte_add(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `add` and `byte_add` has the same
        // safety contract.
        // Additionally safety contract of `add` guarantees that the resulting pointer is pointing
        // to an allocation, there can't be an allocation at null, thus it's safe to construct
        // `NonNull`.
        unsafe { NonNull { pointer: self.as_ptr().byte_add(count) } }
    }

    /// Subtracts an offset from a pointer (convenience for
    /// `.offset((count as isize).wrapping_neg())`).
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * The computed offset, `count * size_of::<T>()` bytes, must not overflow `isize`.
    ///
    /// * If the computed offset is non-zero, then `self` must be derived from a pointer to some
    ///   [allocated object], and the entire memory range between `self` and the result must be in
    ///   bounds of that allocated object. In particular, this range must not "wrap around" the edge
    ///   of the address space.
    ///
    /// Allocated objects can never be larger than `isize::MAX` bytes, so if the computed offset
    /// stays in bounds of the allocated object, it is guaranteed to satisfy the first requirement.
    /// This implies, for instance, that `vec.as_ptr().add(vec.len())` (for `vec: Vec<T>`) is always
    /// safe.
    ///
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let s: &str = "123";
    ///
    /// unsafe {
    ///     let end: NonNull<u8> = NonNull::new(s.as_ptr().cast_mut()).unwrap().add(3);
    ///     println!("{}", end.sub(1).read() as char);
    ///     println!("{}", end.sub(2).read() as char);
    /// }
    /// ```
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(
        count.checked_mul(core::mem::size_of::<T>()).is_some() &&
        count * core::mem::size_of::<T>() <= isize::MAX as usize &&
        core::ub_checks::same_allocation(self.as_ptr(), self.as_ptr().wrapping_sub(count))
    )]
    #[ensures(|result: &NonNull<T>| result.as_ptr() == self.as_ptr().offset(-(count as isize)))]
    pub const unsafe fn sub(self, count: usize) -> Self
    where
        T: Sized,
    {
        if T::IS_ZST {
            // Pointer arithmetic does nothing when the pointee is a ZST.
            self
        } else {
            // SAFETY: the caller must uphold the safety contract for `offset`.
            // Because the pointee is *not* a ZST, that means that `count` is
            // at most `isize::MAX`, and thus the negation cannot overflow.
            unsafe { self.offset((count as isize).unchecked_neg()) }
        }
    }

    /// Calculates the offset from a pointer in bytes (convenience for
    /// `.byte_offset((count as isize).wrapping_neg())`).
    ///
    /// `count` is in units of bytes.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [`sub`][NonNull::sub] on it. See that method for documentation
    /// and safety requirements.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(
        count == 0 || (
            (core::mem::size_of_val_raw(self.as_ptr() as * const _) > 0) &&
            (count <= (isize::MAX as usize)) &&
            (self.as_ptr().addr().checked_sub(count).is_some()) &&
            (core::ub_checks::same_allocation(self.as_ptr(), self.as_ptr().wrapping_byte_sub(count)))
        )
    )]
    pub const unsafe fn byte_sub(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `sub` and `byte_sub` has the same
        // safety contract.
        // Additionally safety contract of `sub` guarantees that the resulting pointer is pointing
        // to an allocation, there can't be an allocation at null, thus it's safe to construct
        // `NonNull`.
        unsafe { NonNull { pointer: self.as_ptr().byte_sub(count) } }
    }

    /// Calculates the distance between two pointers within the same allocation. The returned value is in
    /// units of T: the distance in bytes divided by `mem::size_of::<T>()`.
    ///
    /// This is equivalent to `(self as isize - origin as isize) / (mem::size_of::<T>() as isize)`,
    /// except that it has a lot more opportunities for UB, in exchange for the compiler
    /// better understanding what you are doing.
    ///
    /// The primary motivation of this method is for computing the `len` of an array/slice
    /// of `T` that you are currently representing as a "start" and "end" pointer
    /// (and "end" is "one past the end" of the array).
    /// In that case, `end.offset_from(start)` gets you the length of the array.
    ///
    /// All of the following safety requirements are trivially satisfied for this usecase.
    ///
    /// [`offset`]: #method.offset
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * `self` and `origin` must either
    ///
    ///   * point to the same address, or
    ///   * both be *derived from* a pointer to the same [allocated object], and the memory range between
    ///     the two pointers must be in bounds of that object. (See below for an example.)
    ///
    /// * The distance between the pointers, in bytes, must be an exact multiple
    ///   of the size of `T`.
    ///
    /// As a consequence, the absolute distance between the pointers, in bytes, computed on
    /// mathematical integers (without "wrapping around"), cannot overflow an `isize`. This is
    /// implied by the in-bounds requirement, and the fact that no allocated object can be larger
    /// than `isize::MAX` bytes.
    ///
    /// The requirement for pointers to be derived from the same allocated object is primarily
    /// needed for `const`-compatibility: the distance between pointers into *different* allocated
    /// objects is not known at compile-time. However, the requirement also exists at
    /// runtime and may be exploited by optimizations. If you wish to compute the difference between
    /// pointers that are not guaranteed to be from the same allocation, use `(self as isize -
    /// origin as isize) / mem::size_of::<T>()`.
    // FIXME: recommend `addr()` instead of `as usize` once that is stable.
    ///
    /// [`add`]: #method.add
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Panics
    ///
    /// This function panics if `T` is a Zero-Sized Type ("ZST").
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// let a = [0; 5];
    /// let ptr1: NonNull<u32> = NonNull::from(&a[1]);
    /// let ptr2: NonNull<u32> = NonNull::from(&a[3]);
    /// unsafe {
    ///     assert_eq!(ptr2.offset_from(ptr1), 2);
    ///     assert_eq!(ptr1.offset_from(ptr2), -2);
    ///     assert_eq!(ptr1.offset(2), ptr2);
    ///     assert_eq!(ptr2.offset(-2), ptr1);
    /// }
    /// ```
    ///
    /// *Incorrect* usage:
    ///
    /// ```rust,no_run
    /// use std::ptr::NonNull;
    ///
    /// let ptr1 = NonNull::new(Box::into_raw(Box::new(0u8))).unwrap();
    /// let ptr2 = NonNull::new(Box::into_raw(Box::new(1u8))).unwrap();
    /// let diff = (ptr2.addr().get() as isize).wrapping_sub(ptr1.addr().get() as isize);
    /// // Make ptr2_other an "alias" of ptr2.add(1), but derived from ptr1.
    /// let diff_plus_1 = diff.wrapping_add(1);
    /// let ptr2_other = NonNull::new(ptr1.as_ptr().wrapping_byte_offset(diff_plus_1)).unwrap();
    /// assert_eq!(ptr2.addr(), ptr2_other.addr());
    /// // Since ptr2_other and ptr2 are derived from pointers to different objects,
    /// // computing their offset is undefined behavior, even though
    /// // they point to addresses that are in-bounds of the same object!
    ///
    /// let one = unsafe { ptr2_other.offset_from(ptr2) }; // Undefined Behavior! ⚠️
    /// ```
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(
        core::ub_checks::same_allocation(self.as_ptr(), origin.as_ptr()) &&
        (self.as_ptr().addr().checked_sub(origin.as_ptr().addr()).is_some_and(|distance| distance % core::mem::size_of::<T>() == 0) ||
        origin.as_ptr().addr().checked_sub(self.as_ptr().addr()).is_some_and(|distance| distance % core::mem::size_of::<T>() == 0))
    )] // Ensure both pointers meet safety conditions for offset_from
    #[ensures(|result: &isize| *result == (self.as_ptr() as isize - origin.as_ptr() as isize) / core::mem::size_of::<T>() as isize)]
    pub const unsafe fn offset_from(self, origin: NonNull<T>) -> isize
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `offset_from`.
        unsafe { self.as_ptr().offset_from(origin.as_ptr()) }
    }

    /// Calculates the distance between two pointers within the same allocation. The returned value is in
    /// units of **bytes**.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [`offset_from`][NonNull::offset_from] on it. See that method for
    /// documentation and safety requirements.
    ///
    /// For non-`Sized` pointees this operation considers only the data pointers,
    /// ignoring the metadata.
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(
        self.as_ptr().addr() == origin.as_ptr().addr() ||
        core::ub_checks::same_allocation(self.as_ptr() as *const(), origin.as_ptr() as *const())
    )]
    #[ensures(
        |result: &isize|
        *result == (self.as_ptr() as *const u8).offset_from(origin.as_ptr() as *const u8)
    )]
    pub const unsafe fn byte_offset_from<U: ?Sized>(self, origin: NonNull<U>) -> isize {
        // SAFETY: the caller must uphold the safety contract for `byte_offset_from`.
        unsafe { self.as_ptr().byte_offset_from(origin.as_ptr()) }
    }

    // N.B. `wrapping_offset``, `wrapping_add`, etc are not implemented because they can wrap to null

    /// Calculates the distance between two pointers within the same allocation, *where it's known that
    /// `self` is equal to or greater than `origin`*. The returned value is in
    /// units of T: the distance in bytes is divided by `mem::size_of::<T>()`.
    ///
    /// This computes the same value that [`offset_from`](#method.offset_from)
    /// would compute, but with the added precondition that the offset is
    /// guaranteed to be non-negative.  This method is equivalent to
    /// `usize::try_from(self.offset_from(origin)).unwrap_unchecked()`,
    /// but it provides slightly more information to the optimizer, which can
    /// sometimes allow it to optimize slightly better with some backends.
    ///
    /// This method can be though of as recovering the `count` that was passed
    /// to [`add`](#method.add) (or, with the parameters in the other order,
    /// to [`sub`](#method.sub)).  The following are all equivalent, assuming
    /// that their safety preconditions are met:
    /// ```rust
    /// # #![feature(ptr_sub_ptr)]
    /// # unsafe fn blah(ptr: std::ptr::NonNull<u32>, origin: std::ptr::NonNull<u32>, count: usize) -> bool {
    /// ptr.sub_ptr(origin) == count
    /// # &&
    /// origin.add(count) == ptr
    /// # &&
    /// ptr.sub(count) == origin
    /// # }
    /// ```
    ///
    /// # Safety
    ///
    /// - The distance between the pointers must be non-negative (`self >= origin`)
    ///
    /// - *All* the safety conditions of [`offset_from`](#method.offset_from)
    ///   apply to this method as well; see it for the full details.
    ///
    /// Importantly, despite the return type of this method being able to represent
    /// a larger offset, it's still *not permitted* to pass pointers which differ
    /// by more than `isize::MAX` *bytes*.  As such, the result of this method will
    /// always be less than or equal to `isize::MAX as usize`.
    ///
    /// # Panics
    ///
    /// This function panics if `T` is a Zero-Sized Type ("ZST").
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(ptr_sub_ptr)]
    /// use std::ptr::NonNull;
    ///
    /// let a = [0; 5];
    /// let ptr1: NonNull<u32> = NonNull::from(&a[1]);
    /// let ptr2: NonNull<u32> = NonNull::from(&a[3]);
    /// unsafe {
    ///     assert_eq!(ptr2.sub_ptr(ptr1), 2);
    ///     assert_eq!(ptr1.add(2), ptr2);
    ///     assert_eq!(ptr2.sub(2), ptr1);
    ///     assert_eq!(ptr2.sub_ptr(ptr2), 0);
    /// }
    ///
    /// // This would be incorrect, as the pointers are not correctly ordered:
    /// // ptr1.sub_ptr(ptr2)
    /// ```
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[unstable(feature = "ptr_sub_ptr", issue = "95892")]
    #[rustc_const_unstable(feature = "const_ptr_sub_ptr", issue = "95892")]
    #[requires(
        self.as_ptr().addr().checked_sub(subtracted.as_ptr().addr()).is_some() &&
        core::ub_checks::same_allocation(self.as_ptr(), subtracted.as_ptr()) &&
        (self.as_ptr().addr()) >= (subtracted.as_ptr().addr()) &&
        (self.as_ptr().addr() - subtracted.as_ptr().addr()) % core::mem::size_of::<T>() == 0
    )]
    #[ensures(|result: &usize| *result == self.as_ptr().offset_from(subtracted.as_ptr()) as usize)]
    pub const unsafe fn sub_ptr(self, subtracted: NonNull<T>) -> usize
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `sub_ptr`.
        unsafe { self.as_ptr().sub_ptr(subtracted.as_ptr()) }
    }

    /// Calculates the distance between two pointers within the same allocation, *where it's known that
    /// `self` is equal to or greater than `origin`*. The returned value is in
    /// units of **bytes**.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [`sub_ptr`][NonNull::sub_ptr] on it. See that method for
    /// documentation and safety requirements.
    ///
    /// For non-`Sized` pointees this operation considers only the data pointers,
    /// ignoring the metadata.
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[unstable(feature = "ptr_sub_ptr", issue = "95892")]
    #[rustc_const_unstable(feature = "const_ptr_sub_ptr", issue = "95892")]
    pub const unsafe fn byte_sub_ptr<U: ?Sized>(self, origin: NonNull<U>) -> usize {
        // SAFETY: the caller must uphold the safety contract for `byte_sub_ptr`.
        unsafe { self.as_ptr().byte_sub_ptr(origin.as_ptr()) }
    }

    /// Reads the value from `self` without moving it. This leaves the
    /// memory in `self` unchanged.
    ///
    /// See [`ptr::read`] for safety concerns and examples.
    ///
    /// [`ptr::read`]: crate::ptr::read()
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(ub_checks::can_dereference(self.pointer))]
    pub const unsafe fn read(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `read`.
        unsafe { ptr::read(self.as_ptr()) }
    }

    /// Performs a volatile read of the value from `self` without moving it. This
    /// leaves the memory in `self` unchanged.
    ///
    /// Volatile operations are intended to act on I/O memory, and are guaranteed
    /// to not be elided or reordered by the compiler across other volatile
    /// operations.
    ///
    /// See [`ptr::read_volatile`] for safety concerns and examples.
    ///
    /// [`ptr::read_volatile`]: crate::ptr::read_volatile()
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(ub_checks::can_dereference(self.pointer))]
    pub unsafe fn read_volatile(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `read_volatile`.
        unsafe { ptr::read_volatile(self.as_ptr()) }
    }

    /// Reads the value from `self` without moving it. This leaves the
    /// memory in `self` unchanged.
    ///
    /// Unlike `read`, the pointer may be unaligned.
    ///
    /// See [`ptr::read_unaligned`] for safety concerns and examples.
    ///
    /// [`ptr::read_unaligned`]: crate::ptr::read_unaligned()
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(ub_checks::can_read_unaligned(self.pointer))]
    pub const unsafe fn read_unaligned(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `read_unaligned`.
        unsafe { ptr::read_unaligned(self.as_ptr()) }
    }

    /// Copies `count * size_of<T>` bytes from `self` to `dest`. The source
    /// and destination may overlap.
    ///
    /// NOTE: this has the *same* argument order as [`ptr::copy`].
    ///
    /// See [`ptr::copy`] for safety concerns and examples.
    ///
    /// [`ptr::copy`]: crate::ptr::copy()
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[cfg_attr(kani, kani::modifies(NonNull::slice_from_raw_parts(dest, count).as_ptr()))]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[requires(count.checked_mul(core::mem::size_of::<T>()).map_or_else(|| false, |size| size <= isize::MAX as usize)
        && ub_checks::can_dereference(NonNull::slice_from_raw_parts(self, count).as_ptr())
        && ub_checks::can_write(NonNull::slice_from_raw_parts(dest, count).as_ptr()))]
    #[ensures(|result: &()| ub_checks::can_dereference(self.as_ptr() as *const u8)
        && ub_checks::can_dereference(dest.as_ptr() as *const u8))]
    pub const unsafe fn copy_to(self, dest: NonNull<T>, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy`.
        unsafe { ptr::copy(self.as_ptr(), dest.as_ptr(), count) }
    }

    /// Copies `count * size_of<T>` bytes from `self` to `dest`. The source
    /// and destination may *not* overlap.
    ///
    /// NOTE: this has the *same* argument order as [`ptr::copy_nonoverlapping`].
    ///
    /// See [`ptr::copy_nonoverlapping`] for safety concerns and examples.
    ///
    /// [`ptr::copy_nonoverlapping`]: crate::ptr::copy_nonoverlapping()
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[cfg_attr(kani, kani::modifies(NonNull::slice_from_raw_parts(dest, count).as_ptr()))]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[requires(count.checked_mul(core::mem::size_of::<T>()).map_or_else(|| false, |size| size <= isize::MAX as usize)
        && ub_checks::can_dereference(NonNull::slice_from_raw_parts(self, count).as_ptr())
        && ub_checks::can_write(NonNull::slice_from_raw_parts(dest, count).as_ptr())
        && ub_checks::maybe_is_nonoverlapping(self.as_ptr() as *const (), dest.as_ptr() as *const (), count, core::mem::size_of::<T>()))]
    #[ensures(|result: &()| ub_checks::can_dereference(self.as_ptr() as *const u8)
        && ub_checks::can_dereference(dest.as_ptr() as *const u8))]
    pub const unsafe fn copy_to_nonoverlapping(self, dest: NonNull<T>, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy_nonoverlapping`.
        unsafe { ptr::copy_nonoverlapping(self.as_ptr(), dest.as_ptr(), count) }
    }

    /// Copies `count * size_of<T>` bytes from `src` to `self`. The source
    /// and destination may overlap.
    ///
    /// NOTE: this has the *opposite* argument order of [`ptr::copy`].
    ///
    /// See [`ptr::copy`] for safety concerns and examples.
    ///
    /// [`ptr::copy`]: crate::ptr::copy()
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[cfg_attr(kani, kani::modifies(NonNull::slice_from_raw_parts(self, count).as_ptr()))]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[requires(count.checked_mul(core::mem::size_of::<T>()).map_or_else(|| false, |size| size <= isize::MAX as usize)
        && ub_checks::can_dereference(NonNull::slice_from_raw_parts(src, count).as_ptr())
        && ub_checks::can_write(NonNull::slice_from_raw_parts(self, count).as_ptr()))]
    #[ensures(|result: &()| ub_checks::can_dereference(src.as_ptr() as *const u8)
        && ub_checks::can_dereference(self.as_ptr() as *const u8))]
    pub const unsafe fn copy_from(self, src: NonNull<T>, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy`.
        unsafe { ptr::copy(src.as_ptr(), self.as_ptr(), count) }
    }

    /// Copies `count * size_of<T>` bytes from `src` to `self`. The source
    /// and destination may *not* overlap.
    ///
    /// NOTE: this has the *opposite* argument order of [`ptr::copy_nonoverlapping`].
    ///
    /// See [`ptr::copy_nonoverlapping`] for safety concerns and examples.
    ///
    /// [`ptr::copy_nonoverlapping`]: crate::ptr::copy_nonoverlapping()
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[cfg_attr(kani, kani::modifies(NonNull::slice_from_raw_parts(self, count).as_ptr()))]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[requires(count.checked_mul(core::mem::size_of::<T>()).map_or_else(|| false, |size| size <= isize::MAX as usize)
        && ub_checks::can_dereference(NonNull::slice_from_raw_parts(src, count).as_ptr())
        && ub_checks::can_write(NonNull::slice_from_raw_parts(self, count).as_ptr())
        && ub_checks::maybe_is_nonoverlapping(src.as_ptr() as *const (), self.as_ptr() as *const (), count, core::mem::size_of::<T>()))]
    #[ensures(|result: &()| ub_checks::can_dereference(src.as_ptr() as *const u8)
        && ub_checks::can_dereference(self.as_ptr() as *const u8))]
    pub const unsafe fn copy_from_nonoverlapping(self, src: NonNull<T>, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy_nonoverlapping`.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), self.as_ptr(), count) }
    }

    /// Executes the destructor (if any) of the pointed-to value.
    ///
    /// See [`ptr::drop_in_place`] for safety concerns and examples.
    ///
    /// [`ptr::drop_in_place`]: crate::ptr::drop_in_place()
    #[inline(always)]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[requires(ub_checks::can_dereference(self.as_ptr() as *const()))] // Ensure self is aligned, initialized, and valid for read
    #[requires(ub_checks::can_write(self.as_ptr() as *mut()))] // Ensure self is valid for write
    pub unsafe fn drop_in_place(self) {
        // SAFETY: the caller must uphold the safety contract for `drop_in_place`.
        unsafe { ptr::drop_in_place(self.as_ptr()) }
    }

    /// Overwrites a memory location with the given value without reading or
    /// dropping the old value.
    ///
    /// See [`ptr::write`] for safety concerns and examples.
    ///
    /// [`ptr::write`]: crate::ptr::write()
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_ptr_write", since = "1.83.0")]
    pub const unsafe fn write(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write`.
        unsafe { ptr::write(self.as_ptr(), val) }
    }

    /// Invokes memset on the specified pointer, setting `count * size_of::<T>()`
    /// bytes of memory starting at `self` to `val`.
    ///
    /// See [`ptr::write_bytes`] for safety concerns and examples.
    ///
    /// [`ptr::write_bytes`]: crate::ptr::write_bytes()
    #[inline(always)]
    #[doc(alias = "memset")]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_ptr_write", since = "1.83.0")]
    pub const unsafe fn write_bytes(self, val: u8, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write_bytes`.
        unsafe { ptr::write_bytes(self.as_ptr(), val, count) }
    }

    /// Performs a volatile write of a memory location with the given value without
    /// reading or dropping the old value.
    ///
    /// Volatile operations are intended to act on I/O memory, and are guaranteed
    /// to not be elided or reordered by the compiler across other volatile
    /// operations.
    ///
    /// See [`ptr::write_volatile`] for safety concerns and examples.
    ///
    /// [`ptr::write_volatile`]: crate::ptr::write_volatile()
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[cfg_attr(kani, kani::modifies(self.as_ptr()))]
    #[requires(ub_checks::can_write(self.as_ptr()))]
    pub unsafe fn write_volatile(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write_volatile`.
        unsafe { ptr::write_volatile(self.as_ptr(), val) }
    }

    /// Overwrites a memory location with the given value without reading or
    /// dropping the old value.
    ///
    /// Unlike `write`, the pointer may be unaligned.
    ///
    /// See [`ptr::write_unaligned`] for safety concerns and examples.
    ///
    /// [`ptr::write_unaligned`]: crate::ptr::write_unaligned()
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_ptr_write", since = "1.83.0")]
    pub const unsafe fn write_unaligned(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write_unaligned`.
        unsafe { ptr::write_unaligned(self.as_ptr(), val) }
    }

    /// Replaces the value at `self` with `src`, returning the old
    /// value, without dropping either.
    ///
    /// See [`ptr::replace`] for safety concerns and examples.
    ///
    /// [`ptr::replace`]: crate::ptr::replace()
    #[inline(always)]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[cfg_attr(kani, kani::modifies(self.as_ptr()))]
    #[requires(ub_checks::can_dereference(self.as_ptr()))] // Ensure self is aligned, initialized, and valid for read
    #[requires(ub_checks::can_write(self.as_ptr()))] // Ensure self is valid for write
    pub unsafe fn replace(self, src: T) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `replace`.
        unsafe { ptr::replace(self.as_ptr(), src) }
    }

    /// Swaps the values at two mutable locations of the same type, without
    /// deinitializing either. They may overlap, unlike `mem::swap` which is
    /// otherwise equivalent.
    ///
    /// See [`ptr::swap`] for safety concerns and examples.
    ///
    /// [`ptr::swap`]: crate::ptr::swap()
    #[inline(always)]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[rustc_const_stable(feature = "const_swap", since = "1.85.0")]
    #[cfg_attr(kani, kani::modifies(self.as_ptr(), with.as_ptr()))]
    #[requires(ub_checks::can_dereference(self.as_ptr()) && ub_checks::can_write(self.as_ptr()))]
    #[requires(ub_checks::can_dereference(with.as_ptr()) && ub_checks::can_write(with.as_ptr()))]
    pub const unsafe fn swap(self, with: NonNull<T>)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `swap`.
        unsafe { ptr::swap(self.as_ptr(), with.as_ptr()) }
    }

    /// Computes the offset that needs to be applied to the pointer in order to make it aligned to
    /// `align`.
    ///
    /// If it is not possible to align the pointer, the implementation returns
    /// `usize::MAX`.
    ///
    /// The offset is expressed in number of `T` elements, and not bytes.
    ///
    /// There are no guarantees whatsoever that offsetting the pointer will not overflow or go
    /// beyond the allocation that the pointer points into. It is up to the caller to ensure that
    /// the returned offset is correct in all terms other than alignment.
    ///
    /// When this is called during compile-time evaluation (which is unstable), the implementation
    /// may return `usize::MAX` in cases where that can never happen at runtime. This is because the
    /// actual alignment of pointers is not known yet during compile-time, so an offset with
    /// guaranteed alignment can sometimes not be computed. For example, a buffer declared as `[u8;
    /// N]` might be allocated at an odd or an even address, but at compile-time this is not yet
    /// known, so the execution has to be correct for either choice. It is therefore impossible to
    /// find an offset that is guaranteed to be 2-aligned. (This behavior is subject to change, as usual
    /// for unstable APIs.)
    ///
    /// # Panics
    ///
    /// The function panics if `align` is not a power-of-two.
    ///
    /// # Examples
    ///
    /// Accessing adjacent `u8` as `u16`
    ///
    /// ```
    /// use std::mem::align_of;
    /// use std::ptr::NonNull;
    ///
    /// # unsafe {
    /// let x = [5_u8, 6, 7, 8, 9];
    /// let ptr = NonNull::new(x.as_ptr() as *mut u8).unwrap();
    /// let offset = ptr.align_offset(align_of::<u16>());
    ///
    /// if offset < x.len() - 1 {
    ///     let u16_ptr = ptr.add(offset).cast::<u16>();
    ///     assert!(u16_ptr.read() == u16::from_ne_bytes([5, 6]) || u16_ptr.read() == u16::from_ne_bytes([6, 7]));
    /// } else {
    ///     // while the pointer can be aligned via `offset`, it would point
    ///     // outside the allocation
    /// }
    /// # }
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "non_null_convenience", since = "1.80.0")]
    #[ensures(|result| {
        // Post-condition reference: https://github.com/model-checking/verify-rust-std/pull/69/files
        let stride = crate::mem::size_of::<T>();
        // ZSTs
        if stride == 0 {
            if self.pointer.addr() % align == 0 {
                return *result == 0;
            } else {
                return *result == usize::MAX;
            }
        }
        // In this case, the pointer cannot be aligned
        if (align % stride == 0) && (self.pointer.addr() % stride != 0) {
            return *result == usize::MAX;
        }
        // Checking if the answer should indeed be usize::MAX when align % stride != 0
        // requires computing gcd(a, stride), which is too expensive without
        // quantifiers (https://model-checking.github.io/kani/rfc/rfcs/0010-quantifiers.html).
        // This should be updated once quantifiers are available.
        if (align % stride != 0 && *result == usize::MAX) {
            return true;
        }
        // If we reach this case, either:
        //  - align % stride == 0 and self.pointer.addr() % stride == 0, so it is definitely possible to align the pointer
        //  - align % stride != 0 and result != usize::MAX, so align_offset is claiming that it's possible to align the pointer
        // Check that applying the returned result does indeed produce an aligned address
        let product = usize::wrapping_mul(*result, stride);
        let new_addr = usize::wrapping_add(product, self.pointer.addr());
        *result != usize::MAX && new_addr % align == 0
    })]
    pub fn align_offset(self, align: usize) -> usize
    where
        T: Sized,
    {
        if !align.is_power_of_two() {
            panic!("align_offset: align is not a power-of-two");
        }

        {
            // SAFETY: `align` has been checked to be a power of 2 above.
            unsafe { ptr::align_offset(self.as_ptr(), align) }
        }
    }

    /// Returns whether the pointer is properly aligned for `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// // On some platforms, the alignment of i32 is less than 4.
    /// #[repr(align(4))]
    /// struct AlignedI32(i32);
    ///
    /// let data = AlignedI32(42);
    /// let ptr = NonNull::<AlignedI32>::from(&data);
    ///
    /// assert!(ptr.is_aligned());
    /// assert!(!NonNull::new(ptr.as_ptr().wrapping_byte_add(1)).unwrap().is_aligned());
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "pointer_is_aligned", since = "1.79.0")]
    #[ensures(|result: &bool| *result == (self.as_ptr().addr() % core::mem::align_of::<T>() == 0))]
    pub fn is_aligned(self) -> bool
    where
        T: Sized,
    {
        self.as_ptr().is_aligned()
    }

    /// Returns whether the pointer is aligned to `align`.
    ///
    /// For non-`Sized` pointees this operation considers only the data pointer,
    /// ignoring the metadata.
    ///
    /// # Panics
    ///
    /// The function panics if `align` is not a power-of-two (this includes 0).
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(pointer_is_aligned_to)]
    ///
    /// // On some platforms, the alignment of i32 is less than 4.
    /// #[repr(align(4))]
    /// struct AlignedI32(i32);
    ///
    /// let data = AlignedI32(42);
    /// let ptr = &data as *const AlignedI32;
    ///
    /// assert!(ptr.is_aligned_to(1));
    /// assert!(ptr.is_aligned_to(2));
    /// assert!(ptr.is_aligned_to(4));
    ///
    /// assert!(ptr.wrapping_byte_add(2).is_aligned_to(2));
    /// assert!(!ptr.wrapping_byte_add(2).is_aligned_to(4));
    ///
    /// assert_ne!(ptr.is_aligned_to(8), ptr.wrapping_add(1).is_aligned_to(8));
    /// ```
    #[inline]
    #[must_use]
    #[unstable(feature = "pointer_is_aligned_to", issue = "96284")]
    #[requires(align.is_power_of_two())]
    #[ensures(|result: &bool| *result == (self.as_ptr().addr() % align == 0))] // Ensure the returned value is correct based on the given alignment
    pub fn is_aligned_to(self, align: usize) -> bool {
        self.as_ptr().is_aligned_to(align)
    }
}

impl<T> NonNull<[T]> {
    /// Creates a non-null raw slice from a thin pointer and a length.
    ///
    /// The `len` argument is the number of **elements**, not the number of bytes.
    ///
    /// This function is safe, but dereferencing the return value is unsafe.
    /// See the documentation of [`slice::from_raw_parts`] for slice safety requirements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ptr::NonNull;
    ///
    /// // create a slice pointer when starting out with a pointer to the first element
    /// let mut x = [5, 6, 7];
    /// let nonnull_pointer = NonNull::new(x.as_mut_ptr()).unwrap();
    /// let slice = NonNull::slice_from_raw_parts(nonnull_pointer, 3);
    /// assert_eq!(unsafe { slice.as_ref()[2] }, 7);
    /// ```
    ///
    /// (Note that this example artificially demonstrates a use of this method,
    /// but `let slice = NonNull::from(&x[..]);` would be a better way to write code like this.)
    #[stable(feature = "nonnull_slice_from_raw_parts", since = "1.70.0")]
    #[rustc_const_stable(feature = "const_slice_from_raw_parts_mut", since = "1.83.0")]
    #[must_use]
    #[inline]
    #[ensures(|result| !result.pointer.is_null()
        && result.pointer as *const T == data.pointer
        && unsafe { result.as_ref() }.len() == len)]
    pub const fn slice_from_raw_parts(data: NonNull<T>, len: usize) -> Self {
        // SAFETY: `data` is a `NonNull` pointer which is necessarily non-null
        unsafe { Self::new_unchecked(super::slice_from_raw_parts_mut(data.as_ptr(), len)) }
    }

    /// Returns the length of a non-null raw slice.
    ///
    /// The returned value is the number of **elements**, not the number of bytes.
    ///
    /// This function is safe, even when the non-null raw slice cannot be dereferenced to a slice
    /// because the pointer does not have a valid address.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ptr::NonNull;
    ///
    /// let slice: NonNull<[i8]> = NonNull::slice_from_raw_parts(NonNull::dangling(), 3);
    /// assert_eq!(slice.len(), 3);
    /// ```
    #[stable(feature = "slice_ptr_len_nonnull", since = "1.63.0")]
    #[rustc_const_stable(feature = "const_slice_ptr_len_nonnull", since = "1.63.0")]
    #[must_use]
    #[inline]
    pub const fn len(self) -> usize {
        self.as_ptr().len()
    }

    /// Returns `true` if the non-null raw slice has a length of 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ptr::NonNull;
    ///
    /// let slice: NonNull<[i8]> = NonNull::slice_from_raw_parts(NonNull::dangling(), 3);
    /// assert!(!slice.is_empty());
    /// ```
    #[stable(feature = "slice_ptr_is_empty_nonnull", since = "1.79.0")]
    #[rustc_const_stable(feature = "const_slice_ptr_is_empty_nonnull", since = "1.79.0")]
    #[must_use]
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Returns a non-null pointer to the slice's buffer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(slice_ptr_get)]
    /// use std::ptr::NonNull;
    ///
    /// let slice: NonNull<[i8]> = NonNull::slice_from_raw_parts(NonNull::dangling(), 3);
    /// assert_eq!(slice.as_non_null_ptr(), NonNull::<i8>::dangling());
    /// ```
    #[inline]
    #[must_use]
    #[unstable(feature = "slice_ptr_get", issue = "74265")]
    // Address preservation
    #[ensures(|result: &NonNull<T>| result.as_ptr().addr() == self.as_ptr().addr())]
    pub const fn as_non_null_ptr(self) -> NonNull<T> {
        self.cast()
    }

    /// Returns a raw pointer to the slice's buffer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(slice_ptr_get)]
    /// use std::ptr::NonNull;
    ///
    /// let slice: NonNull<[i8]> = NonNull::slice_from_raw_parts(NonNull::dangling(), 3);
    /// assert_eq!(slice.as_mut_ptr(), NonNull::<i8>::dangling().as_ptr());
    /// ```
    #[inline]
    #[must_use]
    #[unstable(feature = "slice_ptr_get", issue = "74265")]
    #[rustc_never_returns_null_ptr]
    // Address preservation
    #[ensures(|result: &*mut T| *result == self.pointer as *mut T)]
    pub const fn as_mut_ptr(self) -> *mut T {
        self.as_non_null_ptr().as_ptr()
    }

    /// Returns a shared reference to a slice of possibly uninitialized values. In contrast to
    /// [`as_ref`], this does not require that the value has to be initialized.
    ///
    /// For the mutable counterpart see [`as_uninit_slice_mut`].
    ///
    /// [`as_ref`]: NonNull::as_ref
    /// [`as_uninit_slice_mut`]: NonNull::as_uninit_slice_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that all of the following is true:
    ///
    /// * The pointer must be [valid] for reads for `ptr.len() * mem::size_of::<T>()` many bytes,
    ///   and it must be properly aligned. This means in particular:
    ///
    ///     * The entire memory range of this slice must be contained within a single allocated object!
    ///       Slices can never span across multiple allocated objects.
    ///
    ///     * The pointer must be aligned even for zero-length slices. One
    ///       reason for this is that enum layout optimizations may rely on references
    ///       (including slices of any length) being aligned and non-null to distinguish
    ///       them from other data. You can obtain a pointer that is usable as `data`
    ///       for zero-length slices using [`NonNull::dangling()`].
    ///
    /// * The total size `ptr.len() * mem::size_of::<T>()` of the slice must be no larger than `isize::MAX`.
    ///   See the safety documentation of [`pointer::offset`].
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
    ///   arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
    ///   In particular, while this reference exists, the memory the pointer points to must
    ///   not get mutated (except inside `UnsafeCell`).
    ///
    /// This applies even if the result of this method is unused!
    ///
    /// See also [`slice::from_raw_parts`].
    ///
    /// [valid]: crate::ptr#safety
    #[inline]
    #[must_use]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    // Ensure the pointer is properly aligned
    #[requires(self.as_ptr().cast::<T>().align_offset(core::mem::align_of::<T>()) == 0)]
    // Ensure the slice size does not exceed isize::MAX
    #[requires(self.len().checked_mul(core::mem::size_of::<T>()).is_some() && self.len() * core::mem::size_of::<T>() <= isize::MAX as usize)]
    #[requires(self.as_ptr().addr().checked_add(self.len() * core::mem::size_of::<T>()).is_some())]
    // Ensure the slice is contained within a single allocation
    #[requires(core::ub_checks::same_allocation(self.as_ptr() as *const(), self.as_ptr().wrapping_byte_add(self.len() * core::mem::size_of::<T>()) as *const()))]
    #[ensures(|result: &&[MaybeUninit<T>]| result.len() == self.len())]
    #[ensures(|result: &&[MaybeUninit<T>]| core::ptr::eq(result.as_ptr(), self.cast().as_ptr()))]
    pub const unsafe fn as_uninit_slice<'a>(self) -> &'a [MaybeUninit<T>] {
        // SAFETY: the caller must uphold the safety contract for `as_uninit_slice`.
        unsafe { slice::from_raw_parts(self.cast().as_ptr(), self.len()) }
    }

    /// Returns a unique reference to a slice of possibly uninitialized values. In contrast to
    /// [`as_mut`], this does not require that the value has to be initialized.
    ///
    /// For the shared counterpart see [`as_uninit_slice`].
    ///
    /// [`as_mut`]: NonNull::as_mut
    /// [`as_uninit_slice`]: NonNull::as_uninit_slice
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that all of the following is true:
    ///
    /// * The pointer must be [valid] for reads and writes for `ptr.len() * mem::size_of::<T>()`
    ///   many bytes, and it must be properly aligned. This means in particular:
    ///
    ///     * The entire memory range of this slice must be contained within a single allocated object!
    ///       Slices can never span across multiple allocated objects.
    ///
    ///     * The pointer must be aligned even for zero-length slices. One
    ///       reason for this is that enum layout optimizations may rely on references
    ///       (including slices of any length) being aligned and non-null to distinguish
    ///       them from other data. You can obtain a pointer that is usable as `data`
    ///       for zero-length slices using [`NonNull::dangling()`].
    ///
    /// * The total size `ptr.len() * mem::size_of::<T>()` of the slice must be no larger than `isize::MAX`.
    ///   See the safety documentation of [`pointer::offset`].
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
    ///   arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
    ///   In particular, while this reference exists, the memory the pointer points to must
    ///   not get accessed (read or written) through any other pointer.
    ///
    /// This applies even if the result of this method is unused!
    ///
    /// See also [`slice::from_raw_parts_mut`].
    ///
    /// [valid]: crate::ptr#safety
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(allocator_api, ptr_as_uninit)]
    ///
    /// use std::alloc::{Allocator, Layout, Global};
    /// use std::mem::MaybeUninit;
    /// use std::ptr::NonNull;
    ///
    /// let memory: NonNull<[u8]> = Global.allocate(Layout::new::<[u8; 32]>())?;
    /// // This is safe as `memory` is valid for reads and writes for `memory.len()` many bytes.
    /// // Note that calling `memory.as_mut()` is not allowed here as the content may be uninitialized.
    /// # #[allow(unused_variables)]
    /// let slice: &mut [MaybeUninit<u8>] = unsafe { memory.as_uninit_slice_mut() };
    /// # // Prevent leaks for Miri.
    /// # unsafe { Global.deallocate(memory.cast(), Layout::new::<[u8; 32]>()); }
    /// # Ok::<_, std::alloc::AllocError>(())
    /// ```
    #[inline]
    #[must_use]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    // Ensure the pointer is properly aligned
    #[requires(self.as_ptr().cast::<T>().align_offset(core::mem::align_of::<T>()) == 0)]
    // Ensure the slice size does not exceed isize::MAX
    #[requires(self.len().checked_mul(core::mem::size_of::<T>()).is_some() && self.len() * core::mem::size_of::<T>() <= isize::MAX as usize)]
    #[requires(self.as_ptr().addr().checked_add(self.len() * core::mem::size_of::<T>()).is_some())]
    // Ensure the slice is contained within a single allocation
    #[requires(core::ub_checks::same_allocation(self.as_ptr() as *const(), self.as_ptr().wrapping_byte_add(self.len() * core::mem::size_of::<T>()) as *const()))]
    #[ensures(|result: &&mut [MaybeUninit<T>]| result.len() == self.len())] // Length check
    #[ensures(|result: &&mut [MaybeUninit<T>]| core::ptr::eq(result.as_ptr(), self.cast().as_ptr()))] // Address check
    pub const unsafe fn as_uninit_slice_mut<'a>(self) -> &'a mut [MaybeUninit<T>] {
        // SAFETY: the caller must uphold the safety contract for `as_uninit_slice_mut`.
        unsafe { slice::from_raw_parts_mut(self.cast().as_ptr(), self.len()) }
    }

    /// Returns a raw pointer to an element or subslice, without doing bounds
    /// checking.
    ///
    /// Calling this method with an out-of-bounds index or when `self` is not dereferenceable
    /// is *[undefined behavior]* even if the resulting pointer is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(slice_ptr_get)]
    /// use std::ptr::NonNull;
    ///
    /// let x = &mut [1, 2, 4];
    /// let x = NonNull::slice_from_raw_parts(NonNull::new(x.as_mut_ptr()).unwrap(), x.len());
    ///
    /// unsafe {
    ///     assert_eq!(x.get_unchecked_mut(1).as_ptr(), x.as_non_null_ptr().as_ptr().add(1));
    /// }
    /// ```
    #[unstable(feature = "slice_ptr_get", issue = "74265")]
    #[inline]
    #[requires(ub_checks::can_dereference(self.as_ptr()))] // Ensure self can be dereferenced
    pub unsafe fn get_unchecked_mut<I>(self, index: I) -> NonNull<I::Output>
    where
        I: SliceIndex<[T]>,
    {
        // SAFETY: the caller ensures that `self` is dereferenceable and `index` in-bounds.
        // As a consequence, the resulting pointer cannot be null.
        unsafe { NonNull::new_unchecked(self.as_ptr().get_unchecked_mut(index)) }
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> Clone for NonNull<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> Copy for NonNull<T> {}

#[unstable(feature = "coerce_unsized", issue = "18598")]
impl<T: ?Sized, U: ?Sized> CoerceUnsized<NonNull<U>> for NonNull<T> where T: Unsize<U> {}

#[unstable(feature = "dispatch_from_dyn", issue = "none")]
impl<T: ?Sized, U: ?Sized> DispatchFromDyn<NonNull<U>> for NonNull<T> where T: Unsize<U> {}

#[stable(feature = "pin", since = "1.33.0")]
unsafe impl<T: ?Sized> PinCoerceUnsized for NonNull<T> {}

#[unstable(feature = "pointer_like_trait", issue = "none")]
impl<T> core::marker::PointerLike for NonNull<T> {}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> fmt::Debug for NonNull<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> fmt::Pointer for NonNull<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> Eq for NonNull<T> {}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> PartialEq for NonNull<T> {
    #[inline]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> Ord for NonNull<T> {
    #[inline]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ptr().cmp(&other.as_ptr())
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> PartialOrd for NonNull<T> {
    #[inline]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_ptr().partial_cmp(&other.as_ptr())
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> hash::Hash for NonNull<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_ptr().hash(state)
    }
}

#[unstable(feature = "ptr_internals", issue = "none")]
impl<T: ?Sized> From<Unique<T>> for NonNull<T> {
    #[inline]
    fn from(unique: Unique<T>) -> Self {
        unique.as_non_null_ptr()
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> From<&mut T> for NonNull<T> {
    /// Converts a `&mut T` to a `NonNull<T>`.
    ///
    /// This conversion is safe and infallible since references cannot be null.
    #[inline]
    fn from(r: &mut T) -> Self {
        NonNull::from_mut(r)
    }
}

#[stable(feature = "nonnull", since = "1.25.0")]
impl<T: ?Sized> From<&T> for NonNull<T> {
    /// Converts a `&T` to a `NonNull<T>`.
    ///
    /// This conversion is safe and infallible since references cannot be null.
    #[inline]
    fn from(r: &T) -> Self {
        NonNull::from_ref(r)
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::num::NonZeroUsize;
    use core::ptr::NonNull;

    use kani::PointerGenerator;

    use super::*;
    use crate::mem;
    use crate::ptr::null_mut;

    trait SampleTrait {
        fn get_value(&self) -> i32;
    }

    struct SampleStruct {
        value: i32,
    }

    impl SampleTrait for SampleStruct {
        fn get_value(&self) -> i32 {
            self.value
        }
    }

    impl<T> kani::Arbitrary for NonNull<T> {
        fn any() -> Self {
            let ptr: *mut T = kani::any::<usize>() as *mut T;
            kani::assume(!ptr.is_null());
            NonNull::new(ptr).expect("Non-null pointer expected")
        }
    }

    // pub const unsafe fn new_unchecked(ptr: *mut T) -> Self
    #[kani::proof_for_contract(NonNull::new_unchecked)]
    pub fn non_null_check_new_unchecked() {
        let raw_ptr = kani::any::<usize>() as *mut i32;
        unsafe {
            let _ = NonNull::new_unchecked(raw_ptr);
        }
    }

    // pub const fn new(ptr: *mut T) -> Option<Self>
    #[kani::proof_for_contract(NonNull::new)]
    pub fn non_null_check_new() {
        let mut x: i32 = kani::any();
        let xptr = &mut x;
        let maybe_null_ptr = if kani::any() { xptr as *mut i32 } else { null_mut() };
        let _ = NonNull::new(maybe_null_ptr);
    }

    // pub const unsafe fn read(self) -> T where T: Sized
    #[kani::proof_for_contract(NonNull::read)]
    pub fn non_null_check_read() {
        let ptr_u8: *mut u8 = &mut kani::any();
        let nonnull_ptr_u8 = NonNull::new(ptr_u8).unwrap();
        unsafe {
            let result = nonnull_ptr_u8.read();
            kani::assert(*ptr_u8 == result, "read returns the correct value");
        }

        // array example
        const ARR_LEN: usize = 10000;
        let mut generator = PointerGenerator::<ARR_LEN>::new();
        let raw_ptr: *mut i8 = generator.any_in_bounds().ptr;
        let nonnull_ptr = unsafe { NonNull::new(raw_ptr).unwrap() };
        unsafe {
            let result = nonnull_ptr.read();
            kani::assert(*nonnull_ptr.as_ptr() == result, "read returns the correct value");
        }
    }

    // pub unsafe fn read_volatile(self) -> T where T: Sized
    #[kani::proof_for_contract(NonNull::read_volatile)]
    pub fn non_null_check_read_volatile() {
        let ptr_u8: *mut u8 = &mut kani::any();
        let nonnull_ptr_u8 = NonNull::new(ptr_u8).unwrap();
        unsafe {
            let result = nonnull_ptr_u8.read_volatile();
            kani::assert(*ptr_u8 == result, "read returns the correct value");
        }

        // array example
        const ARR_LEN: usize = 10000;
        let mut generator = PointerGenerator::<ARR_LEN>::new();
        let raw_ptr: *mut i8 = generator.any_in_bounds().ptr;
        let nonnull_ptr = unsafe { NonNull::new(raw_ptr).unwrap() };
        unsafe {
            let result = nonnull_ptr.read_volatile();
            kani::assert(*nonnull_ptr.as_ptr() == result, "read returns the correct value");
        }
    }

    #[repr(packed, C)]
    struct Packed {
        _padding: u8,
        unaligned: u32,
    }

    // pub const unsafe fn read_unaligned(self) -> T where T: Sized
    #[kani::proof_for_contract(NonNull::read_unaligned)]
    pub fn non_null_check_read_unaligned() {
        // unaligned pointer
        let mut generator = PointerGenerator::<10000>::new();
        let unaligned_ptr: *mut u8 = generator.any_in_bounds().ptr;
        let unaligned_nonnull_ptr = NonNull::new(unaligned_ptr).unwrap();
        unsafe {
            let result = unaligned_nonnull_ptr.read_unaligned();
            kani::assert(
                *unaligned_nonnull_ptr.as_ptr() == result,
                "read returns the correct value",
            );
        }

        // read an unaligned value from a packed struct
        let unaligned_value: u32 = kani::any();
        let packed = Packed { _padding: kani::any::<u8>(), unaligned: unaligned_value };

        let unaligned_ptr = ptr::addr_of!(packed.unaligned);
        let nonnull_packed_ptr = NonNull::new(unaligned_ptr as *mut u32).unwrap();
        let v = unsafe { nonnull_packed_ptr.read_unaligned() };
        assert_eq!(v, unaligned_value);
    }

    // pub const unsafe fn add(self, count: usize) -> Self
    #[kani::proof_for_contract(NonNull::add)]
    pub fn non_null_check_add() {
        const SIZE: usize = 100000;
        let mut generator = PointerGenerator::<100000>::new();
        let raw_ptr: *mut i8 = generator.any_in_bounds().ptr;
        let ptr = unsafe { NonNull::new(raw_ptr).unwrap() };
        // Create a non-deterministic count value
        let count: usize = kani::any();

        unsafe {
            let result = ptr.add(count);
        }
    }

    // pub fn addr(self) -> NonZero<usize>
    #[kani::proof_for_contract(NonNull::addr)]
    pub fn non_null_check_addr() {
        // Create NonNull pointer & get pointer address
        let x = kani::any::<usize>() as *mut i32;
        let Some(nonnull_xptr) = NonNull::new(x) else {
            return;
        };
        let address = nonnull_xptr.addr();
    }

    // pub fn align_offset(self, align: usize) -> usize
    #[kani::proof_for_contract(NonNull::align_offset)]
    pub fn non_null_check_align_offset() {
        // Create NonNull pointer
        let x = kani::any::<usize>() as *mut i32;
        let Some(nonnull_xptr) = NonNull::new(x) else {
            return;
        };

        // Call align_offset with valid align value
        let align: usize = kani::any();
        kani::assume(align.is_power_of_two());
        nonnull_xptr.align_offset(align);
    }

    // pub fn align_offset(self, align: usize) -> usize
    #[kani::should_panic]
    #[kani::proof_for_contract(NonNull::align_offset)]
    pub fn non_null_check_align_offset_negative() {
        // Create NonNull pointer
        let x = kani::any::<usize>() as *mut i8;
        let Some(nonnull_xptr) = NonNull::new(x) else {
            return;
        };

        // Generate align value that is not necessarily a power of two
        let invalid_align: usize = kani::any();

        // Trigger panic
        let offset = nonnull_xptr.align_offset(invalid_align);
    }

    // FIXME -- the postcondition fails, c.f. https://github.com/model-checking/kani/issues/3905
    // (dangling() calls Alignment::of, and the linked issue tracks the Alignment::of proof)
    // pub const fn dangling() -> Self
    // #[kani::proof_for_contract(NonNull::dangling)]
    // pub fn non_null_check_dangling() {
    // unsigned integer types
    // let ptr_u8 = NonNull::<u8>::dangling();
    // let ptr_u16 = NonNull::<u16>::dangling();
    // let ptr_u32 = NonNull::<u32>::dangling();
    // let ptr_u64 = NonNull::<u64>::dangling();
    // let ptr_u128 = NonNull::<u128>::dangling();
    // let ptr_usize = NonNull::<usize>::dangling();
    // // signed integer types
    // let ptr_i8 = NonNull::<i8>::dangling();
    // let ptr_i16 = NonNull::<i16>::dangling();
    // let ptr_i32 = NonNull::<i32>::dangling();
    // let ptr_i64 = NonNull::<i64>::dangling();
    // let ptr_i128 = NonNull::<i128>::dangling();
    // let ptr_isize = NonNull::<isize>::dangling();
    // // unit type
    // let ptr_unit = NonNull::<()>::dangling();
    // // zero length slice from dangling unit pointer
    // let zero_len_slice = NonNull::slice_from_raw_parts(ptr_unit, 0);
    // }

    // pub const fn from_raw_parts(data_pointer: NonNull<()>, metadata: <T as super::Pointee>::Metadata,) -> NonNull<T>
    // FIXME -- the postcondition fails, c.f. https://github.com/model-checking/kani/issues/3905
    // (dangling() calls Alignment::of, and the linked issue tracks the Alignment::of proof)
    // #[kani::proof_for_contract(NonNull::from_raw_parts)]
    // #[kani::unwind(101)]
    // pub fn non_null_check_from_raw_parts() {
    //     const ARR_LEN: usize = 100;
    //     // Create a non-deterministic array and its slice
    //     let arr: [i8; ARR_LEN] = kani::any();
    //     let arr_slice = kani::slice::any_slice_of_array(&arr);
    //     // Get a raw NonNull pointer to the start of the slice
    //     let arr_slice_raw_ptr = NonNull::new(arr_slice.as_ptr() as *mut ()).unwrap();
    //     // Create NonNull pointer from the start pointer and the length of the slice
    //     let nonnull_slice = NonNull::<[i8]>::from_raw_parts(arr_slice_raw_ptr, arr_slice.len());
    //     // Ensure slice content is preserved, runtime at this step is proportional to ARR_LEN
    //     unsafe {
    //         kani::assert(arr_slice == nonnull_slice.as_ref(), "slice content must be preserve");
    //     }

    //     // zero-length dangling pointer example
    //     let dangling_ptr = NonNull::<()>::dangling();
    //     let zero_length = NonNull::<[()]>::from_raw_parts(dangling_ptr, 0);
    // }

    #[kani::proof_for_contract(NonNull::from_raw_parts)]
    pub fn non_null_check_from_raw_part_trait() {
        // Create a SampleTrait object from SampleStruct
        let sample_struct = SampleStruct { value: kani::any() };
        let trait_object: &dyn SampleTrait = &sample_struct;

        // Get the raw data pointer and metadata for the trait object
        let trait_ptr = NonNull::new(trait_object as *const dyn SampleTrait as *mut ()).unwrap();
        // Safety: For trait objects, the metadata must come from a pointer to the same underlying erased type
        let metadata = core::ptr::metadata(trait_object);

        // Create NonNull<dyn MyTrait> from the data pointer and metadata
        let nonnull_trait_object: NonNull<dyn SampleTrait> =
            NonNull::from_raw_parts(trait_ptr, metadata);

        unsafe {
            // Ensure trait method and member is preserved
            kani::assert(
                trait_object.get_value() == nonnull_trait_object.as_ref().get_value(),
                "trait method and member must correctly preserve",
            );
        }
    }

    // pub const fn slice_from_raw_parts(data: NonNull<T>, len: usize) -> Self
    #[kani::proof_for_contract(NonNull::slice_from_raw_parts)]
    #[kani::unwind(1001)]
    pub fn non_null_check_slice_from_raw_parts() {
        const ARR_LEN: usize = 1000;
        // Create a non-deterministic array
        let mut arr: [i8; ARR_LEN] = kani::any();
        // Get a raw NonNull pointer to the start of the slice
        let arr_raw_ptr = NonNull::new(arr.as_mut_ptr()).unwrap();
        // Create NonNull slice from the start pointer and ends at random slice_len
        // Safety: https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html
        let slice_len: usize = kani::any();
        kani::assume(slice_len <= ARR_LEN);
        let nonnull_slice = NonNull::<[i8]>::slice_from_raw_parts(arr_raw_ptr, slice_len);
        // Ensure slice content is preserved, runtime at this step is proportional to ARR_LEN
        unsafe {
            kani::assert(
                &arr[..slice_len] == nonnull_slice.as_ref(),
                "slice content must be preserve",
            );
        }

        // TODO: zero-length example blocked by kani issue [#3670](https://github.com/model-checking/kani/issues/3670)
        //let dangling_ptr = NonNull::<()>::dangling();
        //let zero_length = NonNull::<[()]>::slice_from_raw_parts(dangling_ptr, 0);
    }

    // pub const fn to_raw_parts(self) -> (NonNull<()>, <T as super::Pointee>::Metadata)
    #[kani::proof_for_contract(NonNull::to_raw_parts)]
    pub fn non_null_check_to_raw_parts() {
        // Create a SampleTrait object from SampleStruct
        let sample_struct = SampleStruct { value: kani::any() };
        let trait_object: &dyn SampleTrait = &sample_struct;

        // Get the raw data pointer and metadata for the trait object
        let trait_ptr = NonNull::from(trait_object).cast::<()>(); //both have eq failure
        //let trait_ptr = NonNull::new(trait_object as *const dyn SampleTrait as *mut ()).unwrap(); //Question: what's the difference
        // Safety: For trait objects, the metadata must come from a pointer to the same underlying erased type
        let metadata = core::ptr::metadata(trait_object);

        // Create NonNull<dyn MyTrait> from the data pointer and metadata
        let nonnull_trait_object: NonNull<dyn SampleTrait> =
            NonNull::from_raw_parts(trait_ptr, metadata);
        let (decomposed_data_ptr, decomposed_metadata) =
            NonNull::to_raw_parts(nonnull_trait_object);
    }

    #[kani::proof_for_contract(NonNull::as_mut)]
    pub fn non_null_check_as_mut() {
        let mut x: i32 = kani::any();
        if let Some(mut ptr) = NonNull::new(&mut x as *mut i32) {
            unsafe {
                let result = ptr.as_mut();
            }
        }
    }

    #[kani::proof_for_contract(NonNull::as_ref)]
    pub fn non_null_check_as_ref() {
        let mut x: i32 = kani::any();
        if let Some(ptr) = NonNull::new(&mut x as *mut i32) {
            unsafe {
                let _ = ptr.as_ref();
            }
        }
    }

    #[kani::proof_for_contract(NonNull::as_uninit_mut)]
    pub fn non_null_check_as_uninit_mut() {
        use core::mem::MaybeUninit;

        // Create an uninitialized MaybeUninit value
        let mut uninit: MaybeUninit<i32> = MaybeUninit::uninit();
        let mut ptr = NonNull::new(uninit.as_mut_ptr()).unwrap();

        unsafe {
            let _ = ptr.as_uninit_mut();
        }
    }

    #[kani::proof_for_contract(NonNull::as_uninit_ref)]
    pub fn non_null_check_as_uninit_ref() {
        use core::mem::MaybeUninit;

        // Create an uninitialized MaybeUninit value
        let mut uninit: MaybeUninit<i32> = MaybeUninit::uninit();
        let ptr = NonNull::new(uninit.as_mut_ptr()).unwrap();

        unsafe {
            let uninit_ref = ptr.as_uninit_ref();
        }
    }

    #[kani::proof_for_contract(NonNull::as_uninit_slice)]
    pub fn non_null_check_as_uninit_slice() {
        use core::mem::MaybeUninit;

        const SIZE: usize = 100000;
        let arr: [MaybeUninit<i32>; SIZE] = MaybeUninit::uninit_array();
        let slice: &[MaybeUninit<i32>] = kani::slice::any_slice_of_array(&arr);
        let ptr = NonNull::slice_from_raw_parts(
            NonNull::new(slice.as_ptr() as *mut MaybeUninit<i32>).unwrap(),
            slice.len(),
        );

        unsafe {
            let _ = ptr.as_uninit_slice();
        }
    }

    #[kani::proof_for_contract(NonNull::as_uninit_slice_mut)]
    pub fn non_null_check_as_uninit_slice_mut() {
        use core::mem::MaybeUninit;

        const SIZE: usize = 100000;
        let mut arr: [MaybeUninit<i32>; SIZE] = MaybeUninit::uninit_array();
        let slice: &[MaybeUninit<i32>] = kani::slice::any_slice_of_array(&mut arr);
        let ptr = NonNull::slice_from_raw_parts(
            NonNull::new(slice.as_ptr() as *mut MaybeUninit<i32>).unwrap(),
            SIZE,
        );

        unsafe {
            let _ = ptr.as_uninit_slice_mut();
        }
    }

    #[kani::proof_for_contract(NonNull::get_unchecked_mut)]
    pub fn non_null_check_get_unchecked_mut() {
        const ARR_SIZE: usize = 100000;
        let mut arr: [i32; ARR_SIZE] = kani::any();
        let raw_ptr = arr.as_mut_ptr();
        let ptr = NonNull::slice_from_raw_parts(NonNull::new(raw_ptr).unwrap(), ARR_SIZE);
        let lower = kani::any_where(|x| *x < ARR_SIZE);
        let upper = kani::any_where(|x| *x < ARR_SIZE && *x >= lower);
        unsafe {
            // NOTE: The `index` parameter cannot be used in the function contracts without being moved.
            // Since the `SliceIndex` trait does not guarantee that `index` implements `Clone` or `Copy`,
            // it cannot be reused after being consumed in the precondition. To comply with Rust's ownership
            // rules and ensure `index` is only used once, the in-bounds check is moved to the proof harness
            // as a workaround.
            kani::assume(ptr.as_ref().get(lower..upper).is_some());
            let _ = ptr.get_unchecked_mut(lower..upper);
        }
    }

    #[kani::proof_for_contract(NonNull::replace)]
    pub fn non_null_check_replace() {
        let mut x: i32 = kani::any();
        let mut y: i32 = kani::any();

        let origin_ptr = NonNull::new(&mut x as *mut i32).unwrap();
        unsafe {
            let captured_original = ptr::read(origin_ptr.as_ptr());
            let replaced = origin_ptr.replace(y);
            let after_replace = ptr::read(origin_ptr.as_ptr());

            assert_eq!(captured_original, replaced);
            assert_eq!(after_replace, y)
        }
    }

    #[kani::proof_for_contract(NonNull::drop_in_place)]
    pub fn non_null_check_drop_in_place() {
        struct Droppable {
            value: i32,
        }
        impl Drop for Droppable {
            fn drop(&mut self) {}
        }

        let mut droppable = Droppable { value: kani::any() };
        let ptr = NonNull::new(&mut droppable as *mut Droppable).unwrap();
        unsafe {
            ptr.drop_in_place();
        }
    }

    #[kani::proof_for_contract(NonNull::swap)]
    pub fn non_null_check_swap() {
        let mut a: i32 = kani::any();
        let mut b: i32 = kani::any();

        let ptr_a = NonNull::new(&mut a as *mut i32).unwrap();
        let ptr_b = NonNull::new(&mut b as *mut i32).unwrap();

        unsafe {
            let old_a = ptr::read(ptr_a.as_ptr());
            let old_b = ptr::read(ptr_b.as_ptr());
            ptr_a.swap(ptr_b);
            // Verify that the values have been swapped.
            let new_a = ptr::read(ptr_a.as_ptr());
            let new_b = ptr::read(ptr_b.as_ptr());
            assert_eq!(old_a, new_b);
            assert_eq!(old_b, new_a);
        }
    }

    #[kani::proof_for_contract(NonNull::as_ptr)]
    pub fn non_null_check_as_ptr() {
        // Create a non-null pointer to a random value
        let non_null_ptr: *mut i32 = kani::any::<usize>() as *mut i32;
        if let Some(ptr) = NonNull::new(non_null_ptr) {
            let result = ptr.as_ptr();
        }
    }

    #[kani::proof_for_contract(NonNull::<[T]>::as_mut_ptr)]
    pub fn non_null_check_as_mut_ptr() {
        const ARR_LEN: usize = 100;
        let mut values: [i32; ARR_LEN] = kani::any();
        let slice = kani::slice::any_slice_of_array_mut(&mut values);
        let non_null_ptr = NonNull::new(slice as *mut [i32]).unwrap();
        let result = non_null_ptr.as_mut_ptr();
    }
    #[kani::proof_for_contract(NonNull::<T>::cast)]
    pub fn non_null_check_cast() {
        // Create a non-null pointer to a random value
        let non_null_ptr: *mut i32 = kani::any::<usize>() as *mut i32;
        if let Some(ptr) = NonNull::new(non_null_ptr) {
            let result: NonNull<u8> = ptr.cast();
        }
    }

    #[kani::proof_for_contract(NonNull::<[T]>::as_non_null_ptr)]
    pub fn non_null_check_as_non_null_ptr() {
        const ARR_LEN: usize = 100;
        let mut values: [i32; ARR_LEN] = kani::any();
        let slice = kani::slice::any_slice_of_array_mut(&mut values);
        let non_null_ptr = NonNull::new(slice as *mut [i32]).unwrap();
        let result = non_null_ptr.as_non_null_ptr();
    }

    #[kani::proof]
    pub fn non_null_check_len() {
        // Create a non-deterministic NonNull pointer using kani::any()
        let non_null_ptr: NonNull<i8> = kani::any();
        // Create a non-deterministic size using kani::any()
        let size: usize = kani::any();
        // Create a NonNull slice from the non-null pointer and size
        let non_null_slice: NonNull<[i8]> = NonNull::slice_from_raw_parts(non_null_ptr, size);

        // Perform the length check
        let len = non_null_slice.len();
        assert!(len == size);
    }

    #[kani::proof]
    pub fn non_null_check_is_empty() {
        // Create a non-deterministic NonNull pointer using kani::any()
        let non_null_ptr: NonNull<i8> = kani::any();
        // Create a non-deterministic size using kani::any(), constrained to zero
        let size: usize = 0;

        // Create a NonNull slice from the non-null pointer and size
        let non_null_slice: NonNull<[i8]> =
            unsafe { NonNull::slice_from_raw_parts(non_null_ptr, size) };

        // Perform the is_empty check
        let is_empty = non_null_slice.is_empty();
        assert!(is_empty);
    }

    #[kani::proof_for_contract(NonNull::is_aligned)]
    pub fn non_null_slice_is_aligned_check() {
        // Create a non-deterministic NonNull pointer using kani::any()
        let non_null_ptr: NonNull<i32> = kani::any();

        // Perform the alignment check
        let result = non_null_ptr.is_aligned();
    }

    #[kani::proof_for_contract(NonNull::is_aligned_to)]
    pub fn non_null_check_is_aligned_to() {
        // Create a non-deterministic NonNull pointer using kani::any()
        let non_null_ptr: NonNull<i32> = kani::any();

        // Create a non-deterministic alignment using kani::any()
        let align: usize = kani::any();
        kani::assume(align > 0); // Ensure alignment is greater than zero

        // Perform the alignment check
        let result = non_null_ptr.is_aligned_to(align);
    }

    #[kani::proof]
    #[kani::should_panic] // Add this if we expect a panic when the alignment is invalid
    pub fn non_null_check_is_aligned_to_no_power_two() {
        // Create a non-deterministic NonNull pointer using kani::any()
        let non_null_ptr: NonNull<i32> = kani::any();

        // Create a non-deterministic alignment value using kani::any()
        let align: usize = kani::any();

        // Perform the alignment check
        let result = non_null_ptr.is_aligned_to(align);
    }

    #[kani::proof_for_contract(NonNull::byte_sub)]
    pub fn non_null_check_byte_sub() {
        const SIZE: usize = mem::size_of::<i32>() * 10000;
        let mut generator = PointerGenerator::<SIZE>::new();
        let count: usize = kani::any();
        let raw_ptr: *mut i32 = generator.any_in_bounds().ptr as *mut i32;
        let ptr = NonNull::new(raw_ptr).unwrap();
        unsafe {
            let result = ptr.byte_sub(count);
        }
    }

    #[kani::proof_for_contract(NonNull::offset)]
    pub fn non_null_check_offset() {
        const SIZE: usize = mem::size_of::<i32>() * 10000;
        let mut generator = PointerGenerator::<SIZE>::new();
        let start_ptr = generator.any_in_bounds().ptr as *mut i32;
        let ptr_nonnull = NonNull::new(start_ptr).unwrap();
        let count: isize = kani::any();
        unsafe {
            let result = ptr_nonnull.offset(count);
        }
    }

    #[kani::proof_for_contract(NonNull::map_addr)]
    pub fn non_null_check_map_addr() {
        const SIZE: usize = 10000;
        let arr: [i32; SIZE] = kani::any();
        let ptr = NonNull::new(arr.as_ptr() as *mut i32).unwrap();
        let new_offset: usize = kani::any_where(|&x| x <= SIZE);
        let f = |addr: NonZeroUsize| -> NonZeroUsize {
            NonZeroUsize::new(addr.get().wrapping_add(new_offset)).unwrap()
        };
        let result = ptr.map_addr(f);
    }

    #[kani::proof_for_contract(NonNull::with_addr)]
    pub fn non_null_check_with_addr() {
        const SIZE: usize = 10000;
        let arr: [i32; SIZE] = kani::any();
        let ptr = NonNull::new(arr.as_ptr() as *mut i32).unwrap();
        let new_offset: usize = kani::any_where(|&x| x <= SIZE);
        let new_addr = NonZeroUsize::new(ptr.as_ptr().addr() + new_offset).unwrap();
        let result = ptr.with_addr(new_addr);
    }

    #[kani::proof_for_contract(NonNull::sub)]
    pub fn non_null_check_sub() {
        const SIZE: usize = 10000;
        let mut generator = kani::PointerGenerator::<SIZE>::new();
        // Get a raw pointer from the generator within bounds
        let raw_ptr: *mut i32 = generator.any_in_bounds().ptr;
        // Create a non-null pointer from the raw pointer
        let ptr = unsafe { NonNull::new(raw_ptr).unwrap() };
        // Create a non-deterministic count value
        let count: usize = kani::any();

        unsafe {
            let result = ptr.sub(count);
        }
    }

    #[kani::proof_for_contract(NonNull::sub_ptr)]
    pub fn non_null_check_sub_ptr() {
        const SIZE: usize = core::mem::size_of::<i32>() * 1000;
        let mut generator1 = kani::PointerGenerator::<SIZE>::new();
        let mut generator2 = kani::PointerGenerator::<SIZE>::new();

        let ptr: *mut i32 = if kani::any() {
            generator1.any_in_bounds().ptr as *mut i32
        } else {
            generator2.any_in_bounds().ptr as *mut i32
        };

        let origin: *mut i32 = if kani::any() {
            generator1.any_in_bounds().ptr as *mut i32
        } else {
            generator2.any_in_bounds().ptr as *mut i32
        };

        let ptr_nonnull = unsafe { NonNull::new(ptr).unwrap() };
        let origin_nonnull = unsafe { NonNull::new(origin).unwrap() };

        unsafe {
            let distance = ptr_nonnull.sub_ptr(origin_nonnull);
        }
    }

    #[kani::proof_for_contract(NonNull::offset_from)]
    pub fn non_null_check_offset_from() {
        const SIZE: usize = core::mem::size_of::<i32>() * 1000;
        let mut generator1 = kani::PointerGenerator::<SIZE>::new();
        let mut generator2 = kani::PointerGenerator::<SIZE>::new();

        let ptr: *mut i32 = if kani::any() {
            generator1.any_in_bounds().ptr as *mut i32
        } else {
            generator2.any_in_bounds().ptr as *mut i32
        };

        let origin: *mut i32 = if kani::any() {
            generator1.any_in_bounds().ptr as *mut i32
        } else {
            generator2.any_in_bounds().ptr as *mut i32
        };

        let ptr_nonnull = unsafe { NonNull::new(ptr).unwrap() };
        let origin_nonnull = unsafe { NonNull::new(origin).unwrap() };

        unsafe {
            let distance = ptr_nonnull.offset_from(origin_nonnull);
        }
    }

    macro_rules! generate_write_volatile_harness {
        ($type:ty, $byte_size:expr, $harness_name:ident) => {
            #[kani::proof_for_contract(NonNull::write_volatile)]
            pub fn $harness_name() {
                // Create a pointer generator for the given type with appropriate byte size
                let mut generator = kani::PointerGenerator::<$byte_size>::new();

                // Get a raw pointer from the generator
                let raw_ptr: *mut $type = generator.any_in_bounds().ptr;

                // Create a non-null pointer from the raw pointer
                let ptr = NonNull::new(raw_ptr).unwrap();

                // Create a non-deterministic value to write
                let new_value: $type = kani::any();

                unsafe {
                    // Perform the volatile write operation
                    ptr.write_volatile(new_value);

                    // Read back the value and assert it's correct
                    assert_eq!(ptr.as_ptr().read_volatile(), new_value);
                }
            }
        };
    }

    // Generate proof harnesses for multiple types with appropriate byte sizes
    generate_write_volatile_harness!(i8, 1, non_null_check_write_volatile_i8);
    generate_write_volatile_harness!(i16, 2, non_null_check_write_volatile_i16);
    generate_write_volatile_harness!(i32, 4, non_null_check_write_volatile_i32);
    generate_write_volatile_harness!(i64, 8, non_null_check_write_volatile_i64);
    generate_write_volatile_harness!(i128, 16, non_null_check_write_volatile_i128);
    generate_write_volatile_harness!(
        isize,
        { core::mem::size_of::<isize>() },
        non_null_check_write_volatile_isize
    );
    generate_write_volatile_harness!(u8, 1, non_null_check_write_volatile_u8);
    generate_write_volatile_harness!(u16, 2, non_null_check_write_volatile_u16);
    generate_write_volatile_harness!(u32, 4, non_null_check_write_volatile_u32);
    generate_write_volatile_harness!(u64, 8, non_null_check_write_volatile_u64);
    generate_write_volatile_harness!(u128, 16, non_null_check_write_volatile_u128);
    generate_write_volatile_harness!(
        usize,
        { core::mem::size_of::<usize>() },
        non_null_check_write_volatile_usize
    );
    generate_write_volatile_harness!((), 1, non_null_check_write_volatile_unit);

    #[kani::proof_for_contract(NonNull::byte_add)]
    pub fn non_null_byte_add_proof() {
        // Make size as 1000 to ensure the array is large enough to cover various senarios
        // while maintaining a reasonable proof runtime
        const ARR_SIZE: usize = mem::size_of::<i32>() * 1000;
        let mut generator = PointerGenerator::<ARR_SIZE>::new();

        let count: usize = kani::any();
        let raw_ptr: *mut i32 = generator.any_in_bounds().ptr as *mut i32;

        unsafe {
            let ptr = NonNull::new(raw_ptr).unwrap();
            let result = ptr.byte_add(count);
        }
    }

    #[kani::proof_for_contract(NonNull::byte_add)]
    pub fn non_null_byte_add_dangling_proof() {
        let ptr = NonNull::<i32>::dangling();
        unsafe {
            let _ = ptr.byte_add(0);
        }
    }

    #[kani::proof_for_contract(NonNull::byte_offset)]
    pub fn non_null_byte_offset_proof() {
        const ARR_SIZE: usize = mem::size_of::<i32>() * 1000;
        let mut generator = PointerGenerator::<ARR_SIZE>::new();

        let count: isize = kani::any();
        let raw_ptr: *mut i32 = generator.any_in_bounds().ptr as *mut i32;

        unsafe {
            let ptr = NonNull::new(raw_ptr).unwrap();
            let result = ptr.byte_offset(count);
        }
    }

    #[kani::proof_for_contract(NonNull::byte_offset_from)]
    pub fn non_null_byte_offset_from_proof() {
        const SIZE: usize = mem::size_of::<i32>() * 1000;
        let mut generator1 = PointerGenerator::<SIZE>::new();
        let mut generator2 = PointerGenerator::<SIZE>::new();

        let ptr: *mut i32 = generator1.any_in_bounds().ptr as *mut i32;

        let origin: *mut i32 = if kani::any() {
            generator1.any_in_bounds().ptr as *mut i32
        } else {
            generator2.any_in_bounds().ptr as *mut i32
        };

        let ptr_nonnull = unsafe { NonNull::new(ptr).unwrap() };
        let origin_nonnull = unsafe { NonNull::new(origin).unwrap() };

        unsafe {
            let result = ptr_nonnull.byte_offset_from(origin_nonnull);
        }
    }

    #[kani::proof_for_contract(NonNull::byte_offset_from)]
    pub fn non_null_byte_offset_from_dangling_proof() {
        let origin = NonNull::<i32>::dangling();
        let ptr = origin;
        unsafe {
            let _ = ptr.byte_offset_from(origin);
        }
    }

    #[kani::proof_for_contract(NonNull::<T>::copy_to)]
    pub fn non_null_check_copy_to() {
        // PointerGenerator instance
        let mut generator = PointerGenerator::<16>::new();
        // Generate arbitrary pointers for src and dest
        let src_ptr = generator.any_in_bounds::<i32>().ptr;
        let dest_ptr = generator.any_in_bounds::<i32>().ptr;
        // Wrap the raw pointers in NonNull
        let src = NonNull::new(src_ptr).unwrap();
        let dest = NonNull::new(dest_ptr).unwrap();
        // Generate an arbitrary count using kani::any
        let count: usize = kani::any();
        unsafe {
            src.copy_to(dest, count);
        }
    }

    #[kani::proof_for_contract(NonNull::<T>::copy_from)]
    pub fn non_null_check_copy_from() {
        // PointerGenerator instance
        let mut generator = PointerGenerator::<16>::new();
        // Generate arbitrary pointers for src and dest
        let src_ptr = generator.any_in_bounds::<i32>().ptr;
        let dest_ptr = generator.any_in_bounds::<i32>().ptr;
        // Wrap the raw pointers in NonNull
        let src = NonNull::new(src_ptr).unwrap();
        let dest = NonNull::new(dest_ptr).unwrap();
        // Generate an arbitrary count using kani::any
        let count: usize = kani::any();
        unsafe {
            src.copy_from(dest, count);
        }
    }
    #[kani::proof_for_contract(NonNull::<T>::copy_to_nonoverlapping)]
    pub fn non_null_check_copy_to_nonoverlapping() {
        // PointerGenerator instance
        let mut generator = PointerGenerator::<16>::new();
        // Generate arbitrary pointers for src and dest
        let src_ptr = generator.any_in_bounds::<i32>().ptr;
        let dest_ptr = generator.any_in_bounds::<i32>().ptr;
        // Wrap the raw pointers in NonNull
        let src = NonNull::new(src_ptr).unwrap();
        let dest = NonNull::new(dest_ptr).unwrap();
        // Generate an arbitrary count using kani::any
        let count: usize = kani::any();
        unsafe {
            src.copy_to_nonoverlapping(dest, count);
        }
    }
    #[kani::proof_for_contract(NonNull::<T>::copy_from_nonoverlapping)]
    pub fn non_null_check_copy_from_nonoverlapping() {
        // PointerGenerator instance
        let mut generator = PointerGenerator::<16>::new();
        // Generate arbitrary pointers for src and dest
        let src_ptr = generator.any_in_bounds::<i32>().ptr;
        let dest_ptr = generator.any_in_bounds::<i32>().ptr;
        // Wrap the raw pointers in NonNull
        let src = NonNull::new(src_ptr).unwrap();
        let dest = NonNull::new(dest_ptr).unwrap();
        // Generate an arbitrary count using kani::any
        let count: usize = kani::any();
        unsafe {
            src.copy_from_nonoverlapping(dest, count);
        }
    }
}
