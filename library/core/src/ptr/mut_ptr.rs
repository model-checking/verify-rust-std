use core::mem;

use safety::{ensures, requires};

use super::*;
use crate::cmp::Ordering::{Equal, Greater, Less};
use crate::intrinsics::const_eval_select;
#[cfg(kani)]
use crate::kani;
use crate::mem::SizedTypeProperties;
use crate::slice::{self, SliceIndex};

impl<T: ?Sized> *mut T {
    /// Returns `true` if the pointer is null.
    ///
    /// Note that unsized types have many possible null pointers, as only the
    /// raw data pointer is considered, not their length, vtable, etc.
    /// Therefore, two pointers that are null may still not compare equal to
    /// each other.
    ///
    /// # Panics during const evaluation
    ///
    /// If this method is used during const evaluation, and `self` is a pointer
    /// that is offset beyond the bounds of the memory it initially pointed to,
    /// then there might not be enough information to determine whether the
    /// pointer is null. This is because the absolute address in memory is not
    /// known at compile time. If the nullness of the pointer cannot be
    /// determined, this method will panic.
    ///
    /// In-bounds pointers are never null, so the method will never panic for
    /// such pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = [1, 2, 3];
    /// let ptr: *mut u32 = s.as_mut_ptr();
    /// assert!(!ptr.is_null());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_ptr_is_null", since = "1.84.0")]
    #[rustc_diagnostic_item = "ptr_is_null"]
    #[inline]
    pub const fn is_null(self) -> bool {
        self.cast_const().is_null()
    }

    /// Casts to a pointer of another type.
    #[stable(feature = "ptr_cast", since = "1.38.0")]
    #[rustc_const_stable(feature = "const_ptr_cast", since = "1.38.0")]
    #[rustc_diagnostic_item = "ptr_cast"]
    #[inline(always)]
    pub const fn cast<U>(self) -> *mut U {
        self as _
    }

    /// Uses the address value in a new pointer of another type.
    ///
    /// This operation will ignore the address part of its `meta` operand and discard existing
    /// metadata of `self`. For pointers to a sized types (thin pointers), this has the same effect
    /// as a simple cast. For pointers to an unsized type (fat pointers) this recombines the address
    /// with new metadata such as slice lengths or `dyn`-vtable.
    ///
    /// The resulting pointer will have provenance of `self`. This operation is semantically the
    /// same as creating a new pointer with the data pointer value of `self` but the metadata of
    /// `meta`, being fat or thin depending on the `meta` operand.
    ///
    /// # Examples
    ///
    /// This function is primarily useful for enabling pointer arithmetic on potentially fat
    /// pointers. The pointer is cast to a sized pointee to utilize offset operations and then
    /// recombined with its own original metadata.
    ///
    /// ```
    /// #![feature(set_ptr_value)]
    /// # use core::fmt::Debug;
    /// let mut arr: [i32; 3] = [1, 2, 3];
    /// let mut ptr = arr.as_mut_ptr() as *mut dyn Debug;
    /// let thin = ptr as *mut u8;
    /// unsafe {
    ///     ptr = thin.add(8).with_metadata_of(ptr);
    ///     # assert_eq!(*(ptr as *mut i32), 3);
    ///     println!("{:?}", &*ptr); // will print "3"
    /// }
    /// ```
    ///
    /// # *Incorrect* usage
    ///
    /// The provenance from pointers is *not* combined. The result must only be used to refer to the
    /// address allowed by `self`.
    ///
    /// ```rust,no_run
    /// #![feature(set_ptr_value)]
    /// let mut x = 0u32;
    /// let mut y = 1u32;
    ///
    /// let x = (&mut x) as *mut u32;
    /// let y = (&mut y) as *mut u32;
    ///
    /// let offset = (x as usize - y as usize) / 4;
    /// let bad = x.wrapping_add(offset).with_metadata_of(y);
    ///
    /// // This dereference is UB. The pointer only has provenance for `x` but points to `y`.
    /// println!("{:?}", unsafe { &*bad });
    #[unstable(feature = "set_ptr_value", issue = "75091")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[inline]
    pub const fn with_metadata_of<U>(self, meta: *const U) -> *mut U
    where
        U: ?Sized,
    {
        from_raw_parts_mut::<U>(self as *mut (), metadata(meta))
    }

    /// Changes constness without changing the type.
    ///
    /// This is a bit safer than `as` because it wouldn't silently change the type if the code is
    /// refactored.
    ///
    /// While not strictly required (`*mut T` coerces to `*const T`), this is provided for symmetry
    /// with [`cast_mut`] on `*const T` and may have documentation value if used instead of implicit
    /// coercion.
    ///
    /// [`cast_mut`]: pointer::cast_mut
    #[stable(feature = "ptr_const_cast", since = "1.65.0")]
    #[rustc_const_stable(feature = "ptr_const_cast", since = "1.65.0")]
    #[rustc_diagnostic_item = "ptr_cast_const"]
    #[inline(always)]
    pub const fn cast_const(self) -> *const T {
        self as _
    }

    /// Gets the "address" portion of the pointer.
    ///
    /// This is similar to `self as usize`, except that the [provenance][crate::ptr#provenance] of
    /// the pointer is discarded and not [exposed][crate::ptr#exposed-provenance]. This means that
    /// casting the returned address back to a pointer yields a [pointer without
    /// provenance][without_provenance_mut], which is undefined behavior to dereference. To properly
    /// restore the lost information and obtain a dereferenceable pointer, use
    /// [`with_addr`][pointer::with_addr] or [`map_addr`][pointer::map_addr].
    ///
    /// If using those APIs is not possible because there is no way to preserve a pointer with the
    /// required provenance, then Strict Provenance might not be for you. Use pointer-integer casts
    /// or [`expose_provenance`][pointer::expose_provenance] and [`with_exposed_provenance`][with_exposed_provenance]
    /// instead. However, note that this makes your code less portable and less amenable to tools
    /// that check for compliance with the Rust memory model.
    ///
    /// On most platforms this will produce a value with the same bytes as the original
    /// pointer, because all the bytes are dedicated to describing the address.
    /// Platforms which need to store additional information in the pointer may
    /// perform a change of representation to produce a value containing only the address
    /// portion of the pointer. What that means is up to the platform to define.
    ///
    /// This is a [Strict Provenance][crate::ptr#strict-provenance] API.
    #[must_use]
    #[inline(always)]
    #[stable(feature = "strict_provenance", since = "1.84.0")]
    pub fn addr(self) -> usize {
        // A pointer-to-integer transmute currently has exactly the right semantics: it returns the
        // address without exposing the provenance. Note that this is *not* a stable guarantee about
        // transmute semantics, it relies on sysroot crates having special status.
        // SAFETY: Pointer-to-integer transmutes are valid (if you are okay with losing the
        // provenance).
        unsafe { mem::transmute(self.cast::<()>()) }
    }

    /// Exposes the ["provenance"][crate::ptr#provenance] part of the pointer for future use in
    /// [`with_exposed_provenance_mut`] and returns the "address" portion.
    ///
    /// This is equivalent to `self as usize`, which semantically discards provenance information.
    /// Furthermore, this (like the `as` cast) has the implicit side-effect of marking the
    /// provenance as 'exposed', so on platforms that support it you can later call
    /// [`with_exposed_provenance_mut`] to reconstitute the original pointer including its provenance.
    ///
    /// Due to its inherent ambiguity, [`with_exposed_provenance_mut`] may not be supported by tools
    /// that help you to stay conformant with the Rust memory model. It is recommended to use
    /// [Strict Provenance][crate::ptr#strict-provenance] APIs such as [`with_addr`][pointer::with_addr]
    /// wherever possible, in which case [`addr`][pointer::addr] should be used instead of `expose_provenance`.
    ///
    /// On most platforms this will produce a value with the same bytes as the original pointer,
    /// because all the bytes are dedicated to describing the address. Platforms which need to store
    /// additional information in the pointer may not support this operation, since the 'expose'
    /// side-effect which is required for [`with_exposed_provenance_mut`] to work is typically not
    /// available.
    ///
    /// This is an [Exposed Provenance][crate::ptr#exposed-provenance] API.
    ///
    /// [`with_exposed_provenance_mut`]: with_exposed_provenance_mut
    #[inline(always)]
    #[stable(feature = "exposed_provenance", since = "1.84.0")]
    pub fn expose_provenance(self) -> usize {
        self.cast::<()>() as usize
    }

    /// Creates a new pointer with the given address and the [provenance][crate::ptr#provenance] of
    /// `self`.
    ///
    /// This is similar to a `addr as *mut T` cast, but copies
    /// the *provenance* of `self` to the new pointer.
    /// This avoids the inherent ambiguity of the unary cast.
    ///
    /// This is equivalent to using [`wrapping_offset`][pointer::wrapping_offset] to offset
    /// `self` to the given address, and therefore has all the same capabilities and restrictions.
    ///
    /// This is a [Strict Provenance][crate::ptr#strict-provenance] API.
    #[must_use]
    #[inline]
    #[stable(feature = "strict_provenance", since = "1.84.0")]
    pub fn with_addr(self, addr: usize) -> Self {
        // This should probably be an intrinsic to avoid doing any sort of arithmetic, but
        // meanwhile, we can implement it with `wrapping_offset`, which preserves the pointer's
        // provenance.
        let self_addr = self.addr() as isize;
        let dest_addr = addr as isize;
        let offset = dest_addr.wrapping_sub(self_addr);
        self.wrapping_byte_offset(offset)
    }

    /// Creates a new pointer by mapping `self`'s address to a new one, preserving the original
    /// pointer's [provenance][crate::ptr#provenance].
    ///
    /// This is a convenience for [`with_addr`][pointer::with_addr], see that method for details.
    ///
    /// This is a [Strict Provenance][crate::ptr#strict-provenance] API.
    #[must_use]
    #[inline]
    #[stable(feature = "strict_provenance", since = "1.84.0")]
    pub fn map_addr(self, f: impl FnOnce(usize) -> usize) -> Self {
        self.with_addr(f(self.addr()))
    }

    /// Decompose a (possibly wide) pointer into its data pointer and metadata components.
    ///
    /// The pointer can be later reconstructed with [`from_raw_parts_mut`].
    #[unstable(feature = "ptr_metadata", issue = "81513")]
    #[inline]
    pub const fn to_raw_parts(self) -> (*mut (), <T as super::Pointee>::Metadata) {
        (self.cast(), super::metadata(self))
    }

    /// Returns `None` if the pointer is null, or else returns a shared reference to
    /// the value wrapped in `Some`. If the value may be uninitialized, [`as_uninit_ref`]
    /// must be used instead.
    ///
    /// For the mutable counterpart see [`as_mut`].
    ///
    /// [`as_uninit_ref`]: pointer#method.as_uninit_ref-1
    /// [`as_mut`]: #method.as_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that *either* the pointer is null *or*
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    ///
    /// # Panics during const evaluation
    ///
    /// This method will panic during const evaluation if the pointer cannot be
    /// determined to be null or not. See [`is_null`] for more information.
    ///
    /// [`is_null`]: #method.is_null-1
    ///
    /// # Examples
    ///
    /// ```
    /// let ptr: *mut u8 = &mut 10u8 as *mut u8;
    ///
    /// unsafe {
    ///     if let Some(val_back) = ptr.as_ref() {
    ///         println!("We got back the value: {val_back}!");
    ///     }
    /// }
    /// ```
    ///
    /// # Null-unchecked version
    ///
    /// If you are sure the pointer can never be null and are looking for some kind of
    /// `as_ref_unchecked` that returns the `&T` instead of `Option<&T>`, know that you can
    /// dereference the pointer directly.
    ///
    /// ```
    /// let ptr: *mut u8 = &mut 10u8 as *mut u8;
    ///
    /// unsafe {
    ///     let val_back = &*ptr;
    ///     println!("We got back the value: {val_back}!");
    /// }
    /// ```
    #[stable(feature = "ptr_as_ref", since = "1.9.0")]
    #[rustc_const_stable(feature = "const_ptr_is_null", since = "1.84.0")]
    #[inline]
    pub const unsafe fn as_ref<'a>(self) -> Option<&'a T> {
        // SAFETY: the caller must guarantee that `self` is valid for a
        // reference if it isn't null.
        if self.is_null() { None } else { unsafe { Some(&*self) } }
    }

    /// Returns a shared reference to the value behind the pointer.
    /// If the pointer may be null or the value may be uninitialized, [`as_uninit_ref`] must be used instead.
    /// If the pointer may be null, but the value is known to have been initialized, [`as_ref`] must be used instead.
    ///
    /// For the mutable counterpart see [`as_mut_unchecked`].
    ///
    /// [`as_ref`]: #method.as_ref
    /// [`as_uninit_ref`]: #method.as_uninit_ref
    /// [`as_mut_unchecked`]: #method.as_mut_unchecked
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(ptr_as_ref_unchecked)]
    /// let ptr: *mut u8 = &mut 10u8 as *mut u8;
    ///
    /// unsafe {
    ///     println!("We got back the value: {}!", ptr.as_ref_unchecked());
    /// }
    /// ```
    // FIXME: mention it in the docs for `as_ref` and `as_uninit_ref` once stabilized.
    #[unstable(feature = "ptr_as_ref_unchecked", issue = "122034")]
    #[inline]
    #[must_use]
    pub const unsafe fn as_ref_unchecked<'a>(self) -> &'a T {
        // SAFETY: the caller must guarantee that `self` is valid for a reference
        unsafe { &*self }
    }

    /// Returns `None` if the pointer is null, or else returns a shared reference to
    /// the value wrapped in `Some`. In contrast to [`as_ref`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the mutable counterpart see [`as_uninit_mut`].
    ///
    /// [`as_ref`]: pointer#method.as_ref-1
    /// [`as_uninit_mut`]: #method.as_uninit_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that *either* the pointer is null *or*
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    /// Note that because the created reference is to `MaybeUninit<T>`, the
    /// source pointer can point to uninitialized memory.
    ///
    /// # Panics during const evaluation
    ///
    /// This method will panic during const evaluation if the pointer cannot be
    /// determined to be null or not. See [`is_null`] for more information.
    ///
    /// [`is_null`]: #method.is_null-1
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(ptr_as_uninit)]
    ///
    /// let ptr: *mut u8 = &mut 10u8 as *mut u8;
    ///
    /// unsafe {
    ///     if let Some(val_back) = ptr.as_uninit_ref() {
    ///         println!("We got back the value: {}!", val_back.assume_init());
    ///     }
    /// }
    /// ```
    #[inline]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    pub const unsafe fn as_uninit_ref<'a>(self) -> Option<&'a MaybeUninit<T>>
    where
        T: Sized,
    {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        if self.is_null() { None } else { Some(unsafe { &*(self as *const MaybeUninit<T>) }) }
    }

    /// Adds a signed offset to a pointer.
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * The offset in bytes, `count * size_of::<T>()`, computed on mathematical integers (without
    ///   "wrapping around"), must fit in an `isize`.
    ///
    /// * If the computed offset is non-zero, then `self` must be [derived from][crate::ptr#provenance] a pointer to some
    ///   [allocated object], and the entire memory range between `self` and the result must be in
    ///   bounds of that allocated object. In particular, this range must not "wrap around" the edge
    ///   of the address space.
    ///
    /// Allocated objects can never be larger than `isize::MAX` bytes, so if the computed offset
    /// stays in bounds of the allocated object, it is guaranteed to satisfy the first requirement.
    /// This implies, for instance, that `vec.as_ptr().add(vec.len())` (for `vec: Vec<T>`) is always
    /// safe.
    ///
    /// Consider using [`wrapping_offset`] instead if these constraints are
    /// difficult to satisfy. The only advantage of this method is that it
    /// enables more aggressive compiler optimizations.
    ///
    /// [`wrapping_offset`]: #method.wrapping_offset
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = [1, 2, 3];
    /// let ptr: *mut u32 = s.as_mut_ptr();
    ///
    /// unsafe {
    ///     assert_eq!(2, *ptr.offset(1));
    ///     assert_eq!(3, *ptr.offset(2));
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[rustc_const_stable(feature = "const_ptr_offset", since = "1.61.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)]
    // even without panics, this helps for Miri backtraces
    // Note: It is the caller's responsibility to ensure that `self` is non-null and properly aligned.
    // These conditions are not verified as part of the preconditions.
    #[requires(
        // Precondition 1: the computed offset `count * size_of::<T>()` does not overflow `isize`.
        // Precondition 2: adding the computed offset to `self` does not cause overflow.
        // These two preconditions are combined for performance reason, as multiplication is computationally expensive in Kani.
        count.checked_mul(core::mem::size_of::<T>() as isize)
        .map_or(false, |computed_offset| (self as isize).checked_add(computed_offset).is_some()) &&
        // Precondition 3: If `T` is a unit type (`size_of::<T>() == 0`), this check is unnecessary as it has no allocated memory.
        // Otherwise, for non-unit types, `self` and `self.wrapping_offset(count)` should point to the same allocated object,
        // restricting `count` to prevent crossing allocation boundaries.
        ((core::mem::size_of::<T>() == 0) || (core::ub_checks::same_allocation(self, self.wrapping_offset(count))))
    )]
    // Postcondition: If `T` is a unit type (`size_of::<T>() == 0`), no allocation check is needed.
    // Otherwise, for non-unit types, ensure that `self` and `result` point to the same allocated object,
    // verifying that the result remains within the same allocation as `self`.
    #[ensures(|result| (core::mem::size_of::<T>() == 0) || core::ub_checks::same_allocation(self as *const T, *result as *const T))]
    pub const unsafe fn offset(self, count: isize) -> *mut T
    where
        T: Sized,
    {
        #[inline]
        #[rustc_allow_const_fn_unstable(const_eval_select)]
        const fn runtime_offset_nowrap(this: *const (), count: isize, size: usize) -> bool {
            // We can use const_eval_select here because this is only for UB checks.
            const_eval_select!(
                @capture { this: *const (), count: isize, size: usize } -> bool:
                if const {
                    true
                } else {
                    // `size` is the size of a Rust type, so we know that
                    // `size <= isize::MAX` and thus `as` cast here is not lossy.
                    let Some(byte_offset) = count.checked_mul(size as isize) else {
                        return false;
                    };
                    let (_, overflow) = this.addr().overflowing_add_signed(byte_offset);
                    !overflow
                }
            )
        }

        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "ptr::offset requires the address calculation to not overflow",
            (
                this: *const () = self as *const (),
                count: isize = count,
                size: usize = size_of::<T>(),
            ) => runtime_offset_nowrap(this, count, size)
        );

        // SAFETY: the caller must uphold the safety contract for `offset`.
        // The obtained pointer is valid for writes since the caller must
        // guarantee that it points to the same allocated object as `self`.
        unsafe { intrinsics::offset(self, count) }
    }

    /// Adds a signed offset in bytes to a pointer.
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
    #[stable(feature = "pointer_byte_offsets", since = "1.75.0")]
    #[rustc_const_stable(feature = "const_pointer_byte_offsets", since = "1.75.0")]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[requires(
        // If count is zero, any pointer is valid including null pointer.
        (count == 0) ||
        // Else if count is not zero, then ensure that subtracting `count` doesn't 
        // cause overflow and that both pointers `self` and the result are in the 
        // same allocation.
        ((self.addr() as isize).checked_add(count).is_some() &&
            core::ub_checks::same_allocation(self, self.wrapping_byte_offset(count)))
    )]
    #[ensures(|&result|
        // The resulting pointer should either be unchanged or still point to the same allocation
        (self.addr() == result.addr()) ||
        (core::ub_checks::same_allocation(self, result))
    )]
    pub const unsafe fn byte_offset(self, count: isize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `offset`.
        unsafe { self.cast::<u8>().offset(count).with_metadata_of(self) }
    }

    /// Adds a signed offset to a pointer using wrapping arithmetic.
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// This operation itself is always safe, but using the resulting pointer is not.
    ///
    /// The resulting pointer "remembers" the [allocated object] that `self` points to; it must not
    /// be used to read or write other allocated objects.
    ///
    /// In other words, `let z = x.wrapping_offset((y as isize) - (x as isize))` does *not* make `z`
    /// the same as `y` even if we assume `T` has size `1` and there is no overflow: `z` is still
    /// attached to the object `x` is attached to, and dereferencing it is Undefined Behavior unless
    /// `x` and `y` point into the same allocated object.
    ///
    /// Compared to [`offset`], this method basically delays the requirement of staying within the
    /// same allocated object: [`offset`] is immediate Undefined Behavior when crossing object
    /// boundaries; `wrapping_offset` produces a pointer but still leads to Undefined Behavior if a
    /// pointer is dereferenced when it is out-of-bounds of the object it is attached to. [`offset`]
    /// can be optimized better and is thus preferable in performance-sensitive code.
    ///
    /// The delayed check only considers the value of the pointer that was dereferenced, not the
    /// intermediate values used during the computation of the final result. For example,
    /// `x.wrapping_offset(o).wrapping_offset(o.wrapping_neg())` is always the same as `x`. In other
    /// words, leaving the allocated object and then re-entering it later is permitted.
    ///
    /// [`offset`]: #method.offset
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// // Iterate using a raw pointer in increments of two elements
    /// let mut data = [1u8, 2, 3, 4, 5];
    /// let mut ptr: *mut u8 = data.as_mut_ptr();
    /// let step = 2;
    /// let end_rounded_up = ptr.wrapping_offset(6);
    ///
    /// while ptr != end_rounded_up {
    ///     unsafe {
    ///         *ptr = 0;
    ///     }
    ///     ptr = ptr.wrapping_offset(step);
    /// }
    /// assert_eq!(&data, &[0, 2, 0, 4, 0]);
    /// ```
    #[stable(feature = "ptr_wrapping_offset", since = "1.16.0")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[rustc_const_stable(feature = "const_ptr_offset", since = "1.61.0")]
    #[inline(always)]
    pub const fn wrapping_offset(self, count: isize) -> *mut T
    where
        T: Sized,
    {
        // SAFETY: the `arith_offset` intrinsic has no prerequisites to be called.
        unsafe { intrinsics::arith_offset(self, count) as *mut T }
    }

    /// Adds a signed offset in bytes to a pointer using wrapping arithmetic.
    ///
    /// `count` is in units of **bytes**.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [wrapping_offset][pointer::wrapping_offset] on it. See that method
    /// for documentation.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[stable(feature = "pointer_byte_offsets", since = "1.75.0")]
    #[rustc_const_stable(feature = "const_pointer_byte_offsets", since = "1.75.0")]
    pub const fn wrapping_byte_offset(self, count: isize) -> Self {
        self.cast::<u8>().wrapping_offset(count).with_metadata_of(self)
    }

    /// Masks out bits of the pointer according to a mask.
    ///
    /// This is convenience for `ptr.map_addr(|a| a & mask)`.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    ///
    /// ## Examples
    ///
    /// ```
    /// #![feature(ptr_mask)]
    /// let mut v = 17_u32;
    /// let ptr: *mut u32 = &mut v;
    ///
    /// // `u32` is 4 bytes aligned,
    /// // which means that lower 2 bits are always 0.
    /// let tag_mask = 0b11;
    /// let ptr_mask = !tag_mask;
    ///
    /// // We can store something in these lower bits
    /// let tagged_ptr = ptr.map_addr(|a| a | 0b10);
    ///
    /// // Get the "tag" back
    /// let tag = tagged_ptr.addr() & tag_mask;
    /// assert_eq!(tag, 0b10);
    ///
    /// // Note that `tagged_ptr` is unaligned, it's UB to read from/write to it.
    /// // To get original pointer `mask` can be used:
    /// let masked_ptr = tagged_ptr.mask(ptr_mask);
    /// assert_eq!(unsafe { *masked_ptr }, 17);
    ///
    /// unsafe { *masked_ptr = 0 };
    /// assert_eq!(v, 0);
    /// ```
    #[unstable(feature = "ptr_mask", issue = "98290")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[inline(always)]
    pub fn mask(self, mask: usize) -> *mut T {
        intrinsics::ptr_mask(self.cast::<()>(), mask).cast_mut().with_metadata_of(self)
    }

    /// Returns `None` if the pointer is null, or else returns a unique reference to
    /// the value wrapped in `Some`. If the value may be uninitialized, [`as_uninit_mut`]
    /// must be used instead.
    ///
    /// For the shared counterpart see [`as_ref`].
    ///
    /// [`as_uninit_mut`]: #method.as_uninit_mut
    /// [`as_ref`]: pointer#method.as_ref-1
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that *either*
    /// the pointer is null *or*
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    ///
    /// # Panics during const evaluation
    ///
    /// This method will panic during const evaluation if the pointer cannot be
    /// determined to be null or not. See [`is_null`] for more information.
    ///
    /// [`is_null`]: #method.is_null-1
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = [1, 2, 3];
    /// let ptr: *mut u32 = s.as_mut_ptr();
    /// let first_value = unsafe { ptr.as_mut().unwrap() };
    /// *first_value = 4;
    /// # assert_eq!(s, [4, 2, 3]);
    /// println!("{s:?}"); // It'll print: "[4, 2, 3]".
    /// ```
    ///
    /// # Null-unchecked version
    ///
    /// If you are sure the pointer can never be null and are looking for some kind of
    /// `as_mut_unchecked` that returns the `&mut T` instead of `Option<&mut T>`, know that
    /// you can dereference the pointer directly.
    ///
    /// ```
    /// let mut s = [1, 2, 3];
    /// let ptr: *mut u32 = s.as_mut_ptr();
    /// let first_value = unsafe { &mut *ptr };
    /// *first_value = 4;
    /// # assert_eq!(s, [4, 2, 3]);
    /// println!("{s:?}"); // It'll print: "[4, 2, 3]".
    /// ```
    #[stable(feature = "ptr_as_ref", since = "1.9.0")]
    #[rustc_const_stable(feature = "const_ptr_is_null", since = "1.84.0")]
    #[inline]
    pub const unsafe fn as_mut<'a>(self) -> Option<&'a mut T> {
        // SAFETY: the caller must guarantee that `self` is be valid for
        // a mutable reference if it isn't null.
        if self.is_null() { None } else { unsafe { Some(&mut *self) } }
    }

    /// Returns a unique reference to the value behind the pointer.
    /// If the pointer may be null or the value may be uninitialized, [`as_uninit_mut`] must be used instead.
    /// If the pointer may be null, but the value is known to have been initialized, [`as_mut`] must be used instead.
    ///
    /// For the shared counterpart see [`as_ref_unchecked`].
    ///
    /// [`as_mut`]: #method.as_mut
    /// [`as_uninit_mut`]: #method.as_uninit_mut
    /// [`as_ref_unchecked`]: #method.as_mut_unchecked
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(ptr_as_ref_unchecked)]
    /// let mut s = [1, 2, 3];
    /// let ptr: *mut u32 = s.as_mut_ptr();
    /// let first_value = unsafe { ptr.as_mut_unchecked() };
    /// *first_value = 4;
    /// # assert_eq!(s, [4, 2, 3]);
    /// println!("{s:?}"); // It'll print: "[4, 2, 3]".
    /// ```
    // FIXME: mention it in the docs for `as_mut` and `as_uninit_mut` once stabilized.
    #[unstable(feature = "ptr_as_ref_unchecked", issue = "122034")]
    #[inline]
    #[must_use]
    pub const unsafe fn as_mut_unchecked<'a>(self) -> &'a mut T {
        // SAFETY: the caller must guarantee that `self` is valid for a reference
        unsafe { &mut *self }
    }

    /// Returns `None` if the pointer is null, or else returns a unique reference to
    /// the value wrapped in `Some`. In contrast to [`as_mut`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the shared counterpart see [`as_uninit_ref`].
    ///
    /// [`as_mut`]: #method.as_mut
    /// [`as_uninit_ref`]: pointer#method.as_uninit_ref-1
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that *either* the pointer is null *or*
    /// the pointer is [convertible to a reference](crate::ptr#pointer-to-reference-conversion).
    ///
    /// # Panics during const evaluation
    ///
    /// This method will panic during const evaluation if the pointer cannot be
    /// determined to be null or not. See [`is_null`] for more information.
    ///
    /// [`is_null`]: #method.is_null-1
    #[inline]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    pub const unsafe fn as_uninit_mut<'a>(self) -> Option<&'a mut MaybeUninit<T>>
    where
        T: Sized,
    {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        if self.is_null() { None } else { Some(unsafe { &mut *(self as *mut MaybeUninit<T>) }) }
    }

    /// Returns whether two pointers are guaranteed to be equal.
    ///
    /// At runtime this function behaves like `Some(self == other)`.
    /// However, in some contexts (e.g., compile-time evaluation),
    /// it is not always possible to determine equality of two pointers, so this function may
    /// spuriously return `None` for pointers that later actually turn out to have its equality known.
    /// But when it returns `Some`, the pointers' equality is guaranteed to be known.
    ///
    /// The return value may change from `Some` to `None` and vice versa depending on the compiler
    /// version and unsafe code must not
    /// rely on the result of this function for soundness. It is suggested to only use this function
    /// for performance optimizations where spurious `None` return values by this function do not
    /// affect the outcome, but just the performance.
    /// The consequences of using this method to make runtime and compile-time code behave
    /// differently have not been explored. This method should not be used to introduce such
    /// differences, and it should also not be stabilized before we have a better understanding
    /// of this issue.
    #[unstable(feature = "const_raw_ptr_comparison", issue = "53020")]
    #[rustc_const_unstable(feature = "const_raw_ptr_comparison", issue = "53020")]
    #[inline]
    pub const fn guaranteed_eq(self, other: *mut T) -> Option<bool>
    where
        T: Sized,
    {
        (self as *const T).guaranteed_eq(other as _)
    }

    /// Returns whether two pointers are guaranteed to be inequal.
    ///
    /// At runtime this function behaves like `Some(self != other)`.
    /// However, in some contexts (e.g., compile-time evaluation),
    /// it is not always possible to determine inequality of two pointers, so this function may
    /// spuriously return `None` for pointers that later actually turn out to have its inequality known.
    /// But when it returns `Some`, the pointers' inequality is guaranteed to be known.
    ///
    /// The return value may change from `Some` to `None` and vice versa depending on the compiler
    /// version and unsafe code must not
    /// rely on the result of this function for soundness. It is suggested to only use this function
    /// for performance optimizations where spurious `None` return values by this function do not
    /// affect the outcome, but just the performance.
    /// The consequences of using this method to make runtime and compile-time code behave
    /// differently have not been explored. This method should not be used to introduce such
    /// differences, and it should also not be stabilized before we have a better understanding
    /// of this issue.
    #[unstable(feature = "const_raw_ptr_comparison", issue = "53020")]
    #[rustc_const_unstable(feature = "const_raw_ptr_comparison", issue = "53020")]
    #[inline]
    pub const fn guaranteed_ne(self, other: *mut T) -> Option<bool>
    where
        T: Sized,
    {
        (self as *const T).guaranteed_ne(other as _)
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
    /// [`offset`]: pointer#method.offset-1
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * `self` and `origin` must either
    ///
    ///   * point to the same address, or
    ///   * both be [derived from][crate::ptr#provenance] a pointer to the same [allocated object], and the memory range between
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
    /// let mut a = [0; 5];
    /// let ptr1: *mut i32 = &mut a[1];
    /// let ptr2: *mut i32 = &mut a[3];
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
    /// let ptr1 = Box::into_raw(Box::new(0u8));
    /// let ptr2 = Box::into_raw(Box::new(1u8));
    /// let diff = (ptr2 as isize).wrapping_sub(ptr1 as isize);
    /// // Make ptr2_other an "alias" of ptr2.add(1), but derived from ptr1.
    /// let ptr2_other = (ptr1 as *mut u8).wrapping_offset(diff).wrapping_offset(1);
    /// assert_eq!(ptr2 as usize, ptr2_other as usize);
    /// // Since ptr2_other and ptr2 are derived from pointers to different objects,
    /// // computing their offset is undefined behavior, even though
    /// // they point to addresses that are in-bounds of the same object!
    /// unsafe {
    ///     let one = ptr2_other.offset_from(ptr2); // Undefined Behavior! ⚠️
    /// }
    ///
    ///
    /// ```
    #[stable(feature = "ptr_offset_from", since = "1.47.0")]
    #[rustc_const_stable(feature = "const_ptr_offset_from", since = "1.65.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[requires(
        // Ensuring that subtracting 'origin' from 'self' doesn't result in an overflow
        (self as isize).checked_sub(origin as isize).is_some() &&
        // Ensuring that the distance between 'self' and 'origin' is aligned to `T`
        (self as isize - origin as isize) % (mem::size_of::<T>() as isize) == 0 &&
        // Ensuring that both pointers point to the same address or are in the same allocation
        (self as isize == origin as isize || core::ub_checks::same_allocation(self, origin))
    )]
    #[ensures(|result| *result == (self as isize - origin as isize) / (mem::size_of::<T>() as isize))]
    pub const unsafe fn offset_from(self, origin: *const T) -> isize
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `offset_from`.
        unsafe { (self as *const T).offset_from(origin) }
    }

    /// Calculates the distance between two pointers within the same allocation. The returned value is in
    /// units of **bytes**.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [`offset_from`][pointer::offset_from] on it. See that method for
    /// documentation and safety requirements.
    ///
    /// For non-`Sized` pointees this operation considers only the data pointers,
    /// ignoring the metadata.
    #[inline(always)]
    #[stable(feature = "pointer_byte_offsets", since = "1.75.0")]
    #[rustc_const_stable(feature = "const_pointer_byte_offsets", since = "1.75.0")]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[requires(
        (mem::size_of_val_raw(self) != 0) &&
        // Ensures subtracting `origin` from `self` doesn't overflow
        (self.addr() as isize).checked_sub(origin.addr() as isize).is_some() &&
        // Ensure both pointers are in the same allocation or are pointing to the same address
        (self.addr() == origin.addr() ||
            core::ub_checks::same_allocation(self as *const u8, origin as *const u8))
    )]
    // The result should equal the distance in terms of bytes
    #[ensures(|result| *result == (self.addr() as isize - origin.addr() as isize))]
    pub const unsafe fn byte_offset_from<U: ?Sized>(self, origin: *const U) -> isize {
        // SAFETY: the caller must uphold the safety contract for `offset_from`.
        unsafe { self.cast::<u8>().offset_from(origin.cast::<u8>()) }
    }

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
    /// This method can be thought of as recovering the `count` that was passed
    /// to [`add`](#method.add) (or, with the parameters in the other order,
    /// to [`sub`](#method.sub)).  The following are all equivalent, assuming
    /// that their safety preconditions are met:
    /// ```rust
    /// # #![feature(ptr_sub_ptr)]
    /// # unsafe fn blah(ptr: *mut i32, origin: *mut i32, count: usize) -> bool {
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
    ///
    /// let mut a = [0; 5];
    /// let p: *mut i32 = a.as_mut_ptr();
    /// unsafe {
    ///     let ptr1: *mut i32 = p.add(1);
    ///     let ptr2: *mut i32 = p.add(3);
    ///
    ///     assert_eq!(ptr2.sub_ptr(ptr1), 2);
    ///     assert_eq!(ptr1.add(2), ptr2);
    ///     assert_eq!(ptr2.sub(2), ptr1);
    ///     assert_eq!(ptr2.sub_ptr(ptr2), 0);
    /// }
    ///
    /// // This would be incorrect, as the pointers are not correctly ordered:
    /// // ptr1.offset_from(ptr2)
    #[unstable(feature = "ptr_sub_ptr", issue = "95892")]
    #[rustc_const_unstable(feature = "const_ptr_sub_ptr", issue = "95892")]
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn sub_ptr(self, origin: *const T) -> usize
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `sub_ptr`.
        unsafe { (self as *const T).sub_ptr(origin) }
    }

    /// Calculates the distance between two pointers within the same allocation, *where it's known that
    /// `self` is equal to or greater than `origin`*. The returned value is in
    /// units of **bytes**.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [`sub_ptr`][pointer::sub_ptr] on it. See that method for
    /// documentation and safety requirements.
    ///
    /// For non-`Sized` pointees this operation considers only the data pointers,
    /// ignoring the metadata.
    #[unstable(feature = "ptr_sub_ptr", issue = "95892")]
    #[rustc_const_unstable(feature = "const_ptr_sub_ptr", issue = "95892")]
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn byte_sub_ptr<U: ?Sized>(self, origin: *mut U) -> usize {
        // SAFETY: the caller must uphold the safety contract for `byte_sub_ptr`.
        unsafe { (self as *const T).byte_sub_ptr(origin) }
    }

    /// Adds an unsigned offset to a pointer.
    ///
    /// This can only move the pointer forward (or not move it). If you need to move forward or
    /// backward depending on the value, then you might want [`offset`](#method.offset) instead
    /// which takes a signed offset.
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * The offset in bytes, `count * size_of::<T>()`, computed on mathematical integers (without
    ///   "wrapping around"), must fit in an `isize`.
    ///
    /// * If the computed offset is non-zero, then `self` must be [derived from][crate::ptr#provenance] a pointer to some
    ///   [allocated object], and the entire memory range between `self` and the result must be in
    ///   bounds of that allocated object. In particular, this range must not "wrap around" the edge
    ///   of the address space.
    ///
    /// Allocated objects can never be larger than `isize::MAX` bytes, so if the computed offset
    /// stays in bounds of the allocated object, it is guaranteed to satisfy the first requirement.
    /// This implies, for instance, that `vec.as_ptr().add(vec.len())` (for `vec: Vec<T>`) is always
    /// safe.
    ///
    /// Consider using [`wrapping_add`] instead if these constraints are
    /// difficult to satisfy. The only advantage of this method is that it
    /// enables more aggressive compiler optimizations.
    ///
    /// [`wrapping_add`]: #method.wrapping_add
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// let s: &str = "123";
    /// let ptr: *const u8 = s.as_ptr();
    ///
    /// unsafe {
    ///     assert_eq!('2', *ptr.add(1) as char);
    ///     assert_eq!('3', *ptr.add(2) as char);
    /// }
    /// ```
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[rustc_const_stable(feature = "const_ptr_offset", since = "1.61.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)]
    // even without panics, this helps for Miri backtraces
    // Note: It is the caller's responsibility to ensure that `self` is non-null and properly aligned.
    // These conditions are not verified as part of the preconditions.
    #[requires(
        // Precondition 1: the computed offset `count * size_of::<T>()` does not overflow `isize`.
        // Precondition 2: adding the computed offset to `self` does not cause overflow.
        // These two preconditions are combined for performance reason, as multiplication is computationally expensive in Kani. 
        count.checked_mul(core::mem::size_of::<T>())
        .map_or(false, |computed_offset| {
            computed_offset <= isize::MAX as usize && (self as isize).checked_add(computed_offset as isize).is_some()
        }) &&
        // Precondition 3: If `T` is a unit type (`size_of::<T>() == 0`), this check is unnecessary as it has no allocated memory.
        // Otherwise, for non-unit types, `self` and `self.wrapping_add(count)` should point to the same allocated object,
        // restricting `count` to prevent crossing allocation boundaries.
        ((core::mem::size_of::<T>() == 0) || (core::ub_checks::same_allocation(self, self.wrapping_add(count))))
    )]
    // Postcondition: If `T` is a unit type (`size_of::<T>() == 0`), no allocation check is needed.
    // Otherwise, for non-unit types, ensure that `self` and `result` point to the same allocated object,
    // verifying that the result remains within the same allocation as `self`.
    #[ensures(|result| (core::mem::size_of::<T>() == 0) || core::ub_checks::same_allocation(self as *const T, *result as *const T))]
    pub const unsafe fn add(self, count: usize) -> Self
    where
        T: Sized,
    {
        #[cfg(debug_assertions)]
        #[inline]
        #[rustc_allow_const_fn_unstable(const_eval_select)]
        const fn runtime_add_nowrap(this: *const (), count: usize, size: usize) -> bool {
            const_eval_select!(
                @capture { this: *const (), count: usize, size: usize } -> bool:
                if const {
                    true
                } else {
                    let Some(byte_offset) = count.checked_mul(size) else {
                        return false;
                    };
                    let (_, overflow) = this.addr().overflowing_add(byte_offset);
                    byte_offset <= (isize::MAX as usize) && !overflow
                }
            )
        }

        #[cfg(debug_assertions)] // Expensive, and doesn't catch much in the wild.
        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "ptr::add requires that the address calculation does not overflow",
            (
                this: *const () = self as *const (),
                count: usize = count,
                size: usize = size_of::<T>(),
            ) => runtime_add_nowrap(this, count, size)
        );

        // SAFETY: the caller must uphold the safety contract for `offset`.
        unsafe { intrinsics::offset(self, count) }
    }

    /// Adds an unsigned offset in bytes to a pointer.
    ///
    /// `count` is in units of bytes.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [add][pointer::add] on it. See that method for documentation
    /// and safety requirements.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[stable(feature = "pointer_byte_offsets", since = "1.75.0")]
    #[rustc_const_stable(feature = "const_pointer_byte_offsets", since = "1.75.0")]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[requires(
        // If count is zero, any pointer is valid including null pointer.
        (count == 0) ||
        // Else if count is not zero, then ensure that subtracting `count` doesn't 
        // cause overflow and that both pointers `self` and the result are in the 
        // same allocation.
        ((self.addr() as isize).checked_add(count as isize).is_some() &&
            core::ub_checks::same_allocation(self, self.wrapping_byte_add(count)))
    )]
    #[ensures(|&result|
        // The resulting pointer should either be unchanged or still point to the same allocation
        (self.addr() == result.addr()) ||
        (core::ub_checks::same_allocation(self, result))
    )]
    pub const unsafe fn byte_add(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `add`.
        unsafe { self.cast::<u8>().add(count).with_metadata_of(self) }
    }

    /// Subtracts an unsigned offset from a pointer.
    ///
    /// This can only move the pointer backward (or not move it). If you need to move forward or
    /// backward depending on the value, then you might want [`offset`](#method.offset) instead
    /// which takes a signed offset.
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is Undefined Behavior:
    ///
    /// * The offset in bytes, `count * size_of::<T>()`, computed on mathematical integers (without
    ///   "wrapping around"), must fit in an `isize`.
    ///
    /// * If the computed offset is non-zero, then `self` must be [derived from][crate::ptr#provenance] a pointer to some
    ///   [allocated object], and the entire memory range between `self` and the result must be in
    ///   bounds of that allocated object. In particular, this range must not "wrap around" the edge
    ///   of the address space.
    ///
    /// Allocated objects can never be larger than `isize::MAX` bytes, so if the computed offset
    /// stays in bounds of the allocated object, it is guaranteed to satisfy the first requirement.
    /// This implies, for instance, that `vec.as_ptr().add(vec.len())` (for `vec: Vec<T>`) is always
    /// safe.
    ///
    /// Consider using [`wrapping_sub`] instead if these constraints are
    /// difficult to satisfy. The only advantage of this method is that it
    /// enables more aggressive compiler optimizations.
    ///
    /// [`wrapping_sub`]: #method.wrapping_sub
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// let s: &str = "123";
    ///
    /// unsafe {
    ///     let end: *const u8 = s.as_ptr().add(3);
    ///     assert_eq!('3', *end.sub(1) as char);
    ///     assert_eq!('2', *end.sub(2) as char);
    /// }
    /// ```
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[rustc_const_stable(feature = "const_ptr_offset", since = "1.61.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)]
    // even without panics, this helps for Miri backtraces
    // Note: It is the caller's responsibility to ensure that `self` is non-null and properly aligned.
    // These conditions are not verified as part of the preconditions.
    #[requires(
        // Precondition 1: the computed offset `count * size_of::<T>()` does not overflow `isize`.
        // Precondition 2: substracting the computed offset from `self` does not cause overflow.
        // These two preconditions are combined for performance reason, as multiplication is computationally expensive in Kani.
        count.checked_mul(core::mem::size_of::<T>())
        .map_or(false, |computed_offset| {
            computed_offset <= isize::MAX as usize && (self as isize).checked_sub(computed_offset as isize).is_some()
        }) &&
        // Precondition 3: If `T` is a unit type (`size_of::<T>() == 0`), this check is unnecessary as it has no allocated memory.
        // Otherwise, for non-unit types, `self` and `self.wrapping_sub(count)` should point to the same allocated object,
        // restricting `count` to prevent crossing allocation boundaries.
        ((core::mem::size_of::<T>() == 0) || (core::ub_checks::same_allocation(self, self.wrapping_sub(count))))
    )]
    // Postcondition: If `T` is a unit type (`size_of::<T>() == 0`), no allocation check is needed.
    // Otherwise, for non-unit types, ensure that `self` and `result` point to the same allocated object,
    // verifying that the result remains within the same allocation as `self`.
    #[ensures(|result| (core::mem::size_of::<T>() == 0) || core::ub_checks::same_allocation(self as *const T, *result as *const T))]
    pub const unsafe fn sub(self, count: usize) -> Self
    where
        T: Sized,
    {
        #[cfg(debug_assertions)]
        #[inline]
        #[rustc_allow_const_fn_unstable(const_eval_select)]
        const fn runtime_sub_nowrap(this: *const (), count: usize, size: usize) -> bool {
            const_eval_select!(
                @capture { this: *const (), count: usize, size: usize } -> bool:
                if const {
                    true
                } else {
                    let Some(byte_offset) = count.checked_mul(size) else {
                        return false;
                    };
                    byte_offset <= (isize::MAX as usize) && this.addr() >= byte_offset
                }
            )
        }

        #[cfg(debug_assertions)] // Expensive, and doesn't catch much in the wild.
        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "ptr::sub requires that the address calculation does not overflow",
            (
                this: *const () = self as *const (),
                count: usize = count,
                size: usize = size_of::<T>(),
            ) => runtime_sub_nowrap(this, count, size)
        );

        if T::IS_ZST {
            // Pointer arithmetic does nothing when the pointee is a ZST.
            self
        } else {
            // SAFETY: the caller must uphold the safety contract for `offset`.
            // Because the pointee is *not* a ZST, that means that `count` is
            // at most `isize::MAX`, and thus the negation cannot overflow.
            unsafe { intrinsics::offset(self, intrinsics::unchecked_sub(0, count as isize)) }
        }
    }

    /// Subtracts an unsigned offset in bytes from a pointer.
    ///
    /// `count` is in units of bytes.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [sub][pointer::sub] on it. See that method for documentation
    /// and safety requirements.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[stable(feature = "pointer_byte_offsets", since = "1.75.0")]
    #[rustc_const_stable(feature = "const_pointer_byte_offsets", since = "1.75.0")]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    #[requires(
        // If count is zero, any pointer is valid including null pointer.
        (count == 0) ||
        // Else if count is not zero, then ensure that subtracting `count` doesn't 
        // cause overflow and that both pointers `self` and the result are in the 
        // same allocation.
        ((self.addr() as isize).checked_sub(count as isize).is_some() &&
            core::ub_checks::same_allocation(self, self.wrapping_byte_sub(count)))
    )]
    #[ensures(|&result|
        // The resulting pointer should either be unchanged or still point to the same allocation
        (self.addr() == result.addr()) ||
        (core::ub_checks::same_allocation(self, result))
    )]
    pub const unsafe fn byte_sub(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `sub`.
        unsafe { self.cast::<u8>().sub(count).with_metadata_of(self) }
    }

    /// Adds an unsigned offset to a pointer using wrapping arithmetic.
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// This operation itself is always safe, but using the resulting pointer is not.
    ///
    /// The resulting pointer "remembers" the [allocated object] that `self` points to; it must not
    /// be used to read or write other allocated objects.
    ///
    /// In other words, `let z = x.wrapping_add((y as usize) - (x as usize))` does *not* make `z`
    /// the same as `y` even if we assume `T` has size `1` and there is no overflow: `z` is still
    /// attached to the object `x` is attached to, and dereferencing it is Undefined Behavior unless
    /// `x` and `y` point into the same allocated object.
    ///
    /// Compared to [`add`], this method basically delays the requirement of staying within the
    /// same allocated object: [`add`] is immediate Undefined Behavior when crossing object
    /// boundaries; `wrapping_add` produces a pointer but still leads to Undefined Behavior if a
    /// pointer is dereferenced when it is out-of-bounds of the object it is attached to. [`add`]
    /// can be optimized better and is thus preferable in performance-sensitive code.
    ///
    /// The delayed check only considers the value of the pointer that was dereferenced, not the
    /// intermediate values used during the computation of the final result. For example,
    /// `x.wrapping_add(o).wrapping_sub(o)` is always the same as `x`. In other words, leaving the
    /// allocated object and then re-entering it later is permitted.
    ///
    /// [`add`]: #method.add
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// // Iterate using a raw pointer in increments of two elements
    /// let data = [1u8, 2, 3, 4, 5];
    /// let mut ptr: *const u8 = data.as_ptr();
    /// let step = 2;
    /// let end_rounded_up = ptr.wrapping_add(6);
    ///
    /// // This loop prints "1, 3, 5, "
    /// while ptr != end_rounded_up {
    ///     unsafe {
    ///         print!("{}, ", *ptr);
    ///     }
    ///     ptr = ptr.wrapping_add(step);
    /// }
    /// ```
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[rustc_const_stable(feature = "const_ptr_offset", since = "1.61.0")]
    #[inline(always)]
    pub const fn wrapping_add(self, count: usize) -> Self
    where
        T: Sized,
    {
        self.wrapping_offset(count as isize)
    }

    /// Adds an unsigned offset in bytes to a pointer using wrapping arithmetic.
    ///
    /// `count` is in units of bytes.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [wrapping_add][pointer::wrapping_add] on it. See that method for documentation.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[stable(feature = "pointer_byte_offsets", since = "1.75.0")]
    #[rustc_const_stable(feature = "const_pointer_byte_offsets", since = "1.75.0")]
    pub const fn wrapping_byte_add(self, count: usize) -> Self {
        self.cast::<u8>().wrapping_add(count).with_metadata_of(self)
    }

    /// Subtracts an unsigned offset from a pointer using wrapping arithmetic.
    ///
    /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// This operation itself is always safe, but using the resulting pointer is not.
    ///
    /// The resulting pointer "remembers" the [allocated object] that `self` points to; it must not
    /// be used to read or write other allocated objects.
    ///
    /// In other words, `let z = x.wrapping_sub((x as usize) - (y as usize))` does *not* make `z`
    /// the same as `y` even if we assume `T` has size `1` and there is no overflow: `z` is still
    /// attached to the object `x` is attached to, and dereferencing it is Undefined Behavior unless
    /// `x` and `y` point into the same allocated object.
    ///
    /// Compared to [`sub`], this method basically delays the requirement of staying within the
    /// same allocated object: [`sub`] is immediate Undefined Behavior when crossing object
    /// boundaries; `wrapping_sub` produces a pointer but still leads to Undefined Behavior if a
    /// pointer is dereferenced when it is out-of-bounds of the object it is attached to. [`sub`]
    /// can be optimized better and is thus preferable in performance-sensitive code.
    ///
    /// The delayed check only considers the value of the pointer that was dereferenced, not the
    /// intermediate values used during the computation of the final result. For example,
    /// `x.wrapping_add(o).wrapping_sub(o)` is always the same as `x`. In other words, leaving the
    /// allocated object and then re-entering it later is permitted.
    ///
    /// [`sub`]: #method.sub
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Examples
    ///
    /// ```
    /// // Iterate using a raw pointer in increments of two elements (backwards)
    /// let data = [1u8, 2, 3, 4, 5];
    /// let mut ptr: *const u8 = data.as_ptr();
    /// let start_rounded_down = ptr.wrapping_sub(2);
    /// ptr = ptr.wrapping_add(4);
    /// let step = 2;
    /// // This loop prints "5, 3, 1, "
    /// while ptr != start_rounded_down {
    ///     unsafe {
    ///         print!("{}, ", *ptr);
    ///     }
    ///     ptr = ptr.wrapping_sub(step);
    /// }
    /// ```
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[must_use = "returns a new pointer rather than modifying its argument"]
    #[rustc_const_stable(feature = "const_ptr_offset", since = "1.61.0")]
    #[inline(always)]
    pub const fn wrapping_sub(self, count: usize) -> Self
    where
        T: Sized,
    {
        self.wrapping_offset((count as isize).wrapping_neg())
    }

    /// Subtracts an unsigned offset in bytes from a pointer using wrapping arithmetic.
    ///
    /// `count` is in units of bytes.
    ///
    /// This is purely a convenience for casting to a `u8` pointer and
    /// using [wrapping_sub][pointer::wrapping_sub] on it. See that method for documentation.
    ///
    /// For non-`Sized` pointees this operation changes only the data pointer,
    /// leaving the metadata untouched.
    #[must_use]
    #[inline(always)]
    #[stable(feature = "pointer_byte_offsets", since = "1.75.0")]
    #[rustc_const_stable(feature = "const_pointer_byte_offsets", since = "1.75.0")]
    pub const fn wrapping_byte_sub(self, count: usize) -> Self {
        self.cast::<u8>().wrapping_sub(count).with_metadata_of(self)
    }

    /// Reads the value from `self` without moving it. This leaves the
    /// memory in `self` unchanged.
    ///
    /// See [`ptr::read`] for safety concerns and examples.
    ///
    /// [`ptr::read`]: crate::ptr::read()
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[rustc_const_stable(feature = "const_ptr_read", since = "1.71.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn read(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for ``.
        unsafe { read(self) }
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
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub unsafe fn read_volatile(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `read_volatile`.
        unsafe { read_volatile(self) }
    }

    /// Reads the value from `self` without moving it. This leaves the
    /// memory in `self` unchanged.
    ///
    /// Unlike `read`, the pointer may be unaligned.
    ///
    /// See [`ptr::read_unaligned`] for safety concerns and examples.
    ///
    /// [`ptr::read_unaligned`]: crate::ptr::read_unaligned()
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[rustc_const_stable(feature = "const_ptr_read", since = "1.71.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn read_unaligned(self) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `read_unaligned`.
        unsafe { read_unaligned(self) }
    }

    /// Copies `count * size_of<T>` bytes from `self` to `dest`. The source
    /// and destination may overlap.
    ///
    /// NOTE: this has the *same* argument order as [`ptr::copy`].
    ///
    /// See [`ptr::copy`] for safety concerns and examples.
    ///
    /// [`ptr::copy`]: crate::ptr::copy()
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn copy_to(self, dest: *mut T, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy`.
        unsafe { copy(self, dest, count) }
    }

    /// Copies `count * size_of<T>` bytes from `self` to `dest`. The source
    /// and destination may *not* overlap.
    ///
    /// NOTE: this has the *same* argument order as [`ptr::copy_nonoverlapping`].
    ///
    /// See [`ptr::copy_nonoverlapping`] for safety concerns and examples.
    ///
    /// [`ptr::copy_nonoverlapping`]: crate::ptr::copy_nonoverlapping()
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn copy_to_nonoverlapping(self, dest: *mut T, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy_nonoverlapping`.
        unsafe { copy_nonoverlapping(self, dest, count) }
    }

    /// Copies `count * size_of<T>` bytes from `src` to `self`. The source
    /// and destination may overlap.
    ///
    /// NOTE: this has the *opposite* argument order of [`ptr::copy`].
    ///
    /// See [`ptr::copy`] for safety concerns and examples.
    ///
    /// [`ptr::copy`]: crate::ptr::copy()
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn copy_from(self, src: *const T, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy`.
        unsafe { copy(src, self, count) }
    }

    /// Copies `count * size_of<T>` bytes from `src` to `self`. The source
    /// and destination may *not* overlap.
    ///
    /// NOTE: this has the *opposite* argument order of [`ptr::copy_nonoverlapping`].
    ///
    /// See [`ptr::copy_nonoverlapping`] for safety concerns and examples.
    ///
    /// [`ptr::copy_nonoverlapping`]: crate::ptr::copy_nonoverlapping()
    #[rustc_const_stable(feature = "const_intrinsic_copy", since = "1.83.0")]
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn copy_from_nonoverlapping(self, src: *const T, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `copy_nonoverlapping`.
        unsafe { copy_nonoverlapping(src, self, count) }
    }

    /// Executes the destructor (if any) of the pointed-to value.
    ///
    /// See [`ptr::drop_in_place`] for safety concerns and examples.
    ///
    /// [`ptr::drop_in_place`]: crate::ptr::drop_in_place()
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    pub unsafe fn drop_in_place(self) {
        // SAFETY: the caller must uphold the safety contract for `drop_in_place`.
        unsafe { drop_in_place(self) }
    }

    /// Overwrites a memory location with the given value without reading or
    /// dropping the old value.
    ///
    /// See [`ptr::write`] for safety concerns and examples.
    ///
    /// [`ptr::write`]: crate::ptr::write()
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[rustc_const_stable(feature = "const_ptr_write", since = "1.83.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn write(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write`.
        unsafe { write(self, val) }
    }

    /// Invokes memset on the specified pointer, setting `count * size_of::<T>()`
    /// bytes of memory starting at `self` to `val`.
    ///
    /// See [`ptr::write_bytes`] for safety concerns and examples.
    ///
    /// [`ptr::write_bytes`]: crate::ptr::write_bytes()
    #[doc(alias = "memset")]
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[rustc_const_stable(feature = "const_ptr_write", since = "1.83.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn write_bytes(self, val: u8, count: usize)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write_bytes`.
        unsafe { write_bytes(self, val, count) }
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
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub unsafe fn write_volatile(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write_volatile`.
        unsafe { write_volatile(self, val) }
    }

    /// Overwrites a memory location with the given value without reading or
    /// dropping the old value.
    ///
    /// Unlike `write`, the pointer may be unaligned.
    ///
    /// See [`ptr::write_unaligned`] for safety concerns and examples.
    ///
    /// [`ptr::write_unaligned`]: crate::ptr::write_unaligned()
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[rustc_const_stable(feature = "const_ptr_write", since = "1.83.0")]
    #[inline(always)]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub const unsafe fn write_unaligned(self, val: T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `write_unaligned`.
        unsafe { write_unaligned(self, val) }
    }

    /// Replaces the value at `self` with `src`, returning the old
    /// value, without dropping either.
    ///
    /// See [`ptr::replace`] for safety concerns and examples.
    ///
    /// [`ptr::replace`]: crate::ptr::replace()
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline(always)]
    pub unsafe fn replace(self, src: T) -> T
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `replace`.
        unsafe { replace(self, src) }
    }

    /// Swaps the values at two mutable locations of the same type, without
    /// deinitializing either. They may overlap, unlike `mem::swap` which is
    /// otherwise equivalent.
    ///
    /// See [`ptr::swap`] for safety concerns and examples.
    ///
    /// [`ptr::swap`]: crate::ptr::swap()
    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[rustc_const_stable(feature = "const_swap", since = "1.85.0")]
    #[inline(always)]
    pub const unsafe fn swap(self, with: *mut T)
    where
        T: Sized,
    {
        // SAFETY: the caller must uphold the safety contract for `swap`.
        unsafe { swap(self, with) }
    }

    /// Computes the offset that needs to be applied to the pointer in order to make it aligned to
    /// `align`.
    ///
    /// If it is not possible to align the pointer, the implementation returns
    /// `usize::MAX`.
    ///
    /// The offset is expressed in number of `T` elements, and not bytes. The value returned can be
    /// used with the `wrapping_add` method.
    ///
    /// There are no guarantees whatsoever that offsetting the pointer will not overflow or go
    /// beyond the allocation that the pointer points into. It is up to the caller to ensure that
    /// the returned offset is correct in all terms other than alignment.
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
    ///
    /// # unsafe {
    /// let mut x = [5_u8, 6, 7, 8, 9];
    /// let ptr = x.as_mut_ptr();
    /// let offset = ptr.align_offset(align_of::<u16>());
    ///
    /// if offset < x.len() - 1 {
    ///     let u16_ptr = ptr.add(offset).cast::<u16>();
    ///     *u16_ptr = 0;
    ///
    ///     assert!(x == [0, 0, 7, 8, 9] || x == [5, 0, 0, 8, 9]);
    /// } else {
    ///     // while the pointer can be aligned via `offset`, it would point
    ///     // outside the allocation
    /// }
    /// # }
    /// ```
    #[must_use]
    #[inline]
    #[stable(feature = "align_offset", since = "1.36.0")]
    pub fn align_offset(self, align: usize) -> usize
    where
        T: Sized,
    {
        if !align.is_power_of_two() {
            panic!("align_offset: align is not a power-of-two");
        }

        // SAFETY: `align` has been checked to be a power of 2 above
        let ret = unsafe { align_offset(self, align) };

        // Inform Miri that we want to consider the resulting pointer to be suitably aligned.
        #[cfg(miri)]
        if ret != usize::MAX {
            intrinsics::miri_promise_symbolic_alignment(
                self.wrapping_add(ret).cast_const().cast(),
                align,
            );
        }

        ret
    }

    /// Returns whether the pointer is properly aligned for `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// // On some platforms, the alignment of i32 is less than 4.
    /// #[repr(align(4))]
    /// struct AlignedI32(i32);
    ///
    /// let mut data = AlignedI32(42);
    /// let ptr = &mut data as *mut AlignedI32;
    ///
    /// assert!(ptr.is_aligned());
    /// assert!(!ptr.wrapping_byte_add(1).is_aligned());
    /// ```
    #[must_use]
    #[inline]
    #[stable(feature = "pointer_is_aligned", since = "1.79.0")]
    pub fn is_aligned(self) -> bool
    where
        T: Sized,
    {
        self.is_aligned_to(mem::align_of::<T>())
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
    /// let mut data = AlignedI32(42);
    /// let ptr = &mut data as *mut AlignedI32;
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
    #[must_use]
    #[inline]
    #[unstable(feature = "pointer_is_aligned_to", issue = "96284")]
    pub fn is_aligned_to(self, align: usize) -> bool {
        if !align.is_power_of_two() {
            panic!("is_aligned_to: align is not a power-of-two");
        }

        self.addr() & (align - 1) == 0
    }
}

impl<T> *mut [T] {
    /// Returns the length of a raw slice.
    ///
    /// The returned value is the number of **elements**, not the number of bytes.
    ///
    /// This function is safe, even when the raw slice cannot be cast to a slice
    /// reference because the pointer is null or unaligned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ptr;
    ///
    /// let slice: *mut [i8] = ptr::slice_from_raw_parts_mut(ptr::null_mut(), 3);
    /// assert_eq!(slice.len(), 3);
    /// ```
    #[inline(always)]
    #[stable(feature = "slice_ptr_len", since = "1.79.0")]
    #[rustc_const_stable(feature = "const_slice_ptr_len", since = "1.79.0")]
    pub const fn len(self) -> usize {
        metadata(self)
    }

    /// Returns `true` if the raw slice has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr;
    ///
    /// let slice: *mut [i8] = ptr::slice_from_raw_parts_mut(ptr::null_mut(), 3);
    /// assert!(!slice.is_empty());
    /// ```
    #[inline(always)]
    #[stable(feature = "slice_ptr_len", since = "1.79.0")]
    #[rustc_const_stable(feature = "const_slice_ptr_len", since = "1.79.0")]
    pub const fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Gets a raw, mutable pointer to the underlying array.
    ///
    /// If `N` is not exactly equal to the length of `self`, then this method returns `None`.
    #[unstable(feature = "slice_as_array", issue = "133508")]
    #[inline]
    #[must_use]
    pub const fn as_mut_array<const N: usize>(self) -> Option<*mut [T; N]> {
        if self.len() == N {
            let me = self.as_mut_ptr() as *mut [T; N];
            Some(me)
        } else {
            None
        }
    }

    /// Divides one mutable raw slice into two at an index.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// # Panics
    ///
    /// Panics if `mid > len`.
    ///
    /// # Safety
    ///
    /// `mid` must be [in-bounds] of the underlying [allocated object].
    /// Which means `self` must be dereferenceable and span a single allocation
    /// that is at least `mid * size_of::<T>()` bytes long. Not upholding these
    /// requirements is *[undefined behavior]* even if the resulting pointers are not used.
    ///
    /// Since `len` being in-bounds it is not a safety invariant of `*mut [T]` the
    /// safety requirements of this method are the same as for [`split_at_mut_unchecked`].
    /// The explicit bounds check is only as useful as `len` is correct.
    ///
    /// [`split_at_mut_unchecked`]: #method.split_at_mut_unchecked
    /// [in-bounds]: #method.add
    /// [allocated object]: crate::ptr#allocated-object
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(raw_slice_split)]
    /// #![feature(slice_ptr_get)]
    ///
    /// let mut v = [1, 0, 3, 0, 5, 6];
    /// let ptr = &mut v as *mut [_];
    /// unsafe {
    ///     let (left, right) = ptr.split_at_mut(2);
    ///     assert_eq!(&*left, [1, 0]);
    ///     assert_eq!(&*right, [3, 0, 5, 6]);
    /// }
    /// ```
    #[inline(always)]
    #[track_caller]
    #[unstable(feature = "raw_slice_split", issue = "95595")]
    pub unsafe fn split_at_mut(self, mid: usize) -> (*mut [T], *mut [T]) {
        assert!(mid <= self.len());
        // SAFETY: The assert above is only a safety-net as long as `self.len()` is correct
        // The actual safety requirements of this function are the same as for `split_at_mut_unchecked`
        unsafe { self.split_at_mut_unchecked(mid) }
    }

    /// Divides one mutable raw slice into two at an index, without doing bounds checking.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// # Safety
    ///
    /// `mid` must be [in-bounds] of the underlying [allocated object].
    /// Which means `self` must be dereferenceable and span a single allocation
    /// that is at least `mid * size_of::<T>()` bytes long. Not upholding these
    /// requirements is *[undefined behavior]* even if the resulting pointers are not used.
    ///
    /// [in-bounds]: #method.add
    /// [out-of-bounds index]: #method.add
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(raw_slice_split)]
    ///
    /// let mut v = [1, 0, 3, 0, 5, 6];
    /// // scoped to restrict the lifetime of the borrows
    /// unsafe {
    ///     let ptr = &mut v as *mut [_];
    ///     let (left, right) = ptr.split_at_mut_unchecked(2);
    ///     assert_eq!(&*left, [1, 0]);
    ///     assert_eq!(&*right, [3, 0, 5, 6]);
    ///     (&mut *left)[1] = 2;
    ///     (&mut *right)[1] = 4;
    /// }
    /// assert_eq!(v, [1, 2, 3, 4, 5, 6]);
    /// ```
    #[inline(always)]
    #[unstable(feature = "raw_slice_split", issue = "95595")]
    pub unsafe fn split_at_mut_unchecked(self, mid: usize) -> (*mut [T], *mut [T]) {
        let len = self.len();
        let ptr = self.as_mut_ptr();

        // SAFETY: Caller must pass a valid pointer and an index that is in-bounds.
        let tail = unsafe { ptr.add(mid) };
        (
            crate::ptr::slice_from_raw_parts_mut(ptr, mid),
            crate::ptr::slice_from_raw_parts_mut(tail, len - mid),
        )
    }

    /// Returns a raw pointer to the slice's buffer.
    ///
    /// This is equivalent to casting `self` to `*mut T`, but more type-safe.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(slice_ptr_get)]
    /// use std::ptr;
    ///
    /// let slice: *mut [i8] = ptr::slice_from_raw_parts_mut(ptr::null_mut(), 3);
    /// assert_eq!(slice.as_mut_ptr(), ptr::null_mut());
    /// ```
    #[inline(always)]
    #[unstable(feature = "slice_ptr_get", issue = "74265")]
    pub const fn as_mut_ptr(self) -> *mut T {
        self as *mut T
    }

    /// Returns a raw pointer to an element or subslice, without doing bounds
    /// checking.
    ///
    /// Calling this method with an [out-of-bounds index] or when `self` is not dereferenceable
    /// is *[undefined behavior]* even if the resulting pointer is not used.
    ///
    /// [out-of-bounds index]: #method.add
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(slice_ptr_get)]
    ///
    /// let x = &mut [1, 2, 4] as *mut [i32];
    ///
    /// unsafe {
    ///     assert_eq!(x.get_unchecked_mut(1), x.as_mut_ptr().add(1));
    /// }
    /// ```
    #[unstable(feature = "slice_ptr_get", issue = "74265")]
    #[inline(always)]
    pub unsafe fn get_unchecked_mut<I>(self, index: I) -> *mut I::Output
    where
        I: SliceIndex<[T]>,
    {
        // SAFETY: the caller ensures that `self` is dereferenceable and `index` in-bounds.
        unsafe { index.get_unchecked_mut(self) }
    }

    /// Returns `None` if the pointer is null, or else returns a shared slice to
    /// the value wrapped in `Some`. In contrast to [`as_ref`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the mutable counterpart see [`as_uninit_slice_mut`].
    ///
    /// [`as_ref`]: pointer#method.as_ref-1
    /// [`as_uninit_slice_mut`]: #method.as_uninit_slice_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that *either* the pointer is null *or*
    /// all of the following is true:
    ///
    /// * The pointer must be [valid] for reads for `ptr.len() * mem::size_of::<T>()` many bytes,
    ///   and it must be properly aligned. This means in particular:
    ///
    ///     * The entire memory range of this slice must be contained within a single [allocated object]!
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
    /// See also [`slice::from_raw_parts`][].
    ///
    /// [valid]: crate::ptr#safety
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Panics during const evaluation
    ///
    /// This method will panic during const evaluation if the pointer cannot be
    /// determined to be null or not. See [`is_null`] for more information.
    ///
    /// [`is_null`]: #method.is_null-1
    #[inline]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    pub const unsafe fn as_uninit_slice<'a>(self) -> Option<&'a [MaybeUninit<T>]> {
        if self.is_null() {
            None
        } else {
            // SAFETY: the caller must uphold the safety contract for `as_uninit_slice`.
            Some(unsafe { slice::from_raw_parts(self as *const MaybeUninit<T>, self.len()) })
        }
    }

    /// Returns `None` if the pointer is null, or else returns a unique slice to
    /// the value wrapped in `Some`. In contrast to [`as_mut`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the shared counterpart see [`as_uninit_slice`].
    ///
    /// [`as_mut`]: #method.as_mut
    /// [`as_uninit_slice`]: #method.as_uninit_slice-1
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that *either* the pointer is null *or*
    /// all of the following is true:
    ///
    /// * The pointer must be [valid] for reads and writes for `ptr.len() * mem::size_of::<T>()`
    ///   many bytes, and it must be properly aligned. This means in particular:
    ///
    ///     * The entire memory range of this slice must be contained within a single [allocated object]!
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
    /// See also [`slice::from_raw_parts_mut`][].
    ///
    /// [valid]: crate::ptr#safety
    /// [allocated object]: crate::ptr#allocated-object
    ///
    /// # Panics during const evaluation
    ///
    /// This method will panic during const evaluation if the pointer cannot be
    /// determined to be null or not. See [`is_null`] for more information.
    ///
    /// [`is_null`]: #method.is_null-1
    #[inline]
    #[unstable(feature = "ptr_as_uninit", issue = "75402")]
    pub const unsafe fn as_uninit_slice_mut<'a>(self) -> Option<&'a mut [MaybeUninit<T>]> {
        if self.is_null() {
            None
        } else {
            // SAFETY: the caller must uphold the safety contract for `as_uninit_slice_mut`.
            Some(unsafe { slice::from_raw_parts_mut(self as *mut MaybeUninit<T>, self.len()) })
        }
    }
}

impl<T, const N: usize> *mut [T; N] {
    /// Returns a raw pointer to the array's buffer.
    ///
    /// This is equivalent to casting `self` to `*mut T`, but more type-safe.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(array_ptr_get)]
    /// use std::ptr;
    ///
    /// let arr: *mut [i8; 3] = ptr::null_mut();
    /// assert_eq!(arr.as_mut_ptr(), ptr::null_mut());
    /// ```
    #[inline]
    #[unstable(feature = "array_ptr_get", issue = "119834")]
    pub const fn as_mut_ptr(self) -> *mut T {
        self as *mut T
    }

    /// Returns a raw pointer to a mutable slice containing the entire array.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(array_ptr_get)]
    ///
    /// let mut arr = [1, 2, 5];
    /// let ptr: *mut [i32; 3] = &mut arr;
    /// unsafe {
    ///     (&mut *ptr.as_mut_slice())[..2].copy_from_slice(&[3, 4]);
    /// }
    /// assert_eq!(arr, [3, 4, 5]);
    /// ```
    #[inline]
    #[unstable(feature = "array_ptr_get", issue = "119834")]
    pub const fn as_mut_slice(self) -> *mut [T] {
        self
    }
}

/// Pointer equality is by address, as produced by the [`<*mut T>::addr`](pointer::addr) method.
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> PartialEq for *mut T {
    #[inline(always)]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn eq(&self, other: &*mut T) -> bool {
        *self == *other
    }
}

/// Pointer equality is an equivalence relation.
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Eq for *mut T {}

/// Pointer comparison is by address, as produced by the [`<*mut T>::addr`](pointer::addr) method.
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Ord for *mut T {
    #[inline]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn cmp(&self, other: &*mut T) -> Ordering {
        if self < other {
            Less
        } else if self == other {
            Equal
        } else {
            Greater
        }
    }
}

/// Pointer comparison is by address, as produced by the [`<*mut T>::addr`](pointer::addr) method.
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> PartialOrd for *mut T {
    #[inline(always)]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn partial_cmp(&self, other: &*mut T) -> Option<Ordering> {
        Some(self.cmp(other))
    }

    #[inline(always)]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn lt(&self, other: &*mut T) -> bool {
        *self < *other
    }

    #[inline(always)]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn le(&self, other: &*mut T) -> bool {
        *self <= *other
    }

    #[inline(always)]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn gt(&self, other: &*mut T) -> bool {
        *self > *other
    }

    #[inline(always)]
    #[allow(ambiguous_wide_pointer_comparisons)]
    fn ge(&self, other: &*mut T) -> bool {
        *self >= *other
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::mem;

    use crate::kani;

    // Chosen for simplicity and sufficient size to test edge cases effectively
    // Represents the number of elements in the slice or array being tested.
    // Doesn't need to be large because all possible values for the slice are explored,
    // including edge cases like pointers at the start, middle, and end of the slice.
    // Symbolic execution generalizes across all possible elements, regardless of the actual array size.
    const ARRAY_SIZE: usize = 5;

    /// This macro generates verification harnesses for the `offset`, `add`, and `sub`
    /// pointer operations for a slice type and function name.
    macro_rules! generate_mut_slice_harnesses {
        ($ty:ty, $offset_fn:ident, $add_fn:ident, $sub_fn:ident) => {
            // Generates a harness for the `offset` operation
            #[kani::proof_for_contract(<*mut $ty>::offset)]
            fn $offset_fn() {
                let mut arr: [$ty; ARRAY_SIZE] = kani::Arbitrary::any_array();
                let test_ptr: *mut $ty = arr.as_mut_ptr();
                let offset: usize = kani::any();
                let count: isize = kani::any();
                kani::assume(offset <= ARRAY_SIZE * mem::size_of::<$ty>());
                let ptr_with_offset: *mut $ty = test_ptr.wrapping_byte_add(offset);
                unsafe {
                    ptr_with_offset.offset(count);
                }
            }

            // Generates a harness for the `add` operation
            #[kani::proof_for_contract(<*mut $ty>::add)]
            fn $add_fn() {
                let mut arr: [$ty; ARRAY_SIZE] = kani::Arbitrary::any_array();
                let test_ptr: *mut $ty = arr.as_mut_ptr();
                let offset: usize = kani::any();
                let count: usize = kani::any();
                kani::assume(offset <= ARRAY_SIZE * mem::size_of::<$ty>());
                let ptr_with_offset: *mut $ty = test_ptr.wrapping_byte_add(offset);
                unsafe {
                    ptr_with_offset.add(count);
                }
            }

            // Generates a harness for the `sub` operation
            #[kani::proof_for_contract(<*mut $ty>::sub)]
            fn $sub_fn() {
                let mut arr: [$ty; ARRAY_SIZE] = kani::Arbitrary::any_array();
                let test_ptr: *mut $ty = arr.as_mut_ptr();
                let offset: usize = kani::any();
                let count: usize = kani::any();
                kani::assume(offset <= ARRAY_SIZE * mem::size_of::<$ty>());
                let ptr_with_offset: *mut $ty = test_ptr.wrapping_byte_add(offset);
                unsafe {
                    ptr_with_offset.sub(count);
                }
            }
        };
    }

    // Generate pointer harnesses for various types (offset, add, sub)
    generate_mut_slice_harnesses!(
        i8,
        check_mut_offset_slice_i8,
        check_mut_add_slice_i8,
        check_mut_sub_slice_i8
    );
    generate_mut_slice_harnesses!(
        i16,
        check_mut_offset_slice_i16,
        check_mut_add_slice_i16,
        check_mut_sub_slice_i16
    );
    generate_mut_slice_harnesses!(
        i32,
        check_mut_offset_slice_i32,
        check_mut_add_slice_i32,
        check_mut_sub_slice_i32
    );
    generate_mut_slice_harnesses!(
        i64,
        check_mut_offset_slice_i64,
        check_mut_add_slice_i64,
        check_mut_sub_slice_i64
    );
    generate_mut_slice_harnesses!(
        i128,
        check_mut_offset_slice_i128,
        check_mut_add_slice_i128,
        check_mut_sub_slice_i128
    );
    generate_mut_slice_harnesses!(
        isize,
        check_mut_offset_slice_isize,
        check_mut_add_slice_isize,
        check_mut_sub_slice_isize
    );
    generate_mut_slice_harnesses!(
        u8,
        check_mut_offset_slice_u8,
        check_mut_add_slice_u8,
        check_mut_sub_slice_u8
    );
    generate_mut_slice_harnesses!(
        u16,
        check_mut_offset_slice_u16,
        check_mut_add_slice_u16,
        check_mut_sub_slice_u16
    );
    generate_mut_slice_harnesses!(
        u32,
        check_mut_offset_slice_u32,
        check_mut_add_slice_u32,
        check_mut_sub_slice_u32
    );
    generate_mut_slice_harnesses!(
        u64,
        check_mut_offset_slice_u64,
        check_mut_add_slice_u64,
        check_mut_sub_slice_u64
    );
    generate_mut_slice_harnesses!(
        u128,
        check_mut_offset_slice_u128,
        check_mut_add_slice_u128,
        check_mut_sub_slice_u128
    );
    generate_mut_slice_harnesses!(
        usize,
        check_mut_offset_slice_usize,
        check_mut_add_slice_usize,
        check_mut_sub_slice_usize
    );

    // Generate pointer harnesses for tuples (offset, add, sub)
    generate_mut_slice_harnesses!(
        (i8, i8),
        check_mut_offset_slice_tuple_1,
        check_mut_add_slice_tuple_1,
        check_mut_sub_slice_tuple_1
    );
    generate_mut_slice_harnesses!(
        (f64, bool),
        check_mut_offset_slice_tuple_2,
        check_mut_add_slice_tuple_2,
        check_mut_sub_slice_tuple_2
    );
    generate_mut_slice_harnesses!(
        (i32, f64, bool),
        check_mut_offset_slice_tuple_3,
        check_mut_add_slice_tuple_3,
        check_mut_sub_slice_tuple_3
    );
    generate_mut_slice_harnesses!(
        (i8, u16, i32, u64, isize),
        check_mut_offset_slice_tuple_4,
        check_mut_add_slice_tuple_4,
        check_mut_sub_slice_tuple_4
    );

    use kani::PointerGenerator;

    /// This macro generates a single verification harness for the `offset`, `add`, or `sub`
    /// pointer operations, supporting integer, composite, or unit types.
    /// - `$ty`: The type of the slice's elements (e.g., `i32`, `u32`, tuples).
    /// - `$fn_name`: The name of the function being checked (`add`, `sub`, or `offset`).
    /// - `$proof_name`: The name assigned to the generated proof for the contract.
    /// - `$count_ty:ty`: The type of the input variable passed to the method being invoked.
    ///
    /// Note: This macro is intended for internal use only and should be invoked exclusively
    /// by the `generate_arithmetic_harnesses` macro. Its purpose is to reduce code duplication,
    /// and it is not meant to be used directly elsewhere in the codebase.
    macro_rules! generate_single_arithmetic_harness {
        ($ty:ty, $proof_name:ident, $fn_name:ident, $count_ty:ty) => {
            #[kani::proof_for_contract(<*mut $ty>::$fn_name)]
            pub fn $proof_name() {
                // 200 bytes are large enough to cover all pointee types used for testing
                const BUF_SIZE: usize = 200;
                let mut generator = kani::PointerGenerator::<BUF_SIZE>::new();
                let test_ptr: *mut $ty = generator.any_in_bounds().ptr;
                let count: $count_ty = kani::any();
                unsafe {
                    test_ptr.$fn_name(count);
                }
            }
        };
    }

    /// This macro generates verification harnesses for the `offset`, `add`, and `sub`
    /// pointer operations, supporting integer, composite, and unit types.
    /// - `$ty`: The pointee type (e.g., i32, u32, tuples).
    /// - `$offset_fn_name`: The name for the `offset` proof for contract.
    /// - `$add_fn_name`: The name for the `add` proof for contract.
    /// - `$sub_fn_name`: The name for the `sub` proof for contract.
    macro_rules! generate_arithmetic_harnesses {
        ($ty:ty, $add_fn_name:ident, $sub_fn_name:ident, $offset_fn_name:ident) => {
            generate_single_arithmetic_harness!($ty, $add_fn_name, add, usize);
            generate_single_arithmetic_harness!($ty, $sub_fn_name, sub, usize);
            generate_single_arithmetic_harness!($ty, $offset_fn_name, offset, isize);
        };
    }

    // Generate harnesses for unit type (add, sub, offset)
    generate_arithmetic_harnesses!(
        (),
        check_mut_add_unit,
        check_mut_sub_unit,
        check_mut_offset_unit
    );

    // Generate harnesses for integer types (add, sub, offset)
    generate_arithmetic_harnesses!(i8, check_mut_add_i8, check_mut_sub_i8, check_mut_offset_i8);
    generate_arithmetic_harnesses!(i16, check_mut_add_i16, check_mut_sub_i16, check_mut_offset_i16);
    generate_arithmetic_harnesses!(i32, check_mut_add_i32, check_mut_sub_i32, check_mut_offset_i32);
    generate_arithmetic_harnesses!(i64, check_mut_add_i64, check_mut_sub_i64, check_mut_offset_i64);
    generate_arithmetic_harnesses!(
        i128,
        check_mut_add_i128,
        check_mut_sub_i128,
        check_mut_offset_i128
    );
    generate_arithmetic_harnesses!(
        isize,
        check_mut_add_isize,
        check_mut_sub_isize,
        check_mut_offset_isize
    );
    // Due to a bug of kani the test `check_mut_add_u8` is malfunctioning for now.
    // Tracking issue: https://github.com/model-checking/kani/issues/3743
    // generate_arithmetic_harnesses!(u8, check_mut_add_u8, check_mut_sub_u8, check_mut_offset_u8);
    generate_arithmetic_harnesses!(u16, check_mut_add_u16, check_mut_sub_u16, check_mut_offset_u16);
    generate_arithmetic_harnesses!(u32, check_mut_add_u32, check_mut_sub_u32, check_mut_offset_u32);
    generate_arithmetic_harnesses!(u64, check_mut_add_u64, check_mut_sub_u64, check_mut_offset_u64);
    generate_arithmetic_harnesses!(
        u128,
        check_mut_add_u128,
        check_mut_sub_u128,
        check_mut_offset_u128
    );
    generate_arithmetic_harnesses!(
        usize,
        check_mut_add_usize,
        check_mut_sub_usize,
        check_mut_offset_usize
    );

    // Generte harnesses for composite types (add, sub, offset)
    generate_arithmetic_harnesses!(
        (i8, i8),
        check_mut_add_tuple_1,
        check_mut_sub_tuple_1,
        check_mut_offset_tuple_1
    );
    generate_arithmetic_harnesses!(
        (f64, bool),
        check_mut_add_tuple_2,
        check_mut_sub_tuple_2,
        check_mut_offset_tuple_2
    );
    generate_arithmetic_harnesses!(
        (i32, f64, bool),
        check_mut_add_tuple_3,
        check_mut_sub_tuple_3,
        check_mut_offset_tuple_3
    );
    generate_arithmetic_harnesses!(
        (i8, u16, i32, u64, isize),
        check_mut_add_tuple_4,
        check_mut_sub_tuple_4,
        check_mut_offset_tuple_4
    );

    // The array's length is set to an arbitrary value, which defines its size.
    // In this case, implementing a dynamic array is not possible, because
    // PointerGenerator does not support dynamic sized arrays.
    const ARRAY_LEN: usize = 40;

    macro_rules! generate_offset_from_harness {
        ($type: ty, $proof_name1: ident, $proof_name2: ident) => {
            #[kani::proof_for_contract(<*mut $type>::offset_from)]
            // Below function is for a single element.
            pub fn $proof_name1() {
                const gen_size: usize = mem::size_of::<$type>();
                let mut generator1 = PointerGenerator::<gen_size>::new();
                let mut generator2 = PointerGenerator::<gen_size>::new();
                let ptr1: *mut $type = generator1.any_in_bounds().ptr;
                let ptr2: *mut $type = if kani::any() {
                    generator1.any_alloc_status().ptr
                } else {
                    generator2.any_alloc_status().ptr
                };

                unsafe {
                    ptr1.offset_from(ptr2);
                }
            }

            // Below function is for large arrays
            pub fn $proof_name2() {
                const gen_size: usize = mem::size_of::<$type>();
                let mut generator1 = PointerGenerator::<{ gen_size * ARRAY_LEN }>::new();
                let mut generator2 = PointerGenerator::<{ gen_size * ARRAY_LEN }>::new();
                let ptr1: *mut $type = generator1.any_in_bounds().ptr;
                let ptr2: *mut $type = if kani::any() {
                    generator1.any_alloc_status().ptr
                } else {
                    generator2.any_alloc_status().ptr
                };

                unsafe {
                    ptr1.offset_from(ptr2);
                }
            }
        };
    }

    // The proof for a unit type panics as offset_from needs the pointee size > 0
    #[kani::proof_for_contract(<*mut ()>::offset_from)]
    #[kani::should_panic]
    pub fn check_mut_offset_from_unit() {
        let mut val: () = ();
        let src_ptr: *mut () = &mut val;
        let dest_ptr: *mut () = &mut val;
        unsafe {
            dest_ptr.offset_from(src_ptr);
        }
    }

    generate_offset_from_harness!(u8, check_mut_offset_from_u8, check_mut_offset_from_u8_array);
    generate_offset_from_harness!(u16, check_mut_offset_from_u16, check_mut_offset_from_u16_array);
    generate_offset_from_harness!(u32, check_mut_offset_from_u32, check_mut_offset_from_u32_array);
    generate_offset_from_harness!(u64, check_mut_offset_from_u64, check_mut_offset_from_u64_array);
    generate_offset_from_harness!(
        u128,
        check_mut_offset_from_u128,
        check_mut_offset_from_u128_array
    );
    generate_offset_from_harness!(
        usize,
        check_mut_offset_from_usize,
        check_mut_offset_from_usize_array
    );

    generate_offset_from_harness!(i8, check_mut_offset_from_i8, check_mut_offset_from_i8_array);
    generate_offset_from_harness!(i16, check_mut_offset_from_i16, check_mut_offset_from_i16_array);
    generate_offset_from_harness!(i32, check_mut_offset_from_i32, check_mut_offset_from_i32_array);
    generate_offset_from_harness!(i64, check_mut_offset_from_i64, check_mut_offset_from_i64_array);
    generate_offset_from_harness!(
        i128,
        check_mut_offset_from_i128,
        check_mut_offset_from_i128_array
    );
    generate_offset_from_harness!(
        isize,
        check_mut_offset_from_isize,
        check_mut_offset_from_isize_array
    );

    generate_offset_from_harness!(
        (i8, i8),
        check_mut_offset_from_tuple_1,
        check_mut_offset_from_tuple_1_array
    );
    generate_offset_from_harness!(
        (f64, bool),
        check_mut_offset_from_tuple_2,
        check_mut_offset_from_tuple_2_array
    );
    generate_offset_from_harness!(
        (u32, i16, f32),
        check_mut_offset_from_tuple_3,
        check_mut_offset_from_tuple_3_array
    );
    generate_offset_from_harness!(
        ((), bool, u8, u16, i32, f64, i128, usize),
        check_mut_offset_from_tuple_4,
        check_mut_offset_from_tuple_4_array
    );

    #[kani::proof_for_contract(<*mut ()>::byte_offset)]
    #[kani::should_panic]
    pub fn check_mut_byte_offset_unit_invalid_count() {
        let mut val = ();
        let ptr: *mut () = &mut val;
        let count: isize = kani::any_where(|&x| x > (mem::size_of::<()>() as isize));
        unsafe {
            ptr.byte_offset(count);
        }
    }

    #[kani::proof_for_contract(<*mut ()>::byte_offset)]
    pub fn check_mut_byte_offset_cast_unit() {
        let mut generator = PointerGenerator::<ARRAY_LEN>::new();
        let ptr: *mut u8 = generator.any_in_bounds().ptr;
        let ptr1: *mut () = ptr as *mut ();
        let count: isize = kani::any();
        unsafe {
            ptr1.byte_offset(count);
        }
    }

    // generate proof for contracts of byte_add, byte_sub and byte_offset to verify
    // unit pointee type.
    // - `$fn_name`: function for which the contract must be verified
    // - `$proof_name`: name of the harness generated
    macro_rules! gen_mut_byte_arith_harness_for_unit {
        (byte_offset, $proof_name:ident) => {
            #[kani::proof_for_contract(<*mut ()>::byte_offset)]
            pub fn $proof_name() {
                let mut val = ();
                let ptr: *mut () = &mut val;
                let count: isize = mem::size_of::<()>() as isize;
                unsafe {
                    ptr.byte_offset(count);
                }
            }
        };

        ($fn_name:ident, $proof_name:ident) => {
            #[kani::proof_for_contract(<*mut ()>::$fn_name)]
            pub fn $proof_name() {
                let mut val = ();
                let ptr: *mut () = &mut val;
                //byte_add and byte_sub need count to be usize unlike byte_offset
                let count: usize = mem::size_of::<()>();
                unsafe {
                    ptr.$fn_name(count);
                }
            }
        };
    }

    gen_mut_byte_arith_harness_for_unit!(byte_add, check_mut_byte_add_unit);
    gen_mut_byte_arith_harness_for_unit!(byte_sub, check_mut_byte_sub_unit);
    gen_mut_byte_arith_harness_for_unit!(byte_offset, check_mut_byte_offset_unit);

    // generate proof for contracts for byte_add, byte_sub and byte_offset
    // - `$type`: pointee type
    // - `$fn_name`: function for which the contract must be verified
    // - `$proof_name`: name of the harness generated
    macro_rules! gen_mut_byte_arith_harness {
        ($type:ty, byte_offset, $proof_name:ident) => {
            #[kani::proof_for_contract(<*mut $type>::byte_offset)]
            pub fn $proof_name() {
                // generator with space for single element
                let mut generator1 = PointerGenerator::<{ mem::size_of::<$type>() }>::new();
                // generator with space for multiple elements
                let mut generator2 =
                    PointerGenerator::<{ mem::size_of::<$type>() * ARRAY_LEN }>::new();

                let ptr: *mut $type = if kani::any() {
                    generator1.any_in_bounds().ptr
                } else {
                    generator2.any_in_bounds().ptr
                };
                let count: isize = kani::any();

                unsafe {
                    ptr.byte_offset(count);
                }
            }
        };

        ($type:ty, $fn_name:ident, $proof_name:ident) => {
            #[kani::proof_for_contract(<*mut $type>::$fn_name)]
            pub fn $proof_name() {
                // generator with space for single element
                let mut generator1 = PointerGenerator::<{ mem::size_of::<$type>() }>::new();
                // generator with space for multiple elements
                let mut generator2 =
                    PointerGenerator::<{ mem::size_of::<$type>() * ARRAY_LEN }>::new();

                let ptr: *mut $type = if kani::any() {
                    generator1.any_in_bounds().ptr
                } else {
                    generator2.any_in_bounds().ptr
                };

                //byte_add and byte_sub need count to be usize unlike byte_offset
                let count: usize = kani::any();

                unsafe {
                    ptr.$fn_name(count);
                }
            }
        };
    }

    gen_mut_byte_arith_harness!(i8, byte_add, check_mut_byte_add_i8);
    gen_mut_byte_arith_harness!(i16, byte_add, check_mut_byte_add_i16);
    gen_mut_byte_arith_harness!(i32, byte_add, check_mut_byte_add_i32);
    gen_mut_byte_arith_harness!(i64, byte_add, check_mut_byte_add_i64);
    gen_mut_byte_arith_harness!(i128, byte_add, check_mut_byte_add_i128);
    gen_mut_byte_arith_harness!(isize, byte_add, check_mut_byte_add_isize);
    gen_mut_byte_arith_harness!(u8, byte_add, check_mut_byte_add_u8);
    gen_mut_byte_arith_harness!(u16, byte_add, check_mut_byte_add_u16);
    gen_mut_byte_arith_harness!(u32, byte_add, check_mut_byte_add_u32);
    gen_mut_byte_arith_harness!(u64, byte_add, check_mut_byte_add_u64);
    gen_mut_byte_arith_harness!(u128, byte_add, check_mut_byte_add_u128);
    gen_mut_byte_arith_harness!(usize, byte_add, check_mut_byte_add_usize);
    gen_mut_byte_arith_harness!((i8, i8), byte_add, check_mut_byte_add_tuple_1);
    gen_mut_byte_arith_harness!((f64, bool), byte_add, check_mut_byte_add_tuple_2);
    gen_mut_byte_arith_harness!((i32, f64, bool), byte_add, check_mut_byte_add_tuple_3);
    gen_mut_byte_arith_harness!((i8, u16, i32, u64, isize), byte_add, check_mut_byte_add_tuple_4);

    gen_mut_byte_arith_harness!(i8, byte_sub, check_mut_byte_sub_i8);
    gen_mut_byte_arith_harness!(i16, byte_sub, check_mut_byte_sub_i16);
    gen_mut_byte_arith_harness!(i32, byte_sub, check_mut_byte_sub_i32);
    gen_mut_byte_arith_harness!(i64, byte_sub, check_mut_byte_sub_i64);
    gen_mut_byte_arith_harness!(i128, byte_sub, check_mut_byte_sub_i128);
    gen_mut_byte_arith_harness!(isize, byte_sub, check_mut_byte_sub_isize);
    gen_mut_byte_arith_harness!(u8, byte_sub, check_mut_byte_sub_u8);
    gen_mut_byte_arith_harness!(u16, byte_sub, check_mut_byte_sub_u16);
    gen_mut_byte_arith_harness!(u32, byte_sub, check_mut_byte_sub_u32);
    gen_mut_byte_arith_harness!(u64, byte_sub, check_mut_byte_sub_u64);
    gen_mut_byte_arith_harness!(u128, byte_sub, check_mut_byte_sub_u128);
    gen_mut_byte_arith_harness!(usize, byte_sub, check_mut_byte_sub_usize);
    gen_mut_byte_arith_harness!((i8, i8), byte_sub, check_mut_byte_sub_tuple_1);
    gen_mut_byte_arith_harness!((f64, bool), byte_sub, check_mut_byte_sub_tuple_2);
    gen_mut_byte_arith_harness!((i32, f64, bool), byte_sub, check_mut_byte_sub_tuple_3);
    gen_mut_byte_arith_harness!((i8, u16, i32, u64, isize), byte_sub, check_mut_byte_sub_tuple_4);

    gen_mut_byte_arith_harness!(i8, byte_offset, check_mut_byte_offset_i8);
    gen_mut_byte_arith_harness!(i16, byte_offset, check_mut_byte_offset_i16);
    gen_mut_byte_arith_harness!(i32, byte_offset, check_mut_byte_offset_i32);
    gen_mut_byte_arith_harness!(i64, byte_offset, check_mut_byte_offset_i64);
    gen_mut_byte_arith_harness!(i128, byte_offset, check_mut_byte_offset_i128);
    gen_mut_byte_arith_harness!(isize, byte_offset, check_mut_byte_offset_isize);
    gen_mut_byte_arith_harness!(u8, byte_offset, check_mut_byte_offset_u8);
    gen_mut_byte_arith_harness!(u16, byte_offset, check_mut_byte_offset_u16);
    gen_mut_byte_arith_harness!(u32, byte_offset, check_mut_byte_offset_u32);
    gen_mut_byte_arith_harness!(u64, byte_offset, check_mut_byte_offset_u64);
    gen_mut_byte_arith_harness!(u128, byte_offset, check_mut_byte_offset_u128);
    gen_mut_byte_arith_harness!(usize, byte_offset, check_mut_byte_offset_usize);
    gen_mut_byte_arith_harness!((i8, i8), byte_offset, check_mut_byte_offset_tuple_1);
    gen_mut_byte_arith_harness!((f64, bool), byte_offset, check_mut_byte_offset_tuple_2);
    gen_mut_byte_arith_harness!((i32, f64, bool), byte_offset, check_mut_byte_offset_tuple_3);
    gen_mut_byte_arith_harness!(
        (i8, u16, i32, u64, isize),
        byte_offset,
        check_mut_byte_offset_tuple_4
    );

    macro_rules! gen_mut_byte_arith_harness_for_slice {
        ($type:ty, byte_offset, $proof_name:ident) => {
            #[kani::proof_for_contract(<*mut [$type]>::byte_offset)]
            pub fn $proof_name() {
                let mut arr: [$type; ARRAY_LEN] = kani::Arbitrary::any_array();
                let slice: &mut [$type] = kani::slice::any_slice_of_array_mut(&mut arr);
                let ptr: *mut [$type] = slice;

                let count: isize = kani::any();

                unsafe {
                    ptr.byte_offset(count);
                }
            }
        };

        ($type:ty, $fn_name: ident, $proof_name:ident) => {
            #[kani::proof_for_contract(<*mut [$type]>::$fn_name)]
            pub fn $proof_name() {
                let mut arr: [$type; ARRAY_LEN] = kani::Arbitrary::any_array();
                let slice: &mut [$type] = kani::slice::any_slice_of_array_mut(&mut arr);
                let ptr: *mut [$type] = slice;

                //byte_add and byte_sub need count to be usize unlike byte_offset
                let count: usize = kani::any();

                unsafe {
                    ptr.$fn_name(count);
                }
            }
        };
    }

    gen_mut_byte_arith_harness_for_slice!(i8, byte_add, check_mut_byte_add_i8_slice);
    gen_mut_byte_arith_harness_for_slice!(i16, byte_add, check_mut_byte_add_i16_slice);
    gen_mut_byte_arith_harness_for_slice!(i32, byte_add, check_mut_byte_add_i32_slice);
    gen_mut_byte_arith_harness_for_slice!(i64, byte_add, check_mut_byte_add_i64_slice);
    gen_mut_byte_arith_harness_for_slice!(i128, byte_add, check_mut_byte_add_i128_slice);
    gen_mut_byte_arith_harness_for_slice!(isize, byte_add, check_mut_byte_add_isize_slice);
    gen_mut_byte_arith_harness_for_slice!(u8, byte_add, check_mut_byte_add_u8_slice);
    gen_mut_byte_arith_harness_for_slice!(u16, byte_add, check_mut_byte_add_u16_slice);
    gen_mut_byte_arith_harness_for_slice!(u32, byte_add, check_mut_byte_add_u32_slice);
    gen_mut_byte_arith_harness_for_slice!(u64, byte_add, check_mut_byte_add_u64_slice);
    gen_mut_byte_arith_harness_for_slice!(u128, byte_add, check_mut_byte_add_u128_slice);
    gen_mut_byte_arith_harness_for_slice!(usize, byte_add, check_mut_byte_add_usize_slice);

    gen_mut_byte_arith_harness_for_slice!(i8, byte_sub, check_mut_byte_sub_i8_slice);
    gen_mut_byte_arith_harness_for_slice!(i16, byte_sub, check_mut_byte_sub_i16_slice);
    gen_mut_byte_arith_harness_for_slice!(i32, byte_sub, check_mut_byte_sub_i32_slice);
    gen_mut_byte_arith_harness_for_slice!(i64, byte_sub, check_mut_byte_sub_i64_slice);
    gen_mut_byte_arith_harness_for_slice!(i128, byte_sub, check_mut_byte_sub_i128_slice);
    gen_mut_byte_arith_harness_for_slice!(isize, byte_sub, check_mut_byte_sub_isize_slice);
    gen_mut_byte_arith_harness_for_slice!(u8, byte_sub, check_mut_byte_sub_u8_slice);
    gen_mut_byte_arith_harness_for_slice!(u16, byte_sub, check_mut_byte_sub_u16_slice);
    gen_mut_byte_arith_harness_for_slice!(u32, byte_sub, check_mut_byte_sub_u32_slice);
    gen_mut_byte_arith_harness_for_slice!(u64, byte_sub, check_mut_byte_sub_u64_slice);
    gen_mut_byte_arith_harness_for_slice!(u128, byte_sub, check_mut_byte_sub_u128_slice);
    gen_mut_byte_arith_harness_for_slice!(usize, byte_sub, check_mut_byte_sub_usize_slice);

    gen_mut_byte_arith_harness_for_slice!(i8, byte_offset, check_mut_byte_offset_i8_slice);
    gen_mut_byte_arith_harness_for_slice!(i16, byte_offset, check_mut_byte_offset_i16_slice);
    gen_mut_byte_arith_harness_for_slice!(i32, byte_offset, check_mut_byte_offset_i32_slice);
    gen_mut_byte_arith_harness_for_slice!(i64, byte_offset, check_mut_byte_offset_i64_slice);
    gen_mut_byte_arith_harness_for_slice!(i128, byte_offset, check_mut_byte_offset_i128_slice);
    gen_mut_byte_arith_harness_for_slice!(isize, byte_offset, check_mut_byte_offset_isize_slice);
    gen_mut_byte_arith_harness_for_slice!(u8, byte_offset, check_mut_byte_offset_u8_slice);
    gen_mut_byte_arith_harness_for_slice!(u16, byte_offset, check_mut_byte_offset_u16_slice);
    gen_mut_byte_arith_harness_for_slice!(u32, byte_offset, check_mut_byte_offset_u32_slice);
    gen_mut_byte_arith_harness_for_slice!(u64, byte_offset, check_mut_byte_offset_u64_slice);
    gen_mut_byte_arith_harness_for_slice!(u128, byte_offset, check_mut_byte_offset_u128_slice);
    gen_mut_byte_arith_harness_for_slice!(usize, byte_offset, check_mut_byte_offset_usize_slice);

    // Trait used exclusively for implementing proofs for contracts for `dyn Trait` type.
    trait TestTrait {}

    // Struct used exclusively for implementing proofs for contracts for `dyn Trait` type.
    #[cfg_attr(kani, derive(kani::Arbitrary))]
    struct TestStruct {
        value: i64,
    }

    impl TestTrait for TestStruct {}

    /// This macro generates proofs for contracts on `byte_add`, `byte_sub`, and `byte_offset`
    /// operations for pointers to dyn Trait.
    /// - `$fn_name`: Specifies the arithmetic operation to verify.
    /// - `$proof_name`: Specifies the name of the generated proof for contract.
    macro_rules! gen_mut_byte_arith_harness_for_dyn {
        (byte_offset, $proof_name:ident) => {
            // tracking issue: https://github.com/model-checking/kani/issues/3763
            // Workaround: Directly verifying the method `<*mut dyn TestTrait>::byte_offset`
            // causes a compilation error. As a workaround, the proof is annotated with the
            // underlying struct type instead.
            #[kani::proof_for_contract(<*mut TestStruct>::byte_offset)]
            pub fn $proof_name() {
                let mut test_struct = TestStruct { value: 42 };
                let trait_object: &mut dyn TestTrait = &mut test_struct;
                let test_ptr: *mut dyn TestTrait = trait_object;

                let count: isize = kani::any();

                unsafe {
                    test_ptr.byte_offset(count);
                }
            }
        };
        ($fn_name: ident, $proof_name:ident) => {
            // tracking issue: https://github.com/model-checking/kani/issues/3763
            // Workaround: Directly verifying the method `<*mut dyn TestTrait>::$fn_name`
            // causes a compilation error. As a workaround, the proof is annotated with the
            // underlying struct type instead.
            #[kani::proof_for_contract(<*mut TestStruct>::$fn_name)]
            pub fn $proof_name() {
                let mut test_struct = TestStruct { value: 42 };
                let trait_object: &mut dyn TestTrait = &mut test_struct;
                let test_ptr: *mut dyn TestTrait = trait_object;

                //byte_add and byte_sub need count to be usize unlike byte_offset
                let count: usize = kani::any();

                unsafe {
                    test_ptr.$fn_name(count);
                }
            }
        };
    }

    // fn <*mut T>::add(), <*mut T>::sub() and <*mut T>::offset() dyn Trait verification
    gen_mut_byte_arith_harness_for_dyn!(byte_add, check_mut_byte_add_dyn);
    gen_mut_byte_arith_harness_for_dyn!(byte_sub, check_mut_byte_sub_dyn);
    gen_mut_byte_arith_harness_for_dyn!(byte_offset, check_mut_byte_offset_dyn);

    #[kani::proof]
    pub fn check_mut_byte_offset_from_fixed_offset() {
        let mut arr: [u32; ARRAY_LEN] = kani::Arbitrary::any_array();
        let offset: usize = kani::any_where(|&x| x <= ARRAY_LEN);
        let origin_ptr: *mut u32 = arr.as_mut_ptr();
        let self_ptr: *mut u32 = unsafe { origin_ptr.byte_offset(offset as isize) };
        let result: isize = unsafe { self_ptr.byte_offset_from(origin_ptr) };
        assert_eq!(result, offset as isize);
        assert_eq!(result, (self_ptr.addr() as isize - origin_ptr.addr() as isize));
    }

    // Proof for unit size
    #[kani::proof_for_contract(<*mut ()>::byte_offset_from)]
    pub fn check_mut_byte_offset_from_unit() {
        let mut val: () = ();
        let src_ptr: *mut () = &mut val;
        let dest_ptr: *mut () = &mut val;
        unsafe {
            dest_ptr.byte_offset_from(src_ptr);
        }
    }

    // Generate proofs for contracts for byte_offset_from to verify pointer to int
    // and composite types.
    // - `$type`: pointee type.
    // - `$proof_name1`: name of the harness for single element.
    // - `$proof_name2`: name of the harness for array of elements.
    macro_rules! generate_mut_byte_offset_from_harness {
        ($type: ty, $proof_name1: ident, $proof_name2: ident) => {
            // Proof for a single element
            #[kani::proof_for_contract(<*mut $type>::byte_offset_from)]
            pub fn $proof_name1() {
                const gen_size: usize = mem::size_of::<$type>();
                let mut generator1 = PointerGenerator::<gen_size>::new();
                let mut generator2 = PointerGenerator::<gen_size>::new();
                let ptr1: *mut $type = generator1.any_in_bounds().ptr;
                let ptr2: *mut $type = if kani::any() {
                    generator1.any_alloc_status().ptr
                } else {
                    generator2.any_alloc_status().ptr
                };

                unsafe {
                    ptr1.byte_offset_from(ptr2);
                }
            }

            // Proof for large arrays
            #[kani::proof_for_contract(<*mut $type>::byte_offset_from)]
            pub fn $proof_name2() {
                const gen_size: usize = mem::size_of::<$type>();
                let mut generator1 = PointerGenerator::<{ gen_size * ARRAY_LEN }>::new();
                let mut generator2 = PointerGenerator::<{ gen_size * ARRAY_LEN }>::new();
                let ptr1: *mut $type = generator1.any_in_bounds().ptr;
                let ptr2: *mut $type = if kani::any() {
                    generator1.any_alloc_status().ptr
                } else {
                    generator2.any_alloc_status().ptr
                };

                unsafe {
                    ptr1.byte_offset_from(ptr2);
                }
            }
        };
    }

    generate_mut_byte_offset_from_harness!(
        u8,
        check_mut_byte_offset_from_u8,
        check_mut_byte_offset_from_u8_arr
    );
    generate_mut_byte_offset_from_harness!(
        u16,
        check_mut_byte_offset_from_u16,
        check_mut_byte_offset_from_u16_arr
    );
    generate_mut_byte_offset_from_harness!(
        u32,
        check_mut_byte_offset_from_u32,
        check_mut_byte_offset_from_u32_arr
    );
    generate_mut_byte_offset_from_harness!(
        u64,
        check_mut_byte_offset_from_u64,
        check_mut_byte_offset_from_u64_arr
    );
    generate_mut_byte_offset_from_harness!(
        u128,
        check_mut_byte_offset_from_u128,
        check_mut_byte_offset_from_u128_arr
    );
    generate_mut_byte_offset_from_harness!(
        usize,
        check_mut_byte_offset_from_usize,
        check_mut_byte_offset_from_usize_arr
    );

    generate_mut_byte_offset_from_harness!(
        i8,
        check_mut_byte_offset_from_i8,
        check_mut_byte_offset_from_i8_arr
    );
    generate_mut_byte_offset_from_harness!(
        i16,
        check_mut_byte_offset_from_i16,
        check_mut_byte_offset_from_i16_arr
    );
    generate_mut_byte_offset_from_harness!(
        i32,
        check_mut_byte_offset_from_i32,
        check_mut_byte_offset_from_i32_arr
    );
    generate_mut_byte_offset_from_harness!(
        i64,
        check_mut_byte_offset_from_i64,
        check_mut_byte_offset_from_i64_arr
    );
    generate_mut_byte_offset_from_harness!(
        i128,
        check_mut_byte_offset_from_i128,
        check_mut_byte_offset_from_i128_arr
    );
    generate_mut_byte_offset_from_harness!(
        isize,
        check_mut_byte_offset_from_isize,
        check_mut_byte_offset_from_isize_arr
    );

    generate_mut_byte_offset_from_harness!(
        (i8, i8),
        check_mut_byte_offset_from_tuple_1,
        check_mut_byte_offset_from_tuple_1_arr
    );
    generate_mut_byte_offset_from_harness!(
        (f64, bool),
        check_mut_byte_offset_from_tuple_2,
        check_mut_byte_offset_from_tuple_2_arr
    );
    generate_mut_byte_offset_from_harness!(
        (u32, i16, f32),
        check_mut_byte_offset_from_tuple_3,
        check_mut_byte_offset_from_tuple_3_arr
    );
    generate_mut_byte_offset_from_harness!(
        ((), bool, u8, u16, i32, f64, i128, usize),
        check_mut_byte_offset_from_tuple_4,
        check_mut_byte_offset_from_tuple_4_arr
    );

    // The length of a slice is set to an arbitrary value, which defines its size.
    // In this case, implementing a slice with a dynamic size set using kani::any()
    // is not possible, because PointerGenerator does not support non-deterministic
    // slice pointers.
    const SLICE_LEN: usize = 10;

    // Generate proofs for contracts for byte_offset_from to verify pointers to slices
    // - `$type`: type of the underlyign element within the slice pointer.
    // - `$proof_name`: name of the harness.
    macro_rules! generate_mut_byte_offset_from_slice_harness {
        ($type: ty, $proof_name: ident) => {
            #[kani::proof_for_contract(<*mut [$type]>::byte_offset_from)]
            pub fn $proof_name() {
                const gen_size: usize = mem::size_of::<$type>();
                let mut generator1 = PointerGenerator::<{ gen_size * ARRAY_LEN }>::new();
                let mut generator2 = PointerGenerator::<{ gen_size * ARRAY_LEN }>::new();
                let ptr1: *mut [$type] = generator1.any_in_bounds().ptr as *mut [$type; SLICE_LEN];
                let ptr2: *mut [$type] = if kani::any() {
                    generator1.any_alloc_status().ptr as *mut [$type; SLICE_LEN]
                } else {
                    generator2.any_alloc_status().ptr as *mut [$type; SLICE_LEN]
                };

                unsafe {
                    ptr1.byte_offset_from(ptr2);
                }
            }
        };
    }

    generate_mut_byte_offset_from_slice_harness!(u8, check_mut_byte_offset_from_u8_slice);
    generate_mut_byte_offset_from_slice_harness!(u16, check_mut_byte_offset_from_u16_slice);
    generate_mut_byte_offset_from_slice_harness!(u32, check_mut_byte_offset_from_u32_slice);
    generate_mut_byte_offset_from_slice_harness!(u64, check_mut_byte_offset_from_u64_slice);
    generate_mut_byte_offset_from_slice_harness!(u128, check_mut_byte_offset_from_u128_slice);
    generate_mut_byte_offset_from_slice_harness!(usize, check_mut_byte_offset_from_usize_slice);
    generate_mut_byte_offset_from_slice_harness!(i8, check_mut_byte_offset_from_i8_slice);
    generate_mut_byte_offset_from_slice_harness!(i16, check_mut_byte_offset_from_i16_slice);
    generate_mut_byte_offset_from_slice_harness!(i32, check_mut_byte_offset_from_i32_slice);
    generate_mut_byte_offset_from_slice_harness!(i64, check_mut_byte_offset_from_i64_slice);
    generate_mut_byte_offset_from_slice_harness!(i128, check_mut_byte_offset_from_i128_slice);
    generate_mut_byte_offset_from_slice_harness!(isize, check_mut_byte_offset_from_isize_slice);

    // tracking issue: https://github.com/model-checking/kani/issues/3763
    // Workaround: Directly verifying the method `<*mut dyn TestTrait>::byte_offset_from`
    // causes a compilation error. As a workaround, the proof is annotated with the
    // underlying struct type instead.
    #[kani::proof_for_contract(<*mut TestStruct>::byte_offset_from)]
    pub fn check_mut_byte_offset_from_dyn() {
        const gen_size: usize = mem::size_of::<TestStruct>();
        // Since the pointer generator cannot directly create pointers to `dyn Trait`,
        // we first generate a pointer to the underlying struct and then cast it to a `dyn Trait` pointer.
        let mut generator_caller = PointerGenerator::<gen_size>::new();
        let mut generator_input = PointerGenerator::<gen_size>::new();
        let ptr_caller: *mut TestStruct = generator_caller.any_in_bounds().ptr;
        let ptr_input: *mut TestStruct = if kani::any() {
            generator_caller.any_alloc_status().ptr
        } else {
            generator_input.any_alloc_status().ptr
        };

        let ptr_caller = ptr_caller as *mut dyn TestTrait;
        let ptr_input = ptr_input as *mut dyn TestTrait;

        unsafe {
            ptr_caller.byte_offset_from(ptr_input);
        }
    }
}
