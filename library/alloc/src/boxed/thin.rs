//! Based on
//! <https://github.com/matthieu-m/rfc2580/blob/b58d1d3cba0d4b5e859d3617ea2d0943aaa31329/examples/thin.rs>
//! by matthieu-m

use core::error::Error;
use core::fmt::{self, Debug, Display, Formatter};
#[cfg(not(no_global_oom_handling))]
use core::intrinsics::{const_allocate, const_make_global};
#[cfg(kani)]
use core::kani;
use core::marker::PhantomData;
#[cfg(not(no_global_oom_handling))]
use core::marker::Unsize;
#[cfg(not(no_global_oom_handling))]
use core::mem::{self, SizedTypeProperties};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, NonNull, Pointee};

use crate::alloc::{self, Layout, LayoutError};

/// ThinBox.
///
/// A thin pointer for heap allocation, regardless of T.
///
/// # Examples
///
/// ```
/// #![feature(thin_box)]
/// use std::boxed::ThinBox;
///
/// let five = ThinBox::new(5);
/// let thin_slice = ThinBox::<[i32]>::new_unsize([1, 2, 3, 4]);
///
/// let size_of_ptr = size_of::<*const ()>();
/// assert_eq!(size_of_ptr, size_of_val(&five));
/// assert_eq!(size_of_ptr, size_of_val(&thin_slice));
/// ```
#[unstable(feature = "thin_box", issue = "92791")]
pub struct ThinBox<T: ?Sized> {
    // This is essentially `WithHeader<<T as Pointee>::Metadata>`,
    // but that would be invariant in `T`, and we want covariance.
    ptr: WithOpaqueHeader,
    _marker: PhantomData<T>,
}

/// `ThinBox<T>` is `Send` if `T` is `Send` because the data is owned.
#[unstable(feature = "thin_box", issue = "92791")]
unsafe impl<T: ?Sized + Send> Send for ThinBox<T> {}

/// `ThinBox<T>` is `Sync` if `T` is `Sync` because the data is owned.
#[unstable(feature = "thin_box", issue = "92791")]
unsafe impl<T: ?Sized + Sync> Sync for ThinBox<T> {}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T> ThinBox<T> {
    /// Moves a type to the heap with its [`Metadata`] stored in the heap allocation instead of on
    /// the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(thin_box)]
    /// use std::boxed::ThinBox;
    ///
    /// let five = ThinBox::new(5);
    /// ```
    ///
    /// [`Metadata`]: core::ptr::Pointee::Metadata
    #[cfg(not(no_global_oom_handling))]
    pub fn new(value: T) -> Self {
        let meta = ptr::metadata(&value);
        let ptr = WithOpaqueHeader::new(meta, value);
        ThinBox { ptr, _marker: PhantomData }
    }

    /// Moves a type to the heap with its [`Metadata`] stored in the heap allocation instead of on
    /// the stack. Returns an error if allocation fails, instead of aborting.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    /// #![feature(thin_box)]
    /// use std::boxed::ThinBox;
    ///
    /// let five = ThinBox::try_new(5)?;
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [`Metadata`]: core::ptr::Pointee::Metadata
    pub fn try_new(value: T) -> Result<Self, core::alloc::AllocError> {
        let meta = ptr::metadata(&value);
        WithOpaqueHeader::try_new(meta, value).map(|ptr| ThinBox { ptr, _marker: PhantomData })
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<Dyn: ?Sized> ThinBox<Dyn> {
    /// Moves a type to the heap with its [`Metadata`] stored in the heap allocation instead of on
    /// the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(thin_box)]
    /// use std::boxed::ThinBox;
    ///
    /// let thin_slice = ThinBox::<[i32]>::new_unsize([1, 2, 3, 4]);
    /// ```
    ///
    /// [`Metadata`]: core::ptr::Pointee::Metadata
    #[cfg(not(no_global_oom_handling))]
    pub fn new_unsize<T>(value: T) -> Self
    where
        T: Unsize<Dyn>,
    {
        if size_of::<T>() == 0 {
            let ptr = WithOpaqueHeader::new_unsize_zst::<Dyn, T>(value);
            ThinBox { ptr, _marker: PhantomData }
        } else {
            let meta = ptr::metadata(&value as &Dyn);
            let ptr = WithOpaqueHeader::new(meta, value);
            ThinBox { ptr, _marker: PhantomData }
        }
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T: ?Sized + Debug> Debug for ThinBox<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.deref(), f)
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T: ?Sized + Display> Display for ThinBox<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.deref(), f)
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T: ?Sized> Deref for ThinBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        let value = self.data();
        let metadata = self.meta();
        let pointer = ptr::from_raw_parts(value as *const (), metadata);
        unsafe { &*pointer }
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T: ?Sized> DerefMut for ThinBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        let value = self.data();
        let metadata = self.meta();
        let pointer = ptr::from_raw_parts_mut::<T>(value as *mut (), metadata);
        unsafe { &mut *pointer }
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T: ?Sized> Drop for ThinBox<T> {
    fn drop(&mut self) {
        unsafe {
            let value = self.deref_mut();
            let value = value as *mut T;
            self.with_header().drop::<T>(value);
        }
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T: ?Sized> ThinBox<T> {
    fn meta(&self) -> <T as Pointee>::Metadata {
        //  Safety:
        //  -   NonNull and valid.
        unsafe { *self.with_header().header() }
    }

    fn data(&self) -> *mut u8 {
        self.with_header().value()
    }

    fn with_header(&self) -> &WithHeader<<T as Pointee>::Metadata> {
        // SAFETY: both types are transparent to `NonNull<u8>`
        unsafe { &*((&raw const self.ptr) as *const WithHeader<_>) }
    }
}

/// A pointer to type-erased data, guaranteed to either be:
/// 1. `NonNull::dangling()`, in the case where both the pointee (`T`) and
///    metadata (`H`) are ZSTs.
/// 2. A pointer to a valid `T` that has a header `H` directly before the
///    pointed-to location.
#[repr(transparent)]
struct WithHeader<H>(NonNull<u8>, PhantomData<H>);

/// An opaque representation of `WithHeader<H>` to avoid the
/// projection invariance of `<T as Pointee>::Metadata`.
#[repr(transparent)]
struct WithOpaqueHeader(NonNull<u8>);

impl WithOpaqueHeader {
    #[cfg(not(no_global_oom_handling))]
    fn new<H, T>(header: H, value: T) -> Self {
        let ptr = WithHeader::new(header, value);
        Self(ptr.0)
    }

    #[cfg(not(no_global_oom_handling))]
    fn new_unsize_zst<Dyn, T>(value: T) -> Self
    where
        Dyn: ?Sized,
        T: Unsize<Dyn>,
    {
        let ptr = WithHeader::<<Dyn as Pointee>::Metadata>::new_unsize_zst::<Dyn, T>(value);
        Self(ptr.0)
    }

    fn try_new<H, T>(header: H, value: T) -> Result<Self, core::alloc::AllocError> {
        WithHeader::try_new(header, value).map(|ptr| Self(ptr.0))
    }
}

impl<H> WithHeader<H> {
    #[cfg(not(no_global_oom_handling))]
    fn new<T>(header: H, value: T) -> WithHeader<H> {
        let value_layout = Layout::new::<T>();
        let Ok((layout, value_offset)) = Self::alloc_layout(value_layout) else {
            // We pass an empty layout here because we do not know which layout caused the
            // arithmetic overflow in `Layout::extend` and `handle_alloc_error` takes `Layout` as
            // its argument rather than `Result<Layout, LayoutError>`, also this function has been
            // stable since 1.28 ._.
            //
            // On the other hand, look at this gorgeous turbofish!
            alloc::handle_alloc_error(Layout::new::<()>());
        };

        unsafe {
            // Note: It's UB to pass a layout with a zero size to `alloc::alloc`, so
            // we use `layout.dangling()` for this case, which should have a valid
            // alignment for both `T` and `H`.
            let ptr = if layout.size() == 0 {
                // Some paranoia checking, mostly so that the ThinBox tests are
                // more able to catch issues.
                debug_assert!(value_offset == 0 && T::IS_ZST && H::IS_ZST);
                layout.dangling()
            } else {
                let ptr = alloc::alloc(layout);
                if ptr.is_null() {
                    alloc::handle_alloc_error(layout);
                }
                // Safety:
                // - The size is at least `aligned_header_size`.
                let ptr = ptr.add(value_offset) as *mut _;

                NonNull::new_unchecked(ptr)
            };

            let result = WithHeader(ptr, PhantomData);
            ptr::write(result.header(), header);
            ptr::write(result.value().cast(), value);

            result
        }
    }

    /// Non-panicking version of `new`.
    /// Any error is returned as `Err(core::alloc::AllocError)`.
    fn try_new<T>(header: H, value: T) -> Result<WithHeader<H>, core::alloc::AllocError> {
        let value_layout = Layout::new::<T>();
        let Ok((layout, value_offset)) = Self::alloc_layout(value_layout) else {
            return Err(core::alloc::AllocError);
        };

        unsafe {
            // Note: It's UB to pass a layout with a zero size to `alloc::alloc`, so
            // we use `layout.dangling()` for this case, which should have a valid
            // alignment for both `T` and `H`.
            let ptr = if layout.size() == 0 {
                // Some paranoia checking, mostly so that the ThinBox tests are
                // more able to catch issues.
                debug_assert!(value_offset == 0 && size_of::<T>() == 0 && size_of::<H>() == 0);
                layout.dangling()
            } else {
                let ptr = alloc::alloc(layout);
                if ptr.is_null() {
                    return Err(core::alloc::AllocError);
                }

                // Safety:
                // - The size is at least `aligned_header_size`.
                let ptr = ptr.add(value_offset) as *mut _;

                NonNull::new_unchecked(ptr)
            };

            let result = WithHeader(ptr, PhantomData);
            ptr::write(result.header(), header);
            ptr::write(result.value().cast(), value);

            Ok(result)
        }
    }

    // `Dyn` is `?Sized` type like `[u32]`, and `T` is ZST type like `[u32; 0]`.
    #[cfg(not(no_global_oom_handling))]
    fn new_unsize_zst<Dyn, T>(value: T) -> WithHeader<H>
    where
        Dyn: Pointee<Metadata = H> + ?Sized,
        T: Unsize<Dyn>,
    {
        assert!(size_of::<T>() == 0);

        const fn max(a: usize, b: usize) -> usize {
            if a > b { a } else { b }
        }

        // Compute a pointer to the right metadata. This will point to the beginning
        // of the header, past the padding, so the assigned type makes sense.
        // It also ensures that the address at the end of the header is sufficiently
        // aligned for T.
        let alloc: &<Dyn as Pointee>::Metadata = const {
            // FIXME: just call `WithHeader::alloc_layout` with size reset to 0.
            // Currently that's blocked on `Layout::extend` not being `const fn`.

            let alloc_align = max(align_of::<T>(), align_of::<<Dyn as Pointee>::Metadata>());

            let alloc_size = max(align_of::<T>(), size_of::<<Dyn as Pointee>::Metadata>());

            unsafe {
                // SAFETY: align is power of two because it is the maximum of two alignments.
                let alloc: *mut u8 = const_allocate(alloc_size, alloc_align);

                let metadata_offset =
                    alloc_size.checked_sub(size_of::<<Dyn as Pointee>::Metadata>()).unwrap();
                // SAFETY: adding offset within the allocation.
                let metadata_ptr: *mut <Dyn as Pointee>::Metadata =
                    alloc.add(metadata_offset).cast();
                // SAFETY: `*metadata_ptr` is within the allocation.
                metadata_ptr.write(ptr::metadata::<Dyn>(ptr::dangling::<T>() as *const Dyn));
                // SAFETY: valid heap allocation
                const_make_global(alloc);
                // SAFETY: we have just written the metadata.
                &*metadata_ptr
            }
        };

        // SAFETY: `alloc` points to `<Dyn as Pointee>::Metadata`, so addition stays in-bounds.
        let value_ptr =
            unsafe { (alloc as *const <Dyn as Pointee>::Metadata).add(1) }.cast::<T>().cast_mut();
        debug_assert!(value_ptr.is_aligned());
        mem::forget(value);
        WithHeader(NonNull::new(value_ptr.cast()).unwrap(), PhantomData)
    }

    // Safety:
    // - Assumes that either `value` can be dereferenced, or is the
    //   `NonNull::dangling()` we use when both `T` and `H` are ZSTs.
    unsafe fn drop<T: ?Sized>(&self, value: *mut T) {
        struct DropGuard<H> {
            ptr: NonNull<u8>,
            value_layout: Layout,
            _marker: PhantomData<H>,
        }

        impl<H> Drop for DropGuard<H> {
            fn drop(&mut self) {
                // All ZST are allocated statically.
                if self.value_layout.size() == 0 {
                    return;
                }

                unsafe {
                    // SAFETY: Layout must have been computable if we're in drop
                    let (layout, value_offset) =
                        WithHeader::<H>::alloc_layout(self.value_layout).unwrap_unchecked();

                    // Since we only allocate for non-ZSTs, the layout size cannot be zero.
                    debug_assert!(layout.size() != 0);
                    alloc::dealloc(self.ptr.as_ptr().sub(value_offset), layout);
                }
            }
        }

        unsafe {
            // `_guard` will deallocate the memory when dropped, even if `drop_in_place` unwinds.
            let _guard = DropGuard {
                ptr: self.0,
                value_layout: Layout::for_value_raw(value),
                _marker: PhantomData::<H>,
            };

            // We only drop the value because the Pointee trait requires that the metadata is copy
            // aka trivially droppable.
            ptr::drop_in_place::<T>(value);
        }
    }

    fn header(&self) -> *mut H {
        //  Safety:
        //  - At least `size_of::<H>()` bytes are allocated ahead of the pointer.
        //  - We know that H will be aligned because the middle pointer is aligned to the greater
        //    of the alignment of the header and the data and the header size includes the padding
        //    needed to align the header. Subtracting the header size from the aligned data pointer
        //    will always result in an aligned header pointer, it just may not point to the
        //    beginning of the allocation.
        let hp = unsafe { self.0.as_ptr().sub(Self::header_size()) as *mut H };
        debug_assert!(hp.is_aligned());
        hp
    }

    fn value(&self) -> *mut u8 {
        self.0.as_ptr()
    }

    const fn header_size() -> usize {
        size_of::<H>()
    }

    fn alloc_layout(value_layout: Layout) -> Result<(Layout, usize), LayoutError> {
        Layout::new::<H>().extend(value_layout)
    }
}

#[unstable(feature = "thin_box", issue = "92791")]
impl<T: ?Sized + Error> Error for ThinBox<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.deref().source()
    }
}

// ==============================================================
// Challenge 29: Verify safety of Boxed functions harnesses
// ==============================================================

// === SAFE FUNCTIONS ===

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::any::Any;

    use super::*;

    macro_rules! gen_thinbox_deref_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Move that value into a `ThinBox` using the sized constructor.
                let thin: ThinBox<$ty> = ThinBox::new(value);

                // Dereference the thin box through the `Deref` implementation.
                let _: &$ty = core::ops::Deref::deref(&thin);
            }
        };
    }

    macro_rules! gen_thinbox_deref_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be unsized into `dyn Any`.
                let value: $src_ty = kani::any();

                // Build a thin box whose pointee metadata is trait-object metadata.
                let thin: ThinBox<dyn Any> = ThinBox::<dyn Any>::new_unsize(value);

                // Dereference the thin box through the `Deref` implementation.
                let _: &dyn Any = core::ops::Deref::deref(&thin);
            }
        };
    }

    macro_rules! gen_thinbox_deref_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be unsized into a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Build a thin box whose pointee metadata is slice length metadata.
                let thin: ThinBox<[$elem]> = ThinBox::<[$elem]>::new_unsize(value);

                // Dereference the thin box through the `Deref` implementation.
                let _: &[$elem] = core::ops::Deref::deref(&thin);
            }
        };
    }

    gen_thinbox_deref_harness!(harness_thinbox_deref_i8, i8);
    gen_thinbox_deref_harness!(harness_thinbox_deref_i16, i16);
    gen_thinbox_deref_harness!(harness_thinbox_deref_i32, i32);
    gen_thinbox_deref_harness!(harness_thinbox_deref_i64, i64);
    gen_thinbox_deref_harness!(harness_thinbox_deref_i128, i128);
    gen_thinbox_deref_harness!(harness_thinbox_deref_u8, u8);
    gen_thinbox_deref_harness!(harness_thinbox_deref_u16, u16);
    gen_thinbox_deref_harness!(harness_thinbox_deref_u32, u32);
    gen_thinbox_deref_harness!(harness_thinbox_deref_u64, u64);
    gen_thinbox_deref_harness!(harness_thinbox_deref_u128, u128);
    gen_thinbox_deref_harness!(harness_thinbox_deref_bool, bool);
    gen_thinbox_deref_harness!(harness_thinbox_deref_unit, ());
    gen_thinbox_deref_harness!(harness_thinbox_deref_array, [u8; 4]);
    gen_thinbox_deref_dyn_any_harness!(harness_thinbox_deref_dyn_any, i32);

    gen_thinbox_deref_slice_harness!(harness_thinbox_deref_slice_u8, u8);
    gen_thinbox_deref_slice_harness!(harness_thinbox_deref_slice_u16, u16);
    gen_thinbox_deref_slice_harness!(harness_thinbox_deref_slice_u32, u32);
    gen_thinbox_deref_slice_harness!(harness_thinbox_deref_slice_u64, u64);
    gen_thinbox_deref_slice_harness!(harness_thinbox_deref_slice_u128, u128);

    macro_rules! gen_thinbox_deref_mut_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Move that value into a mutable `ThinBox` using the sized constructor.
                let mut thin: ThinBox<$ty> = ThinBox::new(value);

                // Mutably dereference the thin box through the `DerefMut` implementation.
                let _: &mut $ty = core::ops::DerefMut::deref_mut(&mut thin);
            }
        };
    }

    macro_rules! gen_thinbox_deref_mut_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be unsized into `dyn Any`.
                let value: $src_ty = kani::any();

                // Build a mutable thin box whose pointee metadata is trait-object metadata.
                let mut thin: ThinBox<dyn Any> = ThinBox::<dyn Any>::new_unsize(value);

                // Mutably dereference the thin box through the `DerefMut` implementation.
                let _: &mut dyn Any = core::ops::DerefMut::deref_mut(&mut thin);
            }
        };
    }

    macro_rules! gen_thinbox_deref_mut_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be unsized into a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Build a mutable thin box whose pointee metadata is slice length metadata.
                let mut thin: ThinBox<[$elem]> = ThinBox::<[$elem]>::new_unsize(value);

                // Mutably dereference the thin box through the `DerefMut` implementation.
                let _: &mut [$elem] = core::ops::DerefMut::deref_mut(&mut thin);
            }
        };
    }

    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_i8, i8);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_i16, i16);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_i32, i32);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_i64, i64);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_i128, i128);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_u8, u8);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_u16, u16);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_u32, u32);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_u64, u64);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_u128, u128);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_bool, bool);
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_unit, ());
    gen_thinbox_deref_mut_harness!(harness_thinbox_deref_mut_array, [u8; 4]);
    gen_thinbox_deref_mut_dyn_any_harness!(harness_thinbox_deref_mut_dyn_any, i32);

    gen_thinbox_deref_mut_slice_harness!(harness_thinbox_deref_mut_slice_u8, u8);
    gen_thinbox_deref_mut_slice_harness!(harness_thinbox_deref_mut_slice_u16, u16);
    gen_thinbox_deref_mut_slice_harness!(harness_thinbox_deref_mut_slice_u32, u32);
    gen_thinbox_deref_mut_slice_harness!(harness_thinbox_deref_mut_slice_u64, u64);
    gen_thinbox_deref_mut_slice_harness!(harness_thinbox_deref_mut_slice_u128, u128);

    macro_rules! gen_thinbox_drop_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Move that value into a `ThinBox` using the sized constructor.
                let thin: ThinBox<$ty> = ThinBox::new(value);

                // Drop the thin box through the normal safe surface.
                core::mem::drop(thin);
            }
        };
    }

    macro_rules! gen_thinbox_drop_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be unsized into `dyn Any`.
                let value: $src_ty = kani::any();

                // Build a thin box whose pointee metadata is trait-object metadata.
                let thin: ThinBox<dyn Any> = ThinBox::<dyn Any>::new_unsize(value);

                // Drop the thin box through the normal safe surface.
                core::mem::drop(thin);
            }
        };
    }

    macro_rules! gen_thinbox_drop_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be unsized into a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Build a thin box whose pointee metadata is slice length metadata.
                let thin: ThinBox<[$elem]> = ThinBox::<[$elem]>::new_unsize(value);

                // Drop the thin box through the normal safe surface.
                core::mem::drop(thin);
            }
        };
    }

    gen_thinbox_drop_harness!(harness_thinbox_drop_i8, i8);
    gen_thinbox_drop_harness!(harness_thinbox_drop_i16, i16);
    gen_thinbox_drop_harness!(harness_thinbox_drop_i32, i32);
    gen_thinbox_drop_harness!(harness_thinbox_drop_i64, i64);
    gen_thinbox_drop_harness!(harness_thinbox_drop_i128, i128);
    gen_thinbox_drop_harness!(harness_thinbox_drop_u8, u8);
    gen_thinbox_drop_harness!(harness_thinbox_drop_u16, u16);
    gen_thinbox_drop_harness!(harness_thinbox_drop_u32, u32);
    gen_thinbox_drop_harness!(harness_thinbox_drop_u64, u64);
    gen_thinbox_drop_harness!(harness_thinbox_drop_u128, u128);
    gen_thinbox_drop_harness!(harness_thinbox_drop_bool, bool);
    gen_thinbox_drop_harness!(harness_thinbox_drop_unit, ());
    gen_thinbox_drop_harness!(harness_thinbox_drop_array, [u8; 4]);
    gen_thinbox_drop_dyn_any_harness!(harness_thinbox_drop_dyn_any, i32);

    gen_thinbox_drop_slice_harness!(harness_thinbox_drop_slice_u8, u8);
    gen_thinbox_drop_slice_harness!(harness_thinbox_drop_slice_u16, u16);
    gen_thinbox_drop_slice_harness!(harness_thinbox_drop_slice_u32, u32);
    gen_thinbox_drop_slice_harness!(harness_thinbox_drop_slice_u64, u64);
    gen_thinbox_drop_slice_harness!(harness_thinbox_drop_slice_u128, u128);

    macro_rules! gen_thinbox_meta_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Move that value into a `ThinBox` using the sized constructor.
                let thin: ThinBox<$ty> = ThinBox::new(value);

                // Read the metadata stored in the thin box header.
                let _metadata: <$ty as Pointee>::Metadata = thin.meta();
            }
        };
    }

    macro_rules! gen_thinbox_meta_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be unsized into `dyn Any`.
                let value: $src_ty = kani::any();

                // Build a thin box whose pointee metadata is trait-object metadata.
                let thin: ThinBox<dyn Any> = ThinBox::<dyn Any>::new_unsize(value);

                // Read the trait-object metadata stored in the thin box header.
                let _metadata: <dyn Any as Pointee>::Metadata = thin.meta();
            }
        };
    }

    macro_rules! gen_thinbox_meta_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be unsized into a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Build a thin box whose pointee metadata is slice length metadata.
                let thin: ThinBox<[$elem]> = ThinBox::<[$elem]>::new_unsize(value);

                // Read the slice metadata stored in the thin box header.
                let _metadata: <[$elem] as Pointee>::Metadata = thin.meta();
            }
        };
    }

    gen_thinbox_meta_harness!(harness_thinbox_meta_i8, i8);
    gen_thinbox_meta_harness!(harness_thinbox_meta_i16, i16);
    gen_thinbox_meta_harness!(harness_thinbox_meta_i32, i32);
    gen_thinbox_meta_harness!(harness_thinbox_meta_i64, i64);
    gen_thinbox_meta_harness!(harness_thinbox_meta_i128, i128);
    gen_thinbox_meta_harness!(harness_thinbox_meta_u8, u8);
    gen_thinbox_meta_harness!(harness_thinbox_meta_u16, u16);
    gen_thinbox_meta_harness!(harness_thinbox_meta_u32, u32);
    gen_thinbox_meta_harness!(harness_thinbox_meta_u64, u64);
    gen_thinbox_meta_harness!(harness_thinbox_meta_u128, u128);
    gen_thinbox_meta_harness!(harness_thinbox_meta_bool, bool);
    gen_thinbox_meta_harness!(harness_thinbox_meta_unit, ());
    gen_thinbox_meta_harness!(harness_thinbox_meta_array, [u8; 4]);
    gen_thinbox_meta_dyn_any_harness!(harness_thinbox_meta_dyn_any, i32);

    gen_thinbox_meta_slice_harness!(harness_thinbox_meta_slice_u8, u8);
    gen_thinbox_meta_slice_harness!(harness_thinbox_meta_slice_u16, u16);
    gen_thinbox_meta_slice_harness!(harness_thinbox_meta_slice_u32, u32);
    gen_thinbox_meta_slice_harness!(harness_thinbox_meta_slice_u64, u64);
    gen_thinbox_meta_slice_harness!(harness_thinbox_meta_slice_u128, u128);

    macro_rules! gen_thinbox_with_header_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Move that value into a `ThinBox` using the sized constructor.
                let thin: ThinBox<$ty> = ThinBox::new(value);

                // Recover the typed header view from the opaque thin-box representation.
                let _header = thin.with_header();
            }
        };
    }

    macro_rules! gen_thinbox_with_header_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be unsized into `dyn Any`.
                let value: $src_ty = kani::any();

                // Build a thin box whose header stores trait-object metadata.
                let thin: ThinBox<dyn Any> = ThinBox::<dyn Any>::new_unsize(value);

                // Recover the typed header view from the opaque thin-box representation.
                let _header = thin.with_header();
            }
        };
    }

    macro_rules! gen_thinbox_with_header_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be unsized into a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Build a thin box whose header stores slice length metadata.
                let thin: ThinBox<[$elem]> = ThinBox::<[$elem]>::new_unsize(value);

                // Recover the typed header view from the opaque thin-box representation.
                let _header = thin.with_header();
            }
        };
    }

    gen_thinbox_with_header_harness!(harness_thinbox_with_header_i8, i8);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_i16, i16);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_i32, i32);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_i64, i64);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_i128, i128);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_u8, u8);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_u16, u16);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_u32, u32);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_u64, u64);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_u128, u128);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_bool, bool);
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_unit, ());
    gen_thinbox_with_header_harness!(harness_thinbox_with_header_array, [u8; 4]);
    gen_thinbox_with_header_dyn_any_harness!(harness_thinbox_with_header_dyn_any, i32);

    gen_thinbox_with_header_slice_harness!(harness_thinbox_with_header_slice_u8, u8);
    gen_thinbox_with_header_slice_harness!(harness_thinbox_with_header_slice_u16, u16);
    gen_thinbox_with_header_slice_harness!(harness_thinbox_with_header_slice_u32, u32);
    gen_thinbox_with_header_slice_harness!(harness_thinbox_with_header_slice_u64, u64);
    gen_thinbox_with_header_slice_harness!(harness_thinbox_with_header_slice_u128, u128);

    macro_rules! gen_with_header_new_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Compute the metadata header that belongs to this sized value.
                let header: <$ty as Pointee>::Metadata = ptr::metadata(&value);

                // Build the raw header/value allocation used by `ThinBox`.
                let with_header: WithHeader<<$ty as Pointee>::Metadata> =
                    WithHeader::new(header, value);

                // Rewrap the raw allocation as a `ThinBox` so normal drop cleans it up.
                let _thin: ThinBox<$ty> =
                    ThinBox { ptr: WithOpaqueHeader(with_header.0), _marker: PhantomData };
            }
        };
    }

    macro_rules! gen_with_header_new_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be represented as `dyn Any`.
                let value: $src_ty = kani::any();

                // Compute the trait-object metadata header for the erased pointee type.
                let header: <dyn Any as Pointee>::Metadata = ptr::metadata(&value as &dyn Any);

                // Build the raw header/value allocation used by `ThinBox<dyn Any>`.
                let with_header: WithHeader<<dyn Any as Pointee>::Metadata> =
                    WithHeader::new(header, value);

                // Rewrap the raw allocation as a `ThinBox<dyn Any>` so normal drop cleans it up.
                let _thin: ThinBox<dyn Any> =
                    ThinBox { ptr: WithOpaqueHeader(with_header.0), _marker: PhantomData };
            }
        };
    }

    macro_rules! gen_with_header_new_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be represented as a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Compute the slice-length metadata header for the unsized pointee type.
                let header: <[$elem] as Pointee>::Metadata = ptr::metadata(&value as &[$elem]);

                // Build the raw header/value allocation used by `ThinBox<[$elem]>`.
                let with_header: WithHeader<<[$elem] as Pointee>::Metadata> =
                    WithHeader::new(header, value);

                // Rewrap the raw allocation as a `ThinBox<[$elem]>` so normal drop cleans it up.
                let _thin: ThinBox<[$elem]> =
                    ThinBox { ptr: WithOpaqueHeader(with_header.0), _marker: PhantomData };
            }
        };
    }

    gen_with_header_new_harness!(harness_with_header_new_i8, i8);
    gen_with_header_new_harness!(harness_with_header_new_i16, i16);
    gen_with_header_new_harness!(harness_with_header_new_i32, i32);
    gen_with_header_new_harness!(harness_with_header_new_i64, i64);
    gen_with_header_new_harness!(harness_with_header_new_i128, i128);
    gen_with_header_new_harness!(harness_with_header_new_u8, u8);
    gen_with_header_new_harness!(harness_with_header_new_u16, u16);
    gen_with_header_new_harness!(harness_with_header_new_u32, u32);
    gen_with_header_new_harness!(harness_with_header_new_u64, u64);
    gen_with_header_new_harness!(harness_with_header_new_u128, u128);
    gen_with_header_new_harness!(harness_with_header_new_bool, bool);
    gen_with_header_new_harness!(harness_with_header_new_unit, ());
    gen_with_header_new_harness!(harness_with_header_new_array, [u8; 4]);
    gen_with_header_new_dyn_any_harness!(harness_with_header_new_dyn_any, i32);

    gen_with_header_new_slice_harness!(harness_with_header_new_slice_u8, u8);
    gen_with_header_new_slice_harness!(harness_with_header_new_slice_u16, u16);
    gen_with_header_new_slice_harness!(harness_with_header_new_slice_u32, u32);
    gen_with_header_new_slice_harness!(harness_with_header_new_slice_u64, u64);
    gen_with_header_new_slice_harness!(harness_with_header_new_slice_u128, u128);

    macro_rules! gen_with_header_try_new_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Compute the metadata header that belongs to this sized value.
                let header: <$ty as Pointee>::Metadata = ptr::metadata(&value);

                // Build the fallible raw header/value allocation used by `ThinBox`.
                let result: Result<
                    WithHeader<<$ty as Pointee>::Metadata>,
                    core::alloc::AllocError,
                > = WithHeader::try_new(header, value);

                // Rewrap successful allocations as `ThinBox` so normal drop cleans them up.
                let _result: Result<ThinBox<$ty>, core::alloc::AllocError> =
                    result.map(|with_header| ThinBox {
                        ptr: WithOpaqueHeader(with_header.0),
                        _marker: PhantomData,
                    });
            }
        };
    }

    macro_rules! gen_with_header_try_new_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be represented as `dyn Any`.
                let value: $src_ty = kani::any();

                // Compute the trait-object metadata header for the erased pointee type.
                let header: <dyn Any as Pointee>::Metadata = ptr::metadata(&value as &dyn Any);

                // Build the fallible raw header/value allocation used by `ThinBox<dyn Any>`.
                let result: Result<
                    WithHeader<<dyn Any as Pointee>::Metadata>,
                    core::alloc::AllocError,
                > = WithHeader::try_new(header, value);

                // Rewrap successful allocations as `ThinBox<dyn Any>` so normal drop cleans them up.
                let _result: Result<ThinBox<dyn Any>, core::alloc::AllocError> =
                    result.map(|with_header| ThinBox {
                        ptr: WithOpaqueHeader(with_header.0),
                        _marker: PhantomData,
                    });
            }
        };
    }

    macro_rules! gen_with_header_try_new_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be represented as a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Compute the slice-length metadata header for the unsized pointee type.
                let header: <[$elem] as Pointee>::Metadata = ptr::metadata(&value as &[$elem]);

                // Build the fallible raw header/value allocation used by `ThinBox<[$elem]>`.
                let result: Result<
                    WithHeader<<[$elem] as Pointee>::Metadata>,
                    core::alloc::AllocError,
                > = WithHeader::try_new(header, value);

                // Rewrap successful allocations as `ThinBox<[$elem]>` so normal drop cleans them up.
                let _result: Result<ThinBox<[$elem]>, core::alloc::AllocError> =
                    result.map(|with_header| ThinBox {
                        ptr: WithOpaqueHeader(with_header.0),
                        _marker: PhantomData,
                    });
            }
        };
    }

    gen_with_header_try_new_harness!(harness_with_header_try_new_i8, i8);
    gen_with_header_try_new_harness!(harness_with_header_try_new_i16, i16);
    gen_with_header_try_new_harness!(harness_with_header_try_new_i32, i32);
    gen_with_header_try_new_harness!(harness_with_header_try_new_i64, i64);
    gen_with_header_try_new_harness!(harness_with_header_try_new_i128, i128);
    gen_with_header_try_new_harness!(harness_with_header_try_new_u8, u8);
    gen_with_header_try_new_harness!(harness_with_header_try_new_u16, u16);
    gen_with_header_try_new_harness!(harness_with_header_try_new_u32, u32);
    gen_with_header_try_new_harness!(harness_with_header_try_new_u64, u64);
    gen_with_header_try_new_harness!(harness_with_header_try_new_u128, u128);
    gen_with_header_try_new_harness!(harness_with_header_try_new_bool, bool);
    gen_with_header_try_new_harness!(harness_with_header_try_new_unit, ());
    gen_with_header_try_new_harness!(harness_with_header_try_new_array, [u8; 4]);
    gen_with_header_try_new_dyn_any_harness!(harness_with_header_try_new_dyn_any, i32);

    gen_with_header_try_new_slice_harness!(harness_with_header_try_new_slice_u8, u8);
    gen_with_header_try_new_slice_harness!(harness_with_header_try_new_slice_u16, u16);
    gen_with_header_try_new_slice_harness!(harness_with_header_try_new_slice_u32, u32);
    gen_with_header_try_new_slice_harness!(harness_with_header_try_new_slice_u64, u64);
    gen_with_header_try_new_slice_harness!(harness_with_header_try_new_slice_u128, u128);
    // `WithHeader<H>::new_unsize_zst<Dyn, T>` is the special constructor used
    // when a zero-sized source `T` is unsized into some `Dyn`.
    macro_rules! gen_with_header_new_unsize_zst_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a zero-length array that can be unsized into a slice.
                let value: [$elem; 0] = [];

                // Build the special ZST-unsizing header/value representation.
                let _with_header: WithHeader<<[$elem] as Pointee>::Metadata> =
                    WithHeader::new_unsize_zst::<[$elem], [$elem; 0]>(value);
            }
        };
    }

    macro_rules! gen_with_header_new_unsize_zst_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a zero-sized concrete value that can be unsized into `dyn Any`.
                let value: $src_ty = <$src_ty>::default();

                // Build the special ZST-unsizing header/value representation.
                let _with_header: WithHeader<<dyn Any as Pointee>::Metadata> =
                    WithHeader::new_unsize_zst::<dyn Any, $src_ty>(value);
            }
        };
    }

    gen_with_header_new_unsize_zst_slice_harness!(harness_with_header_new_unsize_zst_slice_u8, u8);
    gen_with_header_new_unsize_zst_slice_harness!(
        harness_with_header_new_unsize_zst_slice_u16,
        u16
    );
    gen_with_header_new_unsize_zst_slice_harness!(
        harness_with_header_new_unsize_zst_slice_u32,
        u32
    );
    gen_with_header_new_unsize_zst_slice_harness!(
        harness_with_header_new_unsize_zst_slice_u64,
        u64
    );
    // Kani currently cannot prove the alignment returned by `const_allocate`
    // for a ZST slice source whose alignment is stricter than pointer-sized
    // metadata, such as `[u128; 0] -> [u128]`. The implementation computes a
    // correctly aligned value address, but the verifier loses that fact across
    // the const allocation model and reports `value_ptr.is_aligned()` as
    // possibly false.
    gen_with_header_new_unsize_zst_dyn_any_harness!(harness_with_header_new_unsize_zst_dyn_any, ());

    macro_rules! gen_with_header_header_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the requested sized type.
                let value: $ty = kani::any();

                // Compute the metadata header that belongs to this sized value.
                let header: <$ty as Pointee>::Metadata = ptr::metadata(&value);

                // Build the raw header/value allocation used by `ThinBox`.
                let with_header: WithHeader<<$ty as Pointee>::Metadata> =
                    WithHeader::new(header, value);

                // Recover the header pointer from the stored value pointer.
                let _header_ptr: *mut <$ty as Pointee>::Metadata = with_header.header();

                // Rewrap the raw allocation as a `ThinBox` so normal drop cleans it up.
                let _thin: ThinBox<$ty> =
                    ThinBox { ptr: WithOpaqueHeader(with_header.0), _marker: PhantomData };
            }
        };
    }

    macro_rules! gen_with_header_header_dyn_any_harness {
        ($name:ident, $src_ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value that will be represented as `dyn Any`.
                let value: $src_ty = kani::any();

                // Compute the trait-object metadata header for the erased pointee type.
                let header: <dyn Any as Pointee>::Metadata = ptr::metadata(&value as &dyn Any);

                // Build the raw header/value allocation used by `ThinBox<dyn Any>`.
                let with_header: WithHeader<<dyn Any as Pointee>::Metadata> =
                    WithHeader::new(header, value);

                // Recover the header pointer from the stored value pointer.
                let _header_ptr: *mut <dyn Any as Pointee>::Metadata = with_header.header();

                // Rewrap the raw allocation as a `ThinBox<dyn Any>` so normal drop cleans it up.
                let _thin: ThinBox<dyn Any> =
                    ThinBox { ptr: WithOpaqueHeader(with_header.0), _marker: PhantomData };
            }
        };
    }

    macro_rules! gen_with_header_header_slice_harness {
        ($name:ident, $elem:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a non-empty array that will be represented as a slice.
                let value: [$elem; 4] = [kani::any::<$elem>(); 4];

                // Compute the slice-length metadata header for the unsized pointee type.
                let header: <[$elem] as Pointee>::Metadata = ptr::metadata(&value as &[$elem]);

                // Build the raw header/value allocation used by `ThinBox<[$elem]>`.
                let with_header: WithHeader<<[$elem] as Pointee>::Metadata> =
                    WithHeader::new(header, value);

                // Recover the header pointer from the stored value pointer.
                let _header_ptr: *mut <[$elem] as Pointee>::Metadata = with_header.header();

                // Rewrap the raw allocation as a `ThinBox<[$elem]>` so normal drop cleans it up.
                let _thin: ThinBox<[$elem]> =
                    ThinBox { ptr: WithOpaqueHeader(with_header.0), _marker: PhantomData };
            }
        };
    }

    gen_with_header_header_harness!(harness_with_header_header_i8, i8);
    gen_with_header_header_harness!(harness_with_header_header_i16, i16);
    gen_with_header_header_harness!(harness_with_header_header_i32, i32);
    gen_with_header_header_harness!(harness_with_header_header_i64, i64);
    gen_with_header_header_harness!(harness_with_header_header_i128, i128);
    gen_with_header_header_harness!(harness_with_header_header_u8, u8);
    gen_with_header_header_harness!(harness_with_header_header_u16, u16);
    gen_with_header_header_harness!(harness_with_header_header_u32, u32);
    gen_with_header_header_harness!(harness_with_header_header_u64, u64);
    gen_with_header_header_harness!(harness_with_header_header_u128, u128);
    gen_with_header_header_harness!(harness_with_header_header_bool, bool);
    gen_with_header_header_harness!(harness_with_header_header_unit, ());
    gen_with_header_header_harness!(harness_with_header_header_array, [u8; 4]);
    gen_with_header_header_dyn_any_harness!(harness_with_header_header_dyn_any, i32);

    gen_with_header_header_slice_harness!(harness_with_header_header_slice_u8, u8);
    gen_with_header_header_slice_harness!(harness_with_header_header_slice_u16, u16);
    gen_with_header_header_slice_harness!(harness_with_header_header_slice_u32, u32);
    gen_with_header_header_slice_harness!(harness_with_header_header_slice_u64, u64);
    gen_with_header_header_slice_harness!(harness_with_header_header_slice_u128, u128);
}
