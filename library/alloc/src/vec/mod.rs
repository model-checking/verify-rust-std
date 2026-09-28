//! A contiguous growable array type with heap-allocated contents, written
//! `Vec<T>`.
//!
//! Vectors have *O*(1) indexing, amortized *O*(1) push (to the end) and
//! *O*(1) pop (from the end).
//!
//! Vectors ensure they never allocate more than `isize::MAX` bytes.
//!
//! # Examples
//!
//! You can explicitly create a [`Vec`] with [`Vec::new`]:
//!
//! ```
//! let v: Vec<i32> = Vec::new();
//! ```
//!
//! ...or by using the [`vec!`] macro:
//!
//! ```
//! let v: Vec<i32> = vec![];
//!
//! let v = vec![1, 2, 3, 4, 5];
//!
//! let v = vec![0; 10]; // ten zeroes
//! ```
//!
//! You can [`push`] values onto the end of a vector (which will grow the vector
//! as needed):
//!
//! ```
//! let mut v = vec![1, 2];
//!
//! v.push(3);
//! ```
//!
//! Popping values works in much the same way:
//!
//! ```
//! let mut v = vec![1, 2];
//!
//! let two = v.pop();
//! ```
//!
//! Vectors also support indexing (through the [`Index`] and [`IndexMut`] traits):
//!
//! ```
//! let mut v = vec![1, 2, 3];
//! let three = v[2];
//! v[1] = v[1] + 5;
//! ```
//!
//! # Memory layout
//!
//! When the type is non-zero-sized and the capacity is nonzero, [`Vec`] uses the [`Global`]
//! allocator for its allocation. It is valid to convert both ways between such a [`Vec`] and a raw
//! pointer allocated with the [`Global`] allocator, provided that the [`Layout`] used with the
//! allocator is correct for a sequence of `capacity` elements of the type, and the first `len`
//! values pointed to by the raw pointer are valid. More precisely, a `ptr: *mut T` that has been
//! allocated with the [`Global`] allocator with [`Layout::array::<T>(capacity)`][Layout::array] may
//! be converted into a vec using
//! [`Vec::<T>::from_raw_parts(ptr, len, capacity)`](Vec::from_raw_parts). Conversely, the memory
//! backing a `value: *mut T` obtained from [`Vec::<T>::as_mut_ptr`] may be deallocated using the
//! [`Global`] allocator with the same layout.
//!
//! For zero-sized types (ZSTs), or when the capacity is zero, the `Vec` pointer must be non-null
//! and sufficiently aligned. The recommended way to build a `Vec` of ZSTs if [`vec!`] cannot be
//! used is to use [`ptr::NonNull::dangling`].
//!
//! [`push`]: Vec::push
//! [`ptr::NonNull::dangling`]: NonNull::dangling
//! [`Layout`]: crate::alloc::Layout
//! [Layout::array]: crate::alloc::Layout::array

#![stable(feature = "rust1", since = "1.0.0")]

#[cfg(not(no_global_oom_handling))]
use core::clone::TrivialClone;
#[cfg(not(no_global_oom_handling))]
use core::cmp;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
#[cfg(not(no_global_oom_handling))]
use core::iter;
#[cfg(kani)]
use core::kani;
#[cfg(not(no_global_oom_handling))]
use core::marker::Destruct;
use core::marker::{Freeze, PhantomData};
use core::mem::{self, Assume, ManuallyDrop, MaybeUninit, SizedTypeProperties, TransmuteFrom};
use core::ops::{self, Index, IndexMut, Range, RangeBounds};
use core::ptr::{self, NonNull};
use core::slice::{self, SliceIndex};
use core::{fmt, hint, intrinsics, ub_checks};

use safety::{ensures, requires};

#[stable(feature = "extract_if", since = "1.87.0")]
pub use self::extract_if::ExtractIf;
use crate::alloc::{Allocator, Global};
use crate::borrow::{Cow, ToOwned};
use crate::boxed::Box;
use crate::collections::TryReserveError;
use crate::raw_vec::RawVec;

mod extract_if;

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "vec_splice", since = "1.21.0")]
pub use self::splice::Splice;

#[cfg(not(no_global_oom_handling))]
mod splice;

#[stable(feature = "drain", since = "1.6.0")]
pub use self::drain::Drain;

mod drain;

#[cfg(not(no_global_oom_handling))]
mod cow;

#[cfg(not(no_global_oom_handling))]
pub(crate) use self::in_place_collect::AsVecIntoIter;
#[stable(feature = "rust1", since = "1.0.0")]
pub use self::into_iter::IntoIter;

mod into_iter;

#[cfg(not(no_global_oom_handling))]
use self::is_zero::IsZero;

#[cfg(not(no_global_oom_handling))]
mod is_zero;

#[cfg(not(no_global_oom_handling))]
mod in_place_collect;

mod partial_eq;

#[unstable(feature = "vec_peek_mut", issue = "122742")]
pub use self::peek_mut::PeekMut;

mod peek_mut;

#[cfg(not(no_global_oom_handling))]
use self::spec_from_elem::SpecFromElem;

#[cfg(not(no_global_oom_handling))]
mod spec_from_elem;

#[cfg(not(no_global_oom_handling))]
use self::set_len_on_drop::SetLenOnDrop;

#[cfg(not(no_global_oom_handling))]
mod set_len_on_drop;

#[cfg(not(no_global_oom_handling))]
use self::in_place_drop::{InPlaceDrop, InPlaceDstDataSrcBufDrop};

#[cfg(not(no_global_oom_handling))]
mod in_place_drop;

#[cfg(not(no_global_oom_handling))]
use self::spec_from_iter_nested::SpecFromIterNested;

#[cfg(not(no_global_oom_handling))]
mod spec_from_iter_nested;

#[cfg(not(no_global_oom_handling))]
use self::spec_from_iter::SpecFromIter;

#[cfg(not(no_global_oom_handling))]
mod spec_from_iter;

#[cfg(not(no_global_oom_handling))]
use self::spec_extend::SpecExtend;

#[cfg(not(no_global_oom_handling))]
mod spec_extend;

/// A contiguous growable array type, written as `Vec<T>`, short for 'vector'.
///
/// # Examples
///
/// ```
/// let mut vec = Vec::new();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
///
/// vec.extend([1, 2, 3]);
///
/// for x in &vec {
///     println!("{x}");
/// }
/// assert_eq!(vec, [7, 1, 2, 3]);
/// ```
///
/// The [`vec!`] macro is provided for convenient initialization:
///
/// ```
/// let mut vec1 = vec![1, 2, 3];
/// vec1.push(4);
/// let vec2 = Vec::from([1, 2, 3, 4]);
/// assert_eq!(vec1, vec2);
/// ```
///
/// It can also initialize each element of a `Vec<T>` with a given value.
/// This may be more efficient than performing allocation and initialization
/// in separate steps, especially when initializing a vector of zeros:
///
/// ```
/// let vec = vec![0; 5];
/// assert_eq!(vec, [0, 0, 0, 0, 0]);
///
/// // The following is equivalent, but potentially slower:
/// let mut vec = Vec::with_capacity(5);
/// vec.resize(5, 0);
/// assert_eq!(vec, [0, 0, 0, 0, 0]);
/// ```
///
/// For more information, see
/// [Capacity and Reallocation](#capacity-and-reallocation).
///
/// Use a `Vec<T>` as an efficient stack:
///
/// ```
/// let mut stack = Vec::new();
///
/// stack.push(1);
/// stack.push(2);
/// stack.push(3);
///
/// while let Some(top) = stack.pop() {
///     // Prints 3, 2, 1
///     println!("{top}");
/// }
/// ```
///
/// # Indexing
///
/// The `Vec` type allows access to values by index, because it implements the
/// [`Index`] trait. An example will be more explicit:
///
/// ```
/// let v = vec![0, 2, 4, 6];
/// println!("{}", v[1]); // it will display '2'
/// ```
///
/// However be careful: if you try to access an index which isn't in the `Vec`,
/// your software will panic! You cannot do this:
///
/// ```should_panic
/// let v = vec![0, 2, 4, 6];
/// println!("{}", v[6]); // it will panic!
/// ```
///
/// Use [`get`] and [`get_mut`] if you want to check whether the index is in
/// the `Vec`.
///
/// # Slicing
///
/// A `Vec` can be mutable. On the other hand, slices are read-only objects.
/// To get a [slice][prim@slice], use [`&`]. Example:
///
/// ```
/// fn read_slice(slice: &[usize]) {
///     // ...
/// }
///
/// let v = vec![0, 1];
/// read_slice(&v);
///
/// // ... and that's all!
/// // you can also do it like this:
/// let u: &[usize] = &v;
/// // or like this:
/// let u: &[_] = &v;
/// ```
///
/// In Rust, it's more common to pass slices as arguments rather than vectors
/// when you just want to provide read access. The same goes for [`String`] and
/// [`&str`].
///
/// # Capacity and reallocation
///
/// The capacity of a vector is the amount of space allocated for any future
/// elements that will be added onto the vector. This is not to be confused with
/// the *length* of a vector, which specifies the number of actual elements
/// within the vector. If a vector's length exceeds its capacity, its capacity
/// will automatically be increased, but its elements will have to be
/// reallocated.
///
/// For example, a vector with capacity 10 and length 0 would be an empty vector
/// with space for 10 more elements. Pushing 10 or fewer elements onto the
/// vector will not change its capacity or cause reallocation to occur. However,
/// if the vector's length is increased to 11, it will have to reallocate, which
/// can be slow. For this reason, it is recommended to use [`Vec::with_capacity`]
/// whenever possible to specify how big the vector is expected to get.
///
/// # Guarantees
///
/// Due to its incredibly fundamental nature, `Vec` makes a lot of guarantees
/// about its design. This ensures that it's as low-overhead as possible in
/// the general case, and can be correctly manipulated in primitive ways
/// by unsafe code. Note that these guarantees refer to an unqualified `Vec<T>`.
/// If additional type parameters are added (e.g., to support custom allocators),
/// overriding their defaults may change the behavior.
///
/// Most fundamentally, `Vec` is and always will be a (pointer, capacity, length)
/// triplet. No more, no less. The order of these fields is completely
/// unspecified, and you should use the appropriate methods to modify these.
/// The pointer will never be null, so this type is null-pointer-optimized.
///
/// However, the pointer might not actually point to allocated memory. In particular,
/// if you construct a `Vec` with capacity 0 via [`Vec::new`], [`vec![]`][`vec!`],
/// [`Vec::with_capacity(0)`][`Vec::with_capacity`], or by calling [`shrink_to_fit`]
/// on an empty Vec, it will not allocate memory. Similarly, if you store zero-sized
/// types inside a `Vec`, it will not allocate space for them. *Note that in this case
/// the `Vec` might not report a [`capacity`] of 0*. `Vec` will allocate if and only
/// if <code>[size_of::\<T>]\() * [capacity]\() > 0</code>. In general, `Vec`'s allocation
/// details are very subtle --- if you intend to allocate memory using a `Vec`
/// and use it for something else (either to pass to unsafe code, or to build your
/// own memory-backed collection), be sure to deallocate this memory by using
/// `from_raw_parts` to recover the `Vec` and then dropping it.
///
/// If a `Vec` *has* allocated memory, then the memory it points to is on the heap
/// (as defined by the allocator Rust is configured to use by default), and its
/// pointer points to [`len`] initialized, contiguous elements in order (what
/// you would see if you coerced it to a slice), followed by <code>[capacity] - [len]</code>
/// logically uninitialized, contiguous elements.
///
/// A vector containing the elements `'a'` and `'b'` with capacity 4 can be
/// visualized as below. The top part is the `Vec` struct, it contains a
/// pointer to the head of the allocation in the heap, length and capacity.
/// The bottom part is the allocation on the heap, a contiguous memory block.
///
/// ```text
///             ptr      len  capacity
///        +--------+--------+--------+
///        | 0x0123 |      2 |      4 |
///        +--------+--------+--------+
///             |
///             v
/// Heap   +--------+--------+--------+--------+
///        |    'a' |    'b' | uninit | uninit |
///        +--------+--------+--------+--------+
/// ```
///
/// - **uninit** represents memory that is not initialized, see [`MaybeUninit`].
/// - Note: the ABI is not stable and `Vec` makes no guarantees about its memory
///   layout (including the order of fields).
///
/// `Vec` will never perform a "small optimization" where elements are actually
/// stored on the stack for two reasons:
///
/// * It would make it more difficult for unsafe code to correctly manipulate
///   a `Vec`. The contents of a `Vec` wouldn't have a stable address if it were
///   only moved, and it would be more difficult to determine if a `Vec` had
///   actually allocated memory.
///
/// * It would penalize the general case, incurring an additional branch
///   on every access.
///
/// `Vec` will never automatically shrink itself, even if completely empty. This
/// ensures no unnecessary allocations or deallocations occur. Emptying a `Vec`
/// and then filling it back up to the same [`len`] should incur no calls to
/// the allocator. If you wish to free up unused memory, use
/// [`shrink_to_fit`] or [`shrink_to`].
///
/// [`push`] and [`insert`] will never (re)allocate if the reported capacity is
/// sufficient. [`push`] and [`insert`] *will* (re)allocate if
/// <code>[len] == [capacity]</code>. That is, the reported capacity is completely
/// accurate, and can be relied on. It can even be used to manually free the memory
/// allocated by a `Vec` if desired. Bulk insertion methods *may* reallocate, even
/// when not necessary.
///
/// `Vec` does not guarantee any particular growth strategy when reallocating
/// when full, nor when [`reserve`] is called. The current strategy is basic
/// and it may prove desirable to use a non-constant growth factor. Whatever
/// strategy is used will of course guarantee *O*(1) amortized [`push`].
///
/// It is guaranteed, in order to respect the intentions of the programmer, that
/// all of `vec![e_1, e_2, ..., e_n]`, `vec![x; n]`, and [`Vec::with_capacity(n)`] produce a `Vec`
/// that requests an allocation of the exact size needed for precisely `n` elements from the allocator,
/// and no other size (such as, for example: a size rounded up to the nearest power of 2).
/// The allocator will return an allocation that is at least as large as requested, but it may be larger.
///
/// It is guaranteed that the [`Vec::capacity`] method returns a value that is at least the requested capacity
/// and not more than the allocated capacity.
///
/// The method [`Vec::shrink_to_fit`] will attempt to discard excess capacity an allocator has given to a `Vec`.
/// If <code>[len] == [capacity]</code>, then a `Vec<T>` can be converted
/// to and from a [`Box<[T]>`][owned slice] without reallocating or moving the elements.
/// `Vec` exploits this fact as much as reasonable when implementing common conversions
/// such as [`into_boxed_slice`].
///
/// `Vec` will not specifically overwrite any data that is removed from it,
/// but also won't specifically preserve it. Its uninitialized memory is
/// scratch space that it may use however it wants. It will generally just do
/// whatever is most efficient or otherwise easy to implement. Do not rely on
/// removed data to be erased for security purposes. Even if you drop a `Vec`, its
/// buffer may simply be reused by another allocation. Even if you zero a `Vec`'s memory
/// first, that might not actually happen because the optimizer does not consider
/// this a side-effect that must be preserved. There is one case which we will
/// not break, however: using `unsafe` code to write to the excess capacity,
/// and then increasing the length to match, is always valid.
///
/// Currently, `Vec` does not guarantee the order in which elements are dropped.
/// The order has changed in the past and may change again.
///
/// [`get`]: slice::get
/// [`get_mut`]: slice::get_mut
/// [`String`]: crate::string::String
/// [`&str`]: type@str
/// [`shrink_to_fit`]: Vec::shrink_to_fit
/// [`shrink_to`]: Vec::shrink_to
/// [capacity]: Vec::capacity
/// [`capacity`]: Vec::capacity
/// [`Vec::capacity`]: Vec::capacity
/// [size_of::\<T>]: size_of
/// [len]: Vec::len
/// [`len`]: Vec::len
/// [`push`]: Vec::push
/// [`insert`]: Vec::insert
/// [`reserve`]: Vec::reserve
/// [`Vec::with_capacity(n)`]: Vec::with_capacity
/// [`MaybeUninit`]: core::mem::MaybeUninit
/// [owned slice]: Box
/// [`into_boxed_slice`]: Vec::into_boxed_slice
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_diagnostic_item = "Vec"]
#[rustc_insignificant_dtor]
#[doc(alias = "list")]
#[doc(alias = "vector")]
pub struct Vec<T, #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global> {
    buf: RawVec<T, A>,
    len: usize,
}

////////////////////////////////////////////////////////////////////////////////
// Inherent methods
////////////////////////////////////////////////////////////////////////////////

impl<T> Vec<T> {
    /// Constructs a new, empty `Vec<T>`.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// let mut vec: Vec<i32> = Vec::new();
    /// ```
    #[inline]
    #[rustc_const_stable(feature = "const_vec_new", since = "1.39.0")]
    #[rustc_diagnostic_item = "vec_new"]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    pub const fn new() -> Self {
        Vec { buf: RawVec::new(), len: 0 }
    }

    /// Constructs a new, empty `Vec<T>` with at least the specified capacity.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the vector will not allocate.
    ///
    /// It is important to note that although the returned vector has the
    /// minimum *capacity* specified, the vector will have a zero *length*. For
    /// an explanation of the difference between length and capacity, see
    /// *[Capacity and reallocation]*.
    ///
    /// If it is important to know the exact allocated capacity of a `Vec`,
    /// always use the [`capacity`] method after construction.
    ///
    /// For `Vec<T>` where `T` is a zero-sized type, there will be no allocation
    /// and the capacity will always be `usize::MAX`.
    ///
    /// [Capacity and reallocation]: #capacity-and-reallocation
    /// [`capacity`]: Vec::capacity
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = Vec::with_capacity(10);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    /// assert_eq!(vec.len(), 10);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // ...but this may make the vector reallocate
    /// vec.push(11);
    /// assert_eq!(vec.len(), 11);
    /// assert!(vec.capacity() >= 11);
    ///
    /// // A vector of a zero-sized type will always over-allocate, since no
    /// // allocation is necessary
    /// let vec_units = Vec::<()>::with_capacity(10);
    /// assert_eq!(vec_units.capacity(), usize::MAX);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    #[rustc_diagnostic_item = "vec_with_capacity"]
    #[rustc_const_unstable(feature = "const_heap", issue = "79597")]
    pub const fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, Global)
    }

    /// Constructs a new, empty `Vec<T>` with at least the specified capacity.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the vector will not allocate.
    ///
    /// # Errors
    ///
    /// Returns an error if the capacity exceeds `isize::MAX` _bytes_,
    /// or if the allocator reports allocation failure.
    #[inline]
    #[unstable(feature = "try_with_capacity", issue = "91913")]
    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        Self::try_with_capacity_in(capacity, Global)
    }

    /// Creates a `Vec<T>` directly from a pointer, a length, and a capacity.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * If `T` is not a zero-sized type and the capacity is nonzero, `ptr` must have
    ///   been allocated using the global allocator, such as via the [`alloc::alloc`]
    ///   function. If `T` is a zero-sized type or the capacity is zero, `ptr` need
    ///   only be non-null and aligned.
    /// * `T` needs to have the same alignment as what `ptr` was allocated with,
    ///   if the pointer is required to be allocated.
    ///   (`T` having a less strict alignment is not sufficient, the alignment really
    ///   needs to be equal to satisfy the [`dealloc`] requirement that memory must be
    ///   allocated and deallocated with the same layout.)
    /// * The size of `T` times the `capacity` (ie. the allocated size in bytes), if
    ///   nonzero, needs to be the same size as the pointer was allocated with.
    ///   (Because similar to alignment, [`dealloc`] must be called with the same
    ///   layout `size`.)
    /// * `length` needs to be less than or equal to `capacity`.
    /// * The first `length` values must be properly initialized values of type `T`.
    /// * `capacity` needs to be the capacity that the pointer was allocated with,
    ///   if the pointer is required to be allocated.
    /// * The allocated size in bytes must be no larger than `isize::MAX`.
    ///   See the safety documentation of [`pointer::offset`].
    ///
    /// These requirements are always upheld by any `ptr` that has been allocated
    /// via `Vec<T>`. Other allocation sources are allowed if the invariants are
    /// upheld.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example it is normally **not** safe
    /// to build a `Vec<u8>` from a pointer to a C `char` array with length
    /// `size_t`, doing so is only safe if the array was initially allocated by
    /// a `Vec` or `String`.
    /// It's also not safe to build one from a `Vec<u16>` and its length, because
    /// the allocator cares about the alignment, and these two types have different
    /// alignments. The buffer was allocated with alignment 2 (for `u16`), but after
    /// turning it into a `Vec<u8>` it'll be deallocated with alignment 1. To avoid
    /// these issues, it is often preferable to do casting/transmuting using
    /// [`slice::from_raw_parts`] instead.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `Vec<T>` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// [`String`]: crate::string::String
    /// [`alloc::alloc`]: crate::alloc::alloc
    /// [`dealloc`]: crate::alloc::GlobalAlloc::dealloc
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr;
    ///
    /// let v = vec![1, 2, 3];
    ///
    /// // Deconstruct the vector into parts.
    /// let (p, len, cap) = v.into_raw_parts();
    ///
    /// unsafe {
    ///     // Overwrite memory with 4, 5, 6
    ///     for i in 0..len {
    ///         ptr::write(p.add(i), 4 + i);
    ///     }
    ///
    ///     // Put everything back together into a Vec
    ///     let rebuilt = Vec::from_raw_parts(p, len, cap);
    ///     assert_eq!(rebuilt, [4, 5, 6]);
    /// }
    /// ```
    ///
    /// Using memory that was allocated elsewhere:
    ///
    /// ```rust
    /// use std::alloc::{alloc, Layout};
    ///
    /// fn main() {
    ///     let layout = Layout::array::<u32>(16).expect("overflow cannot happen");
    ///
    ///     let vec = unsafe {
    ///         let mem = alloc(layout).cast::<u32>();
    ///         if mem.is_null() {
    ///             return;
    ///         }
    ///
    ///         mem.write(1_000_000);
    ///
    ///         Vec::from_raw_parts(mem, 1, 16)
    ///     };
    ///
    ///     assert_eq!(vec, &[1_000_000]);
    ///     assert_eq!(vec.capacity(), 16);
    /// }
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[requires(length <= capacity)]
    #[requires({
        mem::size_of::<T>()
            .checked_mul(capacity)
            .is_some_and(|size| size <= isize::MAX as usize)
    })]
    #[requires(!ptr.is_null() && ptr.is_aligned())]
    #[requires({
        mem::size_of::<T>() == 0
            || capacity == 0
            || ub_checks::can_write(core::ptr::slice_from_raw_parts_mut(ptr, capacity))
    })]
    #[requires({
        mem::size_of::<T>() == 0
            || capacity == 0
            || {
                let end = ptr.wrapping_add(capacity);
                ub_checks::same_allocation(ptr as *const T, end as *const T)
                    && !ub_checks::same_allocation(
                        ptr as *const T,
                        ptr.wrapping_sub(1) as *const T,
                    )
            }
    })]
    // Kani-specific clause: the tool-independent safety predicate API has no
    // equivalent of `kani::mem::is_inbounds`. This distinguishes the exact
    // one-past allocation endpoint from an interior pointer.
    #[cfg_attr(
        kani,
        kani::requires({
            mem::size_of::<T>() == 0
                || capacity == 0
                || !kani::mem::is_inbounds(ptr.wrapping_add(capacity) as *const T)
        })
    )]
    #[requires({
        length == 0
            || ub_checks::can_dereference(core::ptr::slice_from_raw_parts(ptr as *const T, length))
    })]
    pub unsafe fn from_raw_parts(ptr: *mut T, length: usize, capacity: usize) -> Self {
        unsafe { Self::from_raw_parts_in(ptr, length, capacity, Global) }
    }

    #[doc(alias = "from_non_null_parts")]
    /// Creates a `Vec<T>` directly from a `NonNull` pointer, a length, and a capacity.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * `ptr` must have been allocated using the global allocator, such as via
    ///   the [`alloc::alloc`] function.
    /// * `T` needs to have the same alignment as what `ptr` was allocated with.
    ///   (`T` having a less strict alignment is not sufficient, the alignment really
    ///   needs to be equal to satisfy the [`dealloc`] requirement that memory must be
    ///   allocated and deallocated with the same layout.)
    /// * The size of `T` times the `capacity` (ie. the allocated size in bytes) needs
    ///   to be the same size as the pointer was allocated with. (Because similar to
    ///   alignment, [`dealloc`] must be called with the same layout `size`.)
    /// * `length` needs to be less than or equal to `capacity`.
    /// * The first `length` values must be properly initialized values of type `T`.
    /// * `capacity` needs to be the capacity that the pointer was allocated with.
    /// * The allocated size in bytes must be no larger than `isize::MAX`.
    ///   See the safety documentation of [`pointer::offset`].
    ///
    /// These requirements are always upheld by any `ptr` that has been allocated
    /// via `Vec<T>`. Other allocation sources are allowed if the invariants are
    /// upheld.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example it is normally **not** safe
    /// to build a `Vec<u8>` from a pointer to a C `char` array with length
    /// `size_t`, doing so is only safe if the array was initially allocated by
    /// a `Vec` or `String`.
    /// It's also not safe to build one from a `Vec<u16>` and its length, because
    /// the allocator cares about the alignment, and these two types have different
    /// alignments. The buffer was allocated with alignment 2 (for `u16`), but after
    /// turning it into a `Vec<u8>` it'll be deallocated with alignment 1. To avoid
    /// these issues, it is often preferable to do casting/transmuting using
    /// [`NonNull::slice_from_raw_parts`] instead.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `Vec<T>` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// [`String`]: crate::string::String
    /// [`alloc::alloc`]: crate::alloc::alloc
    /// [`dealloc`]: crate::alloc::GlobalAlloc::dealloc
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// let v = vec![1, 2, 3];
    ///
    /// // Deconstruct the vector into parts.
    /// let (p, len, cap) = v.into_parts();
    ///
    /// unsafe {
    ///     // Overwrite memory with 4, 5, 6
    ///     for i in 0..len {
    ///         p.add(i).write(4 + i);
    ///     }
    ///
    ///     // Put everything back together into a Vec
    ///     let rebuilt = Vec::from_parts(p, len, cap);
    ///     assert_eq!(rebuilt, [4, 5, 6]);
    /// }
    /// ```
    ///
    /// Using memory that was allocated elsewhere:
    ///
    /// ```rust
    /// #![feature(box_vec_non_null)]
    ///
    /// use std::alloc::{alloc, Layout};
    /// use std::ptr::NonNull;
    ///
    /// fn main() {
    ///     let layout = Layout::array::<u32>(16).expect("overflow cannot happen");
    ///
    ///     let vec = unsafe {
    ///         let Some(mem) = NonNull::new(alloc(layout).cast::<u32>()) else {
    ///             return;
    ///         };
    ///
    ///         mem.write(1_000_000);
    ///
    ///         Vec::from_parts(mem, 1, 16)
    ///     };
    ///
    ///     assert_eq!(vec, &[1_000_000]);
    ///     assert_eq!(vec.capacity(), 16);
    /// }
    /// ```
    #[inline]
    #[unstable(feature = "box_vec_non_null", issue = "130364")]
    #[requires(length <= capacity)]
    #[requires({
        mem::size_of::<T>()
            .checked_mul(capacity)
            .is_some_and(|size| size <= isize::MAX as usize)
    })]
    #[requires(ptr.as_ptr().is_aligned())]
    #[requires({
        mem::size_of::<T>() == 0
            || capacity == 0
            || ub_checks::can_write(core::ptr::slice_from_raw_parts_mut(ptr.as_ptr(), capacity))
    })]
    #[requires({
        mem::size_of::<T>() == 0
            || capacity == 0
            || {
                let raw_ptr = ptr.as_ptr();
                let end = raw_ptr.wrapping_add(capacity);
                ub_checks::same_allocation(raw_ptr, end)
                    && !ub_checks::same_allocation(raw_ptr, raw_ptr.wrapping_sub(1))
            }
    })]
    // Kani-specific clause: the tool-independent safety predicate API has no
    // equivalent of `kani::mem::is_inbounds`. This distinguishes the exact
    // one-past allocation endpoint from an interior pointer.
    #[cfg_attr(
        kani,
        kani::requires({
            mem::size_of::<T>() == 0
                || capacity == 0
                || {
                    let raw_ptr = ptr.as_ptr();
                    !kani::mem::is_inbounds(raw_ptr.wrapping_add(capacity))
                }
        })
    )]
    #[requires({
        length == 0
            || ub_checks::can_dereference(core::ptr::slice_from_raw_parts(ptr.as_ptr(), length))
    })]
    pub unsafe fn from_parts(ptr: NonNull<T>, length: usize, capacity: usize) -> Self {
        unsafe { Self::from_parts_in(ptr, length, capacity, Global) }
    }

    /// Creates a `Vec<T>` where each element is produced by calling `f` with
    /// that element's index while walking forward through the `Vec<T>`.
    ///
    /// This is essentially the same as writing
    ///
    /// ```text
    /// vec![f(0), f(1), f(2), …, f(length - 2), f(length - 1)]
    /// ```
    /// and is similar to `(0..i).map(f)`, just for `Vec<T>`s not iterators.
    ///
    /// If `length == 0`, this produces an empty `Vec<T>` without ever calling `f`.
    ///
    /// # Example
    ///
    /// ```rust
    /// #![feature(vec_from_fn)]
    ///
    /// let vec = Vec::from_fn(5, |i| i);
    ///
    /// // indexes are:  0  1  2  3  4
    /// assert_eq!(vec, [0, 1, 2, 3, 4]);
    ///
    /// let vec2 = Vec::from_fn(8, |i| i * 2);
    ///
    /// // indexes are:   0  1  2  3  4  5   6   7
    /// assert_eq!(vec2, [0, 2, 4, 6, 8, 10, 12, 14]);
    ///
    /// let bool_vec = Vec::from_fn(5, |i| i % 2 == 0);
    ///
    /// // indexes are:       0     1      2     3      4
    /// assert_eq!(bool_vec, [true, false, true, false, true]);
    /// ```
    ///
    /// The `Vec<T>` is generated in ascending index order, starting from the front
    /// and going towards the back, so you can use closures with mutable state:
    /// ```
    /// #![feature(vec_from_fn)]
    ///
    /// let mut state = 1;
    /// let a = Vec::from_fn(6, |_| { let x = state; state *= 2; x });
    ///
    /// assert_eq!(a, [1, 2, 4, 8, 16, 32]);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[unstable(feature = "vec_from_fn", issue = "149698")]
    pub fn from_fn<F>(length: usize, f: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        (0..length).map(f).collect()
    }

    /// Decomposes a `Vec<T>` into its raw components: `(pointer, length, capacity)`.
    ///
    /// Returns the raw pointer to the underlying data, the length of
    /// the vector (in elements), and the allocated capacity of the
    /// data (in elements). These are the same arguments in the same
    /// order as the arguments to [`from_raw_parts`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Vec`. Most often, one does
    /// this by converting the raw pointer, length, and capacity back
    /// into a `Vec` with the [`from_raw_parts`] function; more generally,
    /// if `T` is non-zero-sized and the capacity is nonzero, one may use
    /// any method that calls [`dealloc`] with a layout of
    /// `Layout::array::<T>(capacity)`; if `T` is zero-sized or the
    /// capacity is zero, nothing needs to be done.
    ///
    /// [`from_raw_parts`]: Vec::from_raw_parts
    /// [`dealloc`]: crate::alloc::GlobalAlloc::dealloc
    ///
    /// # Examples
    ///
    /// ```
    /// let v: Vec<i32> = vec![-1, 0, 1];
    ///
    /// let (ptr, len, cap) = v.into_raw_parts();
    ///
    /// let rebuilt = unsafe {
    ///     // We can now make changes to the components, such as
    ///     // transmuting the raw pointer to a compatible type.
    ///     let ptr = ptr as *mut u32;
    ///
    ///     Vec::from_raw_parts(ptr, len, cap)
    /// };
    /// assert_eq!(rebuilt, [4294967295, 0, 1]);
    /// ```
    #[must_use = "losing the pointer will leak memory"]
    #[stable(feature = "vec_into_raw_parts", since = "1.93.0")]
    pub fn into_raw_parts(self) -> (*mut T, usize, usize) {
        let mut me = ManuallyDrop::new(self);
        (me.as_mut_ptr(), me.len(), me.capacity())
    }

    #[doc(alias = "into_non_null_parts")]
    /// Decomposes a `Vec<T>` into its raw components: `(NonNull pointer, length, capacity)`.
    ///
    /// Returns the `NonNull` pointer to the underlying data, the length of
    /// the vector (in elements), and the allocated capacity of the
    /// data (in elements). These are the same arguments in the same
    /// order as the arguments to [`from_parts`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Vec`. The only way to do
    /// this is to convert the `NonNull` pointer, length, and capacity back
    /// into a `Vec` with the [`from_parts`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`from_parts`]: Vec::from_parts
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// let v: Vec<i32> = vec![-1, 0, 1];
    ///
    /// let (ptr, len, cap) = v.into_parts();
    ///
    /// let rebuilt = unsafe {
    ///     // We can now make changes to the components, such as
    ///     // transmuting the raw pointer to a compatible type.
    ///     let ptr = ptr.cast::<u32>();
    ///
    ///     Vec::from_parts(ptr, len, cap)
    /// };
    /// assert_eq!(rebuilt, [4294967295, 0, 1]);
    /// ```
    #[must_use = "losing the pointer will leak memory"]
    #[unstable(feature = "box_vec_non_null", issue = "130364")]
    pub fn into_parts(self) -> (NonNull<T>, usize, usize) {
        let (ptr, len, capacity) = self.into_raw_parts();
        // SAFETY: A `Vec` always has a non-null pointer.
        (unsafe { NonNull::new_unchecked(ptr) }, len, capacity)
    }

    /// Interns the `Vec<T>`, making the underlying memory read-only. This method should be
    /// called during compile time. (This is a no-op if called during runtime)
    ///
    /// This method must be called if the memory used by `Vec` needs to appear in the final
    /// values of constants.
    #[unstable(feature = "const_heap", issue = "79597")]
    #[rustc_const_unstable(feature = "const_heap", issue = "79597")]
    pub const fn const_make_global(mut self) -> &'static [T]
    where
        T: Freeze,
    {
        unsafe { core::intrinsics::const_make_global(self.as_mut_ptr().cast()) };
        let me = ManuallyDrop::new(self);
        unsafe { slice::from_raw_parts(me.as_ptr(), me.len) }
    }
}

#[cfg(not(no_global_oom_handling))]
#[rustc_const_unstable(feature = "const_heap", issue = "79597")]
#[rustfmt::skip] // FIXME(fee1-dead): temporary measure before rustfmt is bumped
const impl<T, A: [const] Allocator + [const] Destruct> Vec<T, A> {
    /// Constructs a new, empty `Vec<T, A>` with at least the specified capacity
    /// with the provided allocator.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the vector will not allocate.
    ///
    /// It is important to note that although the returned vector has the
    /// minimum *capacity* specified, the vector will have a zero *length*. For
    /// an explanation of the difference between length and capacity, see
    /// *[Capacity and reallocation]*.
    ///
    /// If it is important to know the exact allocated capacity of a `Vec`,
    /// always use the [`capacity`] method after construction.
    ///
    /// For `Vec<T, A>` where `T` is a zero-sized type, there will be no allocation
    /// and the capacity will always be `usize::MAX`.
    ///
    /// [Capacity and reallocation]: #capacity-and-reallocation
    /// [`capacity`]: Vec::capacity
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut vec = Vec::with_capacity_in(10, System);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    /// assert_eq!(vec.len(), 10);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // ...but this may make the vector reallocate
    /// vec.push(11);
    /// assert_eq!(vec.len(), 11);
    /// assert!(vec.capacity() >= 11);
    ///
    /// // A vector of a zero-sized type will always over-allocate, since no
    /// // allocation is necessary
    /// let vec_units = Vec::<(), System>::with_capacity_in(10, System);
    /// assert_eq!(vec_units.capacity(), usize::MAX);
    /// ```
    #[inline]
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Vec { buf: RawVec::with_capacity_in(capacity, alloc), len: 0 }
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the vector's length would exceed its
    /// capacity after the push, *O*(*capacity*) time is taken to copy the
    /// vector's elements to a larger allocation. This expensive operation is
    /// offset by the *capacity* *O*(1) insertions it allows.
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("push_back", "put", "append")]
    pub fn push(&mut self, value: T) {
        let _ = self.push_mut(value);
    }

    /// Appends an element to the back of a collection, returning a reference to it.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2];
    /// let last = vec.push_mut(3);
    /// assert_eq!(*last, 3);
    /// assert_eq!(vec, [1, 2, 3]);
    ///
    /// let last = vec.push_mut(3);
    /// *last += 1;
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the vector's length would exceed its
    /// capacity after the push, *O*(*capacity*) time is taken to copy the
    /// vector's elements to a larger allocation. This expensive operation is
    /// offset by the *capacity* *O*(1) insertions it allows.
    #[inline]
    #[stable(feature = "push_mut", since = "CURRENT_RUSTC_VERSION")]
    #[must_use = "if you don't need a reference to the value, use `Vec::push` instead"]
    pub fn push_mut(&mut self, value: T) -> &mut T {
        // Inform codegen that the length does not change across grow_one().
        let len = self.len;
        // This will panic or abort if we would allocate > isize::MAX bytes
        // or if the length increment would overflow for zero-sized types.
        if len == self.buf.capacity() {
            self.buf.grow_one();
        }
        unsafe {
            let end = self.as_mut_ptr().add(len);
            ptr::write(end, value);
            self.len = len + 1;
            // SAFETY: We just wrote a value to the pointer that will live the lifetime of the reference.
            &mut *end
        }
    }
}

impl<T, A: Allocator> Vec<T, A> {
    /// Constructs a new, empty `Vec<T, A>`.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// # #[allow(unused_mut)]
    /// let mut vec: Vec<i32, _> = Vec::new_in(System);
    /// ```
    #[inline]
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub const fn new_in(alloc: A) -> Self {
        Vec { buf: RawVec::new_in(alloc), len: 0 }
    }

    /// Constructs a new, empty `Vec<T, A>` with at least the specified capacity
    /// with the provided allocator.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the vector will not allocate.
    ///
    /// # Errors
    ///
    /// Returns an error if the capacity exceeds `isize::MAX` _bytes_,
    /// or if the allocator reports allocation failure.
    #[inline]
    #[unstable(feature = "allocator_api", issue = "32838")]
    // #[unstable(feature = "try_with_capacity", issue = "91913")]
    pub fn try_with_capacity_in(capacity: usize, alloc: A) -> Result<Self, TryReserveError> {
        Ok(Vec { buf: RawVec::try_with_capacity_in(capacity, alloc)?, len: 0 })
    }

    /// Creates a `Vec<T, A>` directly from a pointer, a length, a capacity,
    /// and an allocator.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * `ptr` must be [*currently allocated*] via the given allocator `alloc`.
    /// * `T` needs to have the same alignment as what `ptr` was allocated with.
    ///   (`T` having a less strict alignment is not sufficient, the alignment really
    ///   needs to be equal to satisfy the [`dealloc`] requirement that memory must be
    ///   allocated and deallocated with the same layout.)
    /// * The size of `T` times the `capacity` (ie. the allocated size in bytes) needs
    ///   to be the same size as the pointer was allocated with. (Because similar to
    ///   alignment, [`dealloc`] must be called with the same layout `size`.)
    /// * `length` needs to be less than or equal to `capacity`.
    /// * The first `length` values must be properly initialized values of type `T`.
    /// * `capacity` needs to [*fit*] the layout size that the pointer was allocated with.
    /// * The allocated size in bytes must be no larger than `isize::MAX`.
    ///   See the safety documentation of [`pointer::offset`].
    ///
    /// These requirements are always upheld by any `ptr` that has been allocated
    /// via `Vec<T, A>`. Other allocation sources are allowed if the invariants are
    /// upheld.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example it is **not** safe
    /// to build a `Vec<u8>` from a pointer to a C `char` array with length `size_t`.
    /// It's also not safe to build one from a `Vec<u16>` and its length, because
    /// the allocator cares about the alignment, and these two types have different
    /// alignments. The buffer was allocated with alignment 2 (for `u16`), but after
    /// turning it into a `Vec<u8>` it'll be deallocated with alignment 1.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `Vec<T>` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// [`String`]: crate::string::String
    /// [`dealloc`]: crate::alloc::GlobalAlloc::dealloc
    /// [*currently allocated*]: crate::alloc::Allocator#currently-allocated-memory
    /// [*fit*]: crate::alloc::Allocator#memory-fitting
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// use std::ptr;
    ///
    /// let mut v = Vec::with_capacity_in(3, System);
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// // Deconstruct the vector into parts.
    /// let (p, len, cap, alloc) = v.into_raw_parts_with_alloc();
    ///
    /// unsafe {
    ///     // Overwrite memory with 4, 5, 6
    ///     for i in 0..len {
    ///         ptr::write(p.add(i), 4 + i);
    ///     }
    ///
    ///     // Put everything back together into a Vec
    ///     let rebuilt = Vec::from_raw_parts_in(p, len, cap, alloc.clone());
    ///     assert_eq!(rebuilt, [4, 5, 6]);
    /// }
    /// ```
    ///
    /// Using memory that was allocated elsewhere:
    ///
    /// ```rust
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::{AllocError, Allocator, Global, Layout};
    ///
    /// fn main() {
    ///     let layout = Layout::array::<u32>(16).expect("overflow cannot happen");
    ///
    ///     let vec = unsafe {
    ///         let mem = match Global.allocate(layout) {
    ///             Ok(mem) => mem.cast::<u32>().as_ptr(),
    ///             Err(AllocError) => return,
    ///         };
    ///
    ///         mem.write(1_000_000);
    ///
    ///         Vec::from_raw_parts_in(mem, 1, 16, Global)
    ///     };
    ///
    ///     assert_eq!(vec, &[1_000_000]);
    ///     assert_eq!(vec.capacity(), 16);
    /// }
    /// ```
    #[inline]
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub unsafe fn from_raw_parts_in(ptr: *mut T, length: usize, capacity: usize, alloc: A) -> Self {
        ub_checks::assert_unsafe_precondition!(
            check_library_ub,
            "Vec::from_raw_parts_in requires that length <= capacity",
            (length: usize = length, capacity: usize = capacity) => length <= capacity
        );
        unsafe { Vec { buf: RawVec::from_raw_parts_in(ptr, capacity, alloc), len: length } }
    }

    #[doc(alias = "from_non_null_parts_in")]
    /// Creates a `Vec<T, A>` directly from a `NonNull` pointer, a length, a capacity,
    /// and an allocator.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * `ptr` must be [*currently allocated*] via the given allocator `alloc`.
    /// * `T` needs to have the same alignment as what `ptr` was allocated with.
    ///   (`T` having a less strict alignment is not sufficient, the alignment really
    ///   needs to be equal to satisfy the [`dealloc`] requirement that memory must be
    ///   allocated and deallocated with the same layout.)
    /// * The size of `T` times the `capacity` (ie. the allocated size in bytes) needs
    ///   to be the same size as the pointer was allocated with. (Because similar to
    ///   alignment, [`dealloc`] must be called with the same layout `size`.)
    /// * `length` needs to be less than or equal to `capacity`.
    /// * The first `length` values must be properly initialized values of type `T`.
    /// * `capacity` needs to [*fit*] the layout size that the pointer was allocated with.
    /// * The allocated size in bytes must be no larger than `isize::MAX`.
    ///   See the safety documentation of [`pointer::offset`].
    ///
    /// These requirements are always upheld by any `ptr` that has been allocated
    /// via `Vec<T, A>`. Other allocation sources are allowed if the invariants are
    /// upheld.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example it is **not** safe
    /// to build a `Vec<u8>` from a pointer to a C `char` array with length `size_t`.
    /// It's also not safe to build one from a `Vec<u16>` and its length, because
    /// the allocator cares about the alignment, and these two types have different
    /// alignments. The buffer was allocated with alignment 2 (for `u16`), but after
    /// turning it into a `Vec<u8>` it'll be deallocated with alignment 1.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `Vec<T>` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// [`String`]: crate::string::String
    /// [`dealloc`]: crate::alloc::GlobalAlloc::dealloc
    /// [*currently allocated*]: crate::alloc::Allocator#currently-allocated-memory
    /// [*fit*]: crate::alloc::Allocator#memory-fitting
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api, box_vec_non_null)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut v = Vec::with_capacity_in(3, System);
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// // Deconstruct the vector into parts.
    /// let (p, len, cap, alloc) = v.into_parts_with_alloc();
    ///
    /// unsafe {
    ///     // Overwrite memory with 4, 5, 6
    ///     for i in 0..len {
    ///         p.add(i).write(4 + i);
    ///     }
    ///
    ///     // Put everything back together into a Vec
    ///     let rebuilt = Vec::from_parts_in(p, len, cap, alloc.clone());
    ///     assert_eq!(rebuilt, [4, 5, 6]);
    /// }
    /// ```
    ///
    /// Using memory that was allocated elsewhere:
    ///
    /// ```rust
    /// #![feature(allocator_api, box_vec_non_null)]
    ///
    /// use std::alloc::{AllocError, Allocator, Global, Layout};
    ///
    /// fn main() {
    ///     let layout = Layout::array::<u32>(16).expect("overflow cannot happen");
    ///
    ///     let vec = unsafe {
    ///         let mem = match Global.allocate(layout) {
    ///             Ok(mem) => mem.cast::<u32>(),
    ///             Err(AllocError) => return,
    ///         };
    ///
    ///         mem.write(1_000_000);
    ///
    ///         Vec::from_parts_in(mem, 1, 16, Global)
    ///     };
    ///
    ///     assert_eq!(vec, &[1_000_000]);
    ///     assert_eq!(vec.capacity(), 16);
    /// }
    /// ```
    #[inline]
    #[unstable(feature = "allocator_api", issue = "32838")]
    // #[unstable(feature = "box_vec_non_null", issue = "130364")]
    #[requires(length <= capacity)]
    #[requires({
        mem::size_of::<T>()
            .checked_mul(capacity)
            .is_some_and(|size| size <= isize::MAX as usize)
    })]
    #[requires(ptr.as_ptr().is_aligned())]
    #[requires({
        mem::size_of::<T>() == 0
            || capacity == 0
            || ub_checks::can_write(core::ptr::slice_from_raw_parts_mut(ptr.as_ptr(), capacity))
    })]
    #[requires({
        mem::size_of::<T>() == 0
            || capacity == 0
            || {
                let raw_ptr = ptr.as_ptr();
                let end = raw_ptr.wrapping_add(capacity);
                ub_checks::same_allocation(raw_ptr, end)
                    && !ub_checks::same_allocation(raw_ptr, raw_ptr.wrapping_sub(1))
            }
    })]
    // Kani-specific clause: the tool-independent safety predicate API has no
    // equivalent of `kani::mem::is_inbounds`. This distinguishes the exact
    // one-past allocation endpoint from an interior pointer.
    #[cfg_attr(
        kani,
        kani::requires({
            mem::size_of::<T>() == 0
                || capacity == 0
                || {
                    let raw_ptr = ptr.as_ptr();
                    !kani::mem::is_inbounds(raw_ptr.wrapping_add(capacity))
                }
        })
    )]
    #[requires({
        length == 0
            || ub_checks::can_dereference(core::ptr::slice_from_raw_parts(ptr.as_ptr(), length))
    })]
    pub unsafe fn from_parts_in(ptr: NonNull<T>, length: usize, capacity: usize, alloc: A) -> Self {
        ub_checks::assert_unsafe_precondition!(
            check_library_ub,
            "Vec::from_parts_in requires that length <= capacity",
            (length: usize = length, capacity: usize = capacity) => length <= capacity
        );
        unsafe { Vec { buf: RawVec::from_nonnull_in(ptr, capacity, alloc), len: length } }
    }

    /// Decomposes a `Vec<T>` into its raw components: `(pointer, length, capacity, allocator)`.
    ///
    /// Returns the raw pointer to the underlying data, the length of the vector (in elements),
    /// the allocated capacity of the data (in elements), and the allocator. These are the same
    /// arguments in the same order as the arguments to [`from_raw_parts_in`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Vec`. The only way to do
    /// this is to convert the raw pointer, length, and capacity back
    /// into a `Vec` with the [`from_raw_parts_in`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`from_raw_parts_in`]: Vec::from_raw_parts_in
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut v: Vec<i32, System> = Vec::new_in(System);
    /// v.push(-1);
    /// v.push(0);
    /// v.push(1);
    ///
    /// let (ptr, len, cap, alloc) = v.into_raw_parts_with_alloc();
    ///
    /// let rebuilt = unsafe {
    ///     // We can now make changes to the components, such as
    ///     // transmuting the raw pointer to a compatible type.
    ///     let ptr = ptr as *mut u32;
    ///
    ///     Vec::from_raw_parts_in(ptr, len, cap, alloc)
    /// };
    /// assert_eq!(rebuilt, [4294967295, 0, 1]);
    /// ```
    #[must_use = "losing the pointer will leak memory"]
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub fn into_raw_parts_with_alloc(self) -> (*mut T, usize, usize, A) {
        let mut me = ManuallyDrop::new(self);
        let len = me.len();
        let capacity = me.capacity();
        let ptr = me.as_mut_ptr();
        let alloc = unsafe { ptr::read(me.allocator()) };
        (ptr, len, capacity, alloc)
    }

    #[doc(alias = "into_non_null_parts_with_alloc")]
    /// Decomposes a `Vec<T>` into its raw components: `(NonNull pointer, length, capacity, allocator)`.
    ///
    /// Returns the `NonNull` pointer to the underlying data, the length of the vector (in elements),
    /// the allocated capacity of the data (in elements), and the allocator. These are the same
    /// arguments in the same order as the arguments to [`from_parts_in`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Vec`. The only way to do
    /// this is to convert the `NonNull` pointer, length, and capacity back
    /// into a `Vec` with the [`from_parts_in`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`from_parts_in`]: Vec::from_parts_in
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api, box_vec_non_null)]
    ///
    /// use std::alloc::System;
    ///
    /// let mut v: Vec<i32, System> = Vec::new_in(System);
    /// v.push(-1);
    /// v.push(0);
    /// v.push(1);
    ///
    /// let (ptr, len, cap, alloc) = v.into_parts_with_alloc();
    ///
    /// let rebuilt = unsafe {
    ///     // We can now make changes to the components, such as
    ///     // transmuting the raw pointer to a compatible type.
    ///     let ptr = ptr.cast::<u32>();
    ///
    ///     Vec::from_parts_in(ptr, len, cap, alloc)
    /// };
    /// assert_eq!(rebuilt, [4294967295, 0, 1]);
    /// ```
    #[must_use = "losing the pointer will leak memory"]
    #[unstable(feature = "allocator_api", issue = "32838")]
    // #[unstable(feature = "box_vec_non_null", issue = "130364")]
    pub fn into_parts_with_alloc(self) -> (NonNull<T>, usize, usize, A) {
        let (ptr, len, capacity, alloc) = self.into_raw_parts_with_alloc();
        // SAFETY: A `Vec` always has a non-null pointer.
        (unsafe { NonNull::new_unchecked(ptr) }, len, capacity, alloc)
    }

    /// Returns the total number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec: Vec<i32> = Vec::with_capacity(10);
    /// vec.push(42);
    /// assert!(vec.capacity() >= 10);
    /// ```
    ///
    /// A vector with zero-sized elements will always have a capacity of usize::MAX:
    ///
    /// ```
    /// #[derive(Clone)]
    /// struct ZeroSized;
    ///
    /// fn main() {
    ///     assert_eq!(std::mem::size_of::<ZeroSized>(), 0);
    ///     let v = vec![ZeroSized; 0];
    ///     assert_eq!(v.capacity(), usize::MAX);
    /// }
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `Vec<T>`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1];
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_diagnostic_item = "vec_reserve"]
    pub fn reserve(&mut self, additional: usize) {
        self.buf.reserve(self.len, additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements to
    /// be inserted in the given `Vec<T>`. Unlike [`reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`reserve`] if future insertions are expected.
    ///
    /// [`reserve`]: Vec::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1];
    /// vec.reserve_exact(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.buf.reserve_exact(self.len, additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `Vec<T>`. The collection may reserve more space to speculatively avoid
    /// frequent reallocations. After calling `try_reserve`, capacity will be
    /// greater than or equal to `self.len() + additional` if it returns
    /// `Ok(())`. Does nothing if capacity is already sufficient. This method
    /// preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::TryReserveError;
    ///
    /// fn process_data(data: &[u32]) -> Result<Vec<u32>, TryReserveError> {
    ///     let mut output = Vec::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[stable(feature = "try_reserve", since = "1.57.0")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.buf.try_reserve(self.len, additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional`
    /// elements to be inserted in the given `Vec<T>`. Unlike [`try_reserve`],
    /// this will not deliberately over-allocate to speculatively avoid frequent
    /// allocations. After calling `try_reserve_exact`, capacity will be greater
    /// than or equal to `self.len() + additional` if it returns `Ok(())`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: Vec::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::TryReserveError;
    ///
    /// fn process_data(data: &[u32]) -> Result<Vec<u32>, TryReserveError> {
    ///     let mut output = Vec::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[stable(feature = "try_reserve", since = "1.57.0")]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.buf.try_reserve_exact(self.len, additional)
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// The behavior of this method depends on the allocator, which may either shrink the vector
    /// in-place or reallocate. The resulting vector might still have some excess capacity, just as
    /// is the case for [`with_capacity`]. See [`Allocator::shrink`] for more details.
    ///
    /// [`with_capacity`]: Vec::with_capacity
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3]);
    /// assert!(vec.capacity() >= 10);
    /// vec.shrink_to_fit();
    /// assert!(vec.capacity() >= 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        // The capacity is never less than the length, and there's nothing to do when
        // they are equal, so we can avoid the panic case in `RawVec::shrink_to_fit`
        // by only calling it with a greater capacity.
        if self.capacity() > self.len {
            self.buf.shrink_to_fit(self.len);
        }
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3]);
    /// assert!(vec.capacity() >= 10);
    /// vec.shrink_to(4);
    /// assert!(vec.capacity() >= 4);
    /// vec.shrink_to(0);
    /// assert!(vec.capacity() >= 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "shrink_to", since = "1.56.0")]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        if self.capacity() > min_capacity {
            self.buf.shrink_to_fit(cmp::max(self.len, min_capacity));
        }
    }

    /// Converts the vector into [`Box<[T]>`][owned slice].
    ///
    /// Before doing the conversion, this method discards excess capacity like [`shrink_to_fit`].
    ///
    /// [owned slice]: Box
    /// [`shrink_to_fit`]: Vec::shrink_to_fit
    ///
    /// # Examples
    ///
    /// ```
    /// let v = vec![1, 2, 3];
    ///
    /// let slice = v.into_boxed_slice();
    /// ```
    ///
    /// Any excess capacity is removed:
    ///
    /// ```
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3]);
    ///
    /// assert!(vec.capacity() >= 10);
    /// let slice = vec.into_boxed_slice();
    /// assert_eq!(slice.into_vec().capacity(), 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn into_boxed_slice(mut self) -> Box<[T], A> {
        unsafe {
            self.shrink_to_fit();
            let me = ManuallyDrop::new(self);
            let buf = ptr::read(&me.buf);
            let len = me.len();
            buf.into_box(len).assume_init()
        }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater or equal to the vector's current length, this has
    /// no effect.
    ///
    /// The [`drain`] method can emulate `truncate`, but causes the excess
    /// elements to be returned instead of dropped.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4, 5];
    /// vec.truncate(2);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current
    /// length:
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// vec.truncate(8);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    ///
    /// Truncating when `len == 0` is equivalent to calling the [`clear`]
    /// method.
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// vec.truncate(0);
    /// assert_eq!(vec, []);
    /// ```
    ///
    /// [`clear`]: Vec::clear
    /// [`drain`]: Vec::drain
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn truncate(&mut self, len: usize) {
        // This is safe because:
        //
        // * the slice passed to `drop_in_place` is valid; the `len > self.len`
        //   case avoids creating an invalid slice, and
        // * the `len` of the vector is shrunk before calling `drop_in_place`,
        //   such that no value will be dropped twice in case `drop_in_place`
        //   were to panic once (if it panics twice, the program aborts).
        unsafe {
            // Note: It's intentional that this is `>` and not `>=`.
            //       Changing it to `>=` has negative performance
            //       implications in some cases. See #78884 for more.
            if len > self.len {
                return;
            }
            let remaining_len = self.len - len;
            let s = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            self.len = len;
            ptr::drop_in_place(s);
        }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{self, Write};
    /// let buffer = vec![1, 2, 3, 5, 8];
    /// io::sink().write(buffer.as_slice()).unwrap();
    /// ```
    #[inline]
    #[stable(feature = "vec_as_slice", since = "1.7.0")]
    #[rustc_diagnostic_item = "vec_as_slice"]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn as_slice(&self) -> &[T] {
        // SAFETY: `slice::from_raw_parts` requires pointee is a contiguous, aligned buffer of size
        // `len` containing properly-initialized `T`s. Data must not be mutated for the returned
        // lifetime. Further, `len * size_of::<T>` <= `isize::MAX`, and allocation does not
        // "wrap" through overflowing memory addresses.
        //
        // * Vec API guarantees that self.buf:
        //      * contains only properly-initialized items within 0..len
        //      * is aligned, contiguous, and valid for `len` reads
        //      * obeys size and address-wrapping constraints
        //
        // * We only construct `&mut` references to `self.buf` through `&mut self` methods; borrow-
        //   check ensures that it is not possible to mutably alias `self.buf` within the
        //   returned lifetime.
        unsafe {
            // normally this would use `slice::from_raw_parts`, but it's
            // instantiated often enough that avoiding the UB check is worth it
            &*core::intrinsics::aggregate_raw_ptr::<*const [T], _, _>(self.as_ptr(), self.len)
        }
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{self, Read};
    /// let mut buffer = vec![0; 3];
    /// io::repeat(0b101).read_exact(buffer.as_mut_slice()).unwrap();
    /// ```
    #[inline]
    #[stable(feature = "vec_as_slice", since = "1.7.0")]
    #[rustc_diagnostic_item = "vec_as_mut_slice"]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: `slice::from_raw_parts_mut` requires pointee is a contiguous, aligned buffer of
        // size `len` containing properly-initialized `T`s. Data must not be accessed through any
        // other pointer for the returned lifetime. Further, `len * size_of::<T>` <=
        // `ISIZE::MAX` and allocation does not "wrap" through overflowing memory addresses.
        //
        // * Vec API guarantees that self.buf:
        //      * contains only properly-initialized items within 0..len
        //      * is aligned, contiguous, and valid for `len` reads
        //      * obeys size and address-wrapping constraints
        //
        // * We only construct references to `self.buf` through `&self` and `&mut self` methods;
        //   borrow-check ensures that it is not possible to construct a reference to `self.buf`
        //   within the returned lifetime.
        unsafe {
            // normally this would use `slice::from_raw_parts_mut`, but it's
            // instantiated often enough that avoiding the UB check is worth it
            &mut *core::intrinsics::aggregate_raw_ptr::<*mut [T], _, _>(self.as_mut_ptr(), self.len)
        }
    }

    /// Returns a raw pointer to the vector's buffer, or a dangling raw pointer
    /// valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to
    /// is never written to (except inside an `UnsafeCell`) using this pointer or any pointer
    /// derived from it. If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying slice, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`],
    /// and [`as_non_null`].
    /// Note that calling other methods that materialize mutable references to the slice,
    /// or mutable references to specific elements you are planning on accessing through this pointer,
    /// as well as writing to those elements, may still invalidate this pointer.
    /// See the second example below for how this guarantee can be used.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// let x = vec![1, 2, 4];
    /// let x_ptr = x.as_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         assert_eq!(*x_ptr.add(i), 1 << i);
    ///     }
    /// }
    /// ```
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    /// unsafe {
    ///     let mut v = vec![0, 1, 2];
    ///     let ptr1 = v.as_ptr();
    ///     let _ = ptr1.read();
    ///     let ptr2 = v.as_mut_ptr().offset(2);
    ///     ptr2.write(2);
    ///     // Notably, the write to `ptr2` did *not* invalidate `ptr1`
    ///     // because it mutated a different element:
    ///     let _ = ptr1.read();
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Vec::as_mut_ptr
    /// [`as_ptr`]: Vec::as_ptr
    /// [`as_non_null`]: Vec::as_non_null
    #[stable(feature = "vec_as_ptr", since = "1.37.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    #[rustc_never_returns_null_ptr]
    #[rustc_as_ptr]
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        // We shadow the slice method of the same name to avoid going through
        // `deref`, which creates an intermediate reference.
        self.buf.ptr()
    }

    /// Returns a raw mutable pointer to the vector's buffer, or a dangling
    /// raw pointer valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying slice, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`],
    /// and [`as_non_null`].
    /// Note that calling other methods that materialize references to the slice,
    /// or references to specific elements you are planning on accessing through this pointer,
    /// may still invalidate this pointer.
    /// See the second example below for how this guarantee can be used.
    ///
    /// The method also guarantees that, as long as `T` is not zero-sized and the capacity is
    /// nonzero, the pointer may be passed into [`dealloc`] with a layout of
    /// `Layout::array::<T>(capacity)` in order to deallocate the backing memory. If this is done,
    /// be careful not to run the destructor of the `Vec`, as dropping it will result in
    /// double-frees. Wrapping the `Vec` in a [`ManuallyDrop`] is the typical way to achieve this.
    ///
    /// # Examples
    ///
    /// ```
    /// // Allocate vector big enough for 4 elements.
    /// let size = 4;
    /// let mut x: Vec<i32> = Vec::with_capacity(size);
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         *x_ptr.add(i) = i as i32;
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(&*x, &[0, 1, 2, 3]);
    /// ```
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    /// unsafe {
    ///     let mut v = vec![0];
    ///     let ptr1 = v.as_mut_ptr();
    ///     ptr1.write(1);
    ///     let ptr2 = v.as_mut_ptr();
    ///     ptr2.write(2);
    ///     // Notably, the write to `ptr2` did *not* invalidate `ptr1`:
    ///     ptr1.write(3);
    /// }
    /// ```
    ///
    /// Deallocating a vector using [`Box`] (which uses [`dealloc`] internally):
    ///
    /// ```
    /// use std::mem::{ManuallyDrop, MaybeUninit};
    ///
    /// let mut v = ManuallyDrop::new(vec![0, 1, 2]);
    /// let ptr = v.as_mut_ptr();
    /// let capacity = v.capacity();
    /// let slice_ptr: *mut [MaybeUninit<i32>] =
    ///     std::ptr::slice_from_raw_parts_mut(ptr.cast(), capacity);
    /// drop(unsafe { Box::from_raw(slice_ptr) });
    /// ```
    ///
    /// [`as_mut_ptr`]: Vec::as_mut_ptr
    /// [`as_ptr`]: Vec::as_ptr
    /// [`as_non_null`]: Vec::as_non_null
    /// [`dealloc`]: crate::alloc::GlobalAlloc::dealloc
    /// [`ManuallyDrop`]: core::mem::ManuallyDrop
    #[stable(feature = "vec_as_ptr", since = "1.37.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    #[rustc_never_returns_null_ptr]
    #[rustc_as_ptr]
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        // We shadow the slice method of the same name to avoid going through
        // `deref_mut`, which creates an intermediate reference.
        self.buf.ptr()
    }

    /// Returns a `NonNull` pointer to the vector's buffer, or a dangling
    /// `NonNull` pointer valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying slice, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`],
    /// and [`as_non_null`].
    /// Note that calling other methods that materialize references to the slice,
    /// or references to specific elements you are planning on accessing through this pointer,
    /// may still invalidate this pointer.
    /// See the second example below for how this guarantee can be used.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(box_vec_non_null)]
    ///
    /// // Allocate vector big enough for 4 elements.
    /// let size = 4;
    /// let mut x: Vec<i32> = Vec::with_capacity(size);
    /// let x_ptr = x.as_non_null();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         x_ptr.add(i).write(i as i32);
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(&*x, &[0, 1, 2, 3]);
    /// ```
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    /// #![feature(box_vec_non_null)]
    ///
    /// unsafe {
    ///     let mut v = vec![0];
    ///     let ptr1 = v.as_non_null();
    ///     ptr1.write(1);
    ///     let ptr2 = v.as_non_null();
    ///     ptr2.write(2);
    ///     // Notably, the write to `ptr2` did *not* invalidate `ptr1`:
    ///     ptr1.write(3);
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Vec::as_mut_ptr
    /// [`as_ptr`]: Vec::as_ptr
    /// [`as_non_null`]: Vec::as_non_null
    #[unstable(feature = "box_vec_non_null", issue = "130364")]
    #[rustc_const_unstable(feature = "box_vec_non_null", issue = "130364")]
    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        self.buf.non_null()
    }

    /// Returns a reference to the underlying allocator.
    #[unstable(feature = "allocator_api", issue = "32838")]
    #[inline]
    pub fn allocator(&self) -> &A {
        self.buf.allocator()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type. Normally changing the length of a vector
    /// is done using one of the safe operations instead, such as
    /// [`truncate`], [`resize`], [`extend`], or [`clear`].
    ///
    /// [`truncate`]: Vec::truncate
    /// [`resize`]: Vec::resize
    /// [`extend`]: Extend::extend
    /// [`clear`]: Vec::clear
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: Vec::capacity
    ///
    /// # Examples
    ///
    /// See [`spare_capacity_mut()`] for an example with safe
    /// initialization of capacity elements and use of this method.
    ///
    /// `set_len()` can be useful for situations in which the vector
    /// is serving as a buffer for other code, particularly over FFI:
    ///
    /// ```no_run
    /// # #![allow(dead_code)]
    /// # // This is just a minimal skeleton for the doc example;
    /// # // don't use this as a starting point for a real library.
    /// # pub struct StreamWrapper { strm: *mut std::ffi::c_void }
    /// # const Z_OK: i32 = 0;
    /// # unsafe extern "C" {
    /// #     fn deflateGetDictionary(
    /// #         strm: *mut std::ffi::c_void,
    /// #         dictionary: *mut u8,
    /// #         dictLength: *mut usize,
    /// #     ) -> i32;
    /// # }
    /// # impl StreamWrapper {
    /// pub fn get_dictionary(&self) -> Option<Vec<u8>> {
    ///     // Per the FFI method's docs, "32768 bytes is always enough".
    ///     let mut dict = Vec::with_capacity(32_768);
    ///     let mut dict_length = 0;
    ///     // SAFETY: When `deflateGetDictionary` returns `Z_OK`, it holds that:
    ///     // 1. `dict_length` elements were initialized.
    ///     // 2. `dict_length` <= the capacity (32_768)
    ///     // which makes `set_len` safe to call.
    ///     unsafe {
    ///         // Make the FFI call...
    ///         let r = deflateGetDictionary(self.strm, dict.as_mut_ptr(), &mut dict_length);
    ///         if r == Z_OK {
    ///             // ...and update the length to what was initialized.
    ///             dict.set_len(dict_length);
    ///             Some(dict)
    ///         } else {
    ///             None
    ///         }
    ///     }
    /// }
    /// # }
    /// ```
    ///
    /// While the following example is sound, there is a memory leak since
    /// the inner vectors were not freed prior to the `set_len` call:
    ///
    /// ```
    /// let mut vec = vec![vec![1, 0, 0],
    ///                    vec![0, 1, 0],
    ///                    vec![0, 0, 1]];
    /// // SAFETY:
    /// // 1. `old_len..0` is empty so no elements need to be initialized.
    /// // 2. `0 <= capacity` always holds whatever `capacity` is.
    /// unsafe {
    ///     vec.set_len(0);
    /// #   // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// #   // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// #   vec.set_len(3);
    /// }
    /// ```
    ///
    /// Normally, here, one would use [`clear`] instead to correctly drop
    /// the contents and thus not leak memory.
    ///
    /// [`spare_capacity_mut()`]: Vec::spare_capacity_mut
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[requires(new_len <= self.capacity())]
    #[requires(
        new_len <= self.len
            || ub_checks::can_dereference(core::ptr::slice_from_raw_parts(
                self.as_ptr().wrapping_add(self.len),
                new_len - self.len,
            ))
    )]
    #[cfg_attr(kani, kani::modifies(&mut self.len))]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        ub_checks::assert_unsafe_precondition!(
            check_library_ub,
            "Vec::set_len requires that new_len <= capacity()",
            (new_len: usize = new_len, capacity: usize = self.capacity()) => new_len <= capacity
        );

        self.len = new_len;
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering of the remaining elements, but is *O*(1).
    /// If you need to preserve the element order, use [`remove`] instead.
    ///
    /// [`remove`]: Vec::remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec!["foo", "bar", "baz", "qux"];
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v, ["baz", "qux"]);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn swap_remove(&mut self, index: usize) -> T {
        #[cold]
        #[cfg_attr(not(panic = "immediate-abort"), inline(never))]
        #[optimize(size)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("swap_remove index (is {index}) should be < len (is {len})");
        }

        let len = self.len();
        if index >= len {
            assert_failed(index, len);
        }
        unsafe {
            // We replace self[index] with the last element. Note that if the
            // bounds check above succeeds there must be a last element (which
            // can be self[index] itself).
            let value = ptr::read(self.as_ptr().add(index));
            let base_ptr = self.as_mut_ptr();
            ptr::copy(base_ptr.add(len - 1), base_ptr.add(index), 1);
            self.set_len(len - 1);
            value
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec!['a', 'b', 'c'];
    /// vec.insert(1, 'd');
    /// assert_eq!(vec, ['a', 'd', 'b', 'c']);
    /// vec.insert(4, 'e');
    /// assert_eq!(vec, ['a', 'd', 'b', 'c', 'e']);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*([`Vec::len`]) time. All items after the insertion index must be
    /// shifted to the right. In the worst case, all elements are shifted when
    /// the insertion index is 0.
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[track_caller]
    pub fn insert(&mut self, index: usize, element: T) {
        let _ = self.insert_mut(index, element);
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right, and returning a reference to the new
    /// element.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 3, 5, 9];
    /// let x = vec.insert_mut(3, 6);
    /// *x += 1;
    /// assert_eq!(vec, [1, 3, 5, 7, 9]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*([`Vec::len`]) time. All items after the insertion index must be
    /// shifted to the right. In the worst case, all elements are shifted when
    /// the insertion index is 0.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "push_mut", since = "CURRENT_RUSTC_VERSION")]
    #[track_caller]
    #[must_use = "if you don't need a reference to the value, use `Vec::insert` instead"]
    pub fn insert_mut(&mut self, index: usize, element: T) -> &mut T {
        #[cold]
        #[cfg_attr(not(panic = "immediate-abort"), inline(never))]
        #[track_caller]
        #[optimize(size)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("insertion index (is {index}) should be <= len (is {len})");
        }

        let len = self.len();
        if index > len {
            assert_failed(index, len);
        }

        // space for the new element
        if len == self.buf.capacity() {
            self.buf.grow_one();
        }

        unsafe {
            // infallible
            // The spot to put the new value
            let p = self.as_mut_ptr().add(index);
            {
                if index < len {
                    // Shift everything over to make space. (Duplicating the
                    // `index`th element into two consecutive places.)
                    ptr::copy(p, p.add(1), len - index);
                }
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
            }
            self.set_len(len + 1);
            &mut *p
        }
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// Note: Because this shifts over the remaining elements, it has a
    /// worst-case performance of *O*(*n*). If you don't need the order of elements
    /// to be preserved, use [`swap_remove`] instead. If you'd like to remove
    /// elements from the beginning of the `Vec`, consider using
    /// [`VecDeque::pop_front`] instead.
    ///
    /// [`swap_remove`]: Vec::swap_remove
    /// [`VecDeque::pop_front`]: crate::collections::VecDeque::pop_front
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec!['a', 'b', 'c'];
    /// assert_eq!(v.remove(1), 'b');
    /// assert_eq!(v, ['a', 'c']);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[track_caller]
    #[rustc_confusables("delete", "take")]
    pub fn remove(&mut self, index: usize) -> T {
        #[cold]
        #[cfg_attr(not(panic = "immediate-abort"), inline(never))]
        #[track_caller]
        #[optimize(size)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("removal index (is {index}) should be < len (is {len})");
        }

        match self.try_remove(index) {
            Some(elem) => elem,
            None => assert_failed(index, self.len()),
        }
    }

    /// Remove and return the element at position `index` within the vector,
    /// shifting all elements after it to the left, or [`None`] if it does not
    /// exist.
    ///
    /// Note: Because this shifts over the remaining elements, it has a
    /// worst-case performance of *O*(*n*). If you'd like to remove
    /// elements from the beginning of the `Vec`, consider using
    /// [`VecDeque::pop_front`] instead.
    ///
    /// [`VecDeque::pop_front`]: crate::collections::VecDeque::pop_front
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(vec_try_remove)]
    /// let mut v = vec![1, 2, 3];
    /// assert_eq!(v.try_remove(0), Some(1));
    /// assert_eq!(v.try_remove(2), None);
    /// ```
    #[unstable(feature = "vec_try_remove", issue = "146954")]
    #[rustc_confusables("delete", "take", "remove")]
    pub fn try_remove(&mut self, index: usize) -> Option<T> {
        let len = self.len();
        if index >= len {
            return None;
        }
        unsafe {
            // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().add(index);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                ret = ptr::read(ptr);

                // Shift everything down to fill in that spot.
                ptr::copy(ptr.add(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            Some(ret)
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.retain(|&x| x % 2 == 0);
    /// assert_eq!(vec, [2, 4]);
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4, 5];
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// vec.retain(|_| *iter.next().unwrap());
    /// assert_eq!(vec, [2, 3, 5]);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate, passing a mutable reference to it.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.retain_mut(|x| if *x <= 3 {
    ///     *x += 1;
    ///     true
    /// } else {
    ///     false
    /// });
    /// assert_eq!(vec, [2, 3, 4]);
    /// ```
    #[stable(feature = "vec_retain_mut", since = "1.61.0")]
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let original_len = self.len();

        #[cfg(kani)]
        let modified_items = if mem::size_of::<T>() == 0 {
            core::ptr::slice_from_raw_parts_mut(core::ptr::null_mut::<T>(), 0)
        } else {
            core::ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), original_len)
        };

        if original_len == 0 {
            // Empty case: explicit return allows better optimization, vs letting compiler infer it
            return;
        }

        // Vec: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
        //      |            ^- write                ^- read             |
        //      |<-              original_len                          ->|
        // Kept: Elements which predicate returns true on.
        // Hole: Moved or dropped element slot.
        // Unchecked: Unchecked valid elements.
        //
        // This drop guard will be invoked when predicate or `drop` of element panicked.
        // It shifts unchecked elements to cover holes and `set_len` to the correct length.
        // In cases when predicate and `drop` never panick, it will be optimized out.
        struct PanicGuard<'a, T, A: Allocator> {
            v: &'a mut Vec<T, A>,
            read: usize,
            write: usize,
            original_len: usize,
        }

        impl<T, A: Allocator> Drop for PanicGuard<'_, T, A> {
            #[cold]
            fn drop(&mut self) {
                let remaining = self.original_len - self.read;
                // SAFETY: Trailing unchecked items must be valid since we never touch them.
                unsafe {
                    ptr::copy(
                        self.v.as_ptr().add(self.read),
                        self.v.as_mut_ptr().add(self.write),
                        remaining,
                    );
                }
                // SAFETY: After filling holes, all items are in contiguous memory.
                unsafe {
                    self.v.set_len(self.write + remaining);
                }
            }
        }

        let mut read = 0;
        #[safety::loop_invariant(read < original_len && self.len == original_len)]
        #[cfg_attr(kani, kani::loop_modifies(&read, modified_items))]
        loop {
            // SAFETY: read < original_len
            let cur = unsafe { self.get_unchecked_mut(read) };
            if hint::unlikely(!f(cur)) {
                break;
            }
            read += 1;
            if read == original_len {
                // All elements are kept, return early.
                return;
            }
        }

        // Critical section starts here and at least one element is going to be removed.
        // Advance `g.read` early to avoid double drop if `drop_in_place` panicked.
        let mut g = PanicGuard { v: self, read: read + 1, write: read, original_len };
        // SAFETY: previous `read` is always less than original_len.
        unsafe { ptr::drop_in_place(&mut *g.v.as_mut_ptr().add(read)) };

        #[safety::loop_invariant(g.write < g.read && g.read <= g.original_len && g.v.len == g.original_len)]
        #[cfg_attr(kani, kani::loop_modifies(&g.read, &g.write, modified_items))]
        while g.read < g.original_len {
            // SAFETY: `read` is always less than original_len.
            let cur = unsafe { &mut *g.v.as_mut_ptr().add(g.read) };
            if !f(cur) {
                // Advance `read` early to avoid double drop if `drop_in_place` panicked.
                g.read += 1;
                // SAFETY: We never touch this element again after dropped.
                unsafe { ptr::drop_in_place(cur) };
            } else {
                // SAFETY: `read` > `write`, so the slots don't overlap.
                // We use copy for move, and never touch the source element again.
                unsafe {
                    let hole = g.v.as_mut_ptr().add(g.write);
                    ptr::copy_nonoverlapping(cur, hole, 1);
                }
                g.write += 1;
                g.read += 1;
            }
        }

        // We are leaving the critical section and no panic happened,
        // Commit the length change and forget the guard.
        // SAFETY: `write` is always less than or equal to original_len.
        unsafe { g.v.set_len(g.write) };
        mem::forget(g);
    }

    /// Removes all but the first of consecutive elements in the vector that resolve to the same
    /// key.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![10, 20, 21, 30, 20];
    ///
    /// vec.dedup_by_key(|i| *i / 10);
    ///
    /// assert_eq!(vec, [10, 20, 30, 20]);
    /// ```
    #[stable(feature = "dedup_by", since = "1.16.0")]
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, mut key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.dedup_by(|a, b| key(a) == key(b))
    }

    /// Removes all but the first of consecutive elements in the vector satisfying a given equality
    /// relation.
    ///
    /// The `same_bucket` function is passed references to two elements from the vector and
    /// must determine if the elements compare equal. The elements are passed in opposite order
    /// from their order in the slice, so if `same_bucket(a, b)` returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec!["foo", "bar", "Bar", "baz", "bar"];
    ///
    /// vec.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
    ///
    /// assert_eq!(vec, ["foo", "bar", "baz", "bar"]);
    /// ```
    #[stable(feature = "dedup_by", since = "1.16.0")]
    pub fn dedup_by<F>(&mut self, mut same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        let len = self.len();
        if len <= 1 {
            return;
        }

        // Check if we ever want to remove anything.
        // This allows to use copy_non_overlapping in next cycle.
        // And avoids any memory writes if we don't need to remove anything.
        let mut first_duplicate_idx: usize = 1;
        let start = self.as_mut_ptr();
        #[cfg(kani)]
        let capacity = self.capacity();
        #[cfg(kani)]
        let modified_items = if mem::size_of::<T>() == 0 {
            core::ptr::slice_from_raw_parts_mut(core::ptr::null_mut::<T>(), 0)
        } else {
            core::ptr::slice_from_raw_parts_mut(start, len)
        };

        #[safety::loop_invariant(len <= capacity && first_duplicate_idx >= 1 && first_duplicate_idx <= len)]
        while first_duplicate_idx != len {
            let found_duplicate = unsafe {
                // SAFETY: first_duplicate always in range [1..len)
                // Note that we start iteration from 1 so we never overflow.
                let prev = start.add(first_duplicate_idx.wrapping_sub(1));
                let current = start.add(first_duplicate_idx);
                // We explicitly say in docs that references are reversed.
                same_bucket(&mut *current, &mut *prev)
            };
            if found_duplicate {
                break;
            }
            first_duplicate_idx += 1;
        }
        // Don't need to remove anything.
        // We cannot get bigger than len.
        if first_duplicate_idx == len {
            return;
        }

        /* INVARIANT: vec.len() > read > write > write-1 >= 0 */
        struct FillGapOnDrop<'a, T, A: core::alloc::Allocator> {
            /* Offset of the element we want to check if it is duplicate */
            read: usize,

            /* Offset of the place where we want to place the non-duplicate
             * when we find it. */
            write: usize,

            /* The Vec that would need correction if `same_bucket` panicked */
            vec: &'a mut Vec<T, A>,
        }

        impl<'a, T, A: core::alloc::Allocator> Drop for FillGapOnDrop<'a, T, A> {
            fn drop(&mut self) {
                /* This code gets executed when `same_bucket` panics */

                /* SAFETY: invariant guarantees that `read - write`
                 * and `len - read` never overflow and that the copy is always
                 * in-bounds. */
                unsafe {
                    let ptr = self.vec.as_mut_ptr();
                    let len = self.vec.len();

                    /* How many items were left when `same_bucket` panicked.
                     * Basically vec[read..].len() */
                    let items_left = len.wrapping_sub(self.read);

                    /* Pointer to first item in vec[write..write+items_left] slice */
                    let dropped_ptr = ptr.add(self.write);
                    /* Pointer to first item in vec[read..] slice */
                    let valid_ptr = ptr.add(self.read);

                    /* Copy `vec[read..]` to `vec[write..write+items_left]`.
                     * The slices can overlap, so `copy_nonoverlapping` cannot be used */
                    ptr::copy(valid_ptr, dropped_ptr, items_left);

                    /* How many items have been already dropped
                     * Basically vec[read..write].len() */
                    let dropped = self.read.wrapping_sub(self.write);

                    self.vec.set_len(len - dropped);
                }
            }
        }

        /* Drop items while going through Vec, it should be more efficient than
         * doing slice partition_dedup + truncate */

        // Construct gap first and then drop item to avoid memory corruption if `T::drop` panics.
        let mut gap =
            FillGapOnDrop { read: first_duplicate_idx + 1, write: first_duplicate_idx, vec: self };
        unsafe {
            // SAFETY: we checked that first_duplicate_idx in bounds before.
            // If drop panics, `gap` would remove this item without drop.
            ptr::drop_in_place(start.add(first_duplicate_idx));
        }

        // Kani-only reshaping of loop-local bindings.
        // The shipped second pass declares `read_ptr`, `prev_ptr`,
        // `found_duplicate`, and `write_ptr` inside the loop body. The pinned
        // Kani/CBMC loop-frame instrumentation requires mutable locals written by
        // the loop to be nameable from `loop_modifies`; body-local `let` bindings
        // cannot be named there and lead to assignability/frame failures.
        // Under `cfg(kani)` we therefore only extend the storage lifetime of those
        // temporaries (plus the indices used to derive their pointers). Every
        // temporary is overwritten with exactly the value computed by the shipped
        // statement before its first use. These helper values are integers, bools,
        // and raw pointers and have no drop behavior. Predicate calls, drops,
        // copies, length updates, branch conditions, and their ordering are
        // otherwise identical to the shipped implementation.
        // This is a loop-frame reshaping for the unbounded proof, not a different
        // deduplication algorithm.
        #[cfg(kani)]
        let mut found_duplicate = false;
        #[cfg(kani)]
        let mut read_idx = 0usize;
        #[cfg(kani)]
        let mut gap_prev_idx = 0usize;
        #[cfg(kani)]
        let mut write_idx = 0usize;
        #[cfg(kani)]
        let mut read_ptr = start;
        #[cfg(kani)]
        let mut prev_ptr = start;
        #[cfg(kani)]
        let mut write_ptr = start;

        /* SAFETY: Because of the invariant, read_ptr, prev_ptr and write_ptr
         * are always in-bounds and read_ptr never aliases prev_ptr */
        unsafe {
            #[safety::loop_invariant(
                len <= capacity
                    && first_duplicate_idx < len
                    && gap.vec.len == len
                    && gap.write > 0
                    && gap.write < gap.read
                    && gap.read <= len
            )]
            #[cfg_attr(
                kani,
                kani::loop_modifies(
                    &gap.read,
                    &gap.write,
                    &found_duplicate,
                    &read_idx,
                    &gap_prev_idx,
                    &write_idx,
                    &read_ptr,
                    &prev_ptr,
                    &write_ptr,
                    modified_items
                )
            )]
            while gap.read < len {
                #[cfg(not(kani))]
                let read_ptr = start.add(gap.read);
                #[cfg(kani)]
                {
                    read_idx = gap.read;
                    read_ptr = start.add(read_idx);
                }
                #[cfg(not(kani))]
                let prev_ptr = start.add(gap.write.wrapping_sub(1));
                #[cfg(kani)]
                {
                    gap_prev_idx = gap.write.wrapping_sub(1);
                    prev_ptr = start.add(gap_prev_idx);
                }

                // We explicitly say in docs that references are reversed.
                #[cfg(not(kani))]
                let found_duplicate = same_bucket(&mut *read_ptr, &mut *prev_ptr);
                #[cfg(kani)]
                {
                    found_duplicate = same_bucket(&mut *read_ptr, &mut *prev_ptr);
                }
                if found_duplicate {
                    // Increase `gap.read` now since the drop may panic.
                    gap.read += 1;
                    /* We have found duplicate, drop it in-place */
                    ptr::drop_in_place(read_ptr);
                } else {
                    #[cfg(not(kani))]
                    let write_ptr = start.add(gap.write);
                    #[cfg(kani)]
                    {
                        write_idx = gap.write;
                        write_ptr = start.add(write_idx);
                    }

                    /* read_ptr cannot be equal to write_ptr because at this point
                     * we guaranteed to skip at least one element (before loop starts).
                     */
                    ptr::copy_nonoverlapping(read_ptr, write_ptr, 1);

                    /* We have filled that place, so go further */
                    gap.write += 1;
                    gap.read += 1;
                }
            }

            /* Technically we could let `gap` clean up with its Drop, but
             * when `same_bucket` is guaranteed to not panic, this bloats a little
             * the codegen, so we just do it manually */
            gap.vec.set_len(gap.write);
            mem::forget(gap);
        }
    }

    /// Appends an element and returns a reference to it if there is sufficient spare capacity,
    /// otherwise an error is returned with the element.
    ///
    /// Unlike [`push`] this method will not reallocate when there's insufficient capacity.
    /// The caller should use [`reserve`] or [`try_reserve`] to ensure that there is enough capacity.
    ///
    /// [`push`]: Vec::push
    /// [`reserve`]: Vec::reserve
    /// [`try_reserve`]: Vec::try_reserve
    ///
    /// # Examples
    ///
    /// A manual, panic-free alternative to [`FromIterator`]:
    ///
    /// ```
    /// #![feature(vec_push_within_capacity)]
    ///
    /// use std::collections::TryReserveError;
    /// fn from_iter_fallible<T>(iter: impl Iterator<Item=T>) -> Result<Vec<T>, TryReserveError> {
    ///     let mut vec = Vec::new();
    ///     for value in iter {
    ///         if let Err(value) = vec.push_within_capacity(value) {
    ///             vec.try_reserve(1)?;
    ///             // this cannot fail, the previous line either returned or added at least 1 free slot
    ///             let _ = vec.push_within_capacity(value);
    ///         }
    ///     }
    ///     Ok(vec)
    /// }
    /// assert_eq!(from_iter_fallible(0..100), Ok(Vec::from_iter(0..100)));
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) time.
    #[inline]
    #[unstable(feature = "vec_push_within_capacity", issue = "100486")]
    pub fn push_within_capacity(&mut self, value: T) -> Result<&mut T, T> {
        if self.len == self.buf.capacity() {
            return Err(value);
        }

        unsafe {
            let end = self.as_mut_ptr().add(self.len);
            ptr::write(end, value);
            self.len += 1;

            // SAFETY: We just wrote a value to the pointer that will live the lifetime of the reference.
            Ok(&mut *end)
        }
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    ///
    /// If you'd like to pop the first element, consider using
    /// [`VecDeque::pop_front`] instead.
    ///
    /// [`VecDeque::pop_front`]: crate::collections::VecDeque::pop_front
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) time.
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_diagnostic_item = "vec_pop"]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                self.len -= 1;
                core::hint::assert_unchecked(self.len < self.capacity());
                Some(ptr::read(self.as_ptr().add(self.len())))
            }
        }
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the vector
    /// is empty (the predicate will not be called in that case).
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4];
    /// let pred = |x: &mut i32| *x % 2 == 0;
    ///
    /// assert_eq!(vec.pop_if(pred), Some(4));
    /// assert_eq!(vec, [1, 2, 3]);
    /// assert_eq!(vec.pop_if(pred), None);
    /// ```
    #[stable(feature = "vec_pop_if", since = "1.86.0")]
    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        let last = self.last_mut()?;
        if predicate(last) { self.pop() } else { None }
    }

    /// Returns a mutable reference to the last item in the vector, or
    /// `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(vec_peek_mut)]
    /// let mut vec = Vec::new();
    /// assert!(vec.peek_mut().is_none());
    ///
    /// vec.push(1);
    /// vec.push(5);
    /// vec.push(2);
    /// assert_eq!(vec.last(), Some(&2));
    /// if let Some(mut val) = vec.peek_mut() {
    ///     *val = 0;
    /// }
    /// assert_eq!(vec.last(), Some(&0));
    /// ```
    #[inline]
    #[unstable(feature = "vec_peek_mut", issue = "122742")]
    pub fn peek_mut(&mut self) -> Option<PeekMut<'_, T, A>> {
        PeekMut::new(self)
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// let mut vec2 = vec![4, 5, 6];
    /// vec.append(&mut vec2);
    /// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2, []);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "append", since = "1.4.0")]
    pub fn append(&mut self, other: &mut Self) {
        unsafe {
            self.append_elements(other.as_slice() as _);
            other.set_len(0);
        }
    }

    /// Appends elements to `self` from other buffer.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[requires({
        let count = other.len();
        count == 0
            || (ub_checks::can_dereference(other)
                && (mem::size_of::<T>() == 0
                    || !ub_checks::same_allocation(other as *const T, self.as_ptr())))
    })]
    unsafe fn append_elements(&mut self, other: *const [T]) {
        let count = other.len();
        self.reserve(count);
        let len = self.len();
        if count > 0 {
            unsafe {
                ptr::copy_nonoverlapping(other as *const T, self.as_mut_ptr().add(len), count)
            };
        }
        self.len += count;
    }

    /// Removes the subslice indicated by the given range from the vector,
    /// returning a double-ended iterator over the removed subslice.
    ///
    /// If the iterator is dropped before being fully consumed,
    /// it drops the remaining removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the vector to optimize
    /// its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and past the length of the vector.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`mem::forget`], for example), the vector may have lost and leaked
    /// elements arbitrarily, including elements outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec![1, 2, 3];
    /// let u: Vec<_> = v.drain(1..).collect();
    /// assert_eq!(v, &[1]);
    /// assert_eq!(u, &[2, 3]);
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, &[]);
    /// ```
    #[stable(feature = "drain", since = "1.6.0")]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // When the Drain is first created, it shortens the length of
        // the source vector to make sure no uninitialized or moved-from elements
        // are accessible at all if the Drain's destructor never gets to run.
        //
        // Drain will ptr::read out the values to remove.
        // When finished, remaining tail of the vec is copied back to cover
        // the hole, and the vector length is restored to the new length.
        //
        let len = self.len();
        let Range { start, end } = slice::range(range, ..len);

        unsafe {
            // set self.vec length's to start, to be safe in case Drain is leaked
            self.set_len(start);
            let range_slice = slice::from_raw_parts(self.as_ptr().add(start), end - start);
            Drain {
                tail_start: end,
                tail_len: len - end,
                iter: range_slice.iter(),
                vec: NonNull::from(self),
            }
        }
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec![1, 2, 3];
    ///
    /// v.clear();
    ///
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn clear(&mut self) {
        let elems: *mut [T] = self.as_mut_slice();

        // SAFETY:
        // - `elems` comes directly from `as_mut_slice` and is therefore valid.
        // - Setting `self.len` before calling `drop_in_place` means that,
        //   if an element's `Drop` impl panics, the vector's `Drop` impl will
        //   do nothing (leaking the rest of the elements) instead of dropping
        //   some twice.
        unsafe {
            self.len = 0;
            ptr::drop_in_place(elems);
        }
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = vec![1, 2, 3];
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    #[rustc_confusables("length", "size")]
    pub const fn len(&self) -> usize {
        let len = self.len;

        // SAFETY: The maximum capacity of `Vec<T>` is `isize::MAX` bytes, so the maximum value can
        // be returned is `usize::checked_div(size_of::<T>()).unwrap_or(usize::MAX)`, which
        // matches the definition of `T::MAX_SLICE_LEN`.
        unsafe { intrinsics::assume(len <= T::MAX_SLICE_LEN) };

        len
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = Vec::new();
    /// assert!(v.is_empty());
    ///
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_diagnostic_item = "vec_is_empty"]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated vector containing the elements in the range
    /// `[at, len)`. After the call, the original vector will be left containing
    /// the elements `[0, at)` with its previous capacity unchanged.
    ///
    /// - If you want to take ownership of the entire contents and capacity of
    ///   the vector, see [`mem::take`] or [`mem::replace`].
    /// - If you don't need the returned vector at all, see [`Vec::truncate`].
    /// - If you want to take ownership of an arbitrary subslice, or you don't
    ///   necessarily want to store the removed items in a vector, see [`Vec::drain`].
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec!['a', 'b', 'c'];
    /// let vec2 = vec.split_off(1);
    /// assert_eq!(vec, ['a']);
    /// assert_eq!(vec2, ['b', 'c']);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    #[stable(feature = "split_off", since = "1.4.0")]
    #[track_caller]
    pub fn split_off(&mut self, at: usize) -> Self
    where
        A: Clone,
    {
        #[cold]
        #[cfg_attr(not(panic = "immediate-abort"), inline(never))]
        #[track_caller]
        #[optimize(size)]
        fn assert_failed(at: usize, len: usize) -> ! {
            panic!("`at` split index (is {at}) should be <= len (is {len})");
        }

        if at > self.len() {
            assert_failed(at, self.len());
        }

        let other_len = self.len - at;
        let mut other = Vec::with_capacity_in(other_len, self.allocator().clone());

        // Unsafely `set_len` and copy items to `other`.
        unsafe {
            self.set_len(at);
            other.set_len(other_len);

            ptr::copy_nonoverlapping(self.as_ptr().add(at), other.as_mut_ptr(), other.len());
        }
        other
    }

    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the
    /// difference, with each additional slot filled with the result of
    /// calling the closure `f`. The return values from `f` will end up
    /// in the `Vec` in the order they have been generated.
    ///
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// This method uses a closure to create new values on every push. If
    /// you'd rather [`Clone`] a given value, use [`Vec::resize`]. If you
    /// want to use the [`Default`] trait to generate values, you can
    /// pass [`Default::default`] as the second argument.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// vec.resize_with(5, Default::default);
    /// assert_eq!(vec, [1, 2, 3, 0, 0]);
    ///
    /// let mut vec = vec![];
    /// let mut p = 1;
    /// vec.resize_with(4, || { p *= 2; p });
    /// assert_eq!(vec, [2, 4, 8, 16]);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "vec_resize_with", since = "1.33.0")]
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
    {
        let len = self.len();
        if new_len > len {
            self.extend_trusted(iter::repeat_with(f).take(new_len - len));
        } else {
            self.truncate(new_len);
        }
    }

    /// Consumes and leaks the `Vec`, returning a mutable reference to the contents,
    /// `&'a mut [T]`.
    ///
    /// Note that the type `T` must outlive the chosen lifetime `'a`. If the type
    /// has only static references, or none at all, then this may be chosen to be
    /// `'static`.
    ///
    /// As of Rust 1.57, this method does not reallocate or shrink the `Vec`,
    /// so the leaked allocation may include unused capacity that is not part
    /// of the returned slice.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak.
    ///
    /// # Examples
    ///
    /// Simple usage:
    ///
    /// ```
    /// let x = vec![1, 2, 3];
    /// let static_ref: &'static mut [usize] = x.leak();
    /// static_ref[0] += 1;
    /// assert_eq!(static_ref, &[2, 2, 3]);
    /// # // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// # // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// # drop(unsafe { Box::from_raw(static_ref) });
    /// ```
    #[stable(feature = "vec_leak", since = "1.47.0")]
    #[inline]
    pub fn leak<'a>(self) -> &'a mut [T]
    where
        A: 'a,
    {
        let mut me = ManuallyDrop::new(self);
        unsafe { slice::from_raw_parts_mut(me.as_mut_ptr(), me.len) }
    }

    /// Returns the remaining spare capacity of the vector as a slice of
    /// `MaybeUninit<T>`.
    ///
    /// The returned slice can be used to fill the vector with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// [`set_len`] method.
    ///
    /// [`set_len`]: Vec::set_len
    ///
    /// # Examples
    ///
    /// ```
    /// // Allocate vector big enough for 10 elements.
    /// let mut v = Vec::with_capacity(10);
    ///
    /// // Fill in the first 3 elements.
    /// let uninit = v.spare_capacity_mut();
    /// uninit[0].write(0);
    /// uninit[1].write(1);
    /// uninit[2].write(2);
    ///
    /// // Mark the first 3 elements of the vector as being initialized.
    /// unsafe {
    ///     v.set_len(3);
    /// }
    ///
    /// assert_eq!(&v, &[0, 1, 2]);
    /// ```
    #[stable(feature = "vec_spare_capacity", since = "1.60.0")]
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        // Note:
        // This method is not implemented in terms of `split_at_spare_mut`,
        // to prevent invalidation of pointers to the buffer.
        unsafe {
            slice::from_raw_parts_mut(
                self.as_mut_ptr().add(self.len) as *mut MaybeUninit<T>,
                self.buf.capacity() - self.len,
            )
        }
    }

    /// Returns vector content as a slice of `T`, along with the remaining spare
    /// capacity of the vector as a slice of `MaybeUninit<T>`.
    ///
    /// The returned spare capacity slice can be used to fill the vector with data
    /// (e.g. by reading from a file) before marking the data as initialized using
    /// the [`set_len`] method.
    ///
    /// [`set_len`]: Vec::set_len
    ///
    /// Note that this is a low-level API, which should be used with care for
    /// optimization purposes. If you need to append data to a `Vec`
    /// you can use [`push`], [`extend`], [`extend_from_slice`],
    /// [`extend_from_within`], [`insert`], [`append`], [`resize`] or
    /// [`resize_with`], depending on your exact needs.
    ///
    /// [`push`]: Vec::push
    /// [`extend`]: Vec::extend
    /// [`extend_from_slice`]: Vec::extend_from_slice
    /// [`extend_from_within`]: Vec::extend_from_within
    /// [`insert`]: Vec::insert
    /// [`append`]: Vec::append
    /// [`resize`]: Vec::resize
    /// [`resize_with`]: Vec::resize_with
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(vec_split_at_spare)]
    ///
    /// let mut v = vec![1, 1, 2];
    ///
    /// // Reserve additional space big enough for 10 elements.
    /// v.reserve(10);
    ///
    /// let (init, uninit) = v.split_at_spare_mut();
    /// let sum = init.iter().copied().sum::<u32>();
    ///
    /// // Fill in the next 4 elements.
    /// uninit[0].write(sum);
    /// uninit[1].write(sum * 2);
    /// uninit[2].write(sum * 3);
    /// uninit[3].write(sum * 4);
    ///
    /// // Mark the 4 elements of the vector as being initialized.
    /// unsafe {
    ///     let len = v.len();
    ///     v.set_len(len + 4);
    /// }
    ///
    /// assert_eq!(&v, &[1, 1, 2, 4, 8, 12, 16]);
    /// ```
    #[unstable(feature = "vec_split_at_spare", issue = "81944")]
    #[inline]
    pub fn split_at_spare_mut(&mut self) -> (&mut [T], &mut [MaybeUninit<T>]) {
        // SAFETY:
        // - len is ignored and so never changed
        let (init, spare, _) = unsafe { self.split_at_spare_mut_with_len() };
        (init, spare)
    }

    /// Safety: changing returned .2 (&mut usize) is considered the same as calling `.set_len(_)`.
    ///
    /// This method provides unique access to all vec parts at once in `extend_from_within`.
    #[ensures(|result| *result.2 == old(self.len()))]
    #[ensures(|result| {
        result.0.len() == old(self.len())
            && result.1.len() == old(self.capacity()) - old(self.len())
    })]
    #[ensures(|result| {
            core::ptr::from_ref(&*result.2) == old(core::ptr::addr_of!(self.len))
        })] // RQ-1
    #[ensures(|result| {
        result.0.as_ptr() == old(self.as_ptr())
            && result.1.as_ptr()
                == old(self.as_ptr()).wrapping_add(result.0.len()).cast::<MaybeUninit<T>>()
    })]
    unsafe fn split_at_spare_mut_with_len(
        &mut self,
    ) -> (&mut [T], &mut [MaybeUninit<T>], &mut usize) {
        let ptr = self.as_mut_ptr();
        // SAFETY:
        // - `ptr` is guaranteed to be valid for `self.len` elements
        // - but the allocation extends out to `self.buf.capacity()` elements, possibly
        // uninitialized
        let spare_ptr = unsafe { ptr.add(self.len) };
        let spare_ptr = spare_ptr.cast_uninit();
        let spare_len = self.buf.capacity() - self.len;

        // SAFETY:
        // - `ptr` is guaranteed to be valid for `self.len` elements
        // - `spare_ptr` is pointing one element past the buffer, so it doesn't overlap with `initialized`
        unsafe {
            let initialized = slice::from_raw_parts_mut(ptr, self.len);
            let spare = slice::from_raw_parts_mut(spare_ptr, spare_len);

            (initialized, spare, &mut self.len)
        }
    }

    /// Groups every `N` elements in the `Vec<T>` into chunks to produce a `Vec<[T; N]>`, dropping
    /// elements in the remainder. `N` must be greater than zero.
    ///
    /// If the capacity is not a multiple of the chunk size, the buffer will shrink down to the
    /// nearest multiple with a reallocation or deallocation.
    ///
    /// This function can be used to reverse [`Vec::into_flattened`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(vec_into_chunks)]
    ///
    /// let vec = vec![0, 1, 2, 3, 4, 5, 6, 7];
    /// assert_eq!(vec.into_chunks::<3>(), [[0, 1, 2], [3, 4, 5]]);
    ///
    /// let vec = vec![0, 1, 2, 3];
    /// let chunks: Vec<[u8; 10]> = vec.into_chunks();
    /// assert!(chunks.is_empty());
    ///
    /// let flat = vec![0; 8 * 8 * 8];
    /// let reshaped: Vec<[[[u8; 8]; 8]; 8]> = flat.into_chunks().into_chunks().into_chunks();
    /// assert_eq!(reshaped.len(), 1);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "vec_into_chunks", issue = "142137")]
    pub fn into_chunks<const N: usize>(mut self) -> Vec<[T; N], A> {
        const {
            assert!(N != 0, "chunk size must be greater than zero");
        }

        let (len, cap) = (self.len(), self.capacity());

        let len_remainder = len % N;
        if len_remainder != 0 {
            self.truncate(len - len_remainder);
        }

        let cap_remainder = cap % N;
        if !T::IS_ZST && cap_remainder != 0 {
            self.buf.shrink_to_fit(cap - cap_remainder);
        }

        let (ptr, _, _, alloc) = self.into_raw_parts_with_alloc();

        // SAFETY:
        // - `ptr` and `alloc` were just returned from `self.into_raw_parts_with_alloc()`
        // - `[T; N]` has the same alignment as `T`
        // - `size_of::<[T; N]>() * cap / N == size_of::<T>() * cap`
        // - `len / N <= cap / N` because `len <= cap`
        // - the allocated memory consists of `len / N` valid values of type `[T; N]`
        // - `cap / N` fits the size of the allocated memory after shrinking
        unsafe { Vec::from_raw_parts_in(ptr.cast(), len / N, cap / N, alloc) }
    }

    /// This clears out this `Vec` and recycles the allocation into a new `Vec`.
    /// The item type of the resulting `Vec` needs to have the same size and
    /// alignment as the item type of the original `Vec`.
    ///
    /// # Examples
    ///
    ///  ```
    /// #![feature(vec_recycle, transmutability)]
    /// let a: Vec<u8> = vec![0; 100];
    /// let capacity = a.capacity();
    /// let addr = a.as_ptr().addr();
    /// let b: Vec<i8> = a.recycle();
    /// assert_eq!(b.len(), 0);
    /// assert_eq!(b.capacity(), capacity);
    /// assert_eq!(b.as_ptr().addr(), addr);
    /// ```
    ///
    /// The `Recyclable` bound prevents this method from being called when `T` and `U` have different sizes; e.g.:
    ///
    ///  ```compile_fail,E0277
    /// #![feature(vec_recycle, transmutability)]
    /// let vec: Vec<[u8; 2]> = Vec::new();
    /// let _: Vec<[u8; 1]> = vec.recycle();
    /// ```
    /// ...or different alignments:
    ///
    ///  ```compile_fail,E0277
    /// #![feature(vec_recycle, transmutability)]
    /// let vec: Vec<[u16; 0]> = Vec::new();
    /// let _: Vec<[u8; 0]> = vec.recycle();
    /// ```
    ///
    /// However, due to temporary implementation limitations of `Recyclable`,
    /// this method is not yet callable when `T` or `U` are slices, trait objects,
    /// or other exotic types; e.g.:
    ///
    /// ```compile_fail,E0277
    /// #![feature(vec_recycle, transmutability)]
    /// # let inputs = ["a b c", "d e f"];
    /// # fn process(_: &[&str]) {}
    /// let mut storage: Vec<&[&str]> = Vec::new();
    ///
    /// for input in inputs {
    ///     let mut buffer: Vec<&str> = storage.recycle();
    ///     buffer.extend(input.split(" "));
    ///     process(&buffer);
    ///     storage = buffer.recycle();
    /// }
    /// ```
    #[unstable(feature = "vec_recycle", issue = "148227")]
    #[expect(private_bounds)]
    pub fn recycle<U>(mut self) -> Vec<U, A>
    where
        U: Recyclable<T>,
    {
        self.clear();
        const {
            // FIXME(const-hack, 146097): compare `Layout`s
            assert!(size_of::<T>() == size_of::<U>());
            assert!(align_of::<T>() == align_of::<U>());
        };
        let (ptr, length, capacity, alloc) = self.into_parts_with_alloc();
        debug_assert_eq!(length, 0);
        // SAFETY:
        // - `ptr` and `alloc` were just returned from `self.into_raw_parts_with_alloc()`
        // - `T` & `U` have the same layout, so `capacity` does not need to be changed and we can safely use `alloc.dealloc` later
        // - the original vector was cleared, so there is no problem with "transmuting" the stored values
        unsafe { Vec::from_parts_in(ptr.cast::<U>(), length, capacity, alloc) }
    }
}

/// Denotes that an allocation of `From` can be recycled into an allocation of `Self`.
///
/// # Safety
///
/// `Self` is `Recyclable<From>` if `Layout::new::<Self>() == Layout::new::<From>()`.
unsafe trait Recyclable<From: Sized>: Sized {}

#[unstable_feature_bound(transmutability)]
// SAFETY: enforced by `TransmuteFrom`
unsafe impl<From, To> Recyclable<From> for To
where
    for<'a> &'a MaybeUninit<To>: TransmuteFrom<&'a MaybeUninit<From>, { Assume::SAFETY }>,
    for<'a> &'a MaybeUninit<From>: TransmuteFrom<&'a MaybeUninit<To>, { Assume::SAFETY }>,
{
}

impl<T: Clone, A: Allocator> Vec<T, A> {
    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// This method requires `T` to implement [`Clone`],
    /// in order to be able to clone the passed value.
    /// If you need more flexibility (or want to rely on [`Default`] instead of
    /// [`Clone`]), use [`Vec::resize_with`].
    /// If you only need to resize to a smaller size, use [`Vec::truncate`].
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec!["hello"];
    /// vec.resize(3, "world");
    /// assert_eq!(vec, ["hello", "world", "world"]);
    ///
    /// let mut vec = vec!['a', 'b', 'c', 'd'];
    /// vec.resize(2, '_');
    /// assert_eq!(vec, ['a', 'b']);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "vec_resize", since = "1.5.0")]
    pub fn resize(&mut self, new_len: usize, value: T) {
        let len = self.len();

        if new_len > len {
            self.extend_with(new_len - len, value)
        } else {
            self.truncate(new_len);
        }
    }

    /// Clones and appends all elements in a slice to the `Vec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `Vec`. The `other` slice is traversed in-order.
    ///
    /// Note that this function is the same as [`extend`],
    /// except that it also works with slice elements that are Clone but not Copy.
    /// If Rust gets specialization this function may be deprecated.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1];
    /// vec.extend_from_slice(&[2, 3, 4]);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend`]: Vec::extend
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "vec_extend_from_slice", since = "1.6.0")]
    pub fn extend_from_slice(&mut self, other: &[T]) {
        self.spec_extend(other.iter())
    }

    /// Given a range `src`, clones a slice of elements in that range and appends it to the end.
    ///
    /// `src` must be a range that can form a valid subslice of the `Vec`.
    ///
    /// # Panics
    ///
    /// Panics if starting index is greater than the end index, if the index is
    /// greater than the length of the vector, or if the new capacity exceeds
    /// `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut characters = vec!['a', 'b', 'c', 'd', 'e'];
    /// characters.extend_from_within(2..);
    /// assert_eq!(characters, ['a', 'b', 'c', 'd', 'e', 'c', 'd', 'e']);
    ///
    /// let mut numbers = vec![0, 1, 2, 3, 4];
    /// numbers.extend_from_within(..2);
    /// assert_eq!(numbers, [0, 1, 2, 3, 4, 0, 1]);
    ///
    /// let mut strings = vec![String::from("hello"), String::from("world"), String::from("!")];
    /// strings.extend_from_within(1..=2);
    /// assert_eq!(strings, ["hello", "world", "!", "world", "!"]);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "vec_extend_from_within", since = "1.53.0")]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
    {
        let range = slice::range(src, ..self.len());
        self.reserve(range.len());

        // SAFETY:
        // - `slice::range` guarantees that the given range is valid for indexing self
        unsafe {
            self.spec_extend_from_within(range);
        }
    }
}

impl<T, A: Allocator, const N: usize> Vec<[T; N], A> {
    /// Takes a `Vec<[T; N]>` and flattens it into a `Vec<T>`.
    ///
    /// # Panics
    ///
    /// Panics if the length of the resulting vector would overflow a `usize`.
    ///
    /// This is only possible when flattening a vector of arrays of zero-sized
    /// types, and thus tends to be irrelevant in practice. If
    /// `size_of::<T>() > 0`, this will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![[1, 2, 3], [4, 5, 6], [7, 8, 9]];
    /// assert_eq!(vec.pop(), Some([7, 8, 9]));
    ///
    /// let mut flattened = vec.into_flattened();
    /// assert_eq!(flattened.pop(), Some(6));
    /// ```
    #[stable(feature = "slice_flatten", since = "1.80.0")]
    pub fn into_flattened(self) -> Vec<T, A> {
        let (ptr, len, cap, alloc) = self.into_raw_parts_with_alloc();
        let (new_len, new_cap) = if T::IS_ZST {
            (len.checked_mul(N).expect("vec len overflow"), usize::MAX)
        } else {
            // SAFETY:
            // - `cap * N` cannot overflow because the allocation is already in
            // the address space.
            // - Each `[T; N]` has `N` valid elements, so there are `len * N`
            // valid elements in the allocation.
            unsafe { (len.unchecked_mul(N), cap.unchecked_mul(N)) }
        };
        // SAFETY:
        // - `ptr` was allocated by `self`
        // - `ptr` is well-aligned because `[T; N]` has the same alignment as `T`.
        // - `new_cap` refers to the same sized allocation as `cap` because
        // `new_cap * size_of::<T>()` == `cap * size_of::<[T; N]>()`
        // - `len` <= `cap`, so `len * N` <= `cap * N`.
        unsafe { Vec::<T, A>::from_raw_parts_in(ptr.cast(), new_len, new_cap, alloc) }
    }
}

impl<T: Clone, A: Allocator> Vec<T, A> {
    #[cfg(not(no_global_oom_handling))]
    /// Extend the vector by `n` clones of value.
    fn extend_with(&mut self, n: usize, value: T) {
        self.reserve(n);

        unsafe {
            let mut ptr = self.as_mut_ptr().add(self.len());
            #[cfg(kani)]
            let old_len = self.len();

            #[cfg(kani)]
            let cap = self.capacity();

            #[cfg(kani)]
            let spare_start = ptr;

            #[cfg(kani)]
            let clone_count = if n == 0 { 0 } else { n - 1 };

            // Use SetLenOnDrop to work around bug where compiler
            // might not realize the store through `ptr` through self.set_len()
            // don't alias.
            let mut local_len = SetLenOnDrop::new(&mut self.len);

            #[cfg(kani)]
            let local_len_ptr = local_len.local_len_ptr();

            #[cfg(kani)]
            let spare_write_set = if mem::size_of::<T>() == 0 || clone_count == 0 {
                core::ptr::slice_from_raw_parts_mut(core::ptr::null_mut::<T>(), 0)
            } else {
                core::ptr::slice_from_raw_parts_mut(spare_start, clone_count)
            };

            #[cfg(kani)]
            if mem::size_of::<T>() != 0 && clone_count != 0 {
                assert!(ub_checks::can_write(spare_write_set));
            }

            // Shipped implementation.
            #[cfg(not(kani))]
            // Write all elements except the last one
            for _ in 1..n {
                ptr::write(ptr, value.clone());
                ptr = ptr.add(1);

                // Increment the length in every step in case clone() panics
                local_len.increment_len(1);
            }

            // Kani-only loop transcription for the unbounded loop-contract proof.
            // The shipped loop is:
            //     for _ in 1..n {
            //         write(value.clone());
            //         advance pointer;
            //         increment SetLenOnDrop;
            //     }
            //
            // For `n > 0` it therefore performs exactly `n - 1` clone/write/length
            // updates; for `n == 0` it performs none. At the pinned Kani version,
            // attaching a contract to this exact `1..n` range is unsuitable: Kani
            // rewrites contracted `for` loops through its verifier iterator/index model,
            // whose representation of the `n == 0` `1..n` case and hidden mutable state
            // make the required frame problematic.
            // The Kani branch instead counts `written` from zero to
            // `clone_count = if n == 0 { 0 } else { n - 1 }` and writes
            // `spare_start.add(written)`. This performs the same clone/write/
            // SetLenOnDrop update sequence. After the contracted loop `ptr` is set to
            // the position that the shipped pointer-increment loop would have reached;
            // the final write of the original `value` is shared by both builds.
            // No memory-safety property is assumed by the transcription: the writable
            // spare range is checked with `assert!`.
            #[cfg(kani)]
            {
                let mut written = 0usize;

                #[safety::loop_invariant(
                    old_len <= cap
                        && n <= cap - old_len
                        && clone_count <= n
                        && written <= clone_count
                        && written <= cap - old_len
                        && unsafe {
                            *local_len_ptr == old_len + written
                        }
                )]
                #[kani::loop_modifies(
                    &written,
                    local_len_ptr,
                    spare_write_set
                )]
                while written < clone_count {
                    ptr::write(spare_start.add(written), value.clone());

                    // Increment the length in every step in case clone() panics
                    local_len.increment_len(1);
                    written += 1;
                }

                // Match the pointer position produced by the shipped `for` loop.
                // Keep this outside the contracted loop so `ptr` does not need to
                // be part of the induction state.
                ptr = spare_start.add(clone_count);
            }

            if n > 0 {
                // We can write the last element directly without cloning needlessly
                ptr::write(ptr, value);
                local_len.increment_len(1);
            }

            // len set by scope guard
        }
    }
}

impl<T: PartialEq, A: Allocator> Vec<T, A> {
    /// Removes consecutive repeated elements in the vector according to the
    /// [`PartialEq`] trait implementation.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 2, 3, 2];
    ///
    /// vec.dedup();
    ///
    /// assert_eq!(vec, [1, 2, 3, 2]);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn dedup(&mut self) {
        self.dedup_by(|a, b| a == b)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Internal methods and functions
////////////////////////////////////////////////////////////////////////////////

#[doc(hidden)]
#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_diagnostic_item = "vec_from_elem"]
pub fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T> {
    <T as SpecFromElem>::from_elem(elem, n, Global)
}

#[doc(hidden)]
#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "allocator_api", issue = "32838")]
pub fn from_elem_in<T: Clone, A: Allocator>(elem: T, n: usize, alloc: A) -> Vec<T, A> {
    <T as SpecFromElem>::from_elem(elem, n, alloc)
}

#[cfg(not(no_global_oom_handling))]
trait ExtendFromWithinSpec {
    /// # Safety
    ///
    /// - `src` needs to be valid index
    /// - `self.capacity() - self.len()` must be `>= src.len()`
    unsafe fn spec_extend_from_within(&mut self, src: Range<usize>);
}

#[cfg(not(no_global_oom_handling))]
impl<T: Clone, A: Allocator> ExtendFromWithinSpec for Vec<T, A> {
    default unsafe fn spec_extend_from_within(&mut self, src: Range<usize>) {
        // SAFETY:
        // - len is increased only after initializing elements
        let (this, spare, len) = unsafe { self.split_at_spare_mut_with_len() };

        // SAFETY:
        // - caller guarantees that src is a valid index
        let to_clone = unsafe { this.get_unchecked(src) };

        iter::zip(to_clone, spare)
            .map(|(src, dst)| dst.write(src.clone()))
            // Note:
            // - Element was just initialized with `MaybeUninit::write`, so it's ok to increase len
            // - len is increased after each element to prevent leaks (see issue #82533)
            .for_each(|_| *len += 1);
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: TrivialClone, A: Allocator> ExtendFromWithinSpec for Vec<T, A> {
    unsafe fn spec_extend_from_within(&mut self, src: Range<usize>) {
        let count = src.len();
        {
            let (init, spare) = self.split_at_spare_mut();

            // SAFETY:
            // - caller guarantees that `src` is a valid index
            let source = unsafe { init.get_unchecked(src) };

            // SAFETY:
            // - Both pointers are created from unique slice references (`&mut [_]`)
            //   so they are valid and do not overlap.
            // - Elements implement `TrivialClone` so this is equivalent to calling
            //   `clone` on every one of them.
            // - `count` is equal to the len of `source`, so source is valid for
            //   `count` reads
            // - `.reserve(count)` guarantees that `spare.len() >= count` so spare
            //   is valid for `count` writes
            unsafe { ptr::copy_nonoverlapping(source.as_ptr(), spare.as_mut_ptr() as _, count) };
        }

        // SAFETY:
        // - The elements were just initialized by `copy_nonoverlapping`
        self.len += count;
    }
}

////////////////////////////////////////////////////////////////////////////////
// Common trait implementations for Vec
////////////////////////////////////////////////////////////////////////////////

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> ops::Deref for Vec<T, A> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> ops::DerefMut for Vec<T, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

#[unstable(feature = "deref_pure_trait", issue = "87121")]
unsafe impl<T, A: Allocator> ops::DerefPure for Vec<T, A> {}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone, A: Allocator + Clone> Clone for Vec<T, A> {
    fn clone(&self) -> Self {
        let alloc = self.allocator().clone();
        <[T]>::to_vec_in(&**self, alloc)
    }

    /// Overwrites the contents of `self` with a clone of the contents of `source`.
    ///
    /// This method is preferred over simply assigning `source.clone()` to `self`,
    /// as it avoids reallocation if possible. Additionally, if the element type
    /// `T` overrides `clone_from()`, this will reuse the resources of `self`'s
    /// elements as well.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = vec![5, 6, 7];
    /// let mut y = vec![8, 9, 10];
    /// let yp: *const i32 = y.as_ptr();
    ///
    /// y.clone_from(&x);
    ///
    /// // The value is the same
    /// assert_eq!(x, y);
    ///
    /// // And no reallocation occurred
    /// assert_eq!(yp, y.as_ptr());
    /// ```
    fn clone_from(&mut self, source: &Self) {
        crate::slice::SpecCloneIntoVec::clone_into(source.as_slice(), self);
    }
}

/// The hash of a vector is the same as that of the corresponding slice,
/// as required by the `core::borrow::Borrow` implementation.
///
/// ```
/// use std::hash::BuildHasher;
///
/// let b = std::hash::RandomState::new();
/// let v: Vec<u8> = vec![0xa8, 0x3c, 0x09];
/// let s: &[u8] = &[0xa8, 0x3c, 0x09];
/// assert_eq!(b.hash_one(v), b.hash_one(s));
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Hash, A: Allocator> Hash for Vec<T, A> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        Index::index(&**self, index)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, I: SliceIndex<[T]>, A: Allocator> IndexMut<I> for Vec<T, A> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(&mut **self, index)
    }
}

/// Collects an iterator into a Vec, commonly called via [`Iterator::collect()`]
///
/// # Allocation behavior
///
/// In general `Vec` does not guarantee any particular growth or allocation strategy.
/// That also applies to this trait impl.
///
/// **Note:** This section covers implementation details and is therefore exempt from
/// stability guarantees.
///
/// Vec may use any or none of the following strategies,
/// depending on the supplied iterator:
///
/// * preallocate based on [`Iterator::size_hint()`]
///   * and panic if the number of items is outside the provided lower/upper bounds
/// * use an amortized growth strategy similar to `pushing` one item at a time
/// * perform the iteration in-place on the original allocation backing the iterator
///
/// The last case warrants some attention. It is an optimization that in many cases reduces peak memory
/// consumption and improves cache locality. But when big, short-lived allocations are created,
/// only a small fraction of their items get collected, no further use is made of the spare capacity
/// and the resulting `Vec` is moved into a longer-lived structure, then this can lead to the large
/// allocations having their lifetimes unnecessarily extended which can result in increased memory
/// footprint.
///
/// In cases where this is an issue, the excess capacity can be discarded with [`Vec::shrink_to()`],
/// [`Vec::shrink_to_fit()`] or by collecting into [`Box<[T]>`][owned slice] instead, which additionally reduces
/// the size of the long-lived struct.
///
/// [owned slice]: Box
///
/// ```rust
/// # use std::sync::Mutex;
/// static LONG_LIVED: Mutex<Vec<Vec<u16>>> = Mutex::new(Vec::new());
///
/// for i in 0..10 {
///     let big_temporary: Vec<u16> = (0..1024).collect();
///     // discard most items
///     let mut result: Vec<_> = big_temporary.into_iter().filter(|i| i % 100 == 0).collect();
///     // without this a lot of unused capacity might be moved into the global
///     result.shrink_to_fit();
///     LONG_LIVED.lock().unwrap().push(result);
/// }
/// ```
#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T> FromIterator<T> for Vec<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Vec<T> {
        <Self as SpecFromIter<T, I::IntoIter>>::from_iter(iter.into_iter())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> IntoIterator for Vec<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Creates a consuming iterator, that is, one that moves each value out of
    /// the vector (from start to end). The vector cannot be used after calling
    /// this.
    ///
    /// # Examples
    ///
    /// ```
    /// let v = vec!["a".to_string(), "b".to_string()];
    /// let mut v_iter = v.into_iter();
    ///
    /// let first_element: Option<String> = v_iter.next();
    ///
    /// assert_eq!(first_element, Some("a".to_string()));
    /// assert_eq!(v_iter.next(), Some("b".to_string()));
    /// assert_eq!(v_iter.next(), None);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        unsafe {
            let me = ManuallyDrop::new(self);
            let alloc = ManuallyDrop::new(ptr::read(me.allocator()));
            let buf = me.buf.non_null();
            let begin = buf.as_ptr();
            let end = if T::IS_ZST {
                begin.wrapping_byte_add(me.len())
            } else {
                begin.add(me.len()) as *const T
            };
            let cap = me.buf.capacity();
            IntoIter { buf, phantom: PhantomData, cap, alloc, ptr: buf, end }
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, A: Allocator> IntoIterator for &'a mut Vec<T, A> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> Extend<T> for Vec<T, A> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        <Self as SpecExtend<T, I::IntoIter>>::spec_extend(self, iter.into_iter())
    }

    #[inline]
    fn extend_one(&mut self, item: T) {
        self.push(item);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    #[inline]
    unsafe fn extend_one_unchecked(&mut self, item: T) {
        // SAFETY: Our preconditions ensure the space has been reserved, and `extend_reserve` is implemented correctly.
        unsafe {
            let len = self.len();
            ptr::write(self.as_mut_ptr().add(len), item);
            self.set_len(len + 1);
        }
    }
}

impl<T, A: Allocator> Vec<T, A> {
    // leaf method to which various SpecFrom/SpecExtend implementations delegate when
    // they have no further optimizations to apply
    #[cfg(not(no_global_oom_handling))]
    fn extend_desugared<I: Iterator<Item = T>>(&mut self, mut iterator: I) {
        // This is the case for a general iterator.
        //
        // This function should be the moral equivalent of:
        //
        //      for item in iterator {
        //          self.push(item);
        //      }
        while let Some(element) = iterator.next() {
            let len = self.len();
            if len == self.capacity() {
                let (lower, _) = iterator.size_hint();
                self.reserve(lower.saturating_add(1));
            }
            unsafe {
                ptr::write(self.as_mut_ptr().add(len), element);
                // Since next() executes user code which can panic we have to bump the length
                // after each step.
                // NB can't overflow since we would have had to alloc the address space
                self.set_len(len + 1);
            }
        }
    }

    // specific extend for `TrustedLen` iterators, called both by the specializations
    // and internal places where resolving specialization makes compilation slower
    #[cfg(not(no_global_oom_handling))]
    fn extend_trusted(&mut self, iterator: impl iter::TrustedLen<Item = T>) {
        let (low, high) = iterator.size_hint();
        if let Some(additional) = high {
            debug_assert_eq!(
                low,
                additional,
                "TrustedLen iterator's size hint is not exact: {:?}",
                (low, high)
            );
            self.reserve(additional);
            unsafe {
                let ptr = self.as_mut_ptr();
                let mut local_len = SetLenOnDrop::new(&mut self.len);
                iterator.for_each(move |element| {
                    ptr::write(ptr.add(local_len.current_len()), element);
                    // Since the loop executes user code which can panic we have to update
                    // the length every step to correctly drop what we've written.
                    // NB can't overflow since we would have had to alloc the address space
                    local_len.increment_len(1);
                });
            }
        } else {
            // Per TrustedLen contract a `None` upper bound means that the iterator length
            // truly exceeds usize::MAX, which would eventually lead to a capacity overflow anyway.
            // Since the other branch already panics eagerly (via `reserve()`) we do the same here.
            // This avoids additional codegen for a fallback code path which would eventually
            // panic anyway.
            panic!("capacity overflow");
        }
    }

    /// Creates a splicing iterator that replaces the specified range in the vector
    /// with the given `replace_with` iterator and yields the removed items.
    /// `replace_with` does not need to be the same length as `range`.
    ///
    /// `range` is removed even if the `Splice` iterator is not consumed before it is dropped.
    ///
    /// It is unspecified how many elements are removed from the vector
    /// if the `Splice` value is leaked.
    ///
    /// The input iterator `replace_with` is only consumed when the `Splice` value is dropped.
    ///
    /// This is optimal if:
    ///
    /// * The tail (elements in the vector after `range`) is empty,
    /// * or `replace_with` yields fewer or equal elements than `range`'s length
    /// * or the lower bound of its `size_hint()` is exact.
    ///
    /// Otherwise, a temporary vector is allocated and the tail is moved twice.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and past the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec![1, 2, 3, 4];
    /// let new = [7, 8, 9];
    /// let u: Vec<_> = v.splice(1..3, new).collect();
    /// assert_eq!(v, [1, 7, 8, 9, 4]);
    /// assert_eq!(u, [2, 3]);
    /// ```
    ///
    /// Using `splice` to insert new items into a vector efficiently at a specific position
    /// indicated by an empty range:
    ///
    /// ```
    /// let mut v = vec![1, 5];
    /// let new = [2, 3, 4];
    /// v.splice(1..1, new);
    /// assert_eq!(v, [1, 2, 3, 4, 5]);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "vec_splice", since = "1.21.0")]
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> Splice<'_, I::IntoIter, A>
    where
        R: RangeBounds<usize>,
        I: IntoIterator<Item = T>,
    {
        Splice { drain: self.drain(range), replace_with: replace_with.into_iter() }
    }

    /// Creates an iterator which uses a closure to determine if an element in the range should be removed.
    ///
    /// If the closure returns `true`, the element is removed from the vector
    /// and yielded. If the closure returns `false`, or panics, the element
    /// remains in the vector and will not be yielded.
    ///
    /// Only elements that fall in the provided range are considered for extraction, but any elements
    /// after the range will still have to be moved if any element has been extracted.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without iterating
    /// or the iteration short-circuits, then the remaining elements will be retained.
    /// Use `extract_if().for_each(drop)` if you do not need the returned iterator,
    /// or [`retain_mut`] with a negated predicate if you also do not need to restrict the range.
    ///
    /// [`retain_mut`]: Vec::retain_mut
    ///
    /// Using this method is equivalent to the following code:
    ///
    /// ```
    /// # let some_predicate = |x: &mut i32| { *x % 2 == 1 };
    /// # let mut vec = vec![0, 1, 2, 3, 4, 5, 6];
    /// # let mut vec2 = vec.clone();
    /// # let range = 1..5;
    /// let mut i = range.start;
    /// let end_items = vec.len() - range.end;
    /// # let mut extracted = vec![];
    ///
    /// while i < vec.len() - end_items {
    ///     if some_predicate(&mut vec[i]) {
    ///         let val = vec.remove(i);
    ///         // your code here
    /// #         extracted.push(val);
    ///     } else {
    ///         i += 1;
    ///     }
    /// }
    ///
    /// # let extracted2: Vec<_> = vec2.extract_if(range, some_predicate).collect();
    /// # assert_eq!(vec, vec2);
    /// # assert_eq!(extracted, extracted2);
    /// ```
    ///
    /// But `extract_if` is easier to use. `extract_if` is also more efficient,
    /// because it can backshift the elements of the array in bulk.
    ///
    /// The iterator also lets you mutate the value of each element in the
    /// closure, regardless of whether you choose to keep or remove it.
    ///
    /// # Panics
    ///
    /// If `range` is out of bounds.
    ///
    /// # Examples
    ///
    /// Splitting a vector into even and odd values, reusing the original vector:
    ///
    /// ```
    /// let mut numbers = vec![1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15];
    ///
    /// let evens = numbers.extract_if(.., |x| *x % 2 == 0).collect::<Vec<_>>();
    /// let odds = numbers;
    ///
    /// assert_eq!(evens, vec![2, 4, 6, 8, 14]);
    /// assert_eq!(odds, vec![1, 3, 5, 9, 11, 13, 15]);
    /// ```
    ///
    /// Using the range argument to only process a part of the vector:
    ///
    /// ```
    /// let mut items = vec![0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 1, 2];
    /// let ones = items.extract_if(7.., |x| *x == 1).collect::<Vec<_>>();
    /// assert_eq!(items, vec![0, 0, 0, 0, 0, 0, 0, 2, 2, 2]);
    /// assert_eq!(ones.len(), 3);
    /// ```
    #[stable(feature = "extract_if", since = "1.87.0")]
    pub fn extract_if<F, R>(&mut self, range: R, filter: F) -> ExtractIf<'_, T, F, A>
    where
        F: FnMut(&mut T) -> bool,
        R: RangeBounds<usize>,
    {
        ExtractIf::new(self, filter, range)
    }
}

/// Extend implementation that copies elements out of references before pushing them onto the Vec.
///
/// This implementation is specialized for slice iterators, where it uses [`copy_from_slice`] to
/// append the entire slice at once.
///
/// [`copy_from_slice`]: slice::copy_from_slice
#[cfg(not(no_global_oom_handling))]
#[stable(feature = "extend_ref", since = "1.2.0")]
impl<'a, T: Copy + 'a, A: Allocator> Extend<&'a T> for Vec<T, A> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.spec_extend(iter.into_iter())
    }

    #[inline]
    fn extend_one(&mut self, &item: &'a T) {
        self.push(item);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    #[inline]
    unsafe fn extend_one_unchecked(&mut self, &item: &'a T) {
        // SAFETY: Our preconditions ensure the space has been reserved, and `extend_reserve` is implemented correctly.
        unsafe {
            let len = self.len();
            ptr::write(self.as_mut_ptr().add(len), item);
            self.set_len(len + 1);
        }
    }
}

/// Implements comparison of vectors, [lexicographically](Ord#lexicographical-comparison).
#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A1, A2> PartialOrd<Vec<T, A2>> for Vec<T, A1>
where
    T: PartialOrd,
    A1: Allocator,
    A2: Allocator,
{
    #[inline]
    fn partial_cmp(&self, other: &Vec<T, A2>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Eq, A: Allocator> Eq for Vec<T, A> {}

/// Implements ordering of vectors, [lexicographically](Ord#lexicographical-comparison).
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Ord, A: Allocator> Ord for Vec<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<#[may_dangle] T, A: Allocator> Drop for Vec<T, A> {
    fn drop(&mut self) {
        unsafe {
            // use drop for [T]
            // use a raw slice to refer to the elements of the vector as weakest necessary type;
            // could avoid questions of validity in certain cases
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len))
        }
        // RawVec handles deallocation
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_unstable(feature = "const_default", issue = "143894")]
impl<T> const Default for Vec<T> {
    /// Creates an empty `Vec<T>`.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    fn default() -> Vec<T> {
        Vec::new()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for Vec<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> AsRef<Vec<T, A>> for Vec<T, A> {
    fn as_ref(&self) -> &Vec<T, A> {
        self
    }
}

#[stable(feature = "vec_as_mut", since = "1.5.0")]
impl<T, A: Allocator> AsMut<Vec<T, A>> for Vec<T, A> {
    fn as_mut(&mut self) -> &mut Vec<T, A> {
        self
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> AsRef<[T]> for Vec<T, A> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

#[stable(feature = "vec_as_mut", since = "1.5.0")]
impl<T, A: Allocator> AsMut<[T]> for Vec<T, A> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone> From<&[T]> for Vec<T> {
    /// Allocates a `Vec<T>` and fills it by cloning `s`'s items.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(Vec::from(&[1, 2, 3][..]), vec![1, 2, 3]);
    /// ```
    fn from(s: &[T]) -> Vec<T> {
        s.to_vec()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "vec_from_mut", since = "1.19.0")]
impl<T: Clone> From<&mut [T]> for Vec<T> {
    /// Allocates a `Vec<T>` and fills it by cloning `s`'s items.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(Vec::from(&mut [1, 2, 3][..]), vec![1, 2, 3]);
    /// ```
    fn from(s: &mut [T]) -> Vec<T> {
        s.to_vec()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "vec_from_array_ref", since = "1.74.0")]
impl<T: Clone, const N: usize> From<&[T; N]> for Vec<T> {
    /// Allocates a `Vec<T>` and fills it by cloning `s`'s items.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(Vec::from(&[1, 2, 3]), vec![1, 2, 3]);
    /// ```
    fn from(s: &[T; N]) -> Vec<T> {
        Self::from(s.as_slice())
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "vec_from_array_ref", since = "1.74.0")]
impl<T: Clone, const N: usize> From<&mut [T; N]> for Vec<T> {
    /// Allocates a `Vec<T>` and fills it by cloning `s`'s items.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(Vec::from(&mut [1, 2, 3]), vec![1, 2, 3]);
    /// ```
    fn from(s: &mut [T; N]) -> Vec<T> {
        Self::from(s.as_mut_slice())
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "vec_from_array", since = "1.44.0")]
impl<T, const N: usize> From<[T; N]> for Vec<T> {
    /// Allocates a `Vec<T>` and moves `s`'s items into it.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(Vec::from([1, 2, 3]), vec![1, 2, 3]);
    /// ```
    fn from(s: [T; N]) -> Vec<T> {
        <[T]>::into_vec(Box::new(s))
    }
}

#[stable(feature = "vec_from_cow_slice", since = "1.14.0")]
impl<'a, T> From<Cow<'a, [T]>> for Vec<T>
where
    [T]: ToOwned<Owned = Vec<T>>,
{
    /// Converts a clone-on-write slice into a vector.
    ///
    /// If `s` already owns a `Vec<T>`, it will be returned directly.
    /// If `s` is borrowing a slice, a new `Vec<T>` will be allocated and
    /// filled by cloning `s`'s items into it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// let o: Cow<'_, [i32]> = Cow::Owned(vec![1, 2, 3]);
    /// let b: Cow<'_, [i32]> = Cow::Borrowed(&[1, 2, 3]);
    /// assert_eq!(Vec::from(o), Vec::from(b));
    /// ```
    fn from(s: Cow<'a, [T]>) -> Vec<T> {
        s.into_owned()
    }
}

// note: test pulls in std, which causes errors here
#[stable(feature = "vec_from_box", since = "1.18.0")]
impl<T, A: Allocator> From<Box<[T], A>> for Vec<T, A> {
    /// Converts a boxed slice into a vector by transferring ownership of
    /// the existing heap allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// let b: Box<[i32]> = vec![1, 2, 3].into_boxed_slice();
    /// assert_eq!(Vec::from(b), vec![1, 2, 3]);
    /// ```
    fn from(s: Box<[T], A>) -> Self {
        s.into_vec()
    }
}

// note: test pulls in std, which causes errors here
#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_vec", since = "1.20.0")]
impl<T, A: Allocator> From<Vec<T, A>> for Box<[T], A> {
    /// Converts a vector into a boxed slice.
    ///
    /// Before doing the conversion, this method discards excess capacity like [`Vec::shrink_to_fit`].
    ///
    /// [owned slice]: Box
    /// [`Vec::shrink_to_fit`]: Vec::shrink_to_fit
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(Box::from(vec![1, 2, 3]), vec![1, 2, 3].into_boxed_slice());
    /// ```
    ///
    /// Any excess capacity is removed:
    /// ```
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3]);
    ///
    /// assert_eq!(Box::from(vec), vec![1, 2, 3].into_boxed_slice());
    /// ```
    fn from(v: Vec<T, A>) -> Self {
        v.into_boxed_slice()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl From<&str> for Vec<u8> {
    /// Allocates a `Vec<u8>` and fills it with a UTF-8 string.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(Vec::from("123"), vec![b'1', b'2', b'3']);
    /// ```
    fn from(s: &str) -> Vec<u8> {
        From::from(s.as_bytes())
    }
}

#[stable(feature = "array_try_from_vec", since = "1.48.0")]
impl<T, A: Allocator, const N: usize> TryFrom<Vec<T, A>> for [T; N] {
    type Error = Vec<T, A>;

    /// Gets the entire contents of the `Vec<T>` as an array,
    /// if its size exactly matches that of the requested array.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(vec![1, 2, 3].try_into(), Ok([1, 2, 3]));
    /// assert_eq!(<Vec<i32>>::new().try_into(), Ok([]));
    /// ```
    ///
    /// If the length doesn't match, the input comes back in `Err`:
    /// ```
    /// let r: Result<[i32; 4], _> = (0..10).collect::<Vec<_>>().try_into();
    /// assert_eq!(r, Err(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]));
    /// ```
    ///
    /// If you're fine with just getting a prefix of the `Vec<T>`,
    /// you can call [`.truncate(N)`](Vec::truncate) first.
    /// ```
    /// let mut v = String::from("hello world").into_bytes();
    /// v.sort();
    /// v.truncate(2);
    /// let [a, b]: [_; 2] = v.try_into().unwrap();
    /// assert_eq!(a, b' ');
    /// assert_eq!(b, b'd');
    /// ```
    fn try_from(mut vec: Vec<T, A>) -> Result<[T; N], Vec<T, A>> {
        if vec.len() != N {
            return Err(vec);
        }

        // SAFETY: `.set_len(0)` is always sound.
        unsafe { vec.set_len(0) };

        // SAFETY: A `Vec`'s pointer is always aligned properly, and
        // the alignment the array needs is the same as the items.
        // We checked earlier that we have sufficient items.
        // The items will not double-drop as the `set_len`
        // tells the `Vec` not to also drop them.
        let array = unsafe { ptr::read(vec.as_ptr() as *const [T; N]) };
        Ok(array)
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod kani_vec_harness_helpers {
    use core::alloc::Layout;
    use core::iter::{self, FusedIterator};
    use core::{mem, ptr};

    use super::*;

    // This is a bound of CBMC's object model, not a logical Vec length bound.
    pub(super) const MAX_ALLOCATION_BYTES: usize = 1 << 48;

    pub(super) trait Shape: kani::Arbitrary {
        // The fill byte is used only for pre-existing opaque values.  It must
        // be a valid repeated representation for each shape below.
        fn fill_byte() -> u8 {
            kani::any()
        }
    }

    impl Shape for () {}
    impl Shape for u8 {}
    impl Shape for u64 {}
    impl<T: Shape, const N: usize> Shape for [T; N] {
        fn fill_byte() -> u8 {
            T::fill_byte()
        }
    }

    impl Shape for bool {
        fn fill_byte() -> u8 {
            kani::any_where(|value: &u8| *value <= 1)
        }
    }

    /// Cloneable but non-`Copy` element used to force the default
    /// `ExtendFromWithinSpec` implementation instead of the `TrivialClone`
    /// specialization.
    #[derive(Clone, kani::Arbitrary)]
    #[repr(transparent)]
    pub(super) struct CloneOnly(u8);

    impl Shape for CloneOnly {}

    /// `needs_drop` and non-`Copy` representative element.
    /// Its destructor is intentionally side-effect free: the main purpose of this
    /// shape is to exercise ownership-sensitive and drop-bearing code generation,
    /// not to count destructor invocations. Exact slice-drop behavior is checked
    /// separately by bounded supplementary harnesses.
    #[derive(Clone, kani::Arbitrary)]
    #[repr(transparent)]
    pub(super) struct WithDrop(u8);

    impl Drop for WithDrop {
        fn drop(&mut self) {}
    }

    impl Shape for WithDrop {}

    /// Finish a primary harness without introducing an unrelated symbolic-length
    /// slice-drop loop.
    /// For ordinary shapes the Vec is dropped normally. For `needs_drop` shapes,
    /// the primary proof is concerned with the target operation itself; Vec's
    /// compiler-generated slice drop glue is covered separately in `bounded_evidence`.
    pub(super) fn finish<T>(vec: Vec<T>) {
        if mem::needs_drop::<T>() {
            mem::forget(vec);
        } else {
            drop(vec);
        }
    }

    // A symbolic exact-size iterator used by both general and TrustedLen
    // extension proofs.  Its remaining count is unconstrained except by the
    // allocation/layout assumptions of the caller.
    pub(super) struct AnyIter<T> {
        remaining: usize,
        marker: PhantomData<T>,
    }

    impl<T> AnyIter<T> {
        pub(super) fn new(remaining: usize) -> Self {
            Self { remaining, marker: PhantomData }
        }
    }

    impl<T: kani::Arbitrary> Iterator for AnyIter<T> {
        type Item = T;

        fn next(&mut self) -> Option<Self::Item> {
            if self.remaining == 0 {
                None
            } else {
                self.remaining -= 1;
                Some(kani::any())
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.remaining, Some(self.remaining))
        }
    }

    impl<T: kani::Arbitrary> ExactSizeIterator for AnyIter<T> {}
    impl<T: kani::Arbitrary> FusedIterator for AnyIter<T> {}
    unsafe impl<T: kani::Arbitrary> iter::TrustedLen for AnyIter<T> {}

    pub(super) fn verifier_nondet_vec<T: Shape>() -> Vec<T> {
        // ZSTs have no backing allocation, but their logical length remains
        // symbolic.  Assigning the private field avoids recursively invoking
        // the set_len contract being verified.
        if mem::size_of::<T>() == 0 {
            let mut v = Vec::<T>::new();
            v.len = kani::any();
            kani::cover(v.len == 0, "generator: empty ZST");
            kani::cover(v.len != 0, "generator: nonempty ZST");
            return v;
        }

        let requested: usize = kani::any();
        kani::assume(Layout::array::<T>(requested).is_ok());
        kani::assume(
            requested
                .checked_mul(mem::size_of::<T>())
                .is_some_and(|bytes| bytes <= MAX_ALLOCATION_BYTES),
        );

        let mut v = Vec::<T>::with_capacity(requested);
        let cap = v.capacity();
        let len = kani::any_where(|len: &usize| *len <= cap);

        // Initialize the logical prefix before exposing it through Vec::len.
        // The fill byte is shape-specific, so this does not manufacture
        // invalid values for the validity-constrained shapes in this model.
        unsafe {
            if len != 0 {
                ptr::write_bytes(
                    v.as_mut_ptr().cast::<u8>(),
                    T::fill_byte(),
                    mem::size_of::<T>() * len,
                );
            }
        }
        v.len = len;
        kani::cover(len == 0, "generator: empty");
        kani::cover(len > 0 && len < cap, "generator: partially full");
        kani::cover(len == cap && cap > 0, "generator: full");
        v
    }

    pub(super) fn assume_reserve_no_capacity_overflow<T>(
        len: usize,
        cap: usize,
        additional: usize,
    ) {
        // Restrict the harness to executions in which `Vec::reserve`
        // returns normally and every newly-created allocation is representable
        // in CBMC's object model.
        //
        // These are proof-domain/modeling assumptions, not safety assumptions
        // about the operation being verified. Both the no-growth and growth
        // paths remain possible for non-ZST vectors.
        assert!(len <= cap);

        let elem_size = mem::size_of::<T>();

        if elem_size == 0 {
            assert_eq!(cap, usize::MAX);

            // For a ZST, reserve succeeds exactly while the logical length
            // addition remains representable.
            let zst_len_ok = additional <= usize::MAX - len;
            kani::assume(zst_len_ok);
            kani::cover(
                zst_len_ok,
                "reserve assumption: ZST logical length addition is representable",
            );

            return;
        }

        let spare = cap - len;
        if additional <= spare {
            return;
        }

        // We are now on the real RawVec growth path.
        kani::cover(additional > spare, "reserve model: non-ZST growth path is reachable");

        let required_cap_ok = len.checked_add(additional).is_some();
        kani::assume(required_cap_ok);
        kani::cover(required_cap_ok, "reserve assumption: required capacity is representable");

        let required_cap = len + additional;

        // RawVec stores non-ZST capacity below the high usize bit, so its
        // amortized doubling cannot overflow.
        assert!(cap.checked_mul(2).is_some());
        let doubled_cap = cap * 2;

        let new_cap = core::cmp::max(
            core::cmp::max(doubled_cap, required_cap),
            RawVec::<T>::MIN_NON_ZERO_CAP,
        );

        // `RawVec::finish_grow` must be able to construct the target layout.
        let growth_layout_ok = Layout::array::<T>(new_cap).is_ok();
        kani::assume(growth_layout_ok);
        kani::cover(
            growth_layout_ok,
            "reserve assumption: grown allocation layout is representable",
        );

        // This is a verifier representation bound only.
        let growth_object_model_ok =
            new_cap.checked_mul(elem_size).is_some_and(|bytes| bytes <= MAX_ALLOCATION_BYTES);

        kani::assume(growth_object_model_ok);
        kani::cover(
            growth_object_model_ok,
            "reserve assumption: grown allocation fits the CBMC object model",
        );
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Kani verification for Challenge 23 (`Vec`, part 1).
    //!
    //! # Verification strategy
    //!
    //! The proofs use symbolic `Vec` states produced by `verifier_nondet_vec`:
    //! capacities, logical lengths, indices, ranges, and operation-specific counts
    //! are symbolic rather than chosen from a small fixed array.
    //!
    //! Except for the primary `extend_desugared` and `extend_trusted` proofs, the
    //! main Challenge 23 target harnesses do not impose a program-level
    //! element-count bound and do not use `#[kani::unwind]`. Loops in those primary
    //! proofs are either verified directly or discharged with loop contracts.
    //!
    //! A small set of separate supplementary harnesses uses bounded unwinding for
    //! behaviors that cannot currently carry a Kani loop contract: compiler-generated
    //! slice drop glue for `needs_drop` elements and the iterator loop hidden inside
    //! the default `spec_extend_from_within` implementation. These bounded harnesses
    //! supplement rather than replace the corresponding unbounded primary proofs.
    //!
    //! Non-ZST allocations are still restricted by `MAX_ALLOCATION_BYTES`. This is
    //! a CBMC object-model restriction required to represent one symbolic heap
    //! object; it is not an API precondition and it is intentionally kept separate
    //! from semantic element-count bounds. ZST lengths remain symbolic over the
    //! full `usize` domain.
    //!
    //! # The two bounded target proofs
    //!
    //! `extend_desugared` and `extend_trusted` are the only target families that
    //! currently use bounded unwinding. Both bounded harnesses execute the exact
    //! shipped implementation; they do not replace the target with a verification
    //! model.
    //!
    //! For `extend_desugared`, an unbounded loop-contract proof was attempted first.
    //! Its loop may call `reserve`, so the induction step must model reallocation,
    //! replacement of the backing allocation, and freeing of the old allocation.
    //! At the pinned Kani version the resulting loop frame does not preserve enough
    //! allocation/provenance state to soundly reason about the following iteration.
    //! In addition, the natural invariant would require accessor calls such as
    //! `capacity()`, while model-checking/kani#4796 shows that method calls in loop
    //! invariants can be lowered with missing arguments and replaced by
    //! nondeterministic values.
    //!
    //! For `extend_trusted`, the shipped iteration is hidden inside
    //! `Iterator::for_each` / `fold`, so there is no source-level loop on which a
    //! loop contract can be attached. An explicit repeated-`next` transcription was
    //! also tried, but proving the required `TrustedLen` relation requires querying
    //! iterator state inside the invariant, again running into the pinned loop-
    //! contract limitations including #4796. Rather than claim an unbounded proof
    //! of a replacement body, the current harness executes the shipped `for_each`
    //! implementation directly with bounded unwinding.
    //!
    //! These two harness families are therefore explicit tool limitations of the
    //! current submission; all other target families retain symbolic lengths and
    //! unbounded loop reasoning.
    //!
    //! # Supplementary bounded evidence
    //!
    //! Representative `WithDrop` and `CloneOnly` shapes cover behaviors that are
    //! absent from the primitive `TrivialClone` instantiations.
    //!
    //! `WithDrop` is `Clone`, non-`Copy`, and `needs_drop`. Primary harnesses use it
    //! for ownership-sensitive operations while avoiding an unrelated final
    //! symbolic-length `Vec::drop` through `finish`. Actual slice-drop paths in
    //! `Vec::drop`, `truncate`, `clear`, and `Drain::drop` are checked separately
    //! with bounded unwinding because that compiler-generated drop loop has no
    //! source-level loop contract site.
    //!
    //! `CloneOnly` is `Clone` but not `TrivialClone`, forcing
    //! `spec_extend_from_within` and `extend_from_within` through the default
    //! per-element cloning implementation. That implementation iterates through
    //! `zip` / `map` / `for_each`, so its supplementary evidence is bounded for
    //! the same reason that a loop contract cannot be attached directly to the
    //! hidden iterator loop.
    //!
    //! These supplementary bounds are not used to describe the main Challenge 23
    //! proofs as unbounded evidence.
    //!
    //! # Kani-only source reshaping
    //!
    //! Normal Rust builds retain the shipped implementation. Where the pinned Kani
    //! loop-contract machinery cannot express the shipped loop frame directly,
    //! `cfg(kani)` is used only for a semantics-preserving reshaping needed by the
    //! proof:
    //!
    //! * `dedup_by` predeclares a small set of scalar/raw-pointer loop temporaries
    //!   so that variables written by the loop can be named by `loop_modifies`.
    //!   Every temporary is assigned the same value as in the shipped body before
    //!   its first use; predicate calls, drops, copies, length updates, and their
    //!   ordering are unchanged.
    //! * `extend_with` transcribes the shipped `for _ in 1..n` clone loop into an
    //!   explicit counter loop. Both forms perform exactly `n - 1` clone/write/
    //!   length-increment steps when `n > 0`, no such step when `n == 0`, and then
    //!   execute the same final write of the original value. The transcription is
    //!   used because the pinned Kani lowering of contracted `for` ranges introduces
    //!   verifier iterator/index state that makes this particular frame unsuitable,
    //!   especially for the valid `n == 0` case.
    //!
    //! # Remaining verification limitations
    //!
    //! `set_len`'s contract uses Kani's dereferenceability predicate for the
    //! documented initialized-prefix requirement. The actual `split_off` path has a
    //! separate initialization-order concern: enabling Kani's full uninitialized-
    //! memory instrumentation on the alloc path is currently blocked by the pinned
    //! toolchain's function-pointer/vtable limitation (the Kani #3300 class of
    //! failures). Results obtained without that instrumentation must therefore not
    //! be presented as establishing that separate initialization property.
    //!
    //! `append_elements` is verified with a direct proof rather than
    //! `proof_for_contract`: its `reserve` may replace and free the old allocation,
    //! while the pinned Kani public function-contract API can express writable
    //! `modifies` regions but not the corresponding `frees` frame.
    use core::mem::ManuallyDrop;
    use core::ops::{Deref, DerefMut};

    use super::kani_vec_harness_helpers::*;
    use super::*;
    use crate::vec::Vec;

    #[kani::proof]
    pub fn verify_swap_remove() {
        // Start from a symbolic vector state rather than a fixed-size array.
        let mut vect = verifier_nondet_vec::<u8>();

        let index = kani::any_where(|index: &usize| *index < vect.len());
        let _ = vect.swap_remove(index);
    }

    // Harnesses for `Vec::from_raw_parts`
    macro_rules! gen_from_raw_parts_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Vec::<$ty>::from_raw_parts)]
            pub fn $name() {
                // Create a non-deterministic Vec and prevent it from being dropped
                // before ownership is transferred through the raw parts
                let mut original = ManuallyDrop::new(verifier_nondet_vec::<$ty>());
                // Get the raw pointer, initialized length, and allocation capacity
                let ptr = original.as_mut_ptr();
                let len = original.len();
                let capacity = original.capacity();
                // Rebuild the Vec from the same allocation metadata
                let _: Vec<$ty> = unsafe { Vec::from_raw_parts(ptr, len, capacity) };
            }
        };
    }

    gen_from_raw_parts_harness!(harness_vec_from_raw_parts_u8, u8);
    gen_from_raw_parts_harness!(harness_vec_from_raw_parts_u64, u64);
    gen_from_raw_parts_harness!(harness_vec_from_raw_parts_unit, ());
    gen_from_raw_parts_harness!(harness_vec_from_raw_parts_array, [u8; 4]);
    gen_from_raw_parts_harness!(harness_vec_from_raw_parts_bool, bool);

    // Harnesses for `Vec::from_parts` (Vec::from_nonnull not found as Vec functions)
    macro_rules! gen_from_parts_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Vec::<$ty>::from_parts)]
            pub fn $name() {
                // Create a non-deterministic Vec and prevent it from being dropped
                // before ownership is transferred through the raw parts
                let mut original = ManuallyDrop::new(verifier_nondet_vec::<$ty>());
                // Get a non-null pointer to the Vec allocation
                let ptr = unsafe { NonNull::new_unchecked(original.as_mut_ptr()) };
                // Get the initialized length and allocation capacity
                let len = original.len();
                let capacity = original.capacity();
                // Rebuild the Vec from the same allocation metadata
                let _: Vec<$ty> = unsafe { Vec::from_parts(ptr, len, capacity) };
            }
        };
    }

    gen_from_parts_harness!(harness_vec_from_parts_u8, u8);
    gen_from_parts_harness!(harness_vec_from_parts_u64, u64);
    gen_from_parts_harness!(harness_vec_from_parts_unit, ());
    gen_from_parts_harness!(harness_vec_from_parts_array, [u8; 4]);
    gen_from_parts_harness!(harness_vec_from_parts_bool, bool);

    // Harnesses for `Vec::from_parts_in` (Vec::from_nonnull_in not found as Vec functions)
    macro_rules! gen_from_parts_in_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Vec::<$ty>::from_parts_in)]
            pub fn $name() {
                // Create a non-deterministic Vec and prevent it from being dropped
                // before ownership is transferred through the allocator-aware raw parts
                let mut original = ManuallyDrop::new(verifier_nondet_vec::<$ty>());
                // Get a non-null pointer to the Vec allocation
                let ptr = unsafe { NonNull::new_unchecked(original.as_mut_ptr()) };
                // Get the initialized length and allocation capacity
                let len = original.len();
                let capacity = original.capacity();
                // Rebuild the Vec from the same allocation metadata and allocator
                let _: Vec<$ty> = unsafe { Vec::from_parts_in(ptr, len, capacity, Global) };
            }
        };
    }

    gen_from_parts_in_harness!(harness_vec_from_parts_in_u8, u8);
    gen_from_parts_in_harness!(harness_vec_from_parts_in_u64, u64);
    gen_from_parts_in_harness!(harness_vec_from_parts_in_unit, ());
    gen_from_parts_in_harness!(harness_vec_from_parts_in_array, [u8; 4]);
    gen_from_parts_in_harness!(harness_vec_from_parts_in_bool, bool);

    // Harnesses for `Vec::into_raw_parts_with_alloc`
    macro_rules! gen_into_raw_parts_with_alloc_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let vec = verifier_nondet_vec::<$ty>();
                // Decompose the Vec into raw parts together with its allocator
                let _ = vec.into_raw_parts_with_alloc();
            }
        };
    }

    gen_into_raw_parts_with_alloc_harness!(harness_vec_into_raw_parts_with_alloc_u8, u8);
    gen_into_raw_parts_with_alloc_harness!(harness_vec_into_raw_parts_with_alloc_u64, u64);
    gen_into_raw_parts_with_alloc_harness!(harness_vec_into_raw_parts_with_alloc_unit, ());
    gen_into_raw_parts_with_alloc_harness!(harness_vec_into_raw_parts_with_alloc_bool, bool);
    gen_into_raw_parts_with_alloc_harness!(harness_vec_into_raw_parts_with_alloc_array, [u8; 4]);

    // Harnesses for `Vec::into_boxed_slice`
    macro_rules! gen_into_boxed_slice_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let vec = verifier_nondet_vec::<$ty>();
                // Convert the Vec into a boxed slice containing its initialized elements
                let _: Box<[$ty]> = vec.into_boxed_slice();
            }
        };
    }

    gen_into_boxed_slice_harness!(harness_vec_into_boxed_slice_u8, u8);
    gen_into_boxed_slice_harness!(harness_vec_into_boxed_slice_u64, u64);
    gen_into_boxed_slice_harness!(harness_vec_into_boxed_slice_unit, ());
    gen_into_boxed_slice_harness!(harness_vec_into_boxed_slice_bool, bool);
    gen_into_boxed_slice_harness!(harness_vec_into_boxed_slice_array, [u8; 4]);

    #[cfg(not(no_global_oom_handling))]
    #[kani::proof]
    fn harness_vec_into_boxed_slice_with_drop() {
        let vec = verifier_nondet_vec::<WithDrop>();
        let boxed = vec.into_boxed_slice();
        core::mem::forget(boxed);
    }

    // Harnesses for `Vec::truncate`
    macro_rules! gen_truncate_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Choose a non-deterministic target length
                let new_len: usize = kani::any();
                // Truncate the Vec to the selected length
                vec.truncate(new_len);
            }
        };
    }

    gen_truncate_harness!(harness_vec_truncate_u8, u8);
    gen_truncate_harness!(harness_vec_truncate_u64, u64);
    gen_truncate_harness!(harness_vec_truncate_unit, ());
    gen_truncate_harness!(harness_vec_truncate_bool, bool);
    gen_truncate_harness!(harness_vec_truncate_array, [u8; 4]);

    // Harnesses for `Vec::set_len`
    macro_rules! gen_set_len_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Vec::<$ty>::set_len)]
            pub fn $name() {
                // The generator initializes a symbolic prefix before exposing
                // it through Vec::len, so it can model both shrink and grow.
                let mut vec = verifier_nondet_vec::<$ty>();
                let initialized_len = vec.len();
                let old_len = kani::any_where(|len: &usize| *len <= initialized_len);
                vec.len = old_len;
                let new_len = kani::any_where(|len: &usize| *len <= initialized_len);
                kani::cover(new_len > old_len, "set_len: grow");
                kani::cover(new_len < old_len, "set_len: shrink");
                kani::cover(new_len == old_len, "set_len: unchanged");
                unsafe {
                    vec.set_len(new_len);
                }
            }
        };
    }

    gen_set_len_harness!(harness_vec_set_len_u8, u8);
    gen_set_len_harness!(harness_vec_set_len_u64, u64);
    gen_set_len_harness!(harness_vec_set_len_unit, ());
    gen_set_len_harness!(harness_vec_set_len_array, [u8; 4]);
    gen_set_len_harness!(harness_vec_set_len_bool, bool);

    // Harnesses for `Vec::swap_remove`
    // `swap_remove` must return without panic when `index < len`.
    macro_rules! gen_swap_remove_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Choose a non-deterministic index within the initialized length
                let index = kani::any_where(|index: &usize| *index < vec.len());
                // Remove the selected element by swapping in the last element
                let value = vec.swap_remove(index);
                drop(value);
                finish(vec);
            }
        };
    }

    gen_swap_remove_harness!(harness_vec_swap_remove_u8, u8);
    gen_swap_remove_harness!(harness_vec_swap_remove_u64, u64);
    gen_swap_remove_harness!(harness_vec_swap_remove_unit, ());
    gen_swap_remove_harness!(harness_vec_swap_remove_bool, bool);
    gen_swap_remove_harness!(harness_vec_swap_remove_array, [u8; 4]);
    gen_swap_remove_harness!(harness_vec_swap_remove_with_drop, WithDrop);

    // `swap_remove` must panic when `index >= len`.
    #[kani::proof]
    #[kani::should_panic]
    pub fn harness_vec_swap_remove_out_of_bounds() {
        // Create a non-deterministic Vec for the panic case
        let mut vec = verifier_nondet_vec::<u8>();
        // Choose a non-deterministic index outside the initialized length
        let index = kani::any_where(|index: &usize| *index >= vec.len());
        // Calling `swap_remove` with an out-of-bounds index must panic
        let _ = vec.swap_remove(index);
    }

    // Harnesses for `Vec::insert`
    // `insert` must return without panic when `index <= len`.
    macro_rules! gen_insert_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector with unconstrained length, capacity, and contents.
                let mut vec = verifier_nondet_vec::<$ty>();
                // Require one spare slot so inserting does not overflow capacity.
                let len = vec.len();
                let cap = vec.capacity();
                assume_reserve_no_capacity_overflow::<$ty>(len, cap, 1);
                kani::cover(core::mem::size_of::<$ty>() == 0 || cap == len, "insert: growth");
                kani::cover(
                    core::mem::size_of::<$ty>() == 0 || cap > len,
                    "insert: spare capacity",
                );
                // Pick a symbolic index that satisfies the non-panicking precondition.
                let index = kani::any_where(|index: &usize| *index <= vec.len());
                kani::cover(index == 0, "insert: front");
                kani::cover(index == vec.len(), "insert: end");
                kani::cover(index > 0 && index < vec.len(), "insert: middle");
                // Create a symbolic element to insert.
                let element: $ty = kani::any();
                // Call the function under verification.
                vec.insert(index, element);
                finish(vec);
            }
        };
    }

    gen_insert_harness!(harness_vec_insert_u8, u8);
    gen_insert_harness!(harness_vec_insert_u64, u64);
    gen_insert_harness!(harness_vec_insert_unit, ());
    gen_insert_harness!(harness_vec_insert_bool, bool);
    gen_insert_harness!(harness_vec_insert_array, [u8; 4]);
    gen_insert_harness!(harness_vec_insert_with_drop, WithDrop);

    // `insert` must panic when `index > len`.
    #[cfg(not(no_global_oom_handling))]
    #[kani::proof]
    #[kani::should_panic]
    pub fn harness_vec_insert_out_of_bounds() {
        // Create a non-deterministic Vec for the panic case
        let mut vec = verifier_nondet_vec::<u8>();
        // Choose a non-deterministic index beyond the insertion boundary
        let index = kani::any_where(|index: &usize| *index > vec.len());
        // Calling `insert` past the end must panic
        vec.insert(index, kani::any());
    }

    // Harnesses for `Vec::remove`
    // `remove` must return without panic when `index < len`.
    macro_rules! gen_remove_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a symbolic vector of the target type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Generate a nondeterministic index which is guaranteed to be within bounds
                let index = kani::any_where(|index: &usize| *index < vec.len());
                // Remove and return the selected element
                let value = vec.remove(index);
                drop(value);
                finish(vec);
            }
        };
    }

    gen_remove_harness!(harness_vec_remove_u8, u8);
    gen_remove_harness!(harness_vec_remove_u64, u64);
    gen_remove_harness!(harness_vec_remove_unit, ());
    gen_remove_harness!(harness_vec_remove_bool, bool);
    gen_remove_harness!(harness_vec_remove_array, [u8; 4]);
    gen_remove_harness!(harness_vec_remove_with_drop, WithDrop);

    // `remove` must panic when `index >= len`.
    #[kani::proof]
    #[kani::should_panic]
    pub fn harness_vec_remove_out_of_bounds() {
        // Create a non-deterministic Vec for the panic case
        let mut vec = verifier_nondet_vec::<u8>();
        // Choose a non-deterministic index beyond the removal boundary
        let index = kani::any_where(|index: &usize| *index >= vec.len());
        // Calling `remove` with an out-of-bounds index must panic
        let _ = vec.remove(index);
    }

    // Harnesses for `Vec::retain_mut`
    macro_rules! gen_retain_mut_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Retain each element according to a non-deterministic predicate
                vec.retain_mut(|_| kani::any::<bool>());
                finish(vec);
            }
        };
    }

    gen_retain_mut_harness!(harness_vec_retain_mut_u8, u8);
    gen_retain_mut_harness!(harness_vec_retain_mut_u64, u64);
    gen_retain_mut_harness!(harness_vec_retain_mut_unit, ());
    gen_retain_mut_harness!(harness_vec_retain_mut_array, [u8; 4]);
    gen_retain_mut_harness!(harness_vec_retain_mut_bool, bool);
    gen_retain_mut_harness!(harness_vec_retain_mut_with_drop, WithDrop);

    // Harnesses for `Vec::dedup_by`
    // The proof harness instantiates `same_bucket` with a capture-free ZST
    // closure. The pinned Kani/CBMC crashes when a ZST closure is listed in
    // `loop_modifies` (kani#4786), so the predicate itself is omitted.
    // Mutations through its `&mut T` arguments are covered by `modified_items`.
    macro_rules! gen_dedup_by_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                vec.dedup_by(|_, _| kani::any());
                finish(vec);
            }
        };
    }

    gen_dedup_by_harness!(harness_vec_dedup_by_u8, u8);
    gen_dedup_by_harness!(harness_vec_dedup_by_u64, u64);
    gen_dedup_by_harness!(harness_vec_dedup_by_unit, ());
    gen_dedup_by_harness!(harness_vec_dedup_by_array, [u8; 4]);
    gen_dedup_by_harness!(harness_vec_dedup_by_bool, bool);
    gen_dedup_by_harness!(harness_vec_dedup_by_with_drop, WithDrop);

    // Harnesses for `Vec::push`
    macro_rules! gen_push_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Snapshot the initial length and capacity for the reserve precondition
                let len = vec.len();
                let cap = vec.capacity();
                // Create a non-deterministic element to append
                let value = kani::any();
                // Require enough capacity for one additional element
                assume_reserve_no_capacity_overflow::<$ty>(len, cap, 1);
                let spare = cap.saturating_sub(len);
                kani::cover(core::mem::size_of::<$ty>() == 0 || spare == 0, "push: growth");
                kani::cover(core::mem::size_of::<$ty>() == 0 || spare > 0, "push: spare capacity");
                // Push the selected value onto the Vec
                vec.push(value);
                finish(vec);
            }
        };
    }

    gen_push_harness!(harness_vec_push_u8, u8);
    gen_push_harness!(harness_vec_push_u64, u64);
    gen_push_harness!(harness_vec_push_unit, ());
    gen_push_harness!(harness_vec_push_bool, bool);
    gen_push_harness!(harness_vec_push_array, [u8; 4]);
    gen_push_harness!(harness_vec_push_with_drop, WithDrop);

    // Harnesses for `Vec::push_within_capacity`
    macro_rules! gen_push_within_capacity_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Create a non-deterministic element to append if capacity permits
                let value = kani::any();
                // Attempt to push the value without growing the allocation
                let result = vec.push_within_capacity(value);
                drop(result);
                finish(vec);
            }
        };
    }

    gen_push_within_capacity_harness!(harness_vec_push_within_capacity_u8, u8);
    gen_push_within_capacity_harness!(harness_vec_push_within_capacity_u64, u64);
    gen_push_within_capacity_harness!(harness_vec_push_within_capacity_unit, ());
    gen_push_within_capacity_harness!(harness_vec_push_within_capacity_bool, bool);
    gen_push_within_capacity_harness!(harness_vec_push_within_capacity_array, [u8; 4]);
    gen_push_within_capacity_harness!(harness_vec_push_within_capacity_with_drop, WithDrop);

    // Harnesses for `Vec::pop`
    macro_rules! gen_pop_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Pop the last initialized element if one exists
                let value = vec.pop();
                drop(value);
                finish(vec);
            }
        };
    }

    gen_pop_harness!(harness_vec_pop_u8, u8);
    gen_pop_harness!(harness_vec_pop_u64, u64);
    gen_pop_harness!(harness_vec_pop_unit, ());
    gen_pop_harness!(harness_vec_pop_bool, bool);
    gen_pop_harness!(harness_vec_pop_array, [u8; 4]);
    gen_pop_harness!(harness_vec_pop_with_drop, WithDrop);

    // Harnesses for `Vec::append`
    macro_rules! gen_append_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                // Create the destination Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Create the source Vec whose elements will be moved
                let mut other = verifier_nondet_vec::<$ty>();
                let other_len = other.len();
                // Require enough capacity for all elements from the source Vec
                assume_reserve_no_capacity_overflow::<$ty>(vec.len(), vec.capacity(), other_len);
                // Move all elements from `other` into `vec`
                vec.append(&mut other);

                assert_eq!(other.len(), 0);
                kani::cover(other_len == 0, "append: empty source");
                kani::cover(other_len > 0, "append: non-empty source");

                finish(vec);
                finish(other);
            }
        };
    }

    gen_append_harness!(harness_vec_append_u8, u8);
    gen_append_harness!(harness_vec_append_u64, u64);
    gen_append_harness!(harness_vec_append_unit, ());
    gen_append_harness!(harness_vec_append_array, [u8; 4]);
    gen_append_harness!(harness_vec_append_bool, bool);
    gen_append_harness!(harness_vec_append_with_drop, WithDrop);

    // Harnesses for `Vec::append_elements`
    // * `append_elements` is verified directly rather than with
    //   `proof_for_contract`. Its `reserve` call may reallocate and therefore
    //   deallocate the old buffer. The pinned Kani function-contract API can
    //   express writable regions with `modifies`, but cannot express the
    //   corresponding `frees` frame required for reallocation.
    macro_rules! gen_vec_append_elements_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                // Create the destination Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Create the source Vec whose slice will be appended
                let other = verifier_nondet_vec::<$ty>();
                let count = other.len();
                let old_spare = vec.capacity().saturating_sub(vec.len());
                assume_reserve_no_capacity_overflow::<$ty>(vec.len(), vec.capacity(), count);
                // `other.as_slice()` establishes the readable-source part of
                // `append_elements`'s unsafe precondition. The remaining condition is that
                // a non-empty, non-ZST source must not overlap the destination allocation.
                kani::assume(
                    count == 0
                        || core::mem::size_of::<$ty>() == 0
                        || !kani::mem::same_allocation(other.as_ptr(), vec.as_ptr()),
                );
                kani::cover(
                    core::mem::size_of::<$ty>() == 0 || count <= old_spare,
                    "append_elements: no growth",
                );
                kani::cover(
                    core::mem::size_of::<$ty>() != 0 && count > old_spare,
                    "append_elements: growth",
                );
                unsafe {
                    // Append all elements from the source slice into the destination Vec
                    vec.append_elements(other.as_slice() as _);
                }
            }
        };
    }

    gen_vec_append_elements_harness!(harness_vec_append_elements_u8, u8);
    gen_vec_append_elements_harness!(harness_vec_append_elements_u64, u64);
    gen_vec_append_elements_harness!(harness_vec_append_elements_unit, ());
    gen_vec_append_elements_harness!(harness_vec_append_elements_array, [u8; 4]);
    gen_vec_append_elements_harness!(harness_vec_append_elements_bool, bool);

    // Harnesses for `Vec::drain`
    macro_rules! gen_drain_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut v = verifier_nondet_vec::<$ty>();
                // Snapshot the initialized length to constrain the drain range
                let len = v.len();
                // Choose a non-deterministic in-bounds exclusive range end
                let end = kani::any_where(|end: &usize| *end <= len);
                // Choose a non-deterministic in-bounds range start
                let start = kani::any_where(|start: &usize| *start <= end);
                // Create a drain iterator over the selected range
                let d = v.drain(start..end);
                // Prevent the drain iterator from running its drop logic in this harness
                core::mem::forget(d);
            }
        };
    }

    gen_drain_harness!(harness_vec_drain_u8, u8);
    gen_drain_harness!(harness_vec_drain_u64, u64);
    gen_drain_harness!(harness_vec_drain_unit, ());
    gen_drain_harness!(harness_vec_drain_bool, bool);
    gen_drain_harness!(harness_vec_drain_array, [u8; 4]);

    // `drain` construction is checked unboundedly for a `needs_drop` element type.
    // The iterator is deliberately forgotten here so this proof remains about the
    // Challenge target itself; execution of `Drain::drop` over a symbolic element
    // range is covered separately in `bounded_evidence`.
    #[kani::proof]
    fn harness_vec_drain_with_drop() {
        let mut vec = verifier_nondet_vec::<WithDrop>();
        let len = vec.len();
        let end = kani::any_where(|end: &usize| *end <= len);
        let start = kani::any_where(|start: &usize| *start <= end);
        let drain = vec.drain(start..end);
        core::mem::forget(drain);
        finish(vec);
    }

    // Harnesses for `Vec::clear`
    macro_rules! gen_clear_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut v = verifier_nondet_vec::<$ty>();
                // Remove all initialized elements from the Vec
                v.clear();
            }
        };
    }

    gen_clear_harness!(harness_vec_clear_u8, u8);
    gen_clear_harness!(harness_vec_clear_u64, u64);
    gen_clear_harness!(harness_vec_clear_unit, ());
    gen_clear_harness!(harness_vec_clear_bool, bool);
    gen_clear_harness!(harness_vec_clear_array, [u8; 4]);

    // Harnesses for `Vec::split_off`
    macro_rules! gen_split_off_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                let old_len = vec.len();
                // Choose a non-deterministic split point within the initialized length
                let at = kani::any_where(|at: &usize| *at <= old_len);
                kani::cover(at == 0, "split_off: zero");
                kani::cover(at == vec.len(), "split_off: len");
                kani::cover(at > 0 && at < vec.len(), "split_off: middle");
                // Split off the suffix starting at the selected point
                let tail = vec.split_off(at);
                assert_eq!(vec.len(), at);
                assert_eq!(tail.len(), old_len - at);

                finish(vec);
                finish(tail);
            }
        };
    }

    gen_split_off_harness!(harness_vec_split_off_u8, u8);
    gen_split_off_harness!(harness_vec_split_off_u64, u64);
    gen_split_off_harness!(harness_vec_split_off_unit, ());
    gen_split_off_harness!(harness_vec_split_off_bool, bool);
    gen_split_off_harness!(harness_vec_split_off_array, [u8; 4]);
    gen_split_off_harness!(harness_vec_split_off_with_drop, WithDrop);

    #[cfg(not(no_global_oom_handling))]
    #[kani::proof]
    #[kani::should_panic]
    pub fn harness_vec_split_off_out_of_bounds() {
        // Create a non-deterministic Vec for the panic case
        let mut vec = verifier_nondet_vec::<u8>();
        assert!(vec.len() < usize::MAX);
        let at = kani::any_where(|at: &usize| *at > vec.len());
        // Calling `split_off` with an out-of-bounds split point must panic
        let _ = vec.split_off(at);
    }

    // Harnesses for `Vec::leak`
    macro_rules! gen_leak_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Leak the Vec and return a mutable slice to its initialized elements
                let _ = vec.leak();
            }
        };
    }

    gen_leak_harness!(harness_vec_leak_u8, u8);
    gen_leak_harness!(harness_vec_leak_u64, u64);
    gen_leak_harness!(harness_vec_leak_unit, ());
    gen_leak_harness!(harness_vec_leak_bool, bool);
    gen_leak_harness!(harness_vec_leak_array, [u8; 4]);

    // Harnesses for `Vec::spare_capacity_mut`
    macro_rules! gen_spare_capacity_mut_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Borrow the spare capacity as maybe-uninitialized elements
                let _ = vec.spare_capacity_mut();
            }
        };
    }

    gen_spare_capacity_mut_harness!(harness_vec_spare_capacity_mut_u8, u8);
    gen_spare_capacity_mut_harness!(harness_vec_spare_capacity_mut_u64, u64);
    gen_spare_capacity_mut_harness!(harness_vec_spare_capacity_mut_unit, ());
    gen_spare_capacity_mut_harness!(harness_vec_spare_capacity_mut_bool, bool);
    gen_spare_capacity_mut_harness!(harness_vec_spare_capacity_mut_array, [u8; 4]);

    // Harnesses for `Vec::split_at_spare_mut`
    macro_rules! gen_split_at_spare_mut_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Split the Vec into initialized elements and spare capacity
                let _ = vec.split_at_spare_mut();
            }
        };
    }

    gen_split_at_spare_mut_harness!(harness_vec_split_at_spare_mut_u8, u8);
    gen_split_at_spare_mut_harness!(harness_vec_split_at_spare_mut_u64, u64);
    gen_split_at_spare_mut_harness!(harness_vec_split_at_spare_mut_unit, ());
    gen_split_at_spare_mut_harness!(harness_vec_split_at_spare_mut_bool, bool);
    gen_split_at_spare_mut_harness!(harness_vec_split_at_spare_mut_array, [u8; 4]);

    // Harnesses for `Vec::split_at_spare_mut_with_len`
    macro_rules! gen_split_at_spare_mut_with_len_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof_for_contract(Vec::<$ty>::split_at_spare_mut_with_len)]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Split the Vec and expose the mutable length field under the contract
                let _ = unsafe { vec.split_at_spare_mut_with_len() };
            }
        };
    }

    gen_split_at_spare_mut_with_len_harness!(harness_vec_split_at_spare_mut_with_len_u8, u8);
    gen_split_at_spare_mut_with_len_harness!(harness_vec_split_at_spare_mut_with_len_u64, u64);
    gen_split_at_spare_mut_with_len_harness!(harness_vec_split_at_spare_mut_with_len_unit, ());
    gen_split_at_spare_mut_with_len_harness!(harness_vec_split_at_spare_mut_with_len_bool, bool);
    gen_split_at_spare_mut_with_len_harness!(
        harness_vec_split_at_spare_mut_with_len_array,
        [u8; 4]
    );

    // Harnesses for `Vec::extend_from_within`
    macro_rules! gen_extend_from_within_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof()]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Snapshot the initial length and capacity before choosing the source range
                let len = vec.len();
                let cap = vec.capacity();
                // Choose a non-deterministic in-bounds exclusive range end
                let end: usize = kani::any_where(|end: &usize| *end <= len);
                // Choose a non-deterministic in-bounds range start
                let start: usize = kani::any_where(|start: &usize| *start <= end);
                // Compute how many elements will be cloned from the selected range
                let additional = end - start;
                // Require enough capacity for the cloned elements
                assume_reserve_no_capacity_overflow::<$ty>(len, cap, additional);
                // Perform any possible growth before constraining the raw copy pointers.
                // `extend_from_within` will call `reserve` again, but this makes that call a no-op
                // and lets the non-overlap assumption refer to the buffer used by the copy.
                vec.reserve(additional);

                // Compute the byte length used by `copy_nonoverlapping` and reject overflow states.
                let elem_size = core::mem::size_of::<$ty>();
                assert!(elem_size == 0 || additional <= usize::MAX / elem_size);
                let copy_bytes = elem_size * additional;

                // For non-empty raw copies, the initialized source range `[start, end)`
                // and the spare destination range starting at `len` should not overlap.
                if copy_bytes != 0 {
                    let src_ptr = unsafe { vec.as_ptr().add(start) }.cast::<u8>();
                    let dst_ptr = unsafe { vec.as_mut_ptr().add(len) }.cast::<u8>();
                    assert!(src_ptr.addr().abs_diff(dst_ptr.addr()) >= copy_bytes);
                }
                // Extend the Vec by cloning the selected initialized range
                vec.extend_from_within(start..end);
            }
        };
    }

    gen_extend_from_within_harness!(harness_vec_extend_from_within_u8, u8);
    gen_extend_from_within_harness!(harness_vec_extend_from_within_u64, u64);
    gen_extend_from_within_harness!(harness_vec_extend_from_within_unit, ());
    gen_extend_from_within_harness!(harness_vec_extend_from_within_bool, bool);
    gen_extend_from_within_harness!(harness_vec_extend_from_within_array, [u8; 4]);

    // Harnesses for `Vec::into_flattened`
    macro_rules! gen_into_flattened_harness {
        ($name:ident, [$ty:ty; $n:expr]) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec of fixed-size arrays
                let vec = verifier_nondet_vec::<[$ty; $n]>();
                // Flatten the Vec into a Vec of the array element type
                let _ = vec.into_flattened();
            }
        };
        ($name:ident, zst_no_overflow([$ty:ty; $n:expr])) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec of fixed-size zero-sized arrays
                let vec = verifier_nondet_vec::<[$ty; $n]>();
                // Keep the flattened zero-sized length within usize bounds
                let flattened_len_fits = vec.len() <= usize::MAX / $n;
                kani::assume(flattened_len_fits);
                kani::cover(
                    flattened_len_fits,
                    "into_flattened assumption: ZST flattened length is representable",
                );
                kani::cover(
                    vec.len() == usize::MAX / $n,
                    "into_flattened: largest non-overflowing ZST length",
                );
                // Flatten the Vec under the non-overflow precondition
                let _ = vec.into_flattened();
            }
        };
        ($name:ident, zst_overflow([$ty:ty; $n:expr])) => {
            #[kani::proof]
            #[kani::should_panic]
            pub fn $name() {
                // Create a non-deterministic Vec of fixed-size zero-sized arrays
                let vec = verifier_nondet_vec::<[$ty; $n]>();
                // Force the flattened zero-sized length to overflow
                let flattened_len_overflows = vec.len() > usize::MAX / $n;
                kani::assume(flattened_len_overflows);
                kani::cover(
                    flattened_len_overflows,
                    "into_flattened panic assumption: ZST flattened length overflows usize",
                );
                // Flattening this Vec must panic on length overflow
                let _ = vec.into_flattened();
            }
        };
    }

    gen_into_flattened_harness!(harness_vec_into_flattened_u8_array, [u8; 4]);
    gen_into_flattened_harness!(harness_vec_into_flattened_u64_array, [u64; 4]);
    gen_into_flattened_harness!(harness_vec_into_flattened_bool_array, [bool; 4]);
    gen_into_flattened_harness!(harness_vec_into_flattened_u8_array_array_4, [[u8; 4]; 4]);
    gen_into_flattened_harness!(harness_vec_into_flattened_unit_array, zst_no_overflow([(); 4]));
    gen_into_flattened_harness!(
        harness_vec_into_flattened_unit_array_overflow,
        zst_overflow([(); 4])
    );

    #[kani::proof]
    fn harness_vec_into_flattened_with_drop() {
        let vec = verifier_nondet_vec::<[WithDrop; 4]>();
        let flat: Vec<WithDrop> = vec.into_flattened();
        finish(flat);
    }

    // The main proof is unbounded and verifies the Kani loop-contract transcription above.
    // Harnesses for `Vec::extend_with`
    macro_rules! gen_extend_with_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Snapshot the initial length and capacity for the reserve precondition
                let len = vec.len();
                let cap = vec.capacity();
                // Choose a non-deterministic number of cloned elements to append
                let n: usize = kani::any();
                // Create the value that will be cloned into the spare slots
                let value: $ty = kani::any();
                // Require enough capacity for the appended clones
                assume_reserve_no_capacity_overflow::<$ty>(len, cap, n);
                kani::cover(n == 0, "extend_with: empty");
                kani::cover(n != 0, "extend_with: nonempty");
                // Extend the Vec with `n` clones of `value`
                vec.extend_with(n, value);
                finish(vec);
            }
        };
    }

    gen_extend_with_harness!(harness_vec_extend_with_u8, u8);
    gen_extend_with_harness!(harness_vec_extend_with_u64, u64);
    gen_extend_with_harness!(harness_vec_extend_with_unit, ());
    gen_extend_with_harness!(harness_vec_extend_with_array, [u8; 4]);
    gen_extend_with_harness!(harness_vec_extend_with_bool, bool);
    gen_extend_with_harness!(harness_vec_extend_with_with_drop, WithDrop);

    // Harnesses for `Vec::spec_extend_from_within`
    macro_rules! gen_vec_spec_extend_from_within_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Build a nondeterministic vector for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Snapshot the initial vector length and capacity
                let len = vec.len();
                let cap = vec.capacity();
                // Choose an in-bounds exclusive range start and end
                let end: usize = kani::any_where(|end: &usize| *end <= len);
                let start: usize = kani::any_where(|start: &usize| *start <= end);
                // Compute how many elements will be copied from the initialized prefix
                let count = end - start;
                // Precondition of `spec_extend_from_within`: the complete source
                // range must fit in the current spare capacity.
                let enough_spare = count <= cap - len;
                kani::assume(enough_spare);
                kani::cover(
                    enough_spare,
                    "spec_extend_from_within precondition: source range fits spare capacity",
                );
                kani::cover(count == 0, "spec_extend_from_within: empty source range");
                kani::cover(count > 0, "spec_extend_from_within: non-empty source range");
                // Get the size of each element in bytes for the raw memory overlap check
                let elem_size = core::mem::size_of::<$ty>();
                // Compute the total byte length of the copied region, rejecting overflow states
                // kani::assume(elem_size == 0 || count <= usize::MAX / elem_size);
                assert!(elem_size == 0 || count <= usize::MAX / elem_size);
                let copy_bytes = elem_size * count;
                // Skip raw pointer reasoning when the copied byte range is empty
                if copy_bytes != 0 {
                    // Compute the source byte pointer and destination byte pointer
                    let src_ptr = unsafe { vec.as_ptr().add(start) }.cast::<u8>();
                    let dst_ptr = unsafe { vec.as_mut_ptr().add(len) }.cast::<u8>();

                    // Tell Kani that the source and destination byte ranges do not overlap
                    // kani::assume(src_ptr.addr().abs_diff(dst_ptr.addr()) >= copy_bytes);
                    assert!(src_ptr.addr().abs_diff(dst_ptr.addr()) >= copy_bytes);
                }
                // Call the unsafe internal function under its preconditions
                unsafe {
                    vec.spec_extend_from_within(start..end);
                }
            }
        };
    }

    gen_vec_spec_extend_from_within_harness!(harness_vec_spec_extend_from_within_u8, u8);
    gen_vec_spec_extend_from_within_harness!(harness_vec_spec_extend_from_within_u64, u64);
    gen_vec_spec_extend_from_within_harness!(harness_vec_spec_extend_from_within_unit, ());
    gen_vec_spec_extend_from_within_harness!(harness_vec_spec_extend_from_within_bool, bool);
    gen_vec_spec_extend_from_within_harness!(harness_vec_spec_extend_from_within_array, [u8; 4]);

    // Harnesses for `Vec::deref`
    macro_rules! gen_vec_deref_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let vec = verifier_nondet_vec::<$ty>();
                // Borrow the Vec as an immutable slice
                let _: &[$ty] = vec.deref();
            }
        };
    }

    gen_vec_deref_harness!(harness_vec_deref_u8, u8);
    gen_vec_deref_harness!(harness_vec_deref_u64, u64);
    gen_vec_deref_harness!(harness_vec_deref_unit, ());
    gen_vec_deref_harness!(harness_vec_deref_bool, bool);
    gen_vec_deref_harness!(harness_vec_deref_array, [u8; 4]);

    // Harnesses for `Vec::deref_mut`
    macro_rules! gen_vec_deref_mut_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Borrow the Vec as a mutable slice
                let _: &mut [$ty] = vec.deref_mut();
            }
        };
    }

    gen_vec_deref_mut_harness!(harness_vec_deref_mut_u8, u8);
    gen_vec_deref_mut_harness!(harness_vec_deref_mut_u64, u64);
    gen_vec_deref_mut_harness!(harness_vec_deref_mut_unit, ());
    gen_vec_deref_mut_harness!(harness_vec_deref_mut_bool, bool);
    gen_vec_deref_mut_harness!(harness_vec_deref_mut_array, [u8; 4]);

    // Harnesses for `Vec::into_iter`
    macro_rules! gen_vec_into_iter_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let vec = verifier_nondet_vec::<$ty>();
                // Convert the Vec into its owning iterator
                let _ = vec.into_iter();
            }
        };
    }

    gen_vec_into_iter_harness!(harness_vec_into_iter_u8, u8);
    gen_vec_into_iter_harness!(harness_vec_into_iter_u64, u64);
    gen_vec_into_iter_harness!(harness_vec_into_iter_unit, ());
    gen_vec_into_iter_harness!(harness_vec_into_iter_bool, bool);
    gen_vec_into_iter_harness!(harness_vec_into_iter_array, [u8; 4]);

    #[kani::proof]
    fn harness_vec_into_iter_with_drop() {
        let vec = verifier_nondet_vec::<WithDrop>();
        // Verify transfer of ownership from Vec to IntoIter without entering the
        // compiler-generated symbolic-length drop glue for the iterator.
        let iter = vec.into_iter();
        core::mem::forget(iter);
    }

    // `extend_desugared` is verified with bounded loop unwinding instead of a
    // loop contract.
    // We initially attempted an unbounded proof by attaching a loop contract to
    // the shipped `while let` loop. That approach is not currently viable with
    // the pinned Kani version:
    // - The loop body may call `reserve`, which can reallocate the Vec. During
    //   loop-contract induction, Kani/CBMC must therefore model changes to the
    //   Vec's pointer, capacity, allocation lifetime, and deallocation of the old
    //   buffer. The resulting loop frame does not preserve enough allocation
    //   state to reason soundly about subsequent iterations, leading to spurious
    //   allocation/provenance failures such as invalid realloc/free operations.
    // - Strengthening the invariant with accessors such as `capacity()` is also
    //   not usable with the pinned Kani version because method calls in loop
    //   invariants are affected by Kani issue #4796: they may be lowered with
    //   missing arguments and replaced by non-deterministic values.
    // This is therefore a bounded end-to-end verification of the real
    // implementation, not an unbounded loop-contract proof.
    macro_rules! gen_vec_extend_desugared_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            #[kani::unwind(11)]
            pub fn $name() {
                // Create an arbitrary valid Vec state.
                let mut vec = verifier_nondet_vec::<$ty>();
                // Verify the exact shipped implementation for iterators containing
                // up to 10 elements.
                let n: usize = kani::any_where(|&x| x <= 10);
                // Constrain only allocation/layout representability. This does not
                // force the no-growth path: both existing-spare-capacity and
                // reserve/reallocation executions remain possible.
                assume_reserve_no_capacity_overflow::<$ty>(vec.len(), vec.capacity(), n);

                kani::cover(n == 0, "extend_desugared bounded: empty iterator");
                kani::cover(n == 1, "extend_desugared bounded: one element");
                kani::cover(n > 1, "extend_desugared bounded: multiple elements");
                kani::cover(n == 10, "extend_desugared bounded: maximum length");

                let iter = AnyIter::<$ty>::new(n);

                // Directly verify the real Vec::extend_desugared implementation.
                vec.extend_desugared(iter);
                finish(vec);
            }
        };
    }

    gen_vec_extend_desugared_harness!(harness_vec_extend_desugared_u8, u8);
    gen_vec_extend_desugared_harness!(harness_vec_extend_desugared_u64, u64);
    gen_vec_extend_desugared_harness!(harness_vec_extend_desugared_unit, ());
    gen_vec_extend_desugared_harness!(harness_vec_extend_desugared_array, [u8; 4]);
    gen_vec_extend_desugared_harness!(harness_vec_extend_desugared_bool, bool);
    gen_vec_extend_desugared_harness!(harness_vec_extend_desugared_with_drop, WithDrop);

    // `extend_trusted` is verified with bounded loop unwinding rather than an
    // unbounded loop contract.
    // We initially attempted to verify the iteration unboundedly by replacing the
    // hidden `Iterator::for_each` loop with an explicit verification loop carrying
    // a loop contract. This is not currently reliable with the pinned Kani version:
    // - Kani cannot attach a loop contract directly to the loop hidden inside
    //   `Iterator::for_each` / `fold`, requiring a verification-only transcription.
    // - The explicit loop must preserve the `TrustedLen` relation between the
    //   iterator's remaining elements and the number of elements already written.
    //   Expressing that relation naturally requires querying the iterator (for
    //   example through `size_hint()`), but method calls in loop invariants are
    //   affected by Kani issue #4796 and may be lowered to non-deterministic values.
    // - Attempts to work around the hidden-loop structure also exposed limitations
    //   in the pinned loop-contract MIR transformation for some control-flow shapes.
    //
    // Rather than rely on a Kani-only transcription that does not directly verify
    // the shipped implementation, these harnesses use bounded unwinding and execute
    // the real `Iterator::for_each` implementation below.
    // This is therefore a bounded end-to-end verification of the shipped
    // `extend_trusted` implementation, not an unbounded loop-contract proof.
    macro_rules! gen_vec_extend_trusted_harness {
        ($name:ident, $ty:ty) => {
            #[cfg(not(no_global_oom_handling))]
            #[kani::proof]
            #[kani::unwind(11)]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type.
                let mut vec = verifier_nondet_vec::<$ty>();
                // Directly verify the shipped `extend_trusted` implementation for
                // TrustedLen iterators containing up to 10 elements.
                let n: usize = kani::any_where(|&x| x <= 10);
                // Constrain allocation/layout representability for the initial
                // `reserve(n)`. This does not force a particular allocation path.
                assume_reserve_no_capacity_overflow::<$ty>(vec.len(), vec.capacity(), n);
                kani::cover(n == 0, "extend_trusted bounded: empty iterator");
                kani::cover(n == 1, "extend_trusted bounded: one element");
                kani::cover(n > 1, "extend_trusted bounded: multiple elements");
                kani::cover(n == 10, "extend_trusted bounded: maximum iterator length");
                // `AnyIter` provides an exact finite size hint and satisfies the
                // TrustedLen contract for exactly `n` symbolic elements.
                let iter = AnyIter::<$ty>::new(n);
                // Execute the real shipped implementation, including its
                // Iterator::for_each / fold iteration.
                vec.extend_trusted(iter);
                finish(vec);
            }
        };
    }

    gen_vec_extend_trusted_harness!(harness_vec_extend_trusted_u8, u8);
    gen_vec_extend_trusted_harness!(harness_vec_extend_trusted_u64, u64);
    gen_vec_extend_trusted_harness!(harness_vec_extend_trusted_unit, ());
    gen_vec_extend_trusted_harness!(harness_vec_extend_trusted_array, [u8; 4]);
    gen_vec_extend_trusted_harness!(harness_vec_extend_trusted_bool, bool);
    gen_vec_extend_trusted_harness!(harness_vec_extend_trusted_with_drop, WithDrop);

    // Harnesses for `Vec::extract_if`
    macro_rules! gen_vec_extract_if_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let mut vec = verifier_nondet_vec::<$ty>();
                // Choose a non-deterministic in-bounds extraction range
                let start = kani::any_where(|start: &usize| *start <= vec.len());
                let end = kani::any_where(|end: &usize| *end >= start && *end <= vec.len());
                // Extract elements from the selected range according to a non-deterministic predicate
                let iter = vec.extract_if(start..end, |_x| kani::any::<bool>());
                // Dropping an unconsumed ExtractIf restores the Vec's logical length.
                drop(iter);
                finish(vec);
            }
        };
    }

    gen_vec_extract_if_harness!(harness_vec_extract_if_u8, u8);
    gen_vec_extract_if_harness!(harness_vec_extract_if_u64, u64);
    gen_vec_extract_if_harness!(harness_vec_extract_if_unit, ());
    gen_vec_extract_if_harness!(harness_vec_extract_if_bool, bool);
    gen_vec_extract_if_harness!(harness_vec_extract_if_array, [u8; 4]);
    gen_vec_extract_if_harness!(harness_vec_extract_if_with_drop, WithDrop);

    // Harnesses for `Vec::drop`
    macro_rules! gen_vec_drop_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let vec = verifier_nondet_vec::<$ty>();
                // Drop the Vec and its initialized elements
                drop(vec);
            }
        };
    }

    gen_vec_drop_harness!(harness_vec_drop_u8, u8);
    gen_vec_drop_harness!(harness_vec_drop_u64, u64);
    gen_vec_drop_harness!(harness_vec_drop_unit, ());
    gen_vec_drop_harness!(harness_vec_drop_array, [u8; 4]);
    gen_vec_drop_harness!(harness_vec_drop_bool, bool);

    // Harnesses for `Vec::try_from`
    macro_rules! gen_vec_try_from_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a non-deterministic Vec for the target element type
                let vec = verifier_nondet_vec::<$ty>();
                // Try to convert the Vec into a fixed-size array
                let _: Result<[$ty; 4], Vec<$ty>> =
                    <[$ty; 4] as core::convert::TryFrom<Vec<$ty>>>::try_from(vec);
            }
        };
    }

    gen_vec_try_from_harness!(harness_vec_try_from_u8, u8);
    gen_vec_try_from_harness!(harness_vec_try_from_u64, u64);
    gen_vec_try_from_harness!(harness_vec_try_from_unit, ());
    gen_vec_try_from_harness!(harness_vec_try_from_bool, bool);
    gen_vec_try_from_harness!(harness_vec_try_from_array, [u8; 4]);

    mod bounded_evidence {
        //! Supplementary bounded evidence for paths that cannot currently be
        //! discharged with Kani loop contracts.
        //! The primary Challenge 23 harnesses remain unbounded except for
        //! `extend_desugared` and `extend_trusted`. The proofs in this module are
        //! additional evidence for `needs_drop` behavior and the default
        //! `Clone` specialization.
        //! `Vec` destruction, `truncate`, `clear`, and `Drain::drop` eventually
        //! execute compiler-generated slice drop glue. That loop has no source-level
        //! loop on which this module can attach a Kani loop contract, so these paths
        //! use bounded unwinding.
        //! The default `spec_extend_from_within` implementation similarly hides its
        //! iteration inside `zip` / `map` / `for_each`; `CloneOnly` is used here to
        //! force that implementation instead of the `TrivialClone` specialization.
        use super::*;

        fn bounded_with_drop_vec() -> Vec<WithDrop> {
            let mut vec = verifier_nondet_vec::<WithDrop>();
            // Pick a symbolic logical length for the compiler-generated
            // drop loop to be completely unwound. The original initialized prefix is
            // at least this long, so shortening the logical length preserves Vec's
            // memory-safety invariants.
            let len = kani::any_where(|len: &usize| *len <= 4 && *len <= vec.len());
            vec.len = len;
            vec
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_vec_drop_with_drop() {
            let vec = bounded_with_drop_vec();
            kani::cover(vec.len() == 0, "Vec::drop WithDrop: empty");
            kani::cover(vec.len() > 0, "Vec::drop WithDrop: non-empty");
            kani::cover(vec.len() == 4, "Vec::drop WithDrop: maximum bounded length");
            drop(vec);
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_vec_truncate_with_drop() {
            let mut vec = bounded_with_drop_vec();
            let old_len = vec.len();
            let new_len: usize = kani::any();
            kani::cover(new_len < old_len, "truncate WithDrop: drops elements");
            kani::cover(new_len >= old_len, "truncate WithDrop: no-op");
            kani::cover(
                old_len == 4 && new_len == 0,
                "truncate WithDrop: maximum bounded dropped suffix",
            );
            vec.truncate(new_len);
            drop(vec);
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_vec_clear_with_drop() {
            let mut vec = bounded_with_drop_vec();
            let old_len = vec.len();
            kani::cover(old_len == 0, "clear WithDrop: empty Vec");
            kani::cover(old_len > 0, "clear WithDrop: non-empty Vec");
            kani::cover(old_len == 4, "clear WithDrop: maximum bounded length");
            vec.clear();
            assert_eq!(vec.len(), 0);
            drop(vec);
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_vec_try_from_with_drop_success() {
            let vec = verifier_nondet_vec::<WithDrop>();
            if vec.len() != 4 {
                core::mem::forget(vec);
                return;
            }
            kani::cover(vec.len() == 4, "try_from WithDrop: exact array length");
            let result: Result<[WithDrop; 4], Vec<WithDrop>> =
                <[WithDrop; 4] as core::convert::TryFrom<Vec<WithDrop>>>::try_from(vec);
            assert!(result.is_ok());
            if let Ok(array) = result {
                drop(array);
            }
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_vec_drain_drop_with_drop() {
            let mut vec = bounded_with_drop_vec();
            let old_len = vec.len();
            let end = kani::any_where(|end: &usize| *end <= old_len);
            let start = kani::any_where(|start: &usize| *start <= end);
            kani::cover(start == end, "drain WithDrop: empty range");
            kani::cover(start < end, "drain WithDrop: non-empty range");
            kani::cover(
                old_len == 4 && start == 0 && end == old_len,
                "drain WithDrop: maximum bounded full drain",
            );
            let drain = vec.drain(start..end);
            drop(drain);
            drop(vec);
        }

        #[cfg(not(no_global_oom_handling))]
        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_vec_spec_extend_from_within_clone_only() {
            let mut vec = verifier_nondet_vec::<CloneOnly>();
            let len = vec.len();
            let cap = vec.capacity();

            // `CloneOnly` does not implement `TrivialClone`, so this reaches the
            // default per-element `Clone` implementation. Bound only the number of
            // clone iterations hidden inside `zip` / `map` / `for_each`.
            let count = kani::any_where(|count: &usize| {
                *count <= 4 && *count <= len && *count <= cap - len
            });
            let start = kani::any_where(|start: &usize| *start <= len - count);
            let end = start + count;
            kani::cover(count == 0, "spec_extend_from_within CloneOnly: empty range");
            kani::cover(count > 0, "spec_extend_from_within CloneOnly: non-empty range");
            kani::cover(
                count == 4,
                "spec_extend_from_within CloneOnly: maximum bounded clone count",
            );
            unsafe {
                vec.spec_extend_from_within(start..end);
            }
            finish(vec);
        }

        #[cfg(not(no_global_oom_handling))]
        #[kani::proof]
        #[kani::unwind(6)]
        fn bounded_vec_extend_from_within_clone_only() {
            let mut vec = verifier_nondet_vec::<CloneOnly>();
            let len = vec.len();
            let cap = vec.capacity();
            // Bound only the default Clone implementation's hidden iteration.
            // The surrounding Vec state, including its capacity, remains symbolic.
            let additional =
                kani::any_where(|additional: &usize| *additional <= 4 && *additional <= len);
            let start = kani::any_where(|start: &usize| *start <= len - additional);
            let end = start + additional;
            assume_reserve_no_capacity_overflow::<CloneOnly>(len, cap, additional);
            let old_spare = cap - len;
            kani::cover(additional == 0, "extend_from_within CloneOnly: empty range");
            kani::cover(additional > 0, "extend_from_within CloneOnly: non-empty range");
            kani::cover(
                additional == 4,
                "extend_from_within CloneOnly: maximum bounded clone count",
            );
            kani::cover(
                additional <= old_spare,
                "extend_from_within CloneOnly: existing spare capacity",
            );
            kani::cover(additional > old_spare, "extend_from_within CloneOnly: growth");
            vec.extend_from_within(start..end);
            finish(vec);
        }
    }
}
