use core::any::Any;
#[cfg(not(no_global_oom_handling))]
use core::clone::TrivialClone;
use core::error::Error;
#[cfg(kani)]
use core::kani;
use core::mem;
use core::pin::Pin;
#[cfg(not(no_global_oom_handling))]
use core::{fmt, ptr};

use safety::{ensures, requires};

use crate::alloc::Allocator;
#[cfg(not(no_global_oom_handling))]
use crate::borrow::Cow;
use crate::boxed::Box;
#[cfg(not(no_global_oom_handling))]
use crate::raw_vec::RawVec;
#[cfg(not(no_global_oom_handling))]
use crate::str::from_boxed_utf8_unchecked;
#[cfg(not(no_global_oom_handling))]
use crate::string::String;
#[cfg(not(no_global_oom_handling))]
use crate::vec::Vec;

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "from_for_ptrs", since = "1.6.0")]
impl<T> From<T> for Box<T> {
    /// Converts a `T` into a `Box<T>`
    ///
    /// The conversion allocates on the heap and moves `t`
    /// from the stack into it.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let x = 5;
    /// let boxed = Box::new(5);
    ///
    /// assert_eq!(Box::from(x), boxed);
    /// ```
    fn from(t: T) -> Self {
        Box::new(t)
    }
}

#[stable(feature = "pin", since = "1.33.0")]
impl<T: ?Sized, A: Allocator> From<Box<T, A>> for Pin<Box<T, A>>
where
    A: 'static,
{
    /// Converts a `Box<T>` into a `Pin<Box<T>>`. If `T` does not implement [`Unpin`], then
    /// `*boxed` will be pinned in memory and unable to be moved.
    ///
    /// This conversion does not allocate on the heap and happens in place.
    ///
    /// This is also available via [`Box::into_pin`].
    ///
    /// Constructing and pinning a `Box` with <code><Pin<Box\<T>>>::from([Box::new]\(x))</code>
    /// can also be written more concisely using <code>[Box::pin]\(x)</code>.
    /// This `From` implementation is useful if you already have a `Box<T>`, or you are
    /// constructing a (pinned) `Box` in a different way than with [`Box::new`].
    fn from(boxed: Box<T, A>) -> Self {
        Box::into_pin(boxed)
    }
}

/// Specialization trait used for `From<&[T]>`.
#[cfg(not(no_global_oom_handling))]
trait BoxFromSlice<T> {
    fn from_slice(slice: &[T]) -> Self;
}

#[cfg(not(no_global_oom_handling))]
impl<T: Clone> BoxFromSlice<T> for Box<[T]> {
    #[inline]
    default fn from_slice(slice: &[T]) -> Self {
        slice.to_vec().into_boxed_slice()
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: TrivialClone> BoxFromSlice<T> for Box<[T]> {
    #[inline]
    fn from_slice(slice: &[T]) -> Self {
        let len = slice.len();
        let buf = RawVec::with_capacity(len);
        // SAFETY: since `T` implements `TrivialClone`, this is sound and
        // equivalent to the above.
        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), buf.ptr(), len);
            buf.into_box(slice.len()).assume_init()
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_slice", since = "1.17.0")]
impl<T: Clone> From<&[T]> for Box<[T]> {
    /// Converts a `&[T]` into a `Box<[T]>`
    ///
    /// This conversion allocates on the heap
    /// and performs a copy of `slice` and its contents.
    ///
    /// # Examples
    /// ```rust
    /// // create a &[u8] which will be used to create a Box<[u8]>
    /// let slice: &[u8] = &[104, 101, 108, 108, 111];
    /// let boxed_slice: Box<[u8]> = Box::from(slice);
    ///
    /// println!("{boxed_slice:?}");
    /// ```
    #[inline]
    fn from(slice: &[T]) -> Box<[T]> {
        <Self as BoxFromSlice<T>>::from_slice(slice)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_mut_slice", since = "1.84.0")]
impl<T: Clone> From<&mut [T]> for Box<[T]> {
    /// Converts a `&mut [T]` into a `Box<[T]>`
    ///
    /// This conversion allocates on the heap
    /// and performs a copy of `slice` and its contents.
    ///
    /// # Examples
    /// ```rust
    /// // create a &mut [u8] which will be used to create a Box<[u8]>
    /// let mut array = [104, 101, 108, 108, 111];
    /// let slice: &mut [u8] = &mut array;
    /// let boxed_slice: Box<[u8]> = Box::from(slice);
    ///
    /// println!("{boxed_slice:?}");
    /// ```
    #[inline]
    fn from(slice: &mut [T]) -> Box<[T]> {
        Self::from(&*slice)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_cow", since = "1.45.0")]
impl<T: Clone> From<Cow<'_, [T]>> for Box<[T]> {
    /// Converts a `Cow<'_, [T]>` into a `Box<[T]>`
    ///
    /// When `cow` is the `Cow::Borrowed` variant, this
    /// conversion allocates on the heap and copies the
    /// underlying slice. Otherwise, it will try to reuse the owned
    /// `Vec`'s allocation.
    #[inline]
    fn from(cow: Cow<'_, [T]>) -> Box<[T]> {
        match cow {
            Cow::Borrowed(slice) => Box::from(slice),
            Cow::Owned(slice) => Box::from(slice),
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_slice", since = "1.17.0")]
impl From<&str> for Box<str> {
    /// Converts a `&str` into a `Box<str>`
    ///
    /// This conversion allocates on the heap
    /// and performs a copy of `s`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let boxed: Box<str> = Box::from("hello");
    /// println!("{boxed}");
    /// ```
    #[inline]
    fn from(s: &str) -> Box<str> {
        unsafe { from_boxed_utf8_unchecked(Box::from(s.as_bytes())) }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_mut_slice", since = "1.84.0")]
impl From<&mut str> for Box<str> {
    /// Converts a `&mut str` into a `Box<str>`
    ///
    /// This conversion allocates on the heap
    /// and performs a copy of `s`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut original = String::from("hello");
    /// let original: &mut str = &mut original;
    /// let boxed: Box<str> = Box::from(original);
    /// println!("{boxed}");
    /// ```
    #[inline]
    fn from(s: &mut str) -> Box<str> {
        Self::from(&*s)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_cow", since = "1.45.0")]
impl From<Cow<'_, str>> for Box<str> {
    /// Converts a `Cow<'_, str>` into a `Box<str>`
    ///
    /// When `cow` is the `Cow::Borrowed` variant, this
    /// conversion allocates on the heap and copies the
    /// underlying `str`. Otherwise, it will try to reuse the owned
    /// `String`'s allocation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::borrow::Cow;
    ///
    /// let unboxed = Cow::Borrowed("hello");
    /// let boxed: Box<str> = Box::from(unboxed);
    /// println!("{boxed}");
    /// ```
    ///
    /// ```rust
    /// # use std::borrow::Cow;
    /// let unboxed = Cow::Owned("hello".to_string());
    /// let boxed: Box<str> = Box::from(unboxed);
    /// println!("{boxed}");
    /// ```
    #[inline]
    fn from(cow: Cow<'_, str>) -> Box<str> {
        match cow {
            Cow::Borrowed(s) => Box::from(s),
            Cow::Owned(s) => Box::from(s),
        }
    }
}

#[stable(feature = "boxed_str_conv", since = "1.19.0")]
impl<A: Allocator> From<Box<str, A>> for Box<[u8], A> {
    /// Converts a `Box<str>` into a `Box<[u8]>`
    ///
    /// This conversion does not allocate on the heap and happens in place.
    ///
    /// # Examples
    /// ```rust
    /// // create a Box<str> which will be used to create a Box<[u8]>
    /// let boxed: Box<str> = Box::from("hello");
    /// let boxed_str: Box<[u8]> = Box::from(boxed);
    ///
    /// // create a &[u8] which will be used to create a Box<[u8]>
    /// let slice: &[u8] = &[104, 101, 108, 108, 111];
    /// let boxed_slice = Box::from(slice);
    ///
    /// assert_eq!(boxed_slice, boxed_str);
    /// ```
    #[inline]
    fn from(s: Box<str, A>) -> Self {
        let (raw, alloc) = Box::into_raw_with_allocator(s);
        unsafe { Box::from_raw_in(raw as *mut [u8], alloc) }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_array", since = "1.45.0")]
impl<T, const N: usize> From<[T; N]> for Box<[T]> {
    /// Converts a `[T; N]` into a `Box<[T]>`
    ///
    /// This conversion moves the array to newly heap-allocated memory.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let boxed: Box<[u8]> = Box::from([4, 2]);
    /// println!("{boxed:?}");
    /// ```
    fn from(array: [T; N]) -> Box<[T]> {
        Box::new(array)
    }
}

/// Casts a boxed slice to a boxed array.
///
/// # Safety
///
/// `boxed_slice.len()` must be exactly `N`.
unsafe fn boxed_slice_as_array_unchecked<T, A: Allocator, const N: usize>(
    boxed_slice: Box<[T], A>,
) -> Box<[T; N], A> {
    debug_assert_eq!(boxed_slice.len(), N);

    let (ptr, alloc) = Box::into_raw_with_allocator(boxed_slice);
    // SAFETY: Pointer and allocator came from an existing box,
    // and our safety condition requires that the length is exactly `N`
    unsafe { Box::from_raw_in(ptr as *mut [T; N], alloc) }
}

#[stable(feature = "boxed_slice_try_from", since = "1.43.0")]
impl<T, const N: usize> TryFrom<Box<[T]>> for Box<[T; N]> {
    type Error = Box<[T]>;

    /// Attempts to convert a `Box<[T]>` into a `Box<[T; N]>`.
    ///
    /// The conversion occurs in-place and does not require a
    /// new memory allocation.
    ///
    /// # Errors
    ///
    /// Returns the old `Box<[T]>` in the `Err` variant if
    /// `boxed_slice.len()` does not equal `N`.
    fn try_from(boxed_slice: Box<[T]>) -> Result<Self, Self::Error> {
        if boxed_slice.len() == N {
            Ok(unsafe { boxed_slice_as_array_unchecked(boxed_slice) })
        } else {
            Err(boxed_slice)
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "boxed_array_try_from_vec", since = "1.66.0")]
impl<T, const N: usize> TryFrom<Vec<T>> for Box<[T; N]> {
    type Error = Vec<T>;

    /// Attempts to convert a `Vec<T>` into a `Box<[T; N]>`.
    ///
    /// Like [`Vec::into_boxed_slice`], this is in-place if `vec.capacity() == N`,
    /// but will require a reallocation otherwise.
    ///
    /// # Errors
    ///
    /// Returns the original `Vec<T>` in the `Err` variant if
    /// `boxed_slice.len()` does not equal `N`.
    ///
    /// # Examples
    ///
    /// This can be used with [`vec!`] to create an array on the heap:
    ///
    /// ```
    /// let state: Box<[f32; 100]> = vec![1.0; 100].try_into().unwrap();
    /// assert_eq!(state.len(), 100);
    /// ```
    fn try_from(vec: Vec<T>) -> Result<Self, Self::Error> {
        if vec.len() == N {
            let boxed_slice = vec.into_boxed_slice();
            Ok(unsafe { boxed_slice_as_array_unchecked(boxed_slice) })
        } else {
            Err(vec)
        }
    }
}

impl<A: Allocator> Box<dyn Any, A> {
    /// Attempts to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    ///
    /// fn print_if_string(value: Box<dyn Any>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Box::new(my_string));
    /// print_if_string(Box::new(0i8));
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn downcast<T: Any>(self) -> Result<Box<T, A>, Self> {
        if self.is::<T>() { unsafe { Ok(self.downcast_unchecked::<T>()) } } else { Err(self) }
    }

    /// Downcasts the box to a concrete type.
    ///
    /// For a safe alternative see [`downcast`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(downcast_unchecked)]
    ///
    /// use std::any::Any;
    ///
    /// let x: Box<dyn Any> = Box::new(1_usize);
    ///
    /// unsafe {
    ///     assert_eq!(*x.downcast_unchecked::<usize>(), 1);
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// The contained value must be of type `T`. Calling this method
    /// with the incorrect type is *undefined behavior*.
    ///
    /// [`downcast`]: Self::downcast
    #[inline]
    #[unstable(feature = "downcast_unchecked", issue = "90850")]
    #[requires((*self).is::<T>())]
    #[ensures(|result: &Box<T, A>| core::ptr::addr_eq(
        &raw const **result,
        old(&raw const *self as *const T),
    ))]
    pub unsafe fn downcast_unchecked<T: Any>(self) -> Box<T, A> {
        debug_assert!(self.is::<T>());
        unsafe {
            let (raw, alloc): (*mut dyn Any, _) = Box::into_raw_with_allocator(self);
            Box::from_raw_in(raw as *mut T, alloc)
        }
    }
}

impl<A: Allocator> Box<dyn Any + Send, A> {
    /// Attempts to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    ///
    /// fn print_if_string(value: Box<dyn Any + Send>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Box::new(my_string));
    /// print_if_string(Box::new(0i8));
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn downcast<T: Any>(self) -> Result<Box<T, A>, Self> {
        if self.is::<T>() { unsafe { Ok(self.downcast_unchecked::<T>()) } } else { Err(self) }
    }

    /// Downcasts the box to a concrete type.
    ///
    /// For a safe alternative see [`downcast`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(downcast_unchecked)]
    ///
    /// use std::any::Any;
    ///
    /// let x: Box<dyn Any + Send> = Box::new(1_usize);
    ///
    /// unsafe {
    ///     assert_eq!(*x.downcast_unchecked::<usize>(), 1);
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// The contained value must be of type `T`. Calling this method
    /// with the incorrect type is *undefined behavior*.
    ///
    /// [`downcast`]: Self::downcast
    #[inline]
    #[unstable(feature = "downcast_unchecked", issue = "90850")]
    #[requires((*self).is::<T>())]
    #[ensures(|result: &Box<T, A>| core::ptr::addr_eq(
        &raw const **result,
        old(&raw const *self as *const T),
    ))]
    pub unsafe fn downcast_unchecked<T: Any>(self) -> Box<T, A> {
        debug_assert!(self.is::<T>());
        unsafe {
            let (raw, alloc): (*mut (dyn Any + Send), _) = Box::into_raw_with_allocator(self);
            Box::from_raw_in(raw as *mut T, alloc)
        }
    }
}

impl<A: Allocator> Box<dyn Any + Send + Sync, A> {
    /// Attempts to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    ///
    /// fn print_if_string(value: Box<dyn Any + Send + Sync>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Box::new(my_string));
    /// print_if_string(Box::new(0i8));
    /// ```
    #[inline]
    #[stable(feature = "box_send_sync_any_downcast", since = "1.51.0")]
    pub fn downcast<T: Any>(self) -> Result<Box<T, A>, Self> {
        if self.is::<T>() { unsafe { Ok(self.downcast_unchecked::<T>()) } } else { Err(self) }
    }

    /// Downcasts the box to a concrete type.
    ///
    /// For a safe alternative see [`downcast`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(downcast_unchecked)]
    ///
    /// use std::any::Any;
    ///
    /// let x: Box<dyn Any + Send + Sync> = Box::new(1_usize);
    ///
    /// unsafe {
    ///     assert_eq!(*x.downcast_unchecked::<usize>(), 1);
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// The contained value must be of type `T`. Calling this method
    /// with the incorrect type is *undefined behavior*.
    ///
    /// [`downcast`]: Self::downcast
    #[inline]
    #[unstable(feature = "downcast_unchecked", issue = "90850")]
    #[requires((*self).is::<T>())]
    #[ensures(|result: &Box<T, A>| core::ptr::addr_eq(
        &raw const **result,
        old(&raw const *self as *const T),
    ))]
    pub unsafe fn downcast_unchecked<T: Any>(self) -> Box<T, A> {
        debug_assert!(self.is::<T>());
        unsafe {
            let (raw, alloc): (*mut (dyn Any + Send + Sync), _) =
                Box::into_raw_with_allocator(self);
            Box::from_raw_in(raw as *mut T, alloc)
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, E: Error + 'a> From<E> for Box<dyn Error + 'a> {
    /// Converts a type of [`Error`] into a box of dyn [`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::fmt;
    ///
    /// #[derive(Debug)]
    /// struct AnError;
    ///
    /// impl fmt::Display for AnError {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "An error")
    ///     }
    /// }
    ///
    /// impl Error for AnError {}
    ///
    /// let an_error = AnError;
    /// assert!(0 == size_of_val(&an_error));
    /// let a_boxed_error = Box::<dyn Error>::from(an_error);
    /// assert!(size_of::<Box<dyn Error>>() == size_of_val(&a_boxed_error))
    /// ```
    fn from(err: E) -> Box<dyn Error + 'a> {
        Box::new(err)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, E: Error + Send + Sync + 'a> From<E> for Box<dyn Error + Send + Sync + 'a> {
    /// Converts a type of [`Error`] + [`Send`] + [`Sync`] into a box of
    /// dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::fmt;
    ///
    /// #[derive(Debug)]
    /// struct AnError;
    ///
    /// impl fmt::Display for AnError {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "An error")
    ///     }
    /// }
    ///
    /// impl Error for AnError {}
    ///
    /// unsafe impl Send for AnError {}
    ///
    /// unsafe impl Sync for AnError {}
    ///
    /// let an_error = AnError;
    /// assert!(0 == size_of_val(&an_error));
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(an_error);
    /// assert!(
    ///     size_of::<Box<dyn Error + Send + Sync>>() == size_of_val(&a_boxed_error))
    /// ```
    fn from(err: E) -> Box<dyn Error + Send + Sync + 'a> {
        Box::new(err)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> From<String> for Box<dyn Error + Send + Sync + 'a> {
    /// Converts a [`String`] into a box of dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    ///
    /// let a_string_error = "a string error".to_string();
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(a_string_error);
    /// assert!(
    ///     size_of::<Box<dyn Error + Send + Sync>>() == size_of_val(&a_boxed_error))
    /// ```
    #[inline]
    fn from(err: String) -> Box<dyn Error + Send + Sync + 'a> {
        struct StringError(String);

        impl Error for StringError {}

        impl fmt::Display for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        // Purposefully skip printing "StringError(..)"
        impl fmt::Debug for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&self.0, f)
            }
        }

        Box::new(StringError(err))
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "string_box_error", since = "1.6.0")]
impl<'a> From<String> for Box<dyn Error + 'a> {
    /// Converts a [`String`] into a box of dyn [`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    ///
    /// let a_string_error = "a string error".to_string();
    /// let a_boxed_error = Box::<dyn Error>::from(a_string_error);
    /// assert!(size_of::<Box<dyn Error>>() == size_of_val(&a_boxed_error))
    /// ```
    fn from(str_err: String) -> Box<dyn Error + 'a> {
        let err1: Box<dyn Error + Send + Sync> = From::from(str_err);
        let err2: Box<dyn Error> = err1;
        err2
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> From<&str> for Box<dyn Error + Send + Sync + 'a> {
    /// Converts a [`str`] into a box of dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// [`str`]: prim@str
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    ///
    /// let a_str_error = "a str error";
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(a_str_error);
    /// assert!(
    ///     size_of::<Box<dyn Error + Send + Sync>>() == size_of_val(&a_boxed_error))
    /// ```
    #[inline]
    fn from(err: &str) -> Box<dyn Error + Send + Sync + 'a> {
        From::from(String::from(err))
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "string_box_error", since = "1.6.0")]
impl<'a> From<&str> for Box<dyn Error + 'a> {
    /// Converts a [`str`] into a box of dyn [`Error`].
    ///
    /// [`str`]: prim@str
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    ///
    /// let a_str_error = "a str error";
    /// let a_boxed_error = Box::<dyn Error>::from(a_str_error);
    /// assert!(size_of::<Box<dyn Error>>() == size_of_val(&a_boxed_error))
    /// ```
    fn from(err: &str) -> Box<dyn Error + 'a> {
        From::from(String::from(err))
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "cow_box_error", since = "1.22.0")]
impl<'a, 'b> From<Cow<'b, str>> for Box<dyn Error + Send + Sync + 'a> {
    /// Converts a [`Cow`] into a box of dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::borrow::Cow;
    ///
    /// let a_cow_str_error = Cow::from("a str error");
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(a_cow_str_error);
    /// assert!(
    ///     size_of::<Box<dyn Error + Send + Sync>>() == size_of_val(&a_boxed_error))
    /// ```
    fn from(err: Cow<'b, str>) -> Box<dyn Error + Send + Sync + 'a> {
        From::from(String::from(err))
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "cow_box_error", since = "1.22.0")]
impl<'a, 'b> From<Cow<'b, str>> for Box<dyn Error + 'a> {
    /// Converts a [`Cow`] into a box of dyn [`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::borrow::Cow;
    ///
    /// let a_cow_str_error = Cow::from("a str error");
    /// let a_boxed_error = Box::<dyn Error>::from(a_cow_str_error);
    /// assert!(size_of::<Box<dyn Error>>() == size_of_val(&a_boxed_error))
    /// ```
    fn from(err: Cow<'b, str>) -> Box<dyn Error + 'a> {
        From::from(String::from(err))
    }
}

impl dyn Error {
    /// Attempts to downcast the box to a concrete type.
    #[inline]
    #[stable(feature = "error_downcast", since = "1.3.0")]
    #[rustc_allow_incoherent_impl]
    pub fn downcast<T: Error + 'static>(self: Box<Self>) -> Result<Box<T>, Box<dyn Error>> {
        if self.is::<T>() {
            unsafe {
                let raw: *mut dyn Error = Box::into_raw(self);
                Ok(Box::from_raw(raw as *mut T))
            }
        } else {
            Err(self)
        }
    }
}

impl dyn Error + Send {
    /// Attempts to downcast the box to a concrete type.
    #[inline]
    #[stable(feature = "error_downcast", since = "1.3.0")]
    #[rustc_allow_incoherent_impl]
    pub fn downcast<T: Error + 'static>(self: Box<Self>) -> Result<Box<T>, Box<dyn Error + Send>> {
        let err: Box<dyn Error> = self;
        <dyn Error>::downcast(err).map_err(|s| unsafe {
            // Reapply the `Send` marker.
            mem::transmute::<Box<dyn Error>, Box<dyn Error + Send>>(s)
        })
    }
}

impl dyn Error + Send + Sync {
    /// Attempts to downcast the box to a concrete type.
    #[inline]
    #[stable(feature = "error_downcast", since = "1.3.0")]
    #[rustc_allow_incoherent_impl]
    pub fn downcast<T: Error + 'static>(self: Box<Self>) -> Result<Box<T>, Box<Self>> {
        let err: Box<dyn Error> = self;
        <dyn Error>::downcast(err).map_err(|s| unsafe {
            // Reapply the `Send + Sync` markers.
            mem::transmute::<Box<dyn Error>, Box<dyn Error + Send + Sync>>(s)
        })
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::kani;

    use super::*;
    use crate::alloc::Layout;

    // `proof_for_contract` resolves none of the three same-named `dyn`-self
    // downcast_unchecked impls at this kani version (their impl blocks live in
    // this module while `Box` lives in `boxed`, so the resolver renders them in
    // an `<impl ...>` path form no spelling can match); the contract is
    // exercised by construction below. Once the resolver handles that form,
    // this attribute becomes `proof_for_contract` and this note is deleted. The constructed space is every possible u32 payload
    // behind the erased type; the precondition (contained value is a u32)
    // admits no other erased type, and TypeId equality fixes the metadata.
    #[kani::proof]
    fn check_downcast_unchecked_any_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Any> = Box::new(v);
        let addr = &raw const *b as *const u32;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let d: Box<u32> = unsafe { b.downcast_unchecked::<u32>() };
        assert_eq!(*d, v);
        assert!(core::ptr::addr_eq(&raw const *d, addr));
    }

    // `proof_for_contract` resolves none of the three same-named `dyn`-self
    // downcast_unchecked impls at this kani version (their impl blocks live in
    // this module while `Box` lives in `boxed`, so the resolver renders them in
    // an `<impl ...>` path form no spelling can match); the contract is
    // exercised by construction below. Once the resolver handles that form,
    // this attribute becomes `proof_for_contract` and this note is deleted. The constructed space is every possible u32 payload
    // behind the erased type; the precondition (contained value is a u32)
    // admits no other erased type, and TypeId equality fixes the metadata.
    #[kani::proof]
    fn check_downcast_unchecked_any_send_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Any + Send> = Box::new(v);
        let addr = &raw const *b as *const u32;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let d: Box<u32> = unsafe { b.downcast_unchecked::<u32>() };
        assert_eq!(*d, v);
        assert!(core::ptr::addr_eq(&raw const *d, addr));
    }

    // `proof_for_contract` resolves none of the three same-named `dyn`-self
    // downcast_unchecked impls at this kani version (their impl blocks live in
    // this module while `Box` lives in `boxed`, so the resolver renders them in
    // an `<impl ...>` path form no spelling can match); the contract is
    // exercised by construction below. Once the resolver handles that form,
    // this attribute becomes `proof_for_contract` and this note is deleted. The constructed space is every possible u32 payload
    // behind the erased type; the precondition (contained value is a u32)
    // admits no other erased type, and TypeId equality fixes the metadata.
    #[kani::proof]
    fn check_downcast_unchecked_any_send_sync_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Any + Send + Sync> = Box::new(v);
        let addr = &raw const *b as *const u32;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let d: Box<u32> = unsafe { b.downcast_unchecked::<u32>() };
        assert_eq!(*d, v);
        assert!(core::ptr::addr_eq(&raw const *d, addr));
    }

    #[kani::proof]
    fn check_from_slice_u8() {
        let arr: [u8; 8] = kani::any();
        // n <= 8 mirrors the fixed 8-element source array, not a tractability cap.
        let n = kani::any_where(|n: &usize| *n <= 8);
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        kani::cover(n == 0, "empty slice");
        kani::cover(n > 0, "non-empty slice");
        let b: Box<[u8]> = Box::from(&arr[..n]);
        assert_eq!(b.len(), n);
        // A whole-slice `assert_eq!` compiles to a memcmp-style comparison that
        // CBMC unwinds far past this n<=8 bound; a symbolic-index single read
        // gives the same per-element guarantee without the unbounded unwind.
        if n > 0 {
            let i: usize = kani::any_where(|i: &usize| *i < n);
            assert_eq!(b[i], arr[i]);
        }
    }

    #[kani::proof]
    fn check_from_slice_u32() {
        let arr: [u32; 8] = kani::any();
        // n <= 8 mirrors the fixed 8-element source array, not a tractability cap.
        let n = kani::any_where(|n: &usize| *n <= 8);
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        kani::cover(n == 0, "empty slice");
        kani::cover(n > 0, "non-empty slice");
        let b: Box<[u32]> = Box::from(&arr[..n]);
        assert_eq!(b.len(), n);
        // A whole-slice `assert_eq!` compiles to a memcmp-style comparison that
        // CBMC unwinds far past this n<=8 bound; a symbolic-index single read
        // gives the same per-element guarantee without the unbounded unwind.
        if n > 0 {
            let i: usize = kani::any_where(|i: &usize| *i < n);
            assert_eq!(b[i], arr[i]);
        }
    }

    #[kani::proof]
    fn check_from_str() {
        let mut src: [u8; 8] = kani::any();
        src[0] &= 0x7f;
        src[1] &= 0x7f;
        src[2] &= 0x7f;
        src[3] &= 0x7f;
        src[4] &= 0x7f;
        src[5] &= 0x7f;
        src[6] &= 0x7f;
        src[7] &= 0x7f;
        // Symbolic ASCII content (masked to 0x7f): every byte is a valid 1-byte char, so every n <= len is a char boundary.
        let s = core::str::from_utf8(&src).unwrap();
        // n <= 8: the symbolic source array is 8 bytes; length stays fixed, content is symbolic (above).
        let n = kani::any_where(|n: &usize| *n <= 8);
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        // `.get()` (Option) rather than `&s[..n]` (Index): the Index panic
        // path unconditionally builds an error message via
        // `floor_char_boundary`, whose loop CBMC cannot cheaply bound even
        // though the panic itself is unreachable here.
        let b: Box<str> = Box::from(s.get(..n).unwrap());
        assert_eq!(b.len(), n);
        let addr = &raw const *b as *const u8;
        let bytes: Box<[u8]> = Box::from(b);
        assert_eq!(bytes.len(), n);
        assert!(core::ptr::addr_eq(&raw const *bytes as *const u8, addr));
        // Symbolic-index single-byte read (see check_from_slice_u8) stands in
        // for a whole-slice equality assert. `bytes` is the end of the
        // from(&str)->from(Box<str>) pipeline, so comparing it directly to the
        // original source covers both conversions transitively.
        if n > 0 {
            let i: usize = kani::any_where(|i: &usize| *i < n);
            assert_eq!(bytes[i], s.as_bytes()[i]);
        }
    }

    // No `TryFrom<Box<T>>` (single-value) impl exists; this harnesses the real
    // sibling conversion, `TryFrom<Vec<T>>`.
    #[kani::proof]
    fn check_try_from_vec_u32() {
        // N = 4: a small concrete arm size; n itself stays symbolic and both
        // n == N and n != N arms are covered.
        const N: usize = 4;
        let n: usize = kani::any_where(|n: &usize| Layout::array::<u32>(*n).is_ok());
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        // Built via new_zeroed_slice + assume_init (verified above) rather
        // than an unbounded push loop, whose symbolic unrolling exceeds the
        // object-bits budget.
        let zeroed: Box<[u32]> = unsafe { Box::new_zeroed_slice(n).assume_init() };
        let vec: Vec<u32> = zeroed.into_vec();
        kani::cover(n == N, "len == N arm reached");
        kani::cover(n != N, "len != N arm reached");
        let r: Result<Box<[u32; N]>, _> = vec.try_into();
        assert_eq!(r.is_ok(), n == N);
        if let Ok(arr) = r {
            let i: usize = kani::any_where(|i: &usize| *i < N);
            assert_eq!(arr[i], 0);
        }
    }

    // Single width (u32): payload bytes unread beyond TypeId dispatch; widths
    // exercised in the unsafe-fn families.
    // Every downcast harness below re-downcasts the Err arm's returned box to
    // its real type instead of letting it reach scope-end drop as a trait
    // object. Isolated by direct experiment: a lone `Box<dyn Any>` dropped
    // as-is (regardless of downcast's outcome) hits a kani limitation
    // ("Reached unstable vtable comparison 'Eq'" at
    // NonNull::<dyn Any>::as_ptr); the raw-pointer extraction inside
    // downcast_unchecked (used by both the success arm and this recovery
    // step) is unaffected. This also checks the doc's "Err(self)" claim: the
    // original value comes back unchanged.
    #[kani::proof]
    fn check_downcast_any_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Any> = Box::new(v);
        let addr = &raw const *b as *const u32;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let ok: Result<Box<u32>, Box<dyn Any>> = b.downcast();
        kani::cover(ok.is_ok(), "success arm reached");
        let ok_value = ok.unwrap();
        assert_eq!(*ok_value, v);
        assert!(core::ptr::addr_eq(&raw const *ok_value, addr));

        let w: u8 = kani::any();
        let b2: Box<dyn Any> = Box::new(w);
        let err: Result<Box<u32>, Box<dyn Any>> = b2.downcast();
        kani::cover(err.is_err(), "failure arm reached");
        let recovered: Result<Box<u8>, _> = err.unwrap_err().downcast();
        assert_eq!(*recovered.unwrap(), w);
    }

    #[kani::proof]
    fn check_downcast_any_send_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Any + Send> = Box::new(v);
        let addr = &raw const *b as *const u32;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let ok: Result<Box<u32>, Box<dyn Any + Send>> = b.downcast();
        kani::cover(ok.is_ok(), "success arm reached");
        let ok_value = ok.unwrap();
        assert_eq!(*ok_value, v);
        assert!(core::ptr::addr_eq(&raw const *ok_value, addr));

        let w: u8 = kani::any();
        let b2: Box<dyn Any + Send> = Box::new(w);
        let err: Result<Box<u32>, Box<dyn Any + Send>> = b2.downcast();
        kani::cover(err.is_err(), "failure arm reached");
        let recovered: Result<Box<u8>, _> = err.unwrap_err().downcast();
        assert_eq!(*recovered.unwrap(), w);
    }

    #[kani::proof]
    fn check_downcast_any_send_sync_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Any + Send + Sync> = Box::new(v);
        let addr = &raw const *b as *const u32;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let ok: Result<Box<u32>, Box<dyn Any + Send + Sync>> = b.downcast();
        kani::cover(ok.is_ok(), "success arm reached");
        let ok_value = ok.unwrap();
        assert_eq!(*ok_value, v);
        assert!(core::ptr::addr_eq(&raw const *ok_value, addr));

        let w: u8 = kani::any();
        let b2: Box<dyn Any + Send + Sync> = Box::new(w);
        let err: Result<Box<u32>, Box<dyn Any + Send + Sync>> = b2.downcast();
        kani::cover(err.is_err(), "failure arm reached");
        let recovered: Result<Box<u8>, _> = err.unwrap_err().downcast();
        assert_eq!(*recovered.unwrap(), w);
    }

    // Error-path sentinel for the `dyn Error` downcast family below. `Error:
    // Debug + Display` is the only bound; a static-string `Display` impl needs
    // no formatter machinery on the verified path.
    #[derive(Debug)]
    struct SentinelError(u32);
    impl core::fmt::Display for SentinelError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("sentinel")
        }
    }
    impl Error for SentinelError {}

    #[kani::proof]
    fn check_downcast_error_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Error> = Box::new(SentinelError(v));
        let addr = &raw const *b as *const SentinelError;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let ok = b.downcast::<SentinelError>();
        kani::cover(ok.is_ok(), "success arm reached");
        let ok_value = ok.unwrap();
        // `.0` on a bare `Box<SentinelError>` would hit `Box`'s own private
        // tuple field (visible from inside this crate) instead of
        // `SentinelError`'s; deref through `Box` first.
        assert_eq!((*ok_value).0, v);
        assert!(core::ptr::addr_eq(&raw const *ok_value, addr));

        // `core::fmt::Error: Error` holds at this toolchain (core/src/error.rs);
        // it stands in as the "wrong type" for the Err arm.
        let w: u32 = kani::any();
        let b2: Box<dyn Error> = Box::new(SentinelError(w));
        let err = b2.downcast::<core::fmt::Error>();
        kani::cover(err.is_err(), "failure arm reached");
        // See check_downcast_any_u32: re-downcast the Err arm's returned box
        // to its real type rather than letting it drop as a `dyn Error`
        // (same kani vtable-comparison limitation).
        let recovered = err.unwrap_err().downcast::<SentinelError>();
        assert_eq!((*recovered.unwrap()).0, w);
    }

    #[kani::proof]
    fn check_downcast_error_send_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Error + Send> = Box::new(SentinelError(v));
        let addr = &raw const *b as *const SentinelError;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let ok = b.downcast::<SentinelError>();
        kani::cover(ok.is_ok(), "success arm reached");
        let ok_value = ok.unwrap();
        // `.0` on a bare `Box<SentinelError>` would hit `Box`'s own private
        // tuple field (visible from inside this crate) instead of
        // `SentinelError`'s; deref through `Box` first.
        assert_eq!((*ok_value).0, v);
        assert!(core::ptr::addr_eq(&raw const *ok_value, addr));

        let w: u32 = kani::any();
        let b2: Box<dyn Error + Send> = Box::new(SentinelError(w));
        let err = b2.downcast::<core::fmt::Error>();
        kani::cover(err.is_err(), "failure arm reached");
        let recovered = err.unwrap_err().downcast::<SentinelError>();
        assert_eq!((*recovered.unwrap()).0, w);
    }

    #[kani::proof]
    fn check_downcast_error_send_sync_u32() {
        let v: u32 = kani::any();
        let b: Box<dyn Error + Send + Sync> = Box::new(SentinelError(v));
        let addr = &raw const *b as *const SentinelError;
        kani::cover(true, "non-vacuity witness: the assumed input space is non-empty");
        let ok = b.downcast::<SentinelError>();
        kani::cover(ok.is_ok(), "success arm reached");
        let ok_value = ok.unwrap();
        // `.0` on a bare `Box<SentinelError>` would hit `Box`'s own private
        // tuple field (visible from inside this crate) instead of
        // `SentinelError`'s; deref through `Box` first.
        assert_eq!((*ok_value).0, v);
        assert!(core::ptr::addr_eq(&raw const *ok_value, addr));

        let w: u32 = kani::any();
        let b2: Box<dyn Error + Send + Sync> = Box::new(SentinelError(w));
        let err = b2.downcast::<core::fmt::Error>();
        kani::cover(err.is_err(), "failure arm reached");
        let recovered = err.unwrap_err().downcast::<SentinelError>();
        assert_eq!((*recovered.unwrap()).0, w);
    }
}
