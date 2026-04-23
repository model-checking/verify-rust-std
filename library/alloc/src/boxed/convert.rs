use core::any::Any;
use core::error::Error;
#[cfg(kani)]
use core::kani;
use core::mem;
use core::pin::Pin;
#[cfg(not(no_global_oom_handling))]
use core::{fmt, ptr};

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
impl<T: Copy> BoxFromSlice<T> for Box<[T]> {
    #[inline]
    fn from_slice(slice: &[T]) -> Self {
        let len = slice.len();
        let buf = RawVec::with_capacity(len);
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
    #[cfg_attr(kani, kani::requires(self.is::<T>()))]
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
    #[cfg_attr(kani, kani::requires(self.is::<T>()))]
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
    #[cfg_attr(kani, kani::requires(self.is::<T>()))]
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

// ==============================================================
// Challenge 29: Verify safety of Boxed functions harnesses
// ==============================================================

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod kani_box_convert_harness_helpers {
    use core::fmt;

    use super::*;

    pub trait VerifierErrorWitness {
        fn verifier_any() -> Self;
    }

    macro_rules! gen_verifier_error_type {
        ($name:ident) => {
            #[derive(Debug)]
            pub struct $name;

            impl fmt::Display for $name {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, stringify!($name))
                }
            }

            impl Error for $name {}

            impl VerifierErrorWitness for $name {
                fn verifier_any() -> Self {
                    $name
                }
            }
        };
        ($name:ident, $field:ty) => {
            #[derive(Debug)]
            pub struct $name(pub $field);

            impl fmt::Display for $name {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, stringify!($name))
                }
            }

            impl Error for $name {}

            impl VerifierErrorWitness for $name {
                fn verifier_any() -> Self {
                    $name(kani::any())
                }
            }
        };
    }

    gen_verifier_error_type!(UnitError);
    gen_verifier_error_type!(ByteError, u8);
    gen_verifier_error_type!(BoolError, bool);
    gen_verifier_error_type!(ArrayError, [u8; 4]);
    gen_verifier_error_type!(MismatchError, u8);
}

// === UNSAFE FUNCTIONS ===

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_394 {
    use super::*;

    // `proof_for_contract` currently fails to resolve targets such as
    // `Box<dyn Any>::downcast_unchecked::<T>`. This is not a failure to find
    // the method itself: Kani sees the inherent impl, but it does not bind the
    // full target path to a single contract target when the receiver is a
    // trait-object instantiation and the method is also generic. The failure
    // happens during target-path resolution, before contract checking starts.
    // These harnesses therefore use plain `#[kani::proof]` and restate the
    // contract's key precondition explicitly with `erased.is::<T>()`.
    macro_rules! gen_downcast_unchecked_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the target type.
                let value: $ty = kani::any();

                // Erase the concrete type behind a `dyn Any` box.
                let erased: Box<dyn Any> = Box::new(value);

                // Restate the contract precondition that the erased value is really a `$ty`.
                kani::assume(erased.is::<$ty>());

                // Perform the unchecked downcast back to the concrete box type.
                let _downcasted: Box<$ty> =
                    unsafe { Box::<dyn Any>::downcast_unchecked::<$ty>(erased) };
            }
        };
    }

    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_i8, i8);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_i16, i16);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_i32, i32);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_i64, i64);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_i128, i128);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_u8, u8);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_u16, u16);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_u32, u32);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_u64, u64);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_u128, u128);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_bool, bool);
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_unit, ());
    gen_downcast_unchecked_harness!(harness_box_dyn_any_downcast_unchecked_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_453 {
    use super::*;

    // `proof_for_contract` currently fails to resolve targets such as
    // `Box<dyn Any + Send>::downcast_unchecked::<T>`. This is not a failure to
    // find the method itself: Kani sees the inherent impl, but it does not
    // bind the full target path to a single contract target when the receiver
    // is a trait-object instantiation and the method is also generic. The
    // failure happens during target-path resolution, before contract checking
    // starts. These harnesses therefore use plain `#[kani::proof]` and
    // restate the contract's key precondition explicitly with `erased.is::<T>()`.
    macro_rules! gen_downcast_unchecked_send_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the target type.
                let value: $ty = kani::any();

                // Erase the concrete type behind a `dyn Any + Send` box.
                let erased: Box<dyn Any + Send> = Box::new(value);

                // Restate the contract precondition that the erased value is really a `$ty`.
                kani::assume(erased.is::<$ty>());

                // Perform the unchecked downcast back to the concrete box type.
                let _downcasted: Box<$ty> =
                    unsafe { Box::<dyn Any + Send>::downcast_unchecked::<$ty>(erased) };
            }
        };
    }

    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_i8, i8);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_i16, i16);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_i32, i32);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_i64, i64);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_i128, i128);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_u8, u8);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_u16, u16);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_u32, u32);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_u64, u64);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_u128, u128);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_bool, bool);
    gen_downcast_unchecked_send_harness!(harness_box_dyn_any_send_downcast_unchecked_unit, ());
    gen_downcast_unchecked_send_harness!(
        harness_box_dyn_any_send_downcast_unchecked_array,
        [u8; 4]
    );
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_512 {
    use super::*;

    // `proof_for_contract` currently fails to resolve targets such as
    // `Box<dyn Any + Send + Sync>::downcast_unchecked::<T>`. This is not a
    // failure to find the method itself: Kani sees the inherent impl, but it
    // does not bind the full target path to a single contract target when the
    // receiver is a trait-object instantiation and the method is also generic.
    // The failure happens during target-path resolution, before contract
    // checking starts. These harnesses therefore use plain `#[kani::proof]`
    // and restate the contract's key precondition explicitly with
    // `erased.is::<T>()`.
    macro_rules! gen_downcast_unchecked_send_sync_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic concrete value of the target type.
                let value: $ty = kani::any();

                // Erase the concrete type behind a `dyn Any + Send + Sync` box.
                let erased: Box<dyn Any + Send + Sync> = Box::new(value);

                // Restate the contract precondition that the erased value is really a `$ty`.
                kani::assume(erased.is::<$ty>());

                // Perform the unchecked downcast back to the concrete box type.
                let _downcasted: Box<$ty> =
                    unsafe { Box::<dyn Any + Send + Sync>::downcast_unchecked::<$ty>(erased) };
            }
        };
    }

    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_i8,
        i8
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_i16,
        i16
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_i32,
        i32
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_i64,
        i64
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_i128,
        i128
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_u8,
        u8
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_u16,
        u16
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_u32,
        u32
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_u64,
        u64
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_u128,
        u128
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_bool,
        bool
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_unit,
        ()
    );
    gen_downcast_unchecked_send_sync_harness!(
        harness_box_dyn_any_send_sync_downcast_unchecked_array,
        [u8; 4]
    );
}

// === SAFE FUNCTIONS ===

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_170 {
    use super::*;

    macro_rules! gen_box_from_str_harness {
        ($name:ident, $value:expr) => {
            #[kani::proof]
            pub fn $name() {
                // Convert the input string slice into a boxed string through `From<&str>`.
                let _boxed: Box<str> = Box::<str>::from($value);
            }
        };
    }

    gen_box_from_str_harness!(harness_box_from_str_empty, "");
    gen_box_from_str_harness!(harness_box_from_str_nonempty, "test");
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_251 {
    use super::*;

    macro_rules! gen_box_from_box_str_to_u8_slice_harness {
        ($name:ident, $value:expr) => {
            #[kani::proof]
            pub fn $name() {
                // Build the original boxed string whose backing allocation will be reinterpreted.
                let boxed: Box<str> = Box::<str>::from($value);

                // Convert the boxed string into a boxed byte slice through `From<Box<str, A>>`.
                let _boxed_bytes: Box<[u8]> = <Box<[u8]>>::from(boxed);
            }
        };
    }

    gen_box_from_box_str_to_u8_slice_harness!(harness_box_from_box_str_to_u8_slice_empty, "");
    gen_box_from_box_str_to_u8_slice_harness!(
        harness_box_from_box_str_to_u8_slice_nonempty,
        "test"
    );
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_304 {
    use super::super::kani_box_harness_helpers::*;
    use super::*;

    // `<Box<[T; N]> as TryFrom<Box<[T]>>>::try_from` branches only on
    // `boxed_slice.len() == N`.
    // The harness builds `boxed_slice` from a nondeterministic `Vec<T>`, so
    // the slice length is symbolic. With `N` fixed to 100, Kani explores:
    // - `vec.len() == 100`: the conversion takes the `Ok(...)` path and
    //   reinterprets the boxed slice in place as `Box<[T; 100]>`.
    // - `vec.len() != 100`: the length check fails and the conversion returns
    //   `Err(boxed_slice)` without reinterpreting the allocation as an array.
    macro_rules! gen_box_try_from_box_slice_to_array_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length determines the boxed slice metadata.
                let vec: Vec<$ty> = verifier_nondet_vec_box::<$ty>();

                // Convert the vector into the boxed slice consumed by `TryFrom`.
                let boxed_slice: Box<[$ty]> = vec.into_boxed_slice();

                // Fix the target array length used by the conversion attempt.
                const N: usize = 100;

                // Attempt the in-place conversion from a boxed slice into a boxed array.
                let _result: Result<Box<[$ty; N]>, Box<[$ty]>> =
                    <Box<[$ty; N]>>::try_from(boxed_slice);
            }
        };
    }

    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_i8, i8);
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_i16, i16);
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_i32, i32);
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_i64, i64);
    gen_box_try_from_box_slice_to_array_harness!(
        harness_box_try_from_box_slice_to_array_i128,
        i128
    );
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_u8, u8);
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_u16, u16);
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_u32, u32);
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_u64, u64);
    gen_box_try_from_box_slice_to_array_harness!(
        harness_box_try_from_box_slice_to_array_u128,
        u128
    );
    gen_box_try_from_box_slice_to_array_harness!(harness_box_try_from_box_slice_to_array_unit, ());
    gen_box_try_from_box_slice_to_array_harness!(
        harness_box_try_from_box_slice_to_array_array,
        [u8; 4]
    );
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_336 {
    use super::super::kani_box_harness_helpers::*;
    use super::*;

    // `<Box<[T; N]> as TryFrom<Vec<T>>>::try_from` branches explicitly only on
    // `vec.len() == N`.
    // The harness keeps the input vector length nondeterministic, so with `N`
    // fixed to 100, Kani explores:
    // - `vec.len() == 100`: the conversion first turns the vector into
    //   `Box<[T]>`, then reinterprets that boxed slice in place as
    //   `Box<[T; 100]>`.
    // - `vec.len() != 100`: the length check fails and the function returns
    //   `Err(vec)` without attempting the boxed-slice-to-array reinterpretation.
    macro_rules! gen_box_try_from_vec_to_array_harness {
        ($name:ident, $ty:ty) => {
            #[kani::proof]
            pub fn $name() {
                // Create a symbolic vector whose length drives the `TryFrom` branch.
                let vec: Vec<$ty> = verifier_nondet_vec_box::<$ty>();

                // Fix the target array length used by the conversion attempt.
                const N: usize = 100;

                // Attempt the conversion from a vector directly into a boxed array.
                let _result: Result<Box<[$ty; N]>, Vec<$ty>> = <Box<[$ty; N]>>::try_from(vec);
            }
        };
    }

    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_i8, i8);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_i16, i16);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_i32, i32);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_i64, i64);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_i128, i128);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_u8, u8);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_u16, u16);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_u32, u32);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_u64, u64);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_u128, u128);
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_unit, ());
    gen_box_try_from_vec_to_array_harness!(harness_box_try_from_vec_to_array_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_366 {
    use super::*;
    use crate::string::String;

    // `Box<dyn Any, A>::downcast::<T>` branches only on `self.is::<T>()`.
    // The safe wrapper uses that runtime type test to protect the internal
    // delegation to `downcast_unchecked::<T>()`:
    // - when `self.is::<T>()` is true, the function takes the `Ok(...)` path
    //   and forwards to the unchecked downcast, which is safe because the
    //   erased value is known to have the requested concrete type;
    // - when `self.is::<T>()` is false, the function returns `Err(self)` and
    //   never attempts the unchecked reinterpretation.
    // These harnesses cover both outcomes explicitly by constructing:
    // - a matching erased box whose concrete type is exactly `$ty`;
    // - a non-matching erased box whose concrete type is `String`.
    macro_rules! gen_box_dyn_any_downcast_harness {
        ($name:ident, $ty:ty) => {
            mod $name {
                use super::*;

                #[kani::proof]
                pub fn ok_path() {
                    // Create a symbolic concrete value of the requested target type.
                    let value: $ty = kani::any();

                    // Erase that concrete value behind a `dyn Any` box.
                    let erased: Box<dyn Any> = Box::new(value);

                    // Attempt the downcast with the matching target type.
                    let _result: Result<Box<$ty>, Box<dyn Any>> = erased.downcast::<$ty>();
                }

                #[kani::proof]
                pub fn err_path() {
                    // Create a concrete string used to force a mismatched erased type.
                    let value: String = String::from("mismatch");

                    // Erase that string behind a `dyn Any` box.
                    let erased: Box<dyn Any> = Box::new(value);

                    // Attempt the downcast with a target type that does not match `String`.
                    let _result: Result<Box<$ty>, Box<dyn Any>> = erased.downcast::<$ty>();
                }
            }
        };
    }

    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_i8, i8);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_i16, i16);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_i32, i32);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_i64, i64);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_i128, i128);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_u8, u8);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_u16, u16);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_u32, u32);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_u64, u64);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_u128, u128);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_unit, ());
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_bool, bool);
    gen_box_dyn_any_downcast_harness!(harness_box_dyn_any_downcast_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_426 {
    use super::*;
    use crate::string::String;

    // `Box<dyn Any + Send, A>::downcast::<T>` branches only on `self.is::<T>()`.
    // The safe wrapper uses that runtime type test to protect the internal
    // delegation to `downcast_unchecked::<T>()`:
    // - when `self.is::<T>()` is true, the function takes the `Ok(...)` path
    //   and forwards to the unchecked downcast, which is safe because the
    //   erased value is known to have the requested concrete type;
    // - when `self.is::<T>()` is false, the function returns `Err(self)` and
    //   never attempts the unchecked reinterpretation.
    // These harnesses cover both outcomes explicitly by constructing:
    // - a matching erased box whose concrete type is exactly `$ty`;
    // - a non-matching erased box whose concrete type is `String`.
    macro_rules! gen_box_dyn_any_send_downcast_harness {
        ($name:ident, $ty:ty) => {
            mod $name {
                use super::*;

                #[kani::proof]
                pub fn ok_path() {
                    // Create a symbolic concrete value of the requested target type.
                    let value: $ty = kani::any();

                    // Erase that concrete value behind a `dyn Any + Send` box.
                    let erased: Box<dyn Any + Send> = Box::new(value);

                    // Attempt the downcast with the matching target type.
                    let _result: Result<Box<$ty>, Box<dyn Any + Send>> = erased.downcast::<$ty>();
                }

                #[kani::proof]
                pub fn err_path() {
                    // Create a concrete string used to force a mismatched erased type.
                    let value: String = String::from("mismatch");

                    // Erase that string behind a `dyn Any + Send` box.
                    let erased: Box<dyn Any + Send> = Box::new(value);

                    // Attempt the downcast with a target type that does not match `String`.
                    let _result: Result<Box<$ty>, Box<dyn Any + Send>> = erased.downcast::<$ty>();
                }
            }
        };
    }

    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_i8, i8);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_i16, i16);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_i32, i32);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_i64, i64);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_i128, i128);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_u8, u8);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_u16, u16);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_u32, u32);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_u64, u64);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_u128, u128);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_unit, ());
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_bool, bool);
    gen_box_dyn_any_send_downcast_harness!(harness_box_dyn_any_send_downcast_array, [u8; 4]);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_486 {
    use super::*;
    use crate::string::String;

    // `Box<dyn Any + Send + Sync, A>::downcast::<T>` branches only on
    // `self.is::<T>()`.
    // The safe wrapper uses that runtime type test to protect the internal
    // delegation to `downcast_unchecked::<T>()`:
    // - when `self.is::<T>()` is true, the function takes the `Ok(...)` path
    //   and forwards to the unchecked downcast, which is safe because the
    //   erased value is known to have the requested concrete type;
    // - when `self.is::<T>()` is false, the function returns `Err(self)` and
    //   never attempts the unchecked reinterpretation.
    // These harnesses cover both outcomes explicitly by constructing:
    // - a matching erased box whose concrete type is exactly `$ty`;
    // - a non-matching erased box whose concrete type is `String`.
    macro_rules! gen_box_dyn_any_send_sync_downcast_harness {
        ($name:ident, $ty:ty) => {
            mod $name {
                use super::*;

                #[kani::proof]
                pub fn ok_path() {
                    // Create a symbolic concrete value of the requested target type.
                    let value: $ty = kani::any();

                    // Erase that concrete value behind a `dyn Any + Send + Sync` box.
                    let erased: Box<dyn Any + Send + Sync> = Box::new(value);

                    // Attempt the downcast with the matching target type.
                    let _result: Result<Box<$ty>, Box<dyn Any + Send + Sync>> =
                        erased.downcast::<$ty>();
                }

                #[kani::proof]
                pub fn err_path() {
                    // Create a concrete string used to force a mismatched erased type.
                    let value: String = String::from("mismatch");

                    // Erase that string behind a `dyn Any + Send + Sync` box.
                    let erased: Box<dyn Any + Send + Sync> = Box::new(value);

                    // Attempt the downcast with a target type that does not match `String`.
                    let _result: Result<Box<$ty>, Box<dyn Any + Send + Sync>> =
                        erased.downcast::<$ty>();
                }
            }
        };
    }

    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_i8, i8);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_i16, i16);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_i32, i32);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_i64, i64);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_i128, i128);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_u8, u8);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_u16, u16);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_u32, u32);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_u64, u64);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_u128, u128);
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_unit, ());
    gen_box_dyn_any_send_sync_downcast_harness!(harness_box_dyn_any_send_sync_downcast_bool, bool);
    gen_box_dyn_any_send_sync_downcast_harness!(
        harness_box_dyn_any_send_sync_downcast_array,
        [u8; 4]
    );
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_746 {
    use super::kani_box_convert_harness_helpers::*;
    use super::*;

    // `<dyn Error>::downcast::<T>` branches only on `self.is::<T>()`.
    // The safe wrapper uses that runtime type test to protect the raw pointer
    // reinterpretation in the `Ok(...)` path:
    // - when `self.is::<T>()` is true, the function extracts the raw
    //   `dyn Error` pointer from the box and reinterprets it as `*mut T`,
    //   which is safe because the erased value is known to have concrete type
    //   `T`;
    // - when `self.is::<T>()` is false, the function returns `Err(self)` and
    //   never performs the pointer reinterpretation.
    macro_rules! gen_box_dyn_error_downcast_harness {
        ($name:ident, $ty:ty) => {
            mod $name {
                use super::*;

                #[kani::proof]
                pub fn ok_path() {
                    // Create a concrete error value of the requested target type.
                    let value: $ty = <$ty as VerifierErrorWitness>::verifier_any();

                    // Erase that concrete error behind a `dyn Error` box.
                    let erased: Box<dyn Error> = Box::new(value);

                    // Attempt the downcast with the matching target type.
                    let _result: Result<Box<$ty>, Box<dyn Error>> = erased.downcast::<$ty>();
                }

                #[kani::proof]
                pub fn err_path() {
                    // Create a mismatched concrete error value.
                    let value: MismatchError = MismatchError(kani::any());

                    // Erase that mismatched value behind a `dyn Error` box.
                    let erased: Box<dyn Error> = Box::new(value);

                    // Attempt the downcast with a target type that does not match `MismatchError`.
                    let _result: Result<Box<$ty>, Box<dyn Error>> = erased.downcast::<$ty>();
                }
            }
        };
    }

    gen_box_dyn_error_downcast_harness!(harness_box_dyn_error_downcast_unit, UnitError);
    gen_box_dyn_error_downcast_harness!(harness_box_dyn_error_downcast_byte, ByteError);
    gen_box_dyn_error_downcast_harness!(harness_box_dyn_error_downcast_bool, BoolError);
    gen_box_dyn_error_downcast_harness!(harness_box_dyn_error_downcast_array, ArrayError);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_763 {
    use super::kani_box_convert_harness_helpers::*;
    use super::*;

    // `<dyn Error + Send>::downcast::<T>` delegates to `<dyn Error>::downcast`
    // after first coercing `Box<dyn Error + Send>` into `Box<dyn Error>`.
    // Its explicit branch behavior is therefore still determined by
    // `self.is::<T>()` inside the shared `dyn Error` downcast logic:
    // - when the erased error really has concrete type `T`, the delegated
    //   `dyn Error` downcast returns `Ok(Box<T>)`;
    // - otherwise the delegated call returns `Err(Box<dyn Error>)`, and this
    //   wrapper re-applies the `Send` marker with `mem::transmute`.
    macro_rules! gen_box_dyn_error_send_downcast_harness {
        ($name:ident, $ty:ty) => {
            mod $name {
                use super::*;

                #[kani::proof]
                pub fn ok_path() {
                    // Create a concrete error value of the requested target type.
                    let value: $ty = <$ty as VerifierErrorWitness>::verifier_any();

                    // Erase that concrete error behind a `dyn Error + Send` box.
                    let erased: Box<dyn Error + Send> = Box::new(value);

                    // Attempt the downcast with the matching target type.
                    let _result: Result<Box<$ty>, Box<dyn Error + Send>> = erased.downcast::<$ty>();
                }

                #[kani::proof]
                pub fn err_path() {
                    // Create a mismatched concrete error value.
                    let value: MismatchError = MismatchError(kani::any());

                    // Erase that mismatched value behind a `dyn Error + Send` box.
                    let erased: Box<dyn Error + Send> = Box::new(value);

                    // Attempt the downcast with a target type that does not match `MismatchError`.
                    let _result: Result<Box<$ty>, Box<dyn Error + Send>> = erased.downcast::<$ty>();
                }
            }
        };
    }

    gen_box_dyn_error_send_downcast_harness!(harness_box_dyn_error_send_downcast_unit, UnitError);
    gen_box_dyn_error_send_downcast_harness!(harness_box_dyn_error_send_downcast_byte, ByteError);
    gen_box_dyn_error_send_downcast_harness!(harness_box_dyn_error_send_downcast_bool, BoolError);
    gen_box_dyn_error_send_downcast_harness!(harness_box_dyn_error_send_downcast_array, ArrayError);
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_777 {
    use super::kani_box_convert_harness_helpers::*;
    use super::*;

    // `<dyn Error + Send + Sync>::downcast::<T>` also delegates to
    // `<dyn Error>::downcast` after coercing the boxed trait object to
    // `Box<dyn Error>`.
    // The branch structure is therefore again inherited from the shared
    // `dyn Error` downcast logic:
    // - when the erased error really has concrete type `T`, the delegated
    //   `dyn Error` downcast returns `Ok(Box<T>)`;
    // - otherwise the delegated call returns `Err(Box<dyn Error>)`, and this
    //   wrapper re-applies the `Send + Sync` markers with `mem::transmute`.
    macro_rules! gen_box_dyn_error_send_sync_downcast_harness {
        ($name:ident, $ty:ty) => {
            mod $name {
                use super::*;

                #[kani::proof]
                pub fn ok_path() {
                    // Create a concrete error value of the requested target type.
                    let value: $ty = <$ty as VerifierErrorWitness>::verifier_any();

                    // Erase that concrete error behind a `dyn Error + Send + Sync` box.
                    let erased: Box<dyn Error + Send + Sync> = Box::new(value);

                    // Attempt the downcast with the matching target type.
                    let _result: Result<Box<$ty>, Box<dyn Error + Send + Sync>> =
                        erased.downcast::<$ty>();
                }

                #[kani::proof]
                pub fn err_path() {
                    // Create a mismatched concrete error value.
                    let value: MismatchError = MismatchError(kani::any());

                    // Erase that mismatched value behind a `dyn Error + Send + Sync` box.
                    let erased: Box<dyn Error + Send + Sync> = Box::new(value);

                    // Attempt the downcast with a target type that does not match `MismatchError`.
                    let _result: Result<Box<$ty>, Box<dyn Error + Send + Sync>> =
                        erased.downcast::<$ty>();
                }
            }
        };
    }

    gen_box_dyn_error_send_sync_downcast_harness!(
        harness_box_dyn_error_send_sync_downcast_unit,
        UnitError
    );
    gen_box_dyn_error_send_sync_downcast_harness!(
        harness_box_dyn_error_send_sync_downcast_byte,
        ByteError
    );
    gen_box_dyn_error_send_sync_downcast_harness!(
        harness_box_dyn_error_send_sync_downcast_bool,
        BoolError
    );
    gen_box_dyn_error_send_sync_downcast_harness!(
        harness_box_dyn_error_send_sync_downcast_array,
        ArrayError
    );
}
