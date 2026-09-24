use core::any::Any;
use core::error::Error;
#[cfg(not(no_global_oom_handling))]
use core::fmt;
#[cfg(kani)]
use core::kani;
use core::mem;
use core::pin::Pin;

use safety::{ensures, requires};

use crate::alloc::Allocator;
#[cfg(not(no_global_oom_handling))]
use crate::borrow::Cow;
use crate::boxed::Box;
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
        Box::clone_from_ref(slice)
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
        Box::clone_from_ref(s)
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
    #[requires(self.is::<T>())]
    #[ensures(|result: &Box<T, A>| {
        core::ub_checks::can_dereference(&**result as *const T)
    })]
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
    #[requires(self.is::<T>())]
    #[ensures(|result: &Box<T, A>| {
        core::ub_checks::can_dereference(&**result as *const T)
    })]
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
    #[requires(self.is::<T>())]
    #[ensures(|result: &Box<T, A>| {
        core::ub_checks::can_dereference(&**result as *const T)
    })]
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

// Challenge 29

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::fmt;

    use super::super::kani_box_harness_helpers::*;
    use super::*;
    use crate::string::String;

    // Kani cannot resolve proof_for_contract on generic trait-object methods.
    // Mirror the three downcast_unchecked contracts here; these checks exercise
    // the body but must be kept manually synchronized with the attributes.
    macro_rules! unchecked_downcast {
        ($name:ident, $object:ty, $ty:ty) => {
            #[kani::proof]
            fn $name() {
                let erased: Box<$object> = Box::new(kani::any::<$ty>());
                kani::assume(erased.is::<$ty>());
                let result = unsafe { erased.downcast_unchecked::<$ty>() };
                assert!(core::ub_checks::can_dereference(&*result as *const $ty));
                kani::cover(true, "Box::downcast_unchecked returns the requested type");
            }
        };
    }

    unchecked_downcast!(harness_box_dyn_any_downcast_unchecked_i32, dyn Any, i32);
    unchecked_downcast!(harness_box_dyn_any_downcast_unchecked_unit, dyn Any, ());
    unchecked_downcast!(harness_box_dyn_any_send_downcast_unchecked_i32, dyn Any + Send, i32);
    unchecked_downcast!(harness_box_dyn_any_send_downcast_unchecked_unit, dyn Any + Send, ());
    unchecked_downcast!(
        harness_box_dyn_any_send_sync_downcast_unchecked_i32,
        dyn Any + Send + Sync,
        i32
    );
    unchecked_downcast!(
        harness_box_dyn_any_send_sync_downcast_unchecked_unit,
        dyn Any + Send + Sync,
        ()
    );

    // Checks the named Box<dyn Any...>::downcast or <dyn Error...>::downcast.
    // A symbolic choice checks both branches, including the Error wrappers that
    // restore Send/Sync on failure after delegating to dyn Error::downcast.
    macro_rules! checked_downcast {
        ($name:ident, $object:ty, $ty:ty, $value:expr, $mismatch:expr) => {
            #[kani::proof]
            fn $name() {
                let matches: bool = kani::any();
                let erased: Box<$object> =
                    if matches { Box::new($value) } else { Box::new($mismatch) };
                assert_eq!(erased.downcast::<$ty>().is_ok(), matches);
                kani::cover(matches, "Box::downcast succeeds for matching type");
                kani::cover(!matches, "Box::downcast returns Err for mismatched type");
            }
        };
    }

    checked_downcast!(
        harness_box_dyn_any_downcast_i32,
        dyn Any,
        i32,
        kani::any::<i32>(),
        String::from("mismatch")
    );
    checked_downcast!(harness_box_dyn_any_downcast_unit, dyn Any, (), (), String::from("mismatch"));
    checked_downcast!(
        harness_box_dyn_any_send_downcast_i32,
        dyn Any + Send,
        i32,
        kani::any::<i32>(),
        String::from("mismatch")
    );
    checked_downcast!(
        harness_box_dyn_any_send_downcast_unit,
        dyn Any + Send,
        (),
        (),
        String::from("mismatch")
    );
    checked_downcast!(
        harness_box_dyn_any_send_sync_downcast_i32,
        dyn Any + Send + Sync,
        i32,
        kani::any::<i32>(),
        String::from("mismatch")
    );
    checked_downcast!(
        harness_box_dyn_any_send_sync_downcast_unit,
        dyn Any + Send + Sync,
        (),
        (),
        String::from("mismatch")
    );

    #[derive(Debug)]
    struct Witness<T>(T);

    impl<T: fmt::Debug> fmt::Display for Witness<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("witness")
        }
    }

    impl<T: fmt::Debug> Error for Witness<T> {}

    checked_downcast!(
        harness_box_dyn_error_downcast_byte,
        dyn Error,
        Witness<u8>,
        Witness(kani::any::<u8>()),
        fmt::Error
    );
    checked_downcast!(
        harness_box_dyn_error_downcast_unit,
        dyn Error,
        Witness<()>,
        Witness(()),
        fmt::Error
    );
    checked_downcast!(
        harness_box_dyn_error_send_downcast_byte,
        dyn Error + Send,
        Witness<u8>,
        Witness(kani::any::<u8>()),
        fmt::Error
    );
    checked_downcast!(
        harness_box_dyn_error_send_downcast_unit,
        dyn Error + Send,
        Witness<()>,
        Witness(()),
        fmt::Error
    );
    checked_downcast!(
        harness_box_dyn_error_send_sync_downcast_byte,
        dyn Error + Send + Sync,
        Witness<u8>,
        Witness(kani::any::<u8>()),
        fmt::Error
    );
    checked_downcast!(
        harness_box_dyn_error_send_sync_downcast_unit,
        dyn Error + Send + Sync,
        Witness<()>,
        Witness(()),
        fmt::Error
    );

    /// Checks <Box<str> as From<&str>>::from for empty and nonempty input.
    #[kani::proof]
    fn harness_box_from_str() {
        let value = if kani::any() { "" } else { "test" };
        let boxed = Box::<str>::from(value);
        assert_eq!(boxed.len(), value.len());
        // Compare an arbitrary byte without introducing a memcmp loop.
        if !value.is_empty() {
            let index = kani::any_where(|i: &usize| *i < value.len());
            assert_eq!(boxed.as_bytes()[index], value.as_bytes()[index]);
        }
        kani::cover(value.is_empty(), "Box::from str handles empty input");
        kani::cover(!value.is_empty(), "Box::from str handles nonempty input");
    }

    /// Checks <Box<[u8]> as From<Box<str>>>::from.
    #[kani::proof]
    fn harness_box_from_box_str_to_u8_slice() {
        let value = if kani::any() { "" } else { "test" };
        let bytes = Box::<[u8]>::from(Box::<str>::from(value));
        assert_eq!(bytes.len(), value.len());
        // Compare an arbitrary byte without introducing a memcmp loop.
        if !value.is_empty() {
            let index = kani::any_where(|i: &usize| *i < value.len());
            assert_eq!(bytes[index], value.as_bytes()[index]);
        }
        kani::cover(value.is_empty(), "Box<str> to bytes handles empty input");
        kani::cover(!value.is_empty(), "Box<str> to bytes handles nonempty input");
    }

    /// Checks From<&[u8]> through CloneToUninit's TrivialClone slice specialization.
    #[kani::proof]
    fn harness_box_from_slice_trivial_clone() {
        let source = verifier_nondet_vec_box::<u8>();
        let boxed = Box::<[u8]>::from(source.as_slice());
        assert_eq!(boxed.len(), source.len());
        // A symbolic index checks copying without iterating over the unbounded length.
        if !source.is_empty() {
            let index = kani::any_where(|i: &usize| *i < source.len());
            assert_eq!(boxed[index], source[index]);
        }
        kani::cover(source.is_empty(), "Box::from slice trivial clone handles empty input");
        kani::cover(!source.is_empty(), "Box::from slice trivial clone copies an element");
    }

    // Deriving Clone alone does not implement TrivialClone, so CopySpec uses
    // its generic element-wise Clone implementation.
    #[derive(Clone)]
    struct CloneOnly(u8);

    /// Checks From<&[CloneOnly]> through CloneToUninit's generic slice clone.
    #[kani::proof]
    #[kani::unwind(3)]
    fn harness_box_from_slice_clone() {
        // This element-wise clone path uses a bounded, independently symbolic
        // payload, including an empty slice. Other slice harnesses retain their
        // symbolic lengths without a small fixed cap.
        let values = [CloneOnly(kani::any()), CloneOnly(kani::any())];
        let source = kani::slice::any_slice_of_array(&values);
        let boxed = Box::<[CloneOnly]>::from(source);
        assert_eq!(boxed.len(), source.len());
        if !source.is_empty() {
            let index = kani::any_where(|i: &usize| *i < source.len());
            assert_eq!(boxed[index].0, source[index].0);
        }
        kani::cover(source.is_empty(), "Box::from slice clone handles empty input");
        kani::cover(!source.is_empty(), "Box::from slice clone copies an element");
    }

    // Symbolic lengths cover success (len == N) and failure for fixed N = 100.
    macro_rules! slice_to_array {
        ($name:ident, $ty:ty) => {
            mod $name {
                use super::*;
                const N: usize = 100;

                /// Checks TryFrom<Box<[T]>> for Box<[T; N]>.
                #[kani::proof]
                fn boxed_slice() {
                    let boxed = verifier_nondet_vec_box::<$ty>().into_boxed_slice();
                    let matches = boxed.len() == N;
                    assert_eq!(Box::<[$ty; N]>::try_from(boxed).is_ok(), matches);
                    kani::cover(matches, "Box slice to array accepts matching length");
                    kani::cover(!matches, "Box slice to array rejects mismatched length");
                }

                /// Checks TryFrom<Vec<T>> for Box<[T; N]>.
                #[kani::proof]
                fn vector() {
                    let vec = verifier_nondet_vec_box::<$ty>();
                    let matches = vec.len() == N;
                    assert_eq!(Box::<[$ty; N]>::try_from(vec).is_ok(), matches);
                    kani::cover(matches, "Box Vec to array accepts matching length");
                    kani::cover(!matches, "Box Vec to array rejects mismatched length");
                }
            }
        };
    }

    slice_to_array!(harness_box_try_from_array_i32, i32);
    slice_to_array!(harness_box_try_from_array_unit, ());
}
