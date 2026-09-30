//! A UTF-8–encoded, growable string.
//!
//! This module contains the [`String`] type, the [`ToString`] trait for
//! converting to strings, and several error types that may result from
//! working with [`String`]s.
//!
//! # Examples
//!
//! There are multiple ways to create a new [`String`] from a string literal:
//!
//! ```
//! let s = "Hello".to_string();
//!
//! let s = String::from("world");
//! let s: String = "also this".into();
//! ```
//!
//! You can create a new [`String`] from an existing one by concatenating with
//! `+`:
//!
//! ```
//! let s = "Hello".to_string();
//!
//! let message = s + " world!";
//! ```
//!
//! If you have a vector of valid UTF-8 bytes, you can make a [`String`] out of
//! it. You can do the reverse too.
//!
//! ```
//! let sparkle_heart = vec![240, 159, 146, 150];
//!
//! // We know these bytes are valid, so we'll use `unwrap()`.
//! let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
//!
//! assert_eq!("💖", sparkle_heart);
//!
//! let bytes = sparkle_heart.into_bytes();
//!
//! assert_eq!(bytes, [240, 159, 146, 150]);
//! ```

#![stable(feature = "rust1", since = "1.0.0")]

use core::error::Error;
use core::iter::FusedIterator;
#[cfg(not(no_global_oom_handling))]
use core::iter::from_fn;
#[cfg(not(no_global_oom_handling))]
use core::num::Saturating;
#[cfg(not(no_global_oom_handling))]
use core::ops::Add;
#[cfg(not(no_global_oom_handling))]
use core::ops::AddAssign;
use core::ops::{self, Range, RangeBounds};
use core::str::pattern::{Pattern, Utf8Pattern};
use core::{fmt, hash, ptr, slice};

#[cfg(not(no_global_oom_handling))]
use crate::alloc::Allocator;
#[cfg(not(no_global_oom_handling))]
use crate::borrow::{Cow, ToOwned};
use crate::boxed::Box;
use crate::collections::TryReserveError;
use crate::str::{self, CharIndices, Chars, Utf8Error, from_utf8_unchecked_mut};
#[cfg(not(no_global_oom_handling))]
use crate::str::{FromStr, from_boxed_utf8_unchecked};
use crate::vec::{self, Vec};

/// A UTF-8–encoded, growable string.
///
/// `String` is the most common string type. It has ownership over the contents
/// of the string, stored in a heap-allocated buffer (see [Representation](#representation)).
/// It is closely related to its borrowed counterpart, the primitive [`str`].
///
/// # Examples
///
/// You can create a `String` from [a literal string][`&str`] with [`String::from`]:
///
/// [`String::from`]: From::from
///
/// ```
/// let hello = String::from("Hello, world!");
/// ```
///
/// You can append a [`char`] to a `String` with the [`push`] method, and
/// append a [`&str`] with the [`push_str`] method:
///
/// ```
/// let mut hello = String::from("Hello, ");
///
/// hello.push('w');
/// hello.push_str("orld!");
/// ```
///
/// [`push`]: String::push
/// [`push_str`]: String::push_str
///
/// If you have a vector of UTF-8 bytes, you can create a `String` from it with
/// the [`from_utf8`] method:
///
/// ```
/// // some bytes, in a vector
/// let sparkle_heart = vec![240, 159, 146, 150];
///
/// // We know these bytes are valid, so we'll use `unwrap()`.
/// let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
///
/// assert_eq!("💖", sparkle_heart);
/// ```
///
/// [`from_utf8`]: String::from_utf8
///
/// # UTF-8
///
/// `String`s are always valid UTF-8. If you need a non-UTF-8 string, consider
/// [`OsString`]. It is similar, but without the UTF-8 constraint. Because UTF-8
/// is a variable width encoding, `String`s are typically smaller than an array of
/// the same `char`s:
///
/// ```
/// // `s` is ASCII which represents each `char` as one byte
/// let s = "hello";
/// assert_eq!(s.len(), 5);
///
/// // A `char` array with the same contents would be longer because
/// // every `char` is four bytes
/// let s = ['h', 'e', 'l', 'l', 'o'];
/// let size: usize = s.into_iter().map(|c| size_of_val(&c)).sum();
/// assert_eq!(size, 20);
///
/// // However, for non-ASCII strings, the difference will be smaller
/// // and sometimes they are the same
/// let s = "💖💖💖💖💖";
/// assert_eq!(s.len(), 20);
///
/// let s = ['💖', '💖', '💖', '💖', '💖'];
/// let size: usize = s.into_iter().map(|c| size_of_val(&c)).sum();
/// assert_eq!(size, 20);
/// ```
///
/// This raises interesting questions as to how `s[i]` should work.
/// What should `i` be here? Several options include byte indices and
/// `char` indices but, because of UTF-8 encoding, only byte indices
/// would provide constant time indexing. Getting the `i`th `char`, for
/// example, is available using [`chars`]:
///
/// ```
/// let s = "hello";
/// let third_character = s.chars().nth(2);
/// assert_eq!(third_character, Some('l'));
///
/// let s = "💖💖💖💖💖";
/// let third_character = s.chars().nth(2);
/// assert_eq!(third_character, Some('💖'));
/// ```
///
/// Next, what should `s[i]` return? Because indexing returns a reference
/// to underlying data it could be `&u8`, `&[u8]`, or something similar.
/// Since we're only providing one index, `&u8` makes the most sense but that
/// might not be what the user expects and can be explicitly achieved with
/// [`as_bytes()`]:
///
/// ```
/// // The first byte is 104 - the byte value of `'h'`
/// let s = "hello";
/// assert_eq!(s.as_bytes()[0], 104);
/// // or
/// assert_eq!(s.as_bytes()[0], b'h');
///
/// // The first byte is 240 which isn't obviously useful
/// let s = "💖💖💖💖💖";
/// assert_eq!(s.as_bytes()[0], 240);
/// ```
///
/// Due to these ambiguities/restrictions, indexing with a `usize` is simply
/// forbidden:
///
/// ```compile_fail,E0277
/// let s = "hello";
///
/// // The following will not compile!
/// println!("The first letter of s is {}", s[0]);
/// ```
///
/// It is more clear, however, how `&s[i..j]` should work (that is,
/// indexing with a range). It should accept byte indices (to be constant-time)
/// and return a `&str` which is UTF-8 encoded. This is also called "string slicing".
/// Note this will panic if the byte indices provided are not character
/// boundaries - see [`is_char_boundary`] for more details. See the implementations
/// for [`SliceIndex<str>`] for more details on string slicing. For a non-panicking
/// version of string slicing, see [`get`].
///
/// [`OsString`]: ../../std/ffi/struct.OsString.html "ffi::OsString"
/// [`SliceIndex<str>`]: core::slice::SliceIndex
/// [`as_bytes()`]: str::as_bytes
/// [`get`]: str::get
/// [`is_char_boundary`]: str::is_char_boundary
///
/// The [`bytes`] and [`chars`] methods return iterators over the bytes and
/// codepoints of the string, respectively. To iterate over codepoints along
/// with byte indices, use [`char_indices`].
///
/// [`bytes`]: str::bytes
/// [`chars`]: str::chars
/// [`char_indices`]: str::char_indices
///
/// # Deref
///
/// `String` implements <code>[Deref]<Target = [str]></code>, and so inherits all of [`str`]'s
/// methods. In addition, this means that you can pass a `String` to a
/// function which takes a [`&str`] by using an ampersand (`&`):
///
/// ```
/// fn takes_str(s: &str) { }
///
/// let s = String::from("Hello");
///
/// takes_str(&s);
/// ```
///
/// This will create a [`&str`] from the `String` and pass it in. This
/// conversion is very inexpensive, and so generally, functions will accept
/// [`&str`]s as arguments unless they need a `String` for some specific
/// reason.
///
/// In certain cases Rust doesn't have enough information to make this
/// conversion, known as [`Deref`] coercion. In the following example a string
/// slice [`&'a str`][`&str`] implements the trait `TraitExample`, and the function
/// `example_func` takes anything that implements the trait. In this case Rust
/// would need to make two implicit conversions, which Rust doesn't have the
/// means to do. For that reason, the following example will not compile.
///
/// ```compile_fail,E0277
/// trait TraitExample {}
///
/// impl<'a> TraitExample for &'a str {}
///
/// fn example_func<A: TraitExample>(example_arg: A) {}
///
/// let example_string = String::from("example_string");
/// example_func(&example_string);
/// ```
///
/// There are two options that would work instead. The first would be to
/// change the line `example_func(&example_string);` to
/// `example_func(example_string.as_str());`, using the method [`as_str()`]
/// to explicitly extract the string slice containing the string. The second
/// way changes `example_func(&example_string);` to
/// `example_func(&*example_string);`. In this case we are dereferencing a
/// `String` to a [`str`], then referencing the [`str`] back to
/// [`&str`]. The second way is more idiomatic, however both work to do the
/// conversion explicitly rather than relying on the implicit conversion.
///
/// # Representation
///
/// A `String` is made up of three components: a pointer to some bytes, a
/// length, and a capacity. The pointer points to the internal buffer which `String`
/// uses to store its data. The length is the number of bytes currently stored
/// in the buffer, and the capacity is the size of the buffer in bytes. As such,
/// the length will always be less than or equal to the capacity.
///
/// This buffer is always stored on the heap.
///
/// You can look at these with the [`as_ptr`], [`len`], and [`capacity`]
/// methods:
///
/// ```
/// let story = String::from("Once upon a time...");
///
/// // Deconstruct the String into parts.
/// let (ptr, len, capacity) = story.into_raw_parts();
///
/// // story has nineteen bytes
/// assert_eq!(19, len);
///
/// // We can re-build a String out of ptr, len, and capacity. This is all
/// // unsafe because we are responsible for making sure the components are
/// // valid:
/// let s = unsafe { String::from_raw_parts(ptr, len, capacity) } ;
///
/// assert_eq!(String::from("Once upon a time..."), s);
/// ```
///
/// [`as_ptr`]: str::as_ptr
/// [`len`]: String::len
/// [`capacity`]: String::capacity
///
/// If a `String` has enough capacity, adding elements to it will not
/// re-allocate. For example, consider this program:
///
/// ```
/// let mut s = String::new();
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
///
/// This will output the following:
///
/// ```text
/// 0
/// 8
/// 16
/// 16
/// 32
/// 32
/// ```
///
/// At first, we have no memory allocated at all, but as we append to the
/// string, it increases its capacity appropriately. If we instead use the
/// [`with_capacity`] method to allocate the correct capacity initially:
///
/// ```
/// let mut s = String::with_capacity(25);
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
///
/// [`with_capacity`]: String::with_capacity
///
/// We end up with a different output:
///
/// ```text
/// 25
/// 25
/// 25
/// 25
/// 25
/// 25
/// ```
///
/// Here, there's no need to allocate more memory inside the loop.
///
/// [str]: prim@str "str"
/// [`str`]: prim@str "str"
/// [`&str`]: prim@str "&str"
/// [Deref]: core::ops::Deref "ops::Deref"
/// [`Deref`]: core::ops::Deref "ops::Deref"
/// [`as_str()`]: String::as_str
#[derive(PartialEq, PartialOrd, Eq, Ord)]
#[stable(feature = "rust1", since = "1.0.0")]
#[lang = "String"]
pub struct String {
    vec: Vec<u8>,
}

/// A possible error value when converting a `String` from a UTF-8 byte vector.
///
/// This type is the error type for the [`from_utf8`] method on [`String`]. It
/// is designed in such a way to carefully avoid reallocations: the
/// [`into_bytes`] method will give back the byte vector that was used in the
/// conversion attempt.
///
/// [`from_utf8`]: String::from_utf8
/// [`into_bytes`]: FromUtf8Error::into_bytes
///
/// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
/// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
/// an analogue to `FromUtf8Error`, and you can get one from a `FromUtf8Error`
/// through the [`utf8_error`] method.
///
/// [`Utf8Error`]: str::Utf8Error "std::str::Utf8Error"
/// [`std::str`]: core::str "std::str"
/// [`&str`]: prim@str "&str"
/// [`utf8_error`]: FromUtf8Error::utf8_error
///
/// # Examples
///
/// ```
/// // some invalid bytes, in a vector
/// let bytes = vec![0, 159];
///
/// let value = String::from_utf8(bytes);
///
/// assert!(value.is_err());
/// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
#[cfg_attr(not(no_global_oom_handling), derive(Clone))]
#[derive(Debug, PartialEq, Eq)]
pub struct FromUtf8Error {
    bytes: Vec<u8>,
    error: Utf8Error,
}

/// A possible error value when converting a `String` from a UTF-16 byte slice.
///
/// This type is the error type for the [`from_utf16`] method on [`String`].
///
/// [`from_utf16`]: String::from_utf16
///
/// # Examples
///
/// ```
/// // 𝄞mu<invalid>ic
/// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
///           0xD800, 0x0069, 0x0063];
///
/// assert!(String::from_utf16(v).is_err());
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Debug)]
pub struct FromUtf16Error(());

impl String {
    /// Creates a new empty `String`.
    ///
    /// Given that the `String` is empty, this will not allocate any initial
    /// buffer. While that means that this initial operation is very
    /// inexpensive, it may cause excessive allocation later when you add
    /// data. If you have an idea of how much data the `String` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: String::with_capacity
    ///
    /// # Examples
    ///
    /// ```
    /// let s = String::new();
    /// ```
    #[inline]
    #[rustc_const_stable(feature = "const_string_new", since = "1.39.0")]
    #[rustc_diagnostic_item = "string_new"]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    pub const fn new() -> String {
        String { vec: Vec::new() }
    }

    /// Creates a new empty `String` with at least the specified capacity.
    ///
    /// `String`s have an internal buffer to hold their data. The capacity is
    /// the length of that buffer, and can be queried with the [`capacity`]
    /// method. This method creates an empty `String`, but one with an initial
    /// buffer that can hold at least `capacity` bytes. This is useful when you
    /// may be appending a bunch of data to the `String`, reducing the number of
    /// reallocations it needs to do.
    ///
    /// [`capacity`]: String::capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: String::new
    ///
    /// # Panics
    ///
    /// Panics if the capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::with_capacity(10);
    ///
    /// // The String contains no chars, even though it has capacity for more
    /// assert_eq!(s.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// let cap = s.capacity();
    /// for _ in 0..10 {
    ///     s.push('a');
    /// }
    ///
    /// assert_eq!(s.capacity(), cap);
    ///
    /// // ...but this may make the string reallocate
    /// s.push('a');
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> String {
        String { vec: Vec::with_capacity(capacity) }
    }

    /// Creates a new empty `String` with at least the specified capacity.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the capacity exceeds `isize::MAX` bytes,
    /// or if the memory allocator reports failure.
    ///
    #[inline]
    #[unstable(feature = "try_with_capacity", issue = "91913")]
    pub fn try_with_capacity(capacity: usize) -> Result<String, TryReserveError> {
        Ok(String { vec: Vec::try_with_capacity(capacity)? })
    }

    /// Converts a vector of bytes to a `String`.
    ///
    /// A string ([`String`]) is made of bytes ([`u8`]), and a vector of bytes
    /// ([`Vec<u8>`]) is made of bytes, so this function converts between the
    /// two. Not all byte slices are valid `String`s, however: `String`
    /// requires that it is valid UTF-8. `from_utf8()` checks to ensure that
    /// the bytes are valid UTF-8, and then does the conversion.
    ///
    /// If you are sure that the byte slice is valid UTF-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe version
    /// of this function, [`from_utf8_unchecked`], which has the same behavior
    /// but skips the check.
    ///
    /// This method will take care to not copy the vector, for efficiency's
    /// sake.
    ///
    /// If you need a [`&str`] instead of a `String`, consider
    /// [`str::from_utf8`].
    ///
    /// The inverse of this method is [`into_bytes`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not UTF-8 with a description as to why the
    /// provided bytes are not UTF-8. The vector you moved in is also included.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// // We know these bytes are valid, so we'll use `unwrap()`.
    /// let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let sparkle_heart = vec![0, 159, 146, 150];
    ///
    /// assert!(String::from_utf8(sparkle_heart).is_err());
    /// ```
    ///
    /// See the docs for [`FromUtf8Error`] for more details on what you can do
    /// with this error.
    ///
    /// [`from_utf8_unchecked`]: String::from_utf8_unchecked
    /// [`Vec<u8>`]: crate::vec::Vec "Vec"
    /// [`&str`]: prim@str "&str"
    /// [`into_bytes`]: String::into_bytes
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_diagnostic_item = "string_from_utf8"]
    pub fn from_utf8(vec: Vec<u8>) -> Result<String, FromUtf8Error> {
        match str::from_utf8(&vec) {
            Ok(..) => Ok(String { vec }),
            Err(e) => Err(FromUtf8Error { bytes: vec, error: e }),
        }
    }

    /// Converts a slice of bytes to a string, including invalid characters.
    ///
    /// Strings are made of bytes ([`u8`]), and a slice of bytes
    /// ([`&[u8]`][byteslice]) is made of bytes, so this function converts
    /// between the two. Not all byte slices are valid strings, however: strings
    /// are required to be valid UTF-8. During this conversion,
    /// `from_utf8_lossy()` will replace any invalid UTF-8 sequences with
    /// [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD], which looks like this: �
    ///
    /// [byteslice]: prim@slice
    /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    ///
    /// If you are sure that the byte slice is valid UTF-8, and you don't want
    /// to incur the overhead of the conversion, there is an unsafe version
    /// of this function, [`from_utf8_unchecked`], which has the same behavior
    /// but skips the checks.
    ///
    /// [`from_utf8_unchecked`]: String::from_utf8_unchecked
    ///
    /// This function returns a [`Cow<'a, str>`]. If our byte slice is invalid
    /// UTF-8, then we need to insert the replacement characters, which will
    /// change the size of the string, and hence, require a `String`. But if
    /// it's already valid UTF-8, we don't need a new allocation. This return
    /// type allows us to handle both cases.
    ///
    /// [`Cow<'a, str>`]: crate::borrow::Cow "borrow::Cow"
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = String::from_utf8_lossy(&sparkle_heart);
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// // some invalid bytes
    /// let input = b"Hello \xF0\x90\x80World";
    /// let output = String::from_utf8_lossy(input);
    ///
    /// assert_eq!("Hello �World", output);
    /// ```
    #[must_use]
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn from_utf8_lossy(v: &[u8]) -> Cow<'_, str> {
        let mut iter = v.utf8_chunks();

        let Some(chunk) = iter.next() else {
            return Cow::Borrowed("");
        };
        let first_valid = chunk.valid();
        if chunk.invalid().is_empty() {
            debug_assert_eq!(first_valid.len(), v.len());
            return Cow::Borrowed(first_valid);
        }

        const REPLACEMENT: &str = "\u{FFFD}";

        let mut res = String::with_capacity(v.len());
        res.push_str(first_valid);
        res.push_str(REPLACEMENT);

        for chunk in iter {
            res.push_str(chunk.valid());
            if !chunk.invalid().is_empty() {
                res.push_str(REPLACEMENT);
            }
        }

        Cow::Owned(res)
    }

    /// Converts a [`Vec<u8>`] to a `String`, substituting invalid UTF-8
    /// sequences with replacement characters.
    ///
    /// See [`from_utf8_lossy`] for more details.
    ///
    /// [`from_utf8_lossy`]: String::from_utf8_lossy
    ///
    /// Note that this function does not guarantee reuse of the original `Vec`
    /// allocation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(string_from_utf8_lossy_owned)]
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = String::from_utf8_lossy_owned(sparkle_heart);
    ///
    /// assert_eq!(String::from("💖"), sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// #![feature(string_from_utf8_lossy_owned)]
    /// // some invalid bytes
    /// let input: Vec<u8> = b"Hello \xF0\x90\x80World".into();
    /// let output = String::from_utf8_lossy_owned(input);
    ///
    /// assert_eq!(String::from("Hello �World"), output);
    /// ```
    #[must_use]
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "string_from_utf8_lossy_owned", issue = "129436")]
    pub fn from_utf8_lossy_owned(v: Vec<u8>) -> String {
        if let Cow::Owned(string) = String::from_utf8_lossy(&v) {
            string
        } else {
            // SAFETY: `String::from_utf8_lossy`'s contract ensures that if
            // it returns a `Cow::Borrowed`, it is a valid UTF-8 string.
            // Otherwise, it returns a new allocation of an owned `String`, with
            // replacement characters for invalid sequences, which is returned
            // above.
            unsafe { String::from_utf8_unchecked(v) }
        }
    }

    /// Decode a native endian UTF-16–encoded vector `v` into a `String`,
    /// returning [`Err`] if `v` contains any invalid data.
    ///
    /// # Examples
    ///
    /// ```
    /// // 𝄞music
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0x0069, 0x0063];
    /// assert_eq!(String::from("𝄞music"),
    ///            String::from_utf16(v).unwrap());
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0xD800, 0x0069, 0x0063];
    /// assert!(String::from_utf16(v).is_err());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn from_utf16(v: &[u16]) -> Result<String, FromUtf16Error> {
        // This isn't done via collect::<Result<_, _>>() for performance reasons.
        // FIXME: the function can be simplified again when #48994 is closed.
        let mut ret = String::with_capacity(v.len());
        for c in char::decode_utf16(v.iter().cloned()) {
            let Ok(c) = c else {
                return Err(FromUtf16Error(()));
            };
            ret.push(c);
        }
        Ok(ret)
    }

    /// Decode a native endian UTF-16–encoded slice `v` into a `String`,
    /// replacing invalid data with [the replacement character (`U+FFFD`)][U+FFFD].
    ///
    /// Unlike [`from_utf8_lossy`] which returns a [`Cow<'a, str>`],
    /// `from_utf16_lossy` returns a `String` since the UTF-16 to UTF-8
    /// conversion requires a memory allocation.
    ///
    /// [`from_utf8_lossy`]: String::from_utf8_lossy
    /// [`Cow<'a, str>`]: crate::borrow::Cow "borrow::Cow"
    /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// ```
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0xDD1E, 0x0069, 0x0063,
    ///           0xD834];
    ///
    /// assert_eq!(String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            String::from_utf16_lossy(v));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn from_utf16_lossy(v: &[u16]) -> String {
        char::decode_utf16(v.iter().cloned())
            .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect()
    }

    /// Decode a UTF-16LE–encoded vector `v` into a `String`,
    /// returning [`Err`] if `v` contains any invalid data.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(str_from_utf16_endian)]
    /// // 𝄞music
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x73, 0x00, 0x69, 0x00, 0x63, 0x00];
    /// assert_eq!(String::from("𝄞music"),
    ///            String::from_utf16le(v).unwrap());
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x00, 0xD8, 0x69, 0x00, 0x63, 0x00];
    /// assert!(String::from_utf16le(v).is_err());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "str_from_utf16_endian", issue = "116258")]
    pub fn from_utf16le(v: &[u8]) -> Result<String, FromUtf16Error> {
        let (chunks, []) = v.as_chunks::<2>() else {
            return Err(FromUtf16Error(()));
        };
        match (cfg!(target_endian = "little"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16(v),
            _ => char::decode_utf16(chunks.iter().copied().map(u16::from_le_bytes))
                .collect::<Result<_, _>>()
                .map_err(|_| FromUtf16Error(())),
        }
    }

    /// Decode a UTF-16LE–encoded slice `v` into a `String`, replacing
    /// invalid data with [the replacement character (`U+FFFD`)][U+FFFD].
    ///
    /// Unlike [`from_utf8_lossy`] which returns a [`Cow<'a, str>`],
    /// `from_utf16le_lossy` returns a `String` since the UTF-16 to UTF-8
    /// conversion requires a memory allocation.
    ///
    /// [`from_utf8_lossy`]: String::from_utf8_lossy
    /// [`Cow<'a, str>`]: crate::borrow::Cow "borrow::Cow"
    /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(str_from_utf16_endian)]
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x73, 0x00, 0x1E, 0xDD, 0x69, 0x00, 0x63, 0x00,
    ///           0x34, 0xD8];
    ///
    /// assert_eq!(String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            String::from_utf16le_lossy(v));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "str_from_utf16_endian", issue = "116258")]
    pub fn from_utf16le_lossy(v: &[u8]) -> String {
        match (cfg!(target_endian = "little"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_remainder])) => Self::from_utf16_lossy(v) + "\u{FFFD}",
            _ => {
                let (chunks, remainder) = v.as_chunks::<2>();
                let string = char::decode_utf16(chunks.iter().copied().map(u16::from_le_bytes))
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect();
                if remainder.is_empty() { string } else { string + "\u{FFFD}" }
            }
        }
    }

    /// Decode a UTF-16BE–encoded vector `v` into a `String`,
    /// returning [`Err`] if `v` contains any invalid data.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(str_from_utf16_endian)]
    /// // 𝄞music
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0x00, 0x73, 0x00, 0x69, 0x00, 0x63];
    /// assert_eq!(String::from("𝄞music"),
    ///            String::from_utf16be(v).unwrap());
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0xD8, 0x00, 0x00, 0x69, 0x00, 0x63];
    /// assert!(String::from_utf16be(v).is_err());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "str_from_utf16_endian", issue = "116258")]
    pub fn from_utf16be(v: &[u8]) -> Result<String, FromUtf16Error> {
        let (chunks, []) = v.as_chunks::<2>() else {
            return Err(FromUtf16Error(()));
        };
        match (cfg!(target_endian = "big"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16(v),
            _ => char::decode_utf16(chunks.iter().copied().map(u16::from_be_bytes))
                .collect::<Result<_, _>>()
                .map_err(|_| FromUtf16Error(())),
        }
    }

    /// Decode a UTF-16BE–encoded slice `v` into a `String`, replacing
    /// invalid data with [the replacement character (`U+FFFD`)][U+FFFD].
    ///
    /// Unlike [`from_utf8_lossy`] which returns a [`Cow<'a, str>`],
    /// `from_utf16le_lossy` returns a `String` since the UTF-16 to UTF-8
    /// conversion requires a memory allocation.
    ///
    /// [`from_utf8_lossy`]: String::from_utf8_lossy
    /// [`Cow<'a, str>`]: crate::borrow::Cow "borrow::Cow"
    /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(str_from_utf16_endian)]
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0x00, 0x73, 0xDD, 0x1E, 0x00, 0x69, 0x00, 0x63,
    ///           0xD8, 0x34];
    ///
    /// assert_eq!(String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            String::from_utf16be_lossy(v));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "str_from_utf16_endian", issue = "116258")]
    pub fn from_utf16be_lossy(v: &[u8]) -> String {
        match (cfg!(target_endian = "big"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_remainder])) => Self::from_utf16_lossy(v) + "\u{FFFD}",
            _ => {
                let (chunks, remainder) = v.as_chunks::<2>();
                let string = char::decode_utf16(chunks.iter().copied().map(u16::from_be_bytes))
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect();
                if remainder.is_empty() { string } else { string + "\u{FFFD}" }
            }
        }
    }

    /// Decomposes a `String` into its raw components: `(pointer, length, capacity)`.
    ///
    /// Returns the raw pointer to the underlying data, the length of
    /// the string (in bytes), and the allocated capacity of the data
    /// (in bytes). These are the same arguments in the same order as
    /// the arguments to [`from_raw_parts`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `String`. The only way to do
    /// this is to convert the raw pointer, length, and capacity back
    /// into a `String` with the [`from_raw_parts`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`from_raw_parts`]: String::from_raw_parts
    ///
    /// # Examples
    ///
    /// ```
    /// let s = String::from("hello");
    ///
    /// let (ptr, len, cap) = s.into_raw_parts();
    ///
    /// let rebuilt = unsafe { String::from_raw_parts(ptr, len, cap) };
    /// assert_eq!(rebuilt, "hello");
    /// ```
    #[must_use = "losing the pointer will leak memory"]
    #[stable(feature = "vec_into_raw_parts", since = "1.93.0")]
    pub fn into_raw_parts(self) -> (*mut u8, usize, usize) {
        self.vec.into_raw_parts()
    }

    /// Creates a new `String` from a pointer, a length and a capacity.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * all safety requirements for [`Vec::<u8>::from_raw_parts`].
    /// * all safety requirements for [`String::from_utf8_unchecked`].
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example, it is normally **not** safe to
    /// build a `String` from a pointer to a C `char` array containing UTF-8
    /// _unless_ you are certain that array was originally allocated by the
    /// Rust standard library's allocator.
    ///
    /// The ownership of `buf` is effectively transferred to the
    /// `String` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// # Examples
    ///
    /// ```
    /// unsafe {
    ///     let s = String::from("hello");
    ///
    ///     // Deconstruct the String into parts.
    ///     let (ptr, len, capacity) = s.into_raw_parts();
    ///
    ///     let s = String::from_raw_parts(ptr, len, capacity);
    ///
    ///     assert_eq!(String::from("hello"), s);
    /// }
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> String {
        unsafe { String { vec: Vec::from_raw_parts(buf, length, capacity) } }
    }

    /// Converts a vector of bytes to a `String` without checking that the
    /// string contains valid UTF-8.
    ///
    /// See the safe version, [`from_utf8`], for more details.
    ///
    /// [`from_utf8`]: String::from_utf8
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `String`, as the rest of
    /// the standard library assumes that `String`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = unsafe {
    ///     String::from_utf8_unchecked(sparkle_heart)
    /// };
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> String {
        String { vec: bytes }
    }

    /// Converts a `String` into a byte vector.
    ///
    /// This consumes the `String`, so we do not need to copy its contents.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = String::from("hello");
    /// let bytes = s.into_bytes();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
    /// ```
    #[inline]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    #[rustc_allow_const_fn_unstable(const_precise_live_drops)]
    pub const fn into_bytes(self) -> Vec<u8> {
        self.vec
    }

    /// Extracts a string slice containing the entire `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = String::from("foo");
    ///
    /// assert_eq!("foo", s.as_str());
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "string_as_str", since = "1.7.0")]
    #[rustc_diagnostic_item = "string_as_str"]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn as_str(&self) -> &str {
        // SAFETY: String contents are stipulated to be valid UTF-8, invalid contents are an error
        // at construction.
        unsafe { str::from_utf8_unchecked(self.vec.as_slice()) }
    }

    /// Converts a `String` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("foobar");
    /// let s_mut_str = s.as_mut_str();
    ///
    /// s_mut_str.make_ascii_uppercase();
    ///
    /// assert_eq!("FOOBAR", s_mut_str);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "string_as_str", since = "1.7.0")]
    #[rustc_diagnostic_item = "string_as_mut_str"]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn as_mut_str(&mut self) -> &mut str {
        // SAFETY: String contents are stipulated to be valid UTF-8, invalid contents are an error
        // at construction.
        unsafe { str::from_utf8_unchecked_mut(self.vec.as_mut_slice()) }
    }

    /// Appends a given string slice onto the end of this `String`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// s.push_str("bar");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("append", "push")]
    #[rustc_diagnostic_item = "string_push_str"]
    pub fn push_str(&mut self, string: &str) {
        self.vec.extend_from_slice(string.as_bytes())
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    fn push_str_slice(&mut self, slice: &[&str]) {
        // use saturating arithmetic to ensure that in the case of an overflow, reserve() throws OOM
        let additional: Saturating<usize> = slice.iter().map(|x| Saturating(x.len())).sum();
        self.reserve(additional.0);
        let (ptr, len, cap) = core::mem::take(self).into_raw_parts();
        unsafe {
            let mut dst = ptr.add(len);
            for new in slice {
                core::ptr::copy_nonoverlapping(new.as_ptr(), dst, new.len());
                dst = dst.add(new.len());
            }
            *self = String::from_raw_parts(ptr, len + additional.0, cap);
        }
    }

    /// Copies elements from `src` range to the end of the string.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, if the range is
    /// bounded on either end and does not lie on a [`char`] boundary, or if the
    /// new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut string = String::from("abcde");
    ///
    /// string.extend_from_within(2..);
    /// assert_eq!(string, "abcdecde");
    ///
    /// string.extend_from_within(..2);
    /// assert_eq!(string, "abcdecdeab");
    ///
    /// string.extend_from_within(4..8);
    /// assert_eq!(string, "abcdecdeabecde");
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "string_extend_from_within", since = "1.87.0")]
    #[track_caller]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
    {
        let src @ Range { start, end } = slice::range(src, ..self.len());

        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        self.vec.extend_from_within(src);
    }

    /// Returns this `String`'s capacity, in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = String::with_capacity(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Reserves capacity for at least `additional` bytes more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::new();
    ///
    /// s.reserve(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This might not actually increase the capacity:
    ///
    /// ```
    /// let mut s = String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of at least 10
    /// let capacity = s.capacity();
    /// assert_eq!(2, s.len());
    /// assert!(capacity >= 10);
    ///
    /// // Since we already have at least an extra 8 capacity, calling this...
    /// s.reserve(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(capacity, s.capacity());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional)
    }

    /// Reserves the minimum capacity for at least `additional` bytes more than
    /// the current length. Unlike [`reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// [`reserve`]: String::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::new();
    ///
    /// s.reserve_exact(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This might not actually increase the capacity:
    ///
    /// ```
    /// let mut s = String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of at least 10
    /// let capacity = s.capacity();
    /// assert_eq!(2, s.len());
    /// assert!(capacity >= 10);
    ///
    /// // Since we already have at least an extra 8 capacity, calling this...
    /// s.reserve_exact(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(capacity, s.capacity());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional)
    }

    /// Tries to reserve capacity for at least `additional` bytes more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `try_reserve`, capacity will be
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
    /// fn process_data(data: &str) -> Result<String, TryReserveError> {
    ///     let mut output = String::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    #[stable(feature = "try_reserve", since = "1.57.0")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` bytes
    /// more than the current length. Unlike [`try_reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or
    /// equal to `self.len() + additional` if it returns `Ok(())`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: String::try_reserve
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
    /// fn process_data(data: &str) -> Result<String, TryReserveError> {
    ///     let mut output = String::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    #[stable(feature = "try_reserve", since = "1.57.0")]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `String` to match its length.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit()
    }

    /// Shrinks the capacity of this `String` with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to(10);
    /// assert!(s.capacity() >= 10);
    /// s.shrink_to(0);
    /// assert!(s.capacity() >= 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "shrink_to", since = "1.56.0")]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.vec.shrink_to(min_capacity)
    }

    /// Appends the given [`char`] to the end of this `String`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("abc");
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!("abc123", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn push(&mut self, ch: char) {
        let len = self.len();
        let ch_len = ch.len_utf8();
        self.reserve(ch_len);

        // SAFETY: Just reserved capacity for at least the length needed to encode `ch`.
        unsafe {
            core::char::encode_utf8_raw_unchecked(ch as u32, self.vec.as_mut_ptr().add(self.len()));
            self.vec.set_len(len + ch_len);
        }
    }

    /// Returns a byte slice of this `String`'s contents.
    ///
    /// The inverse of this method is [`from_utf8`].
    ///
    /// [`from_utf8`]: String::from_utf8
    ///
    /// # Examples
    ///
    /// ```
    /// let s = String::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const fn as_bytes(&self) -> &[u8] {
        self.vec.as_slice()
    }

    /// Shortens this `String` to the specified length.
    ///
    /// If `new_len` is greater than or equal to the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[track_caller]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `String` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("abč");
    ///
    /// assert_eq!(s.pop(), Some('č'));
    /// assert_eq!(s.pop(), Some('b'));
    /// assert_eq!(s.pop(), Some('a'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.vec.set_len(newlen);
        }
        Some(ch)
    }

    /// Removes a [`char`] from this `String` at byte position `idx` and returns it.
    ///
    /// Copies all bytes after the removed char to new positions.
    ///
    /// Note that calling this in a loop can result in quadratic behavior.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `String`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("abç");
    ///
    /// assert_eq!(s.remove(0), 'a');
    /// assert_eq!(s.remove(1), 'ç');
    /// assert_eq!(s.remove(0), 'b');
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[track_caller]
    #[rustc_confusables("delete", "take")]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(self.vec.as_ptr().add(next), self.vec.as_mut_ptr().add(idx), len - next);
            self.vec.set_len(len - (next - idx));
        }
        ch
    }

    /// Remove all matches of pattern `pat` in the `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(string_remove_matches)]
    /// let mut s = String::from("Trees are not green, the sky is not blue.");
    /// s.remove_matches("not ");
    /// assert_eq!("Trees are green, the sky is blue.", s);
    /// ```
    ///
    /// Matches will be detected and removed iteratively, so in cases where
    /// patterns overlap, only the first pattern will be removed:
    ///
    /// ```
    /// #![feature(string_remove_matches)]
    /// let mut s = String::from("banana");
    /// s.remove_matches("ana");
    /// assert_eq!("bna", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "string_remove_matches", issue = "72826")]
    pub fn remove_matches<P: Pattern>(&mut self, pat: P) {
        use core::str::pattern::Searcher;

        let rejections = {
            let mut searcher = pat.into_searcher(self);
            // Per Searcher::next:
            //
            // A Match result needs to contain the whole matched pattern,
            // however Reject results may be split up into arbitrary many
            // adjacent fragments. Both ranges may have zero length.
            //
            // In practice the implementation of Searcher::next_match tends to
            // be more efficient, so we use it here and do some work to invert
            // matches into rejections since that's what we want to copy below.
            let mut front = 0;
            let rejections: Vec<_> = from_fn(|| {
                let (start, end) = searcher.next_match()?;
                let prev_front = front;
                front = end;
                Some((prev_front, start))
            })
            .collect();
            rejections.into_iter().chain(core::iter::once((front, self.len())))
        };

        let mut len = 0;
        let ptr = self.vec.as_mut_ptr();

        for (start, end) in rejections {
            let count = end - start;
            if start != len {
                // SAFETY: per Searcher::next:
                //
                // The stream of Match and Reject values up to a Done will
                // contain index ranges that are adjacent, non-overlapping,
                // covering the whole haystack, and laying on utf8
                // boundaries.
                unsafe {
                    ptr::copy(ptr.add(start), ptr.add(len), count);
                }
            }
            len += count;
        }

        unsafe {
            self.vec.set_len(len);
        }
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place, visiting each character exactly once in the
    /// original order, and preserves the order of the retained characters.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("f_o_ob_ar");
    ///
    /// s.retain(|c| c != '_');
    ///
    /// assert_eq!(s, "foobar");
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// let mut s = String::from("abcde");
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// s.retain(|_| *iter.next().unwrap());
    /// assert_eq!(s, "bce");
    /// ```
    #[inline]
    #[stable(feature = "string_retain", since = "1.26.0")]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        struct SetLenOnDrop<'a> {
            s: &'a mut String,
            idx: usize,
            del_bytes: usize,
        }

        impl<'a> Drop for SetLenOnDrop<'a> {
            fn drop(&mut self) {
                let new_len = self.idx - self.del_bytes;
                debug_assert!(new_len <= self.s.len());
                unsafe { self.s.vec.set_len(new_len) };
            }
        }

        let len = self.len();
        let mut guard = SetLenOnDrop { s: self, idx: 0, del_bytes: 0 };

        while guard.idx < len {
            let ch =
                // SAFETY: `guard.idx` is positive-or-zero and less that len so the `get_unchecked`
                // is in bound. `self` is valid UTF-8 like string and the returned slice starts at
                // a unicode code point so the `Chars` always return one character.
                unsafe { guard.s.get_unchecked(guard.idx..len).chars().next().unwrap_unchecked() };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                guard.del_bytes += ch_len;
            } else if guard.del_bytes > 0 {
                // SAFETY: `guard.idx` is in bound and `guard.del_bytes` represent the number of
                // bytes that are erased from the string so the resulting `guard.idx -
                // guard.del_bytes` always represent a valid unicode code point.
                //
                // `guard.del_bytes` >= `ch.len_utf8()`, so taking a slice with `ch.len_utf8()` len
                // is safe.
                ch.encode_utf8(unsafe {
                    crate::slice::from_raw_parts_mut(
                        guard.s.as_mut_ptr().add(guard.idx - guard.del_bytes),
                        ch.len_utf8(),
                    )
                });
            }

            // Point idx to the next char
            guard.idx += ch_len;
        }

        drop(guard);
    }

    /// Inserts a character into this `String` at byte position `idx`.
    ///
    /// Reallocates if `self.capacity()` is insufficient, which may involve copying all
    /// `self.capacity()` bytes. Makes space for the insertion by copying all bytes of
    /// `&self[idx..]` to new positions.
    ///
    /// Note that calling this in a loop can result in quadratic behavior.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::with_capacity(3);
    ///
    /// s.insert(0, 'f');
    /// s.insert(1, 'o');
    /// s.insert(2, 'o');
    ///
    /// assert_eq!("foo", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("set")]
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx));

        let len = self.len();
        let ch_len = ch.len_utf8();
        self.reserve(ch_len);

        // SAFETY: Move the bytes starting from `idx` to their new location `ch_len`
        // bytes ahead. This is safe because sufficient capacity was reserved, and `idx`
        // is a char boundary.
        unsafe {
            ptr::copy(
                self.vec.as_ptr().add(idx),
                self.vec.as_mut_ptr().add(idx + ch_len),
                len - idx,
            );
        }

        // SAFETY: Encode the character into the vacated region if `idx != len`,
        // or into the uninitialized spare capacity otherwise.
        unsafe {
            core::char::encode_utf8_raw_unchecked(ch as u32, self.vec.as_mut_ptr().add(idx));
        }

        // SAFETY: Update the length to include the newly added bytes.
        unsafe {
            self.vec.set_len(len + ch_len);
        }
    }

    /// Inserts a string slice into this `String` at byte position `idx`.
    ///
    /// Reallocates if `self.capacity()` is insufficient, which may involve copying all
    /// `self.capacity()` bytes. Makes space for the insertion by copying all bytes of
    /// `&self[idx..]` to new positions.
    ///
    /// Note that calling this in a loop can result in quadratic behavior.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("bar");
    ///
    /// s.insert_str(0, "foo");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    #[stable(feature = "insert_str", since = "1.16.0")]
    #[rustc_diagnostic_item = "string_insert_str"]
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));

        let len = self.len();
        let amt = string.len();
        self.reserve(amt);

        // SAFETY: Move the bytes starting from `idx` to their new location `amt` bytes
        // ahead. This is safe because sufficient capacity was just reserved, and `idx`
        // is a char boundary.
        unsafe {
            ptr::copy(self.vec.as_ptr().add(idx), self.vec.as_mut_ptr().add(idx + amt), len - idx);
        }

        // SAFETY: Copy the new string slice into the vacated region if `idx != len`,
        // or into the uninitialized spare capacity otherwise. The borrow checker
        // ensures that the source and destination do not overlap.
        unsafe {
            ptr::copy_nonoverlapping(string.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
        }

        // SAFETY: Update the length to include the newly added bytes.
        unsafe {
            self.vec.set_len(len + amt);
        }
    }

    /// Returns a mutable reference to the contents of this `String`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid UTF-8. If this constraint is violated, using
    /// the original `String` after dropping the `&mut Vec` may violate memory
    /// safety, as the rest of the standard library assumes that `String`s are
    /// valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh");
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    pub const unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.vec
    }

    /// Returns the length of this `String`, in bytes, not [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = String::from("foo");
    /// assert_eq!(a.len(), 3);
    ///
    /// let fancy_f = String::from("ƒoo");
    /// assert_eq!(fancy_f.len(), 4);
    /// assert_eq!(fancy_f.chars().count(), 3);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    #[rustc_confusables("length", "size")]
    #[rustc_no_implicit_autorefs]
    pub const fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if this `String` has a length of zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = String::new();
    /// assert!(v.is_empty());
    ///
    /// v.push('a');
    /// assert!(!v.is_empty());
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_vec_string_slice", since = "1.87.0")]
    #[rustc_no_implicit_autorefs]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the string into two at the given byte index.
    ///
    /// Returns a newly allocated `String`. `self` contains bytes `[0, at)`, and
    /// the returned `String` contains bytes `[at, len)`. `at` must be on the
    /// boundary of a UTF-8 code point.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
    /// code point of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// let mut hello = String::from("Hello, World!");
    /// let world = hello.split_off(7);
    /// assert_eq!(hello, "Hello, ");
    /// assert_eq!(world, "World!");
    /// # }
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    #[stable(feature = "string_split_off", since = "1.16.0")]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> String {
        assert!(self.is_char_boundary(at));
        let other = self.vec.split_off(at);
        unsafe { String::from_utf8_unchecked(other) }
    }

    /// Truncates this `String`, removing all contents.
    ///
    /// While this means the `String` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn clear(&mut self) {
        self.vec.clear()
    }

    /// Removes the specified range from the string in bulk, returning all
    /// removed characters as an iterator.
    ///
    /// The returned iterator keeps a mutable borrow on the string to optimize
    /// its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and does not lie on a [`char`] boundary.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`core::mem::forget`], for example), the string may still contain a copy
    /// of any drained characters, or may have lost characters arbitrarily,
    /// including characters outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Remove the range up until the β from the string
    /// let t: String = s.drain(..beta_offset).collect();
    /// assert_eq!(t, "α is alpha, ");
    /// assert_eq!(s, "β is beta");
    ///
    /// // A full range clears the string, like `clear()` does
    /// s.drain(..);
    /// assert_eq!(s, "");
    /// ```
    #[stable(feature = "drain", since = "1.6.0")]
    #[track_caller]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // The String version of Drain does not have the memory safety issues
        // of the vector version. The data is just plain bytes.
        // Because the range removal happens in Drop, if the Drain iterator is leaked,
        // the removal will not happen.
        let Range { start, end } = slice::range(range, ..self.len());
        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        // Take out two simultaneous borrows. The &mut String won't be accessed
        // until iteration is over, in Drop.
        let self_ptr = self as *mut _;
        // SAFETY: `slice::range` and `is_char_boundary` do the appropriate bounds checks.
        let chars_iter = unsafe { self.get_unchecked(start..end) }.chars();

        Drain { start, end, iter: chars_iter, string: self_ptr }
    }

    /// Converts a `String` into an iterator over the [`char`]s of the string.
    ///
    /// As a string consists of valid UTF-8, we can iterate through a string
    /// by [`char`]. This method returns such an iterator.
    ///
    /// It's important to remember that [`char`] represents a Unicode Scalar
    /// Value, and might not match your idea of what a 'character' is. Iteration
    /// over grapheme clusters may be what you actually want. That functionality
    /// is not provided by Rust's standard library, check crates.io instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(string_into_chars)]
    ///
    /// let word = String::from("goodbye");
    ///
    /// let mut chars = word.into_chars();
    ///
    /// assert_eq!(Some('g'), chars.next());
    /// assert_eq!(Some('o'), chars.next());
    /// assert_eq!(Some('o'), chars.next());
    /// assert_eq!(Some('d'), chars.next());
    /// assert_eq!(Some('b'), chars.next());
    /// assert_eq!(Some('y'), chars.next());
    /// assert_eq!(Some('e'), chars.next());
    ///
    /// assert_eq!(None, chars.next());
    /// ```
    ///
    /// Remember, [`char`]s might not match your intuition about characters:
    ///
    /// ```
    /// #![feature(string_into_chars)]
    ///
    /// let y = String::from("y̆");
    ///
    /// let mut chars = y.into_chars();
    ///
    /// assert_eq!(Some('y'), chars.next()); // not 'y̆'
    /// assert_eq!(Some('\u{0306}'), chars.next());
    ///
    /// assert_eq!(None, chars.next());
    /// ```
    ///
    /// [`char`]: prim@char
    #[inline]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[unstable(feature = "string_into_chars", issue = "133125")]
    pub fn into_chars(self) -> IntoChars {
        IntoChars { bytes: self.into_bytes().into_iter() }
    }

    /// Removes the specified range in the string,
    /// and replaces it with the given string.
    /// The given string doesn't need to be the same length as the range.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Replace the range up until the β from the string
    /// s.replace_range(..beta_offset, "Α is capital alpha; ");
    /// assert_eq!(s, "Α is capital alpha; β is beta");
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "splice", since = "1.27.0")]
    #[track_caller]
    pub fn replace_range<R>(&mut self, range: R, replace_with: &str)
    where
        R: RangeBounds<usize>,
    {
        // We avoid #81138 (nondeterministic RangeBounds impls) because we only use `range` once, here.
        let checked_range = slice::range(range, ..self.len());

        assert!(
            self.is_char_boundary(checked_range.start),
            "start of range should be a character boundary"
        );
        assert!(
            self.is_char_boundary(checked_range.end),
            "end of range should be a character boundary"
        );

        unsafe { self.as_mut_vec() }.splice(checked_range, replace_with.bytes());
    }

    /// Replaces the leftmost occurrence of a pattern with another string, in-place.
    ///
    /// This method can be preferred over [`string = string.replacen(..., 1);`][replacen],
    /// as it can use the `String`'s existing capacity to prevent a reallocation if
    /// sufficient space is available.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(string_replace_in_place)]
    ///
    /// let mut s = String::from("Test Results: ❌❌❌");
    ///
    /// // Replace the leftmost ❌ with a ✅
    /// s.replace_first('❌', "✅");
    /// assert_eq!(s, "Test Results: ✅❌❌");
    /// ```
    ///
    /// [replacen]: ../../std/primitive.str.html#method.replacen
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "string_replace_in_place", issue = "147949")]
    pub fn replace_first<P: Pattern>(&mut self, from: P, to: &str) {
        let range = match self.match_indices(from).next() {
            Some((start, match_str)) => start..start + match_str.len(),
            None => return,
        };

        self.replace_range(range, to);
    }

    /// Replaces the rightmost occurrence of a pattern with another string, in-place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(string_replace_in_place)]
    ///
    /// let mut s = String::from("Test Results: ❌❌❌");
    ///
    /// // Replace the rightmost ❌ with a ✅
    /// s.replace_last('❌', "✅");
    /// assert_eq!(s, "Test Results: ❌❌✅");
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "string_replace_in_place", issue = "147949")]
    pub fn replace_last<P: Pattern>(&mut self, from: P, to: &str)
    where
        for<'a> P::Searcher<'a>: core::str::pattern::ReverseSearcher<'a>,
    {
        let range = match self.rmatch_indices(from).next() {
            Some((start, match_str)) => start..start + match_str.len(),
            None => return,
        };

        self.replace_range(range, to);
    }

    /// Converts this `String` into a <code>[Box]<[str]></code>.
    ///
    /// Before doing the conversion, this method discards excess capacity like [`shrink_to_fit`].
    /// Note that this call may reallocate and copy the bytes of the string.
    ///
    /// [`shrink_to_fit`]: String::shrink_to_fit
    /// [str]: prim@str "str"
    ///
    /// # Examples
    ///
    /// ```
    /// let s = String::from("hello");
    ///
    /// let b = s.into_boxed_str();
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "box_str", since = "1.4.0")]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[inline]
    pub fn into_boxed_str(self) -> Box<str> {
        let slice = self.vec.into_boxed_slice();
        unsafe { from_boxed_utf8_unchecked(slice) }
    }

    /// Consumes and leaks the `String`, returning a mutable reference to the contents,
    /// `&'a mut str`.
    ///
    /// The caller has free choice over the returned lifetime, including `'static`. Indeed,
    /// this function is ideally used for data that lives for the remainder of the program's life,
    /// as dropping the returned reference will cause a memory leak.
    ///
    /// It does not reallocate or shrink the `String`, so the leaked allocation may include unused
    /// capacity that is not part of the returned slice. If you want to discard excess capacity,
    /// call [`into_boxed_str`], and then [`Box::leak`] instead. However, keep in mind that
    /// trimming the capacity may result in a reallocation and copy.
    ///
    /// [`into_boxed_str`]: Self::into_boxed_str
    ///
    /// # Examples
    ///
    /// ```
    /// let x = String::from("bucket");
    /// let static_ref: &'static mut str = x.leak();
    /// assert_eq!(static_ref, "bucket");
    /// # // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// # // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// # drop(unsafe { Box::from_raw(static_ref) });
    /// ```
    #[stable(feature = "string_leak", since = "1.72.0")]
    #[inline]
    pub fn leak<'a>(self) -> &'a mut str {
        let slice = self.vec.leak();
        unsafe { from_utf8_unchecked_mut(slice) }
    }
}

impl FromUtf8Error {
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = String::from_utf8(bytes);
    ///
    /// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
    /// ```
    #[must_use]
    #[stable(feature = "from_utf8_error_as_bytes", since = "1.26.0")]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Converts the bytes into a `String` lossily, substituting invalid UTF-8
    /// sequences with replacement characters.
    ///
    /// See [`String::from_utf8_lossy`] for more details on replacement of
    /// invalid sequences, and [`String::from_utf8_lossy_owned`] for the
    /// `String` function which corresponds to this function.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(string_from_utf8_lossy_owned)]
    /// // some invalid bytes
    /// let input: Vec<u8> = b"Hello \xF0\x90\x80World".into();
    /// let output = String::from_utf8(input).unwrap_or_else(|e| e.into_utf8_lossy());
    ///
    /// assert_eq!(String::from("Hello �World"), output);
    /// ```
    #[must_use]
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "string_from_utf8_lossy_owned", issue = "129436")]
    pub fn into_utf8_lossy(self) -> String {
        const REPLACEMENT: &str = "\u{FFFD}";

        let mut res = {
            let mut v = Vec::with_capacity(self.bytes.len());

            // `Utf8Error::valid_up_to` returns the maximum index of validated
            // UTF-8 bytes. Copy the valid bytes into the output buffer.
            v.extend_from_slice(&self.bytes[..self.error.valid_up_to()]);

            // SAFETY: This is safe because the only bytes present in the buffer
            // were validated as UTF-8 by the call to `String::from_utf8` which
            // produced this `FromUtf8Error`.
            unsafe { String::from_utf8_unchecked(v) }
        };

        let iter = self.bytes[self.error.valid_up_to()..].utf8_chunks();

        for chunk in iter {
            res.push_str(chunk.valid());
            if !chunk.invalid().is_empty() {
                res.push_str(REPLACEMENT);
            }
        }

        res
    }

    /// Returns the bytes that were attempted to convert to a `String`.
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// # Examples
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = String::from_utf8(bytes);
    ///
    /// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Fetch a `Utf8Error` to get more details about the conversion failure.
    ///
    /// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
    /// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
    /// an analogue to `FromUtf8Error`. See its documentation for more details
    /// on using it.
    ///
    /// [`std::str`]: core::str "std::str"
    /// [`&str`]: prim@str "&str"
    ///
    /// # Examples
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let error = String::from_utf8(bytes).unwrap_err().utf8_error();
    ///
    /// // the first byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Display for FromUtf8Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Display for FromUtf16Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt("invalid utf-16: lone surrogate found", f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Error for FromUtf8Error {}

#[stable(feature = "rust1", since = "1.0.0")]
impl Error for FromUtf16Error {}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl Clone for String {
    fn clone(&self) -> Self {
        String { vec: self.vec.clone() }
    }

    /// Clones the contents of `source` into `self`.
    ///
    /// This method is preferred over simply assigning `source.clone()` to `self`,
    /// as it avoids reallocation if possible.
    fn clone_from(&mut self, source: &Self) {
        self.vec.clone_from(&source.vec);
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl FromIterator<char> for String {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "string_from_iter_by_ref", since = "1.17.0")]
impl<'a> FromIterator<&'a char> for String {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> FromIterator<&'a str> for String {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "extend_string", since = "1.4.0")]
impl FromIterator<String> for String {
    fn from_iter<I: IntoIterator<Item = String>>(iter: I) -> String {
        let mut iterator = iter.into_iter();

        // Because we're iterating over `String`s, we can avoid at least
        // one allocation by getting the first string from the iterator
        // and appending to it all the subsequent strings.
        match iterator.next() {
            None => String::new(),
            Some(mut buf) => {
                buf.extend(iterator);
                buf
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_str2", since = "1.45.0")]
impl<A: Allocator> FromIterator<Box<str, A>> for String {
    fn from_iter<I: IntoIterator<Item = Box<str, A>>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "herd_cows", since = "1.19.0")]
impl<'a> FromIterator<Cow<'a, str>> for String {
    fn from_iter<I: IntoIterator<Item = Cow<'a, str>>>(iter: I) -> String {
        let mut iterator = iter.into_iter();

        // Because we're iterating over CoWs, we can (potentially) avoid at least
        // one allocation by getting the first item and appending to it all the
        // subsequent items.
        match iterator.next() {
            None => String::new(),
            Some(cow) => {
                let mut buf = cow.into_owned();
                buf.extend(iterator);
                buf
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "ascii_char", issue = "110998")]
impl FromIterator<core::ascii::Char> for String {
    fn from_iter<T: IntoIterator<Item = core::ascii::Char>>(iter: T) -> Self {
        let buf = iter.into_iter().map(core::ascii::Char::to_u8).collect();
        // SAFETY: `buf` is guaranteed to be valid UTF-8 because the `core::ascii::Char` type
        // only contains ASCII values (0x00-0x7F), which are valid UTF-8.
        unsafe { String::from_utf8_unchecked(buf) }
    }
}

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "ascii_char", issue = "110998")]
impl<'a> FromIterator<&'a core::ascii::Char> for String {
    fn from_iter<T: IntoIterator<Item = &'a core::ascii::Char>>(iter: T) -> Self {
        let buf = iter.into_iter().copied().map(core::ascii::Char::to_u8).collect();
        // SAFETY: `buf` is guaranteed to be valid UTF-8 because the `core::ascii::Char` type
        // only contains ASCII values (0x00-0x7F), which are valid UTF-8.
        unsafe { String::from_utf8_unchecked(buf) }
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl Extend<char> for String {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push(c));
    }

    #[inline]
    fn extend_one(&mut self, c: char) {
        self.push(c);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "extend_ref", since = "1.2.0")]
impl<'a> Extend<&'a char> for String {
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    fn extend_one(&mut self, &c: &'a char) {
        self.push(c);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> Extend<&'a str> for String {
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        <I as SpecExtendStr>::spec_extend_into(iter, self)
    }

    #[inline]
    fn extend_one(&mut self, s: &'a str) {
        self.push_str(s);
    }
}

#[cfg(not(no_global_oom_handling))]
trait SpecExtendStr {
    fn spec_extend_into(self, s: &mut String);
}

#[cfg(not(no_global_oom_handling))]
impl<'a, T: IntoIterator<Item = &'a str>> SpecExtendStr for T {
    default fn spec_extend_into(self, target: &mut String) {
        self.into_iter().for_each(move |s| target.push_str(s));
    }
}

#[cfg(not(no_global_oom_handling))]
impl SpecExtendStr for [&str] {
    fn spec_extend_into(self, target: &mut String) {
        target.push_str_slice(&self);
    }
}

#[cfg(not(no_global_oom_handling))]
impl<const N: usize> SpecExtendStr for [&str; N] {
    fn spec_extend_into(self, target: &mut String) {
        target.push_str_slice(&self[..]);
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_str2", since = "1.45.0")]
impl<A: Allocator> Extend<Box<str, A>> for String {
    fn extend<I: IntoIterator<Item = Box<str, A>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "extend_string", since = "1.4.0")]
impl Extend<String> for String {
    fn extend<I: IntoIterator<Item = String>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }

    #[inline]
    fn extend_one(&mut self, s: String) {
        self.push_str(&s);
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "herd_cows", since = "1.19.0")]
impl<'a> Extend<Cow<'a, str>> for String {
    fn extend<I: IntoIterator<Item = Cow<'a, str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }

    #[inline]
    fn extend_one(&mut self, s: Cow<'a, str>) {
        self.push_str(&s);
    }
}

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "ascii_char", issue = "110998")]
impl Extend<core::ascii::Char> for String {
    #[inline]
    fn extend<I: IntoIterator<Item = core::ascii::Char>>(&mut self, iter: I) {
        self.vec.extend(iter.into_iter().map(|c| c.to_u8()));
    }

    #[inline]
    fn extend_one(&mut self, c: core::ascii::Char) {
        self.vec.push(c.to_u8());
    }
}

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "ascii_char", issue = "110998")]
impl<'a> Extend<&'a core::ascii::Char> for String {
    #[inline]
    fn extend<I: IntoIterator<Item = &'a core::ascii::Char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    fn extend_one(&mut self, c: &'a core::ascii::Char) {
        self.vec.push(c.to_u8());
    }
}

/// A convenience impl that delegates to the impl for `&str`.
///
/// # Examples
///
/// ```
/// assert_eq!(String::from("Hello world").find("world"), Some(6));
/// ```
#[unstable(
    feature = "pattern",
    reason = "API not fully fleshed out and ready to be stabilized",
    issue = "27721"
)]
impl<'b> Pattern for &'b String {
    type Searcher<'a> = <&'b str as Pattern>::Searcher<'a>;

    fn into_searcher(self, haystack: &str) -> <&'b str as Pattern>::Searcher<'_> {
        self[..].into_searcher(haystack)
    }

    #[inline]
    fn is_contained_in(self, haystack: &str) -> bool {
        self[..].is_contained_in(haystack)
    }

    #[inline]
    fn is_prefix_of(self, haystack: &str) -> bool {
        self[..].is_prefix_of(haystack)
    }

    #[inline]
    fn strip_prefix_of(self, haystack: &str) -> Option<&str> {
        self[..].strip_prefix_of(haystack)
    }

    #[inline]
    fn is_suffix_of<'a>(self, haystack: &'a str) -> bool
    where
        Self::Searcher<'a>: core::str::pattern::ReverseSearcher<'a>,
    {
        self[..].is_suffix_of(haystack)
    }

    #[inline]
    fn strip_suffix_of<'a>(self, haystack: &'a str) -> Option<&'a str>
    where
        Self::Searcher<'a>: core::str::pattern::ReverseSearcher<'a>,
    {
        self[..].strip_suffix_of(haystack)
    }

    #[inline]
    fn as_utf8_pattern(&self) -> Option<Utf8Pattern<'_>> {
        Some(Utf8Pattern::StringPattern(self.as_bytes()))
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {
        #[stable(feature = "rust1", since = "1.0.0")]
        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }

        #[stable(feature = "rust1", since = "1.0.0")]
        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }
    };
}

impl_eq! { String, str }
impl_eq! { String, &'a str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'a, str>, str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'a, str>, &'b str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'a, str>, String }

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_unstable(feature = "const_default", issue = "143894")]
impl const Default for String {
    /// Creates an empty `String`.
    #[inline]
    fn default() -> String {
        String::new()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Display for String {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Debug for String {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl hash::Hash for String {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

/// Implements the `+` operator for concatenating two strings.
///
/// This consumes the `String` on the left-hand side and re-uses its buffer (growing it if
/// necessary). This is done to avoid allocating a new `String` and copying the entire contents on
/// every operation, which would lead to *O*(*n*^2) running time when building an *n*-byte string by
/// repeated concatenation.
///
/// The string on the right-hand side is only borrowed; its contents are copied into the returned
/// `String`.
///
/// # Examples
///
/// Concatenating two `String`s takes the first by value and borrows the second:
///
/// ```
/// let a = String::from("hello");
/// let b = String::from(" world");
/// let c = a + &b;
/// // `a` is moved and can no longer be used here.
/// ```
///
/// If you want to keep using the first `String`, you can clone it and append to the clone instead:
///
/// ```
/// let a = String::from("hello");
/// let b = String::from(" world");
/// let c = a.clone() + &b;
/// // `a` is still valid here.
/// ```
///
/// Concatenating `&str` slices can be done by converting the first to a `String`:
///
/// ```
/// let a = "hello";
/// let b = " world";
/// let c = a.to_string() + b;
/// ```
#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl Add<&str> for String {
    type Output = String;

    #[inline]
    fn add(mut self, other: &str) -> String {
        self.push_str(other);
        self
    }
}

/// Implements the `+=` operator for appending to a `String`.
///
/// This has the same behavior as the [`push_str`][String::push_str] method.
#[cfg(not(no_global_oom_handling))]
#[stable(feature = "stringaddassign", since = "1.12.0")]
impl AddAssign<&str> for String {
    #[inline]
    fn add_assign(&mut self, other: &str) {
        self.push_str(other);
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> ops::Index<I> for String
where
    I: slice::SliceIndex<str>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self.as_str())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I> ops::IndexMut<I> for String
where
    I: slice::SliceIndex<str>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self.as_mut_str())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl ops::Deref for String {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

#[unstable(feature = "deref_pure_trait", issue = "87121")]
unsafe impl ops::DerefPure for String {}

#[stable(feature = "derefmut_for_string", since = "1.3.0")]
impl ops::DerefMut for String {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

/// A type alias for [`Infallible`].
///
/// This alias exists for backwards compatibility, and may be eventually deprecated.
///
/// [`Infallible`]: core::convert::Infallible "convert::Infallible"
#[stable(feature = "str_parse_error", since = "1.5.0")]
pub type ParseError = core::convert::Infallible;

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl FromStr for String {
    type Err = core::convert::Infallible;
    #[inline]
    fn from_str(s: &str) -> Result<String, Self::Err> {
        Ok(String::from(s))
    }
}

/// A trait for converting a value to a `String`.
///
/// This trait is automatically implemented for any type which implements the
/// [`Display`] trait. As such, `ToString` shouldn't be implemented directly:
/// [`Display`] should be implemented instead, and you get the `ToString`
/// implementation for free.
///
/// [`Display`]: fmt::Display
#[rustc_diagnostic_item = "ToString"]
#[stable(feature = "rust1", since = "1.0.0")]
pub trait ToString {
    /// Converts the given value to a `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// let i = 5;
    /// let five = String::from("5");
    ///
    /// assert_eq!(five, i.to_string());
    /// ```
    #[rustc_conversion_suggestion]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_diagnostic_item = "to_string_method"]
    fn to_string(&self) -> String;
}

/// # Panics
///
/// In this implementation, the `to_string` method panics
/// if the `Display` implementation returns an error.
/// This indicates an incorrect `Display` implementation
/// since `fmt::Write for String` never returns an error itself.
#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Display + ?Sized> ToString for T {
    #[inline]
    fn to_string(&self) -> String {
        <Self as SpecToString>::spec_to_string(self)
    }
}

#[cfg(not(no_global_oom_handling))]
trait SpecToString {
    fn spec_to_string(&self) -> String;
}

#[cfg(not(no_global_oom_handling))]
impl<T: fmt::Display + ?Sized> SpecToString for T {
    // A common guideline is to not inline generic functions. However,
    // removing `#[inline]` from this method causes non-negligible regressions.
    // See <https://github.com/rust-lang/rust/pull/74852>, the last attempt
    // to try to remove it.
    #[inline]
    default fn spec_to_string(&self) -> String {
        let mut buf = String::new();
        let mut formatter =
            core::fmt::Formatter::new(&mut buf, core::fmt::FormattingOptions::new());
        // Bypass format_args!() to avoid write_str with zero-length strs
        fmt::Display::fmt(self, &mut formatter)
            .expect("a Display implementation returned an error unexpectedly");
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl SpecToString for core::ascii::Char {
    #[inline]
    fn spec_to_string(&self) -> String {
        self.as_str().to_owned()
    }
}

#[cfg(not(no_global_oom_handling))]
impl SpecToString for char {
    #[inline]
    fn spec_to_string(&self) -> String {
        String::from(self.encode_utf8(&mut [0; char::MAX_LEN_UTF8]))
    }
}

#[cfg(not(no_global_oom_handling))]
impl SpecToString for bool {
    #[inline]
    fn spec_to_string(&self) -> String {
        String::from(if *self { "true" } else { "false" })
    }
}

macro_rules! impl_to_string {
    ($($signed:ident, $unsigned:ident,)*) => {
        $(
        #[cfg(not(no_global_oom_handling))]
        #[cfg(not(feature = "optimize_for_size"))]
        impl SpecToString for $signed {
            #[inline]
            fn spec_to_string(&self) -> String {
                const SIZE: usize = $signed::MAX.ilog10() as usize + 1;
                let mut buf = [core::mem::MaybeUninit::<u8>::uninit(); SIZE];
                // Only difference between signed and unsigned are these 8 lines.
                let mut out;
                if *self < 0 {
                    out = String::with_capacity(SIZE + 1);
                    out.push('-');
                } else {
                    out = String::with_capacity(SIZE);
                }

                // SAFETY: `buf` is always big enough to contain all the digits.
                unsafe { out.push_str(self.unsigned_abs()._fmt(&mut buf)); }
                out
            }
        }
        #[cfg(not(no_global_oom_handling))]
        #[cfg(not(feature = "optimize_for_size"))]
        impl SpecToString for $unsigned {
            #[inline]
            fn spec_to_string(&self) -> String {
                const SIZE: usize = $unsigned::MAX.ilog10() as usize + 1;
                let mut buf = [core::mem::MaybeUninit::<u8>::uninit(); SIZE];

                // SAFETY: `buf` is always big enough to contain all the digits.
                unsafe { self._fmt(&mut buf).to_string() }
            }
        }
        )*
    }
}

impl_to_string! {
    i8, u8,
    i16, u16,
    i32, u32,
    i64, u64,
    isize, usize,
    i128, u128,
}

#[cfg(not(no_global_oom_handling))]
#[cfg(feature = "optimize_for_size")]
impl SpecToString for u8 {
    #[inline]
    fn spec_to_string(&self) -> String {
        let mut buf = String::with_capacity(3);
        let mut n = *self;
        if n >= 10 {
            if n >= 100 {
                buf.push((b'0' + n / 100) as char);
                n %= 100;
            }
            buf.push((b'0' + n / 10) as char);
            n %= 10;
        }
        buf.push((b'0' + n) as char);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
#[cfg(feature = "optimize_for_size")]
impl SpecToString for i8 {
    #[inline]
    fn spec_to_string(&self) -> String {
        let mut buf = String::with_capacity(4);
        if self.is_negative() {
            buf.push('-');
        }
        let mut n = self.unsigned_abs();
        if n >= 10 {
            if n >= 100 {
                buf.push('1');
                n -= 100;
            }
            buf.push((b'0' + n / 10) as char);
            n %= 10;
        }
        buf.push((b'0' + n) as char);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
macro_rules! to_string_str {
    {$($type:ty,)*} => {
        $(
            impl SpecToString for $type {
                #[inline]
                fn spec_to_string(&self) -> String {
                    let s: &str = self;
                    String::from(s)
                }
            }
        )*
    };
}

#[cfg(not(no_global_oom_handling))]
to_string_str! {
    Cow<'_, str>,
    String,
    // Generic/generated code can sometimes have multiple, nested references
    // for strings, including `&&&str`s that would never be written
    // by hand.
    &&&&&&&&&&&&str,
    &&&&&&&&&&&str,
    &&&&&&&&&&str,
    &&&&&&&&&str,
    &&&&&&&&str,
    &&&&&&&str,
    &&&&&&str,
    &&&&&str,
    &&&&str,
    &&&str,
    &&str,
    &str,
    str,
}

#[cfg(not(no_global_oom_handling))]
impl SpecToString for fmt::Arguments<'_> {
    #[inline]
    fn spec_to_string(&self) -> String {
        crate::fmt::format(*self)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl AsRef<str> for String {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

#[stable(feature = "string_as_mut", since = "1.43.0")]
impl AsMut<str> for String {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl AsRef<[u8]> for String {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl From<&str> for String {
    /// Converts a `&str` into a [`String`].
    ///
    /// The result is allocated on the heap.
    #[inline]
    fn from(s: &str) -> String {
        s.to_owned()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "from_mut_str_for_string", since = "1.44.0")]
impl From<&mut str> for String {
    /// Converts a `&mut str` into a [`String`].
    ///
    /// The result is allocated on the heap.
    #[inline]
    fn from(s: &mut str) -> String {
        s.to_owned()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "from_ref_string", since = "1.35.0")]
impl From<&String> for String {
    /// Converts a `&String` into a [`String`].
    ///
    /// This clones `s` and returns the clone.
    #[inline]
    fn from(s: &String) -> String {
        s.clone()
    }
}

// note: test pulls in std, which causes errors here
#[stable(feature = "string_from_box", since = "1.18.0")]
impl From<Box<str>> for String {
    /// Converts the given boxed `str` slice to a [`String`].
    /// It is notable that the `str` slice is owned.
    ///
    /// # Examples
    ///
    /// ```
    /// let s1: String = String::from("hello world");
    /// let s2: Box<str> = s1.into_boxed_str();
    /// let s3: String = String::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: Box<str>) -> String {
        s.into_string()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "box_from_str", since = "1.20.0")]
impl From<String> for Box<str> {
    /// Converts the given [`String`] to a boxed `str` slice that is owned.
    ///
    /// # Examples
    ///
    /// ```
    /// let s1: String = String::from("hello world");
    /// let s2: Box<str> = Box::from(s1);
    /// let s3: String = String::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: String) -> Box<str> {
        s.into_boxed_str()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "string_from_cow_str", since = "1.14.0")]
impl<'a> From<Cow<'a, str>> for String {
    /// Converts a clone-on-write string to an owned
    /// instance of [`String`].
    ///
    /// This extracts the owned string,
    /// clones the string if it is not already owned.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// // If the string is not owned...
    /// let cow: Cow<'_, str> = Cow::Borrowed("eggplant");
    /// // It will allocate on the heap and copy the string.
    /// let owned: String = String::from(cow);
    /// assert_eq!(&owned[..], "eggplant");
    /// ```
    fn from(s: Cow<'a, str>) -> String {
        s.into_owned()
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> From<&'a str> for Cow<'a, str> {
    /// Converts a string slice into a [`Borrowed`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// assert_eq!(Cow::from("eggplant"), Cow::Borrowed("eggplant"));
    /// ```
    ///
    /// [`Borrowed`]: crate::borrow::Cow::Borrowed "borrow::Cow::Borrowed"
    #[inline]
    fn from(s: &'a str) -> Cow<'a, str> {
        Cow::Borrowed(s)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> From<String> for Cow<'a, str> {
    /// Converts a [`String`] into an [`Owned`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// let s = "eggplant".to_string();
    /// let s2 = "eggplant".to_string();
    /// assert_eq!(Cow::from(s), Cow::<'static, str>::Owned(s2));
    /// ```
    ///
    /// [`Owned`]: crate::borrow::Cow::Owned "borrow::Cow::Owned"
    #[inline]
    fn from(s: String) -> Cow<'a, str> {
        Cow::Owned(s)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "cow_from_string_ref", since = "1.28.0")]
impl<'a> From<&'a String> for Cow<'a, str> {
    /// Converts a [`String`] reference into a [`Borrowed`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// let s = "eggplant".to_string();
    /// assert_eq!(Cow::from(&s), Cow::Borrowed("eggplant"));
    /// ```
    ///
    /// [`Borrowed`]: crate::borrow::Cow::Borrowed "borrow::Cow::Borrowed"
    #[inline]
    fn from(s: &'a String) -> Cow<'a, str> {
        Cow::Borrowed(s.as_str())
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "cow_str_from_iter", since = "1.12.0")]
impl<'a> FromIterator<char> for Cow<'a, str> {
    fn from_iter<I: IntoIterator<Item = char>>(it: I) -> Cow<'a, str> {
        Cow::Owned(FromIterator::from_iter(it))
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "cow_str_from_iter", since = "1.12.0")]
impl<'a, 'b> FromIterator<&'b str> for Cow<'a, str> {
    fn from_iter<I: IntoIterator<Item = &'b str>>(it: I) -> Cow<'a, str> {
        Cow::Owned(FromIterator::from_iter(it))
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "cow_str_from_iter", since = "1.12.0")]
impl<'a> FromIterator<String> for Cow<'a, str> {
    fn from_iter<I: IntoIterator<Item = String>>(it: I) -> Cow<'a, str> {
        Cow::Owned(FromIterator::from_iter(it))
    }
}

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "ascii_char", issue = "110998")]
impl<'a> FromIterator<core::ascii::Char> for Cow<'a, str> {
    fn from_iter<T: IntoIterator<Item = core::ascii::Char>>(it: T) -> Self {
        Cow::Owned(FromIterator::from_iter(it))
    }
}

#[stable(feature = "from_string_for_vec_u8", since = "1.14.0")]
impl From<String> for Vec<u8> {
    /// Converts the given [`String`] to a vector [`Vec`] that holds values of type [`u8`].
    ///
    /// # Examples
    ///
    /// ```
    /// let s1 = String::from("hello world");
    /// let v1 = Vec::from(s1);
    ///
    /// for b in v1 {
    ///     println!("{b}");
    /// }
    /// ```
    fn from(string: String) -> Vec<u8> {
        string.into_bytes()
    }
}

#[stable(feature = "try_from_vec_u8_for_string", since = "1.87.0")]
impl TryFrom<Vec<u8>> for String {
    type Error = FromUtf8Error;
    /// Converts the given [`Vec<u8>`] into a  [`String`] if it contains valid UTF-8 data.
    ///
    /// # Examples
    ///
    /// ```
    /// let s1 = b"hello world".to_vec();
    /// let v1 = String::try_from(s1).unwrap();
    /// assert_eq!(v1, "hello world");
    ///
    /// ```
    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        Self::from_utf8(bytes)
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Write for String {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

/// An iterator over the [`char`]s of a string.
///
/// This struct is created by the [`into_chars`] method on [`String`].
/// See its documentation for more.
///
/// [`char`]: prim@char
/// [`into_chars`]: String::into_chars
#[cfg_attr(not(no_global_oom_handling), derive(Clone))]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[unstable(feature = "string_into_chars", issue = "133125")]
pub struct IntoChars {
    bytes: vec::IntoIter<u8>,
}

#[unstable(feature = "string_into_chars", issue = "133125")]
impl fmt::Debug for IntoChars {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoChars").field(&self.as_str()).finish()
    }
}

impl IntoChars {
    /// Views the underlying data as a subslice of the original data.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(string_into_chars)]
    ///
    /// let mut chars = String::from("abc").into_chars();
    ///
    /// assert_eq!(chars.as_str(), "abc");
    /// chars.next();
    /// assert_eq!(chars.as_str(), "bc");
    /// chars.next();
    /// chars.next();
    /// assert_eq!(chars.as_str(), "");
    /// ```
    #[unstable(feature = "string_into_chars", issue = "133125")]
    #[must_use]
    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: `bytes` is a valid UTF-8 string.
        unsafe { str::from_utf8_unchecked(self.bytes.as_slice()) }
    }

    /// Consumes the `IntoChars`, returning the remaining string.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(string_into_chars)]
    ///
    /// let chars = String::from("abc").into_chars();
    /// assert_eq!(chars.into_string(), "abc");
    ///
    /// let mut chars = String::from("def").into_chars();
    /// chars.next();
    /// assert_eq!(chars.into_string(), "ef");
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[unstable(feature = "string_into_chars", issue = "133125")]
    #[inline]
    pub fn into_string(self) -> String {
        // Safety: `bytes` are kept in UTF-8 form, only removing whole `char`s at a time.
        unsafe { String::from_utf8_unchecked(self.bytes.collect()) }
    }

    #[inline]
    fn iter(&self) -> CharIndices<'_> {
        self.as_str().char_indices()
    }
}

#[unstable(feature = "string_into_chars", issue = "133125")]
impl Iterator for IntoChars {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        let mut iter = self.iter();
        match iter.next() {
            None => None,
            Some((_, ch)) => {
                let offset = iter.offset();
                // `offset` is a valid index.
                let _ = self.bytes.advance_by(offset);
                Some(ch)
            }
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.iter().count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter().size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

#[unstable(feature = "string_into_chars", issue = "133125")]
impl DoubleEndedIterator for IntoChars {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        let len = self.as_str().len();
        let mut iter = self.iter();
        match iter.next_back() {
            None => None,
            Some((idx, ch)) => {
                // `idx` is a valid index.
                let _ = self.bytes.advance_back_by(len - idx);
                Some(ch)
            }
        }
    }
}

#[unstable(feature = "string_into_chars", issue = "133125")]
impl FusedIterator for IntoChars {}

/// A draining iterator for `String`.
///
/// This struct is created by the [`drain`] method on [`String`]. See its
/// documentation for more.
///
/// [`drain`]: String::drain
#[stable(feature = "drain", since = "1.6.0")]
pub struct Drain<'a> {
    /// Will be used as &'a mut String in the destructor
    string: *mut String,
    /// Start of part to remove
    start: usize,
    /// End of part to remove
    end: usize,
    /// Current remaining range to remove
    iter: Chars<'a>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl fmt::Debug for Drain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_str()).finish()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
unsafe impl Sync for Drain<'_> {}
#[stable(feature = "drain", since = "1.6.0")]
unsafe impl Send for Drain<'_> {}

#[stable(feature = "drain", since = "1.6.0")]
impl Drop for Drain<'_> {
    fn drop(&mut self) {
        unsafe {
            // Use Vec::drain. "Reaffirm" the bounds checks to avoid
            // panic code being inserted again.
            let self_vec = (*self.string).as_mut_vec();
            if self.start <= self.end && self.end <= self_vec.len() {
                self_vec.drain(self.start..self.end);
            }
        }
    }
}

impl<'a> Drain<'a> {
    /// Returns the remaining (sub)string of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("abc");
    /// let mut drain = s.drain(..);
    /// assert_eq!(drain.as_str(), "abc");
    /// let _ = drain.next().unwrap();
    /// assert_eq!(drain.as_str(), "bc");
    /// ```
    #[must_use]
    #[stable(feature = "string_drain_as_str", since = "1.55.0")]
    pub fn as_str(&self) -> &str {
        self.iter.as_str()
    }
}

#[stable(feature = "string_drain_as_str", since = "1.55.0")]
impl<'a> AsRef<str> for Drain<'a> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

#[stable(feature = "string_drain_as_str", since = "1.55.0")]
impl<'a> AsRef<[u8]> for Drain<'a> {
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl Iterator for Drain<'_> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

#[stable(feature = "drain", since = "1.6.0")]
impl DoubleEndedIterator for Drain<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for Drain<'_> {}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "from_char_for_string", since = "1.46.0")]
impl From<char> for String {
    /// Allocates an owned [`String`] from a single character.
    ///
    /// # Example
    /// ```rust
    /// let c: char = 'a';
    /// let s: String = String::from(c);
    /// assert_eq!("a", &s[..]);
    /// ```
    #[inline]
    fn from(c: char) -> Self {
        c.to_string()
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Challenge 10: memory safety of `String` methods that are safe abstractions over unsafe code.
    //!
    //! Bounds. Strings have a symbolic length and capacity, limited only by the largest object
    //! CBMC can represent under `--object-bits 12` (see `MAX_ALLOC`), except where stated below.
    //!
    //! * Unbounded: `check_insert_str` and `check_split_off` (both "unbounded" in the challenge),
    //!   and `check_pop`, `check_remove`, `check_insert`, `check_drain_drop`, `check_drain_next`,
    //!   `check_into_boxed_str`, `check_leak`. No loop is reachable on their verified paths, so
    //!   no unwind bound limits the input. `check_remove` has `#[kani::unwind(2)]` only to cut an
    //!   infeasible panic-formatting path (see the comment on it). The `check_*_panics`
    //!   harnesses are unbounded too (`#[kani::unwind(1)]` on `check_replace_range_panics` only
    //!   covers loops that no input reaches, see the comment on it).
    //! * Receiver of any length, bounded edit: `check_replace_range` (removed and inserted
    //!   ranges of at most 4 bytes each) and `check_remove_matches` (at most 5 matches). Their
    //!   loops run once per edited byte or per match, never once per receiver byte.
    //! * Bounded because of tool limits: `check_retain_bounded` (strings of up to 12 chars) and
    //!   the `from_utf16*` harnesses (inputs of up to 12 bytes). See the comment above them.
    //!
    //! Every `#[kani::unwind]` bound is checked by unwinding assertions, so a bound that is too
    //! small makes the proof fail instead of silently cutting executions.
    //!
    //! Restrictions. There is no `kani::assume` in this module: every restriction of an input
    //! is a `kani::any_where` domain at the point where the input is generated (sizes that fit
    //! in one CBMC object, indices inside the string, the bounds above, and in the panic
    //! harnesses indices without a char boundary, `any_non_boundary`). Nothing is assumed
    //! about the result of a function under test.
    //!
    //! Contents. Every generated `String` is initialized, valid UTF-8. The harnesses with a
    //! symbolic length use a zeroed buffer, i.e. a string of NUL chars (`any_string`), and, where a
    //! function decodes a char, put the UTF-8 encoding of an arbitrary `char` at an arbitrary
    //! position (`with_char_at`). This is a modeling argument, not a quantification over all
    //! contents: memory safety of these functions depends only on the length, the capacity, the
    //! indices, the outcome of the char-boundary checks at those indices, and the one char that
    //! `pop`, `remove` and `Drain::next` decode. Any other bytes are only copied or moved, never
    //! used for control flow or address computation. On an all-NUL string every index up to the
    //! length is a char boundary, so the model reaches every combination of these quantities for
    //! which the boundary checks pass; the combinations for which they fail are the panics below.
    //!
    //! Panics. Panics are not UB. The harnesses stay out of the documented panic conditions
    //! through their input domains: indices are at most the length (an `any_where` domain), and
    //! every such index of an all-NUL string is a char boundary by construction (the harnesses
    //! `assert!` this before the call); `with_char_at` puts a char at the index that `remove`
    //! removes. The `check_*_panics` harnesses (`#[kani::should_panic]`) show for `insert`,
    //! `insert_str`, `split_off`, `drain` and `replace_range` that an index strictly inside a
    //! multi-byte char, or past the end, panics. Reversed ranges and `Bound` overflow
    //! (`..=usize::MAX`) are not exercised there.
    use core::cell::Cell;
    use core::kani;
    use core::ops::Bound;
    use core::str::pattern::{Pattern, SearchStep, Searcher};

    use crate::string::String;
    use crate::vec::Vec;

    /// Largest positive offset CBMC can represent within one object with `--object-bits 12` (the
    /// setting used by `scripts/run-kani.sh`): 52 offset bits, signed. A limit of the memory
    /// model, not a bound chosen for tractability (2^51 bytes = 2 PiB).
    const MAX_ALLOC: usize = (1usize << 51) - 1;

    /// A `String` with symbolic capacity (`<= MAX_ALLOC`) and symbolic length (`<= max_len`)
    /// whose bytes are all 0 (NUL, a one-byte UTF-8 char). The buffer is a zeroed allocation
    /// (`vec![0; cap]`), so it is initialized without a loop or a fill of symbolic size. See the
    /// module comment on contents.
    fn any_string_max_len(max_len: usize) -> String {
        let cap: usize = kani::any_where(|c: &usize| *c <= MAX_ALLOC);
        let len: usize = kani::any_where(|l: &usize| *l <= cap && *l <= max_len);
        let mut v: Vec<u8> = vec![0u8; cap];
        v.truncate(len);
        // SAFETY (harness): all bytes are 0, which is valid UTF-8.
        unsafe { String::from_utf8_unchecked(v) }
    }

    /// `any_string_max_len` without a limit on the length other than the capacity.
    fn any_string() -> String {
        any_string_max_len(MAX_ALLOC)
    }

    /// `prefix ++ encode_utf8(c) ++ suffix` with an arbitrary `char` `c` and all-zero `prefix`
    /// and `suffix` of arbitrary lengths. Returns the string, the start of `c`, and `c`.
    fn with_char_at() -> (String, usize, char) {
        let c: char = kani::any();
        let c_len = c.len_utf8();
        // `prefix + c_len + suffix <= MAX_ALLOC`: the string fits in one CBMC object.
        let prefix: usize = kani::any_where(|p: &usize| *p <= MAX_ALLOC - c_len);
        let suffix: usize = kani::any_where(|s: &usize| *s <= MAX_ALLOC - c_len - prefix);
        let len = prefix + c_len + suffix;
        // `cap >= len`, so `cap == len` is possible for chars of every width.
        let cap: usize = kani::any_where(|k: &usize| *k >= len && *k <= MAX_ALLOC);
        let mut v: Vec<u8> = vec![0u8; cap];
        // SAFETY (harness): `prefix + c_len <= cap = v.len()`, so the char's bytes are written
        // inside the zeroed, initialized buffer.
        unsafe {
            c.encode_utf8(core::slice::from_raw_parts_mut(v.as_mut_ptr().add(prefix), c_len));
        }
        v.truncate(len);
        // SAFETY (harness): zero bytes, a well-formed char encoding, zero bytes: valid UTF-8.
        (unsafe { String::from_utf8_unchecked(v) }, prefix, c)
    }

    /// The byte range `start..end` of a string of length `len` as an arbitrary `(Bound, Bound)`
    /// pair: every `RangeBounds` shape (`a..b`, `a..=b`, `a..`, `..b`, `..=b`, `..`, and
    /// `Excluded` starts) that denotes this range.
    fn any_bounds(start: usize, end: usize, len: usize) -> (Bound<usize>, Bound<usize>) {
        let sb = if start > 0 && kani::any() {
            Bound::Excluded(start - 1)
        } else if start == 0 && kani::any() {
            Bound::Unbounded
        } else {
            Bound::Included(start)
        };
        let eb = if end > 0 && kani::any() {
            Bound::Included(end - 1)
        } else if end == len && kani::any() {
            Bound::Unbounded
        } else {
            Bound::Excluded(end)
        };
        kani::cover(matches!(sb, Bound::Included(_)), "start bound Included");
        kani::cover(matches!(sb, Bound::Excluded(_)), "start bound Excluded");
        kani::cover(matches!(sb, Bound::Unbounded), "start bound Unbounded");
        kani::cover(matches!(eb, Bound::Included(_)), "end bound Included");
        kani::cover(matches!(eb, Bound::Excluded(_)), "end bound Excluded");
        kani::cover(matches!(eb, Bound::Unbounded), "end bound Unbounded");
        (sb, eb)
    }

    #[kani::proof]
    fn check_pop() {
        // Either empty, or `c` is the last char, after a NUL prefix of arbitrary length.
        let (mut s, start, c) = with_char_at();
        let has_last_char: bool = kani::any();
        // SAFETY (harness): shrinking the length keeps a prefix of the initialized bytes. The new
        // length is 0 or `start + c.len_utf8()`, the end of `c`, so the kept bytes are NULs
        // followed by the whole encoding of `c`: valid UTF-8.
        unsafe { s.as_mut_vec().set_len(if has_last_char { start + c.len_utf8() } else { 0 }) };
        kani::cover(has_last_char && start > 64, "pop from a long string");
        let res = s.pop();
        if has_last_char {
            assert!(res == Some(c));
            assert!(s.len() == start);
        } else {
            assert!(res.is_none());
            assert!(s.len() == 0);
        }
    }

    // `self[idx..]` has a panic path (`str::slice_error_fail`) that formats the error message
    // with loops over the string. Under this harness that path is infeasible (`idx` is the
    // start of a well-formed char), but symbolic execution would still unfold it without end.
    // The unwind bound only cuts that path: unwinding assertions stay enabled, so any loop that
    // is actually reachable and needs more iterations makes the proof fail. No loop is
    // reachable on the verified (non-panicking) path, so input sizes stay unbounded.
    #[kani::proof]
    #[kani::unwind(2)]
    fn check_remove() {
        let (mut s, idx, c) = with_char_at();
        let len = s.len();
        kani::cover(idx > 64 && len > idx + 64, "remove in the middle of a long string");
        let res = s.remove(idx);
        assert!(res == c);
        assert!(s.len() == len - c.len_utf8());
    }

    #[kani::proof]
    fn check_insert() {
        // `len + 4 <= MAX_ALLOC`: the length of the result stays within `MAX_ALLOC`.
        let mut s = any_string_max_len(MAX_ALLOC - 4);
        let len = s.len();
        let ch: char = kani::any();
        let idx: usize = kani::any_where(|i: &usize| *i <= len);
        // Every index up to the length of an all-NUL string is a char boundary, so the
        // documented panic is excluded by construction. Checked here, not assumed.
        assert!(s.is_char_boundary(idx));
        kani::cover(idx > 64 && len > idx + 64, "insert in the middle of a long string");
        kani::cover(s.capacity() == len, "full buffer: insert reallocates");
        s.insert(idx, ch);
        assert!(s.len() == len + ch.len_utf8());
    }

    #[kani::proof]
    fn check_insert_str() {
        let mut s = any_string();
        let len = s.len();
        // `len + amt <= MAX_ALLOC`: the length of the result stays within `MAX_ALLOC`.
        let t = any_string_max_len(MAX_ALLOC - len);
        let amt = t.len();
        let idx: usize = kani::any_where(|i: &usize| *i <= len);
        // No panic by construction, as in `check_insert`.
        assert!(s.is_char_boundary(idx));
        kani::cover(idx > 64 && len > idx + 64 && amt > 64, "long insert in the middle");
        kani::cover(s.capacity() == len && amt > 0, "full buffer: insert_str reallocates");
        s.insert_str(idx, t.as_str());
        assert!(s.len() == len + amt);
    }

    #[kani::proof]
    fn check_split_off() {
        let mut s = any_string();
        let len = s.len();
        let at: usize = kani::any_where(|a: &usize| *a <= len);
        // No panic by construction, as in `check_insert`.
        assert!(s.is_char_boundary(at));
        kani::cover(at > 64 && len > at + 64, "split in the middle of a long string");
        let other = s.split_off(at);
        assert!(s.len() == at);
        assert!(other.len() == len - at);
    }

    #[kani::proof]
    fn check_drain_drop() {
        // Arbitrary range, given in every `RangeBounds` shape; the `Drain` is dropped without
        // being iterated.
        let mut s = any_string();
        let len = s.len();
        let start: usize = kani::any_where(|x: &usize| *x <= len);
        let end: usize = kani::any_where(|x: &usize| *x >= start && *x <= len);
        // No panic by construction, as in `check_insert`.
        assert!(s.is_char_boundary(start) && s.is_char_boundary(end));
        kani::cover(start > 64 && end > start + 64 && len > end + 64, "drain in the middle");
        drop(s.drain(any_bounds(start, end, len)));
        assert!(s.len() == len - (end - start));
    }

    #[kani::proof]
    fn check_drain_next() {
        // The drained range starts with a well-formed char, which the iterator decodes.
        let (mut s, start, c) = with_char_at();
        let len = s.len();
        let end: usize = kani::any_where(|x: &usize| *x >= start + c.len_utf8() && *x <= len);
        // `start` is the start of `c`, and `end` is in the NUL suffix after `c` or at the end
        // of the string: both are char boundaries by construction. Checked here, not assumed.
        assert!(s.is_char_boundary(start) && s.is_char_boundary(end));
        kani::cover(start > 64 && len > end + 64, "drain and iterate in the middle");
        let mut d = s.drain(any_bounds(start, end, len));
        assert!(d.next() == Some(c));
        drop(d);
        assert!(s.len() == len - (end - start));
    }

    #[kani::proof]
    fn check_into_boxed_str() {
        let s = any_string();
        let len = s.len();
        kani::cover(len > 64 && s.capacity() > len, "shrinking a long string");
        let b = s.into_boxed_str();
        assert!(b.len() == len);
    }

    #[kani::proof]
    fn check_leak() {
        let s = any_string();
        let len = s.len();
        kani::cover(len > 64, "long string");
        let r: &'static mut str = s.leak();
        assert!(r.len() == len);
    }

    // ---------------------------------------------------------------------------------------
    // replace_range / remove_matches: arbitrary receiver length, bounded edit size.
    //
    // Every loop reachable from these two functions iterates once per *edited* byte or per
    // *match* (Splice::drop's drain/fill/extend/collect loops; remove_matches' rejection-collect
    // and compaction loops), never once per byte of the receiver: the receiver-sized work is the
    // tail `ptr::copy`, which is loop-free. So the receiver has arbitrary length and capacity,
    // and only the number of edited bytes / matches is bounded, with a matching
    // `#[kani::unwind]` (an insufficient bound fails the unwinding assertion).
    // ---------------------------------------------------------------------------------------

    /// Every valid UTF-8 string of at most `E` bytes: up to `E` arbitrary chars encoded back to
    /// back into the zeroed buffer `buf`, stopping at the first char that does not fit. A string
    /// of `k` chars whose encodings fit in `E` bytes is produced when those chars come first and
    /// `n = k`. The bytes are valid UTF-8 by construction; nothing is checked or assumed.
    fn any_short_str<const E: usize>(buf: &mut [u8; E]) -> &str {
        let chars: [char; E] = kani::any();
        let n: usize = kani::any_where(|n: &usize| *n <= E);
        let mut off = 0;
        for i in 0..n {
            let l = chars[i].len_utf8();
            if l > E - off {
                break;
            }
            chars[i].encode_utf8(&mut buf[off..off + l]);
            off += l;
        }
        // SAFETY (harness): `buf[..off]` is the concatenation of the UTF-8 encodings of whole
        // chars: valid UTF-8.
        unsafe { core::str::from_utf8_unchecked(&buf[..off]) }
    }

    /// Arbitrary-length receiver, symbolic range `start..end` (any position,
    /// `end - start <= E`) on char boundaries, given as an arbitrary `(Bound, Bound)` pair,
    /// and an arbitrary valid UTF-8 replacement of `<= E` bytes.
    fn replace_range_harness<const E: usize>() {
        // `len + E <= MAX_ALLOC`: the length of the result stays within `MAX_ALLOC`.
        let mut s = any_string_max_len(MAX_ALLOC - E);
        let len = s.len();
        let start: usize = kani::any_where(|a: &usize| *a <= len);
        let removed: usize = kani::any_where(|n: &usize| *n <= E && *n <= len - start);
        let end = start + removed;
        // No panic by construction, as in `check_insert`.
        assert!(s.is_char_boundary(start) && s.is_char_boundary(end));
        let mut buf = [0u8; E];
        let repl = any_short_str(&mut buf);
        let rl = repl.len();
        kani::cover(len > 64 && start > 0 && end < len && rl > removed, "grow in the middle");
        kani::cover(len > 64 && start > 0 && end < len && rl < removed, "shrink in the middle");
        kani::cover(len > 64 && end == len && rl > 0, "append at the end");
        kani::cover(s.capacity() == len && rl > removed, "full buffer, growing: reallocates");
        kani::cover(rl >= 4 && repl.as_bytes()[0] >= 0xF0, "replacement starts with a 4-byte char");
        s.replace_range(any_bounds(start, end, len), repl);
        assert!(s.len() == len - removed + rl);
    }

    // `unwind(5)`: the longest loops here run at most 4 times (the chars of `any_short_str`;
    // the `Splice` loops, once per removed or inserted byte), plus the exit test.
    #[kani::proof]
    #[kani::unwind(5)]
    fn check_replace_range() {
        replace_range_harness::<4>();
    }

    /// A `Pattern` whose searcher returns an arbitrary sequence of matches allowed by the
    /// `unsafe trait Searcher` contract that `remove_matches` relies on (its SAFETY comment).
    /// The docs of `Searcher::next` say: "The stream of Match and Reject values up to a Done
    /// will contain index ranges that are adjacent, non-overlapping, covering the whole
    /// haystack, and laying on utf8 boundaries." and "Both ranges may have zero length."
    /// `next_match` returns the `Match` ranges of that stream. So the successive `next_match`
    /// results `(a, b)` are exactly the sequences with `front <= a <= b <= haystack.len()`,
    /// where `front` is the end of the previous match (0 at first), and `a`, `b` on char
    /// boundaries; the gap `front..a` is the implied `Reject`.
    ///
    /// This searcher generates every such sequence of at most `max_matches` matches (the only
    /// bound) on a haystack where every index is a char boundary, which is the all-NUL receiver
    /// of `check_remove_matches`: matches in increasing order, non-overlapping, possibly empty,
    /// possibly an empty match repeated at one position (adjacent zero-length ranges, which the
    /// contract allows; `remove_matches` then copies 0 bytes), within the haystack. The boundary
    /// requirement is asserted, not assumed. On a haystack with multi-byte chars the contract
    /// allows only a subset of these sequences, and `remove_matches` never reads the bytes
    /// itself (it only moves them), so this covers every searcher that meets the contract at
    /// once; the std searchers' own conformance is the subject of Challenges 20/21.
    struct AnyPattern<'c> {
        removed: &'c Cell<usize>,
        matches: &'c Cell<usize>,
        max_matches: usize,
    }

    struct AnySearcher<'a, 'c> {
        haystack: &'a str,
        front: usize,
        left: usize,
        removed: &'c Cell<usize>,
        matches: &'c Cell<usize>,
    }

    // SAFETY: `next_match` returns the `Match` ranges of a stream that meets the contract of
    // `Searcher::next` (see `AnyPattern`): in increasing order, non-overlapping (possibly empty,
    // and possibly an empty match repeated at one position, as the contract allows), within the
    // haystack, on char boundaries (asserted in `next_match`); the gaps between them are the
    // implied `Reject`s. `next` reports the rest of the haystack (from the end of the last
    // match) as one `Reject`, then `Done`.
    unsafe impl<'a, 'c> Searcher<'a> for AnySearcher<'a, 'c> {
        fn haystack(&self) -> &'a str {
            self.haystack
        }

        fn next(&mut self) -> SearchStep {
            let len = self.haystack.len();
            if self.front == len {
                return SearchStep::Done;
            }
            let a = self.front;
            self.front = len;
            SearchStep::Reject(a, len)
        }

        fn next_match(&mut self) -> Option<(usize, usize)> {
            if self.left == 0 || kani::any() {
                return None;
            }
            let len = self.haystack.len();
            let front = self.front;
            let a: usize = kani::any_where(|a: &usize| *a >= front && *a <= len);
            let b: usize = kani::any_where(|b: &usize| *b >= a && *b <= len);
            // The contract's boundary requirement. Every index of the all-NUL haystack is a
            // char boundary, so this holds for every pair above; checked, not assumed.
            assert!(self.haystack.is_char_boundary(a) && self.haystack.is_char_boundary(b));
            self.front = b;
            self.left -= 1;
            self.removed.set(self.removed.get() + (b - a));
            self.matches.set(self.matches.get() + 1);
            Some((a, b))
        }
    }

    impl<'c> Pattern for AnyPattern<'c> {
        type Searcher<'a> = AnySearcher<'a, 'c>;

        fn into_searcher(self, haystack: &str) -> AnySearcher<'_, 'c> {
            AnySearcher {
                haystack,
                front: 0,
                left: self.max_matches,
                removed: self.removed,
                matches: self.matches,
            }
        }
    }

    /// At most 5 matches. `remove_matches` collects the gaps between matches into a
    /// `Vec<(usize, usize)>` that starts with capacity 4, so the 5th match exercises its
    /// reallocation. `unwind(7)`: the loops run at most 6 times (5 gaps plus the tail), plus
    /// the exit test.
    #[kani::proof]
    #[kani::unwind(7)]
    fn check_remove_matches() {
        let mut s = any_string();
        let len = s.len();
        let removed = Cell::new(0usize);
        let matches = Cell::new(0usize);
        s.remove_matches(AnyPattern { removed: &removed, matches: &matches, max_matches: 5 });
        let r = removed.get();
        kani::cover(r > 0 && s.len() > 64, "real removal, long string left");
        kani::cover(matches.get() == 5, "5 matches: the rejections Vec reallocates");
        assert!(s.len() == len - r);
    }

    // ---------------------------------------------------------------------------------------
    // BOUNDED harnesses for the remaining "(U)" functions (`retain`, `from_utf16le/be` and their
    // `_lossy` variants). Their loops cannot be given loop contracts with the pinned Kani.
    // `retain`: symbolic-bound quantifiers are dropped by the SAT backend, calls inside loop
    // invariants are replaced by nondeterministic values, and the `Chars` temporary of the loop
    // body cannot be named in `loop_modifies`. `from_utf16*`: the aligned `from_utf16le` path
    // loops with `for` over `DecodeUtf16`, which the loop-contract macro rejects; every other
    // path loops inside the generic default `Iterator::try_fold` / `fold` (via `collect`), whose
    // state cannot be named in an invariant; and each of these loops pushes to a `String`, while
    // loop contracts do not allow the loop body to allocate or free memory. These harnesses
    // verify the real bodies up to the stated sizes (the unwinding assertions make an
    // insufficient bound fail).
    // ---------------------------------------------------------------------------------------

    /// Up to `N` arbitrary chars encoded back to back into a zeroed (initialized) buffer of
    /// `4 * N` bytes, which is then truncated to the encoded length (valid UTF-8 by construction;
    /// no reallocation, which keeps the harness CI-sized).
    fn any_valid_string<const N: usize>() -> String {
        let chars: [char; N] = kani::any();
        let n: usize = kani::any_where(|n: &usize| *n <= N);
        let mut v: Vec<u8> = vec![0u8; 4 * N];
        let mut off = 0;
        for i in 0..n {
            let l = chars[i].len_utf8();
            chars[i].encode_utf8(&mut v[off..off + l]);
            off += l;
        }
        v.truncate(off);
        // SAFETY (harness): `v` is exactly the concatenation of the UTF-8 encodings of
        // `chars[..n]` (`truncate` drops only the unused zero bytes after them): valid UTF-8.
        unsafe { String::from_utf8_unchecked(v) }
    }

    /// `retain` on any valid string of up to 12 chars (<= 48 bytes), arbitrary keep-predicate.
    /// `unwind(13)`: the generator's loop and the `retain` loop run once per char (at most 12),
    /// plus the exit test.
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_retain_bounded() {
        let mut s = any_valid_string::<12>();
        // Bytes of the chars the predicate keeps (`retain` calls it once per char, in order).
        let kept = Cell::new(0usize);
        // Observers for the cover below; they do not influence the predicate's result.
        let deleted = Cell::new(false);
        let kept_multibyte_after_deletion = Cell::new(false);
        s.retain(|c| {
            let keep: bool = kani::any();
            if !keep {
                deleted.set(true);
            } else {
                kept.set(kept.get() + c.len_utf8());
                if c.len_utf8() > 1 && deleted.get() {
                    kept_multibyte_after_deletion.set(true);
                }
            }
            keep
        });
        kani::cover(
            kept_multibyte_after_deletion.get(),
            "multi-byte char kept after a deletion (moved by the unsafe re-encode)",
        );
        assert!(s.len() == kept.get());
    }

    /// An arbitrary byte slice of length `<= N` at an arbitrary (odd or even) address, so both
    /// the aligned (`align_to` succeeds) and the unaligned paths, and odd lengths, are
    /// exercised. Each UTF-16 code unit decodes to at most 3 UTF-8 bytes (a surrogate pair,
    /// 2 units, to 4), and a trailing odd byte becomes U+FFFD (3 bytes) in the lossy variants.
    /// An input whose first code unit (in the byte order of the function, `$be`) is a low
    /// surrogate is invalid UTF-16, so the strict variants must return `Err`. The covers read
    /// only the input and whether the result is `Ok`: reading the bytes of the decoded string
    /// made CBMC run out of memory at these sizes.
    macro_rules! utf16_harness {
        ($name:ident, $n:literal, $unwind:literal, $lossy:literal, $be:literal, $call:expr) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $name() {
                let arr: [u8; $n] = kani::any();
                let v = kani::slice::any_slice_of_array(&arr);
                // Code unit `i` of `v`, in the byte order of the function under test.
                let unit = |i: usize| {
                    let b = [v[2 * i], v[2 * i + 1]];
                    if $be { u16::from_be_bytes(b) } else { u16::from_le_bytes(b) }
                };
                let lone = v.len() >= 2 && (0xDC00..=0xDFFF).contains(&unit(0));
                let pair = v.len() >= 4
                    && (0xD800..=0xDBFF).contains(&unit(0))
                    && (0xDC00..=0xDFFF).contains(&unit(1));
                kani::cover(v.len() >= 4 && (v.as_ptr() as usize) % 2 == 1, "unaligned");
                kani::cover(v.len() >= 4 && (v.as_ptr() as usize) % 2 == 0, "aligned");
                kani::cover(v.len() % 2 == 1, "odd length");
                let max = 3 * (v.len() / 2) + if $lossy { 3 } else { 0 };
                let f: fn(&[u8]) -> Option<String> = $call;
                let res = f(v);
                kani::cover(pair && res.is_some(), "starts with a surrogate pair, decoded");
                kani::cover(lone && v.len() % 2 == 0, "starts with an unpaired low surrogate");
                match res {
                    Some(s) => {
                        assert!(s.len() <= max);
                        // Invalid UTF-16: only the lossy variants return a string.
                        assert!($lossy || !lone);
                    }
                    None => assert!(!$lossy),
                }
            }
        };
    }
    // `unwind(7)`: an input of at most 12 bytes has at most 6 code units, and the decode,
    // collect and push loops run at most once per code unit, plus the exit test.
    utf16_harness!(check_from_utf16le_bounded, 12, 7, false, false, |v| {
        String::from_utf16le(v).ok()
    });
    utf16_harness!(check_from_utf16be_bounded, 12, 7, false, true, |v| {
        String::from_utf16be(v).ok()
    });
    utf16_harness!(check_from_utf16le_lossy_bounded, 12, 7, true, false, |v| {
        Some(String::from_utf16le_lossy(v))
    });
    utf16_harness!(check_from_utf16be_lossy_bounded, 12, 7, true, true, |v| {
        Some(String::from_utf16be_lossy(v))
    });

    // ---------------------------------------------------------------------------------------
    // Panic harnesses: the documented panic conditions that the harnesses above exclude do
    // panic. Each takes a string from `with_char_at` and an index at which it has no char
    // boundary: strictly inside its char (so the char is multi-byte), or past the end. With
    // `#[kani::should_panic]`, Kani checks that a panic-class failure is reachable and that
    // every failing check is of that class (assertions, including arithmetic overflow and
    // out-of-bounds indexing), so no UB is reachable before the panic (Kani uses
    // `panic=abort`). That the failing checks are exactly the documented panics was checked in
    // the verification logs.
    // `pop` has no panic condition. `remove` has no panic harness: its panic path for an index
    // inside a char formats the message with loops over the string (see `check_remove`).
    // ---------------------------------------------------------------------------------------

    /// An index at which the string from `with_char_at` (`c` at `start`, length `len`) has no
    /// char boundary: strictly inside `c`, or past the end.
    fn any_non_boundary(len: usize, start: usize, c: char) -> usize {
        let c_end = start + c.len_utf8();
        let i: usize = kani::any_where(|i: &usize| (start < *i && *i < c_end) || *i > len);
        kani::cover(i < len && start > 64 && len > c_end + 64, "inside a char, long string");
        kani::cover(i < len && c.len_utf8() == 4, "inside a 4-byte char");
        kani::cover(i > len, "past the end");
        i
    }

    /// A range `a..b` with `a <= b` where at least one end comes from `any_non_boundary` and
    /// the other end is arbitrary.
    fn any_bad_range(len: usize, start: usize, c: char) -> (usize, usize) {
        let bad = any_non_boundary(len, start, c);
        let other: usize = kani::any();
        let (a, b) = if bad <= other { (bad, other) } else { (other, bad) };
        kani::cover(a == bad && b <= len, "start not on a char boundary, end in bounds");
        kani::cover(b == bad && b <= len, "end not on a char boundary");
        (a, b)
    }

    #[kani::proof]
    #[kani::should_panic]
    fn check_insert_panics() {
        let (mut s, start, c) = with_char_at();
        let idx = any_non_boundary(s.len(), start, c);
        s.insert(idx, kani::any());
    }

    #[kani::proof]
    #[kani::should_panic]
    fn check_insert_str_panics() {
        let (mut s, start, c) = with_char_at();
        let len = s.len();
        let idx = any_non_boundary(len, start, c);
        let t = any_string_max_len(MAX_ALLOC - len);
        s.insert_str(idx, t.as_str());
    }

    #[kani::proof]
    #[kani::should_panic]
    fn check_split_off_panics() {
        let (mut s, start, c) = with_char_at();
        let at = any_non_boundary(s.len(), start, c);
        let _ = s.split_off(at);
    }

    #[kani::proof]
    #[kani::should_panic]
    fn check_drain_panics() {
        let (mut s, start, c) = with_char_at();
        let (a, b) = any_bad_range(s.len(), start, c);
        drop(s.drain(a..b));
    }

    // `unwind(1)`: the `Splice` loops are reachable only after both boundary checks pass, which
    // no input here does. Unwinding assertions stay on, so a reachable loop would fail.
    #[kani::proof]
    #[kani::should_panic]
    #[kani::unwind(1)]
    fn check_replace_range_panics() {
        let (mut s, start, c) = with_char_at();
        let (a, b) = any_bad_range(s.len(), start, c);
        s.replace_range(a..b, "");
    }
}
