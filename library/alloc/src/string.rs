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
use core::{fmt, hash, hint, ptr, slice};

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
pub struct FromUtf16Error {
    kind: FromUtf16ErrorKind,
}

#[cfg_attr(no_global_oom_handling, expect(dead_code))]
#[derive(Clone, PartialEq, Eq, Debug)]
enum FromUtf16ErrorKind {
    LoneSurrogate,
    OddBytes,
}

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
    /// [U+FFFD]: char::REPLACEMENT_CHARACTER
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
    /// // some invalid bytes
    /// let input: Vec<u8> = b"Hello \xF0\x90\x80World".into();
    /// let output = String::from_utf8_lossy_owned(input);
    ///
    /// assert_eq!(String::from("Hello �World"), output);
    /// ```
    #[must_use]
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "string_from_utf8_lossy_owned", since = "1.99.0")]
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
        Self::from_utf16_units(v.iter().cloned(), v.len())
    }

    /// Decodes an iterator of UTF-16 code units into a `String`, returning
    /// [`Err`] on the first lone surrogate. `capacity` should be the number of
    /// code units, which is used to preallocate the output buffer.
    // This isn't done via collect::<Result<_, _>>() for performance reasons.
    // FIXME: the function can be simplified again when #48994 is closed.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    fn from_utf16_units(
        units: impl Iterator<Item = u16>,
        capacity: usize,
    ) -> Result<String, FromUtf16Error> {
        let mut ret = String::with_capacity(capacity);
        for c in char::decode_utf16(units) {
            let Ok(c) = c else {
                return Err(FromUtf16Error { kind: FromUtf16ErrorKind::LoneSurrogate });
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
    /// [U+FFFD]: char::REPLACEMENT_CHARACTER
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
    #[stable(feature = "str_from_utf16_endian", since = "1.98.0")]
    pub fn from_utf16le(v: &[u8]) -> Result<String, FromUtf16Error> {
        let (chunks, []) = v.as_chunks::<2>() else {
            return Err(FromUtf16Error { kind: FromUtf16ErrorKind::OddBytes });
        };
        // ignore-tidy-undocumented-unsafe
        match (cfg!(target_endian = "little"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16(v),
            _ => {
                Self::from_utf16_units(chunks.iter().copied().map(u16::from_le_bytes), chunks.len())
            }
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
    /// [U+FFFD]: char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x73, 0x00, 0x1E, 0xDD, 0x69, 0x00, 0x63, 0x00,
    ///           0x34, 0xD8];
    ///
    /// assert_eq!(String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            String::from_utf16le_lossy(v));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "str_from_utf16_endian", since = "1.98.0")]
    pub fn from_utf16le_lossy(v: &[u8]) -> String {
        // ignore-tidy-undocumented-unsafe
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
    #[stable(feature = "str_from_utf16_endian", since = "1.98.0")]
    pub fn from_utf16be(v: &[u8]) -> Result<String, FromUtf16Error> {
        let (chunks, []) = v.as_chunks::<2>() else {
            return Err(FromUtf16Error { kind: FromUtf16ErrorKind::OddBytes });
        };
        // ignore-tidy-undocumented-unsafe
        match (cfg!(target_endian = "big"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16(v),
            _ => {
                Self::from_utf16_units(chunks.iter().copied().map(u16::from_be_bytes), chunks.len())
            }
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
    /// [U+FFFD]: char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0x00, 0x73, 0xDD, 0x1E, 0x00, 0x69, 0x00, 0x63,
    ///           0xD8, 0x34];
    ///
    /// assert_eq!(String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            String::from_utf16be_lossy(v));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "str_from_utf16_endian", since = "1.98.0")]
    pub fn from_utf16be_lossy(v: &[u8]) -> String {
        // ignore-tidy-undocumented-unsafe
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
    #[inline]
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
        // SAFETY: Upheld by caller.
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

    /// Appends a given string slice onto the end of this `String`, returning
    /// [`TryReserveError`] otherwise.
    #[cfg_attr(
        not(no_global_oom_handling),
        expect(
            dead_code,
            reason = "currently only used in IO module when global OOM handling is disabled"
        )
    )]
    pub(crate) fn try_push_str(&mut self, string: &str) -> Result<(), TryReserveError> {
        self.vec.try_extend_from_slice_of_bytes(string.as_bytes())
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    fn push_str_slice(&mut self, slice: &[&str]) {
        // use saturating arithmetic to ensure that in the case of an overflow, reserve() throws OOM
        let additional: Saturating<usize> = slice.iter().map(|x| Saturating(x.len())).sum();
        self.reserve(additional.0);
        let (ptr, len, cap) = core::mem::take(self).into_raw_parts();
        // ignore-tidy-undocumented-unsafe
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
    /// # process_data("rust").expect("reserving capacity for 12 bytes should never fail");
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
    /// # process_data("rust").expect("reserving capacity for 12 bytes should never fail");
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
            core::char::encode_utf8_raw_unchecked(ch as u32, self.vec.as_mut_ptr().add(len));
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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

        // ignore-tidy-undocumented-unsafe
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
        let len = self.len();
        if len == 0 {
            // Explicit check results in better optimization
            return;
        }

        struct PanicGuard<'a> {
            s: &'a mut String,
            write: usize,
        }

        impl Drop for PanicGuard<'_> {
            fn drop(&mut self) {
                debug_assert!(self.write <= self.s.len());
                debug_assert!(str::from_utf8(&self.s.vec[..self.write]).is_ok());
                // SAFETY: Restore the string length to the number of bytes written so far.
                unsafe { self.s.vec.set_len(self.write) }
            }
        }

        // Fast path: find the first character that should be removed or return early.
        let mut chars = self.char_indices();
        let (mut read, write) = loop {
            let Some((idx, ch)) = chars.next() else { return };
            if hint::unlikely(!f(ch)) {
                break (idx + ch.len_utf8(), idx);
            }
        };
        drop(chars);

        // Slow path: at least one character is going to be removed.
        let mut g = PanicGuard { s: self, write };
        while read < len {
            // SAFETY: `read` is within bound because `read` < `len`, so taking
            // a slice with `len` is safe.
            let ch = unsafe { g.s.get_unchecked(read..len).chars().next().unwrap_unchecked() };
            let ch_len = ch.len_utf8();
            if f(ch) {
                // SAFETY: `read` is on a char boundary, as guaranteed above; `g.write` is
                // within bounds because it is always behind `read`.
                unsafe {
                    let ptr = g.s.vec.as_mut_ptr();
                    ptr::copy(ptr.add(read), ptr.add(g.write), ch_len);
                }
                g.write += ch_len;
            }
            read += ch_len;
        }

        // All bytes processed; commit the final length by dropping the guard.
        drop(g);
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
        // ignore-tidy-undocumented-unsafe
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

        if replace_with.len() > checked_range.len() {
            self.reserve(replace_with.len() - checked_range.len());
        }
        // SAFETY: We ensure that we're not replacing across a char boundary and
        // that the new contents are valid UTF-8. The only potentially-unsound
        // unwind from `splice` that would leave the string in an invalid state
        // would be from an error growing the allocation, which we protect against
        // by reserving it preemptively.
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
    /// This is useful in conjunction with [`String::from_utf8`] when you need
    /// to branch on whether the bytes are valid UTF-8, but still want to
    /// recover a lossily converted `String` in the error case. Use
    /// [`String::from_utf8_lossy_owned`] if you always need a lossily converted
    /// `String`.
    ///
    /// Since the original [`String::from_utf8`] error records where validation
    /// stopped, this method does not need to re-check the already valid prefix
    /// of the byte sequence.
    ///
    /// # Examples
    ///
    /// ```
    /// // some invalid bytes
    /// let input: Vec<u8> = b"Hello \xF0\x90\x80World".into();
    ///
    /// let (output, had_invalid_utf8) = match String::from_utf8(input) {
    ///     Ok(output) => (output, false),
    ///     Err(error) => {
    ///         // The bytes were not valid UTF-8, but we can still recover a string.
    ///         (error.into_utf8_lossy(), true)
    ///     }
    /// };
    ///
    /// assert_eq!(String::from("Hello �World"), output);
    /// assert!(had_invalid_utf8);
    /// ```
    #[must_use]
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "string_from_utf8_lossy_owned", since = "1.99.0")]
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
        match self.kind {
            FromUtf16ErrorKind::LoneSurrogate => "invalid utf-16: lone surrogate found",
            FromUtf16ErrorKind::OddBytes => "invalid utf-16: odd number of bytes",
        }
        .fmt(f)
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
    fn from_iter<I: IntoIterator<Item = core::ascii::Char>>(iter: I) -> Self {
        let buf = iter.into_iter().map(core::ascii::Char::to_u8).collect();
        // SAFETY: `buf` is guaranteed to be valid UTF-8 because the `core::ascii::Char` type
        // only contains ASCII values (0x00-0x7F), which are valid UTF-8.
        unsafe { String::from_utf8_unchecked(buf) }
    }
}

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "ascii_char", issue = "110998")]
impl<'a> FromIterator<&'a core::ascii::Char> for String {
    fn from_iter<I: IntoIterator<Item = &'a core::ascii::Char>>(iter: I) -> Self {
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
        Some(Utf8Pattern::StringPattern(self.as_str()))
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {
        #[stable(feature = "rust1", since = "1.0.0")]
        impl PartialEq<$rhs> for $lhs {
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
        impl PartialEq<$lhs> for $rhs {
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
impl_eq! { String, &str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'_, str>, str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'_, str>, &'_ str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'_, str>, String }

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_unstable(feature = "const_default", issue = "143894")]
const impl Default for String {
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

/// A type alias for [`!`].
///
/// This alias exists for backwards compatibility, and may be eventually deprecated.
#[stable(feature = "str_parse_error", since = "1.5.0")]
pub type ParseError = !;

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl FromStr for String {
    type Err = !;
    #[inline]
    fn from_str(s: &str) -> Result<String, !> {
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
    fn from_iter<I: IntoIterator<Item = core::ascii::Char>>(it: I) -> Self {
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
        // SAFETY: `bytes` are kept in UTF-8 form, only removing whole `char`s at a time.
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
        // ignore-tidy-undocumented-unsafe
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
    use core::cell::Cell;
    use core::ops::Bound;
    use core::str::pattern::{Pattern, SearchStep, Searcher};
    use core::{kani, ptr};

    use super::*;

    // =================================================================
    // Challenge 10: memory safety of String functions.
    //
    // Every harness runs the real, unmodified function body; no product
    // code path is compiled out under Kani. Inputs are built
    // constructively: nothing is `kani::assume`d anywhere in this module,
    // and every char-boundary index a harness feeds a function is
    // asserted to be one. One stub, `utf8_validate_unrolled`, replaces
    // `core::str::from_utf8` in the `retain` harness only (see there).
    //
    // Two input models, used side by side:
    //
    // - Unbounded length and capacity. `any_nul_string` builds a `String`
    //   of symbolic capacity and symbolic length, bounded only by CBMC's
    //   allocation model (`MAX_ALLOCATION_BYTES`, the constant and
    //   rationale of the VecDeque proofs in #681), every byte NUL, on a
    //   zeroed allocation (`nul_string`). Every function whose verified
    //   path is loop-free in the receiver has a harness on it: `pop`,
    //   `remove`, `insert`, `insert_str`, `split_off`, `drain`,
    //   `into_boxed_str`, `leak`, `replace_range` and `remove_matches`.
    //   NUL is the content these paths do not inspect (a `ptr::copy`
    //   moves whatever bytes are there); the one byte they do read,
    //   through `is_char_boundary`, is a boundary.
    // - Exhaustive content, bounded length. Where a function reads and
    //   returns characters (`pop`, `remove`, `drain`'s iterator,
    //   `remove_matches`'s match positions), a companion harness
    //   runs it on a string of at most `CONTENT_BYTES` bytes whose
    //   capacity is still symbolic and which carries a window of up to two
    //   symbolic `char`s (symbolic value, hence symbolic width) at a
    //   symbolic char boundary: every width class and every position, with
    //   the result asserted exactly. Reading such a window back inside a
    //   2^48-byte buffer makes CBMC's symbolic execution run out of memory
    //   at the pinned Kani, which is why content and length are split
    //   between two harnesses rather than combined.
    //
    // Bounded dimensions, each stated on its harness: the edit size of
    // `replace_range`, the number of matches of `remove_matches`, the
    // character count of `retain`, and the unit count of `from_utf16*`.
    //
    // Panic behaviour is documented, not UB: the `should_panic` harnesses
    // at the end check, separately, the inside-a-character and
    // past-the-end panics of every index-taking function.
    //
    // Findings at the pinned Kani (`1640445`, CBMC 6.11.0), each with the
    // workaround used:
    //
    // 1. A region initialized by a `write_bytes` of symbolic length on a
    //    2^48-byte object: once every property of a harness is decided,
    //    CBMC materialises the model of that region and runs out of memory
    //    (or past the 10-minute budget) whenever the solver happened to
    //    pick a large length, so the same harness passes or dies from one
    //    run to the next. The receivers are built on `alloc_zeroed` instead
    //    (one zero-filled object, `nul_string`), and no cover asks for a
    //    witness with a huge length.
    // 2. Slice accesses are not free: Kani's `offset` model now checks that
    //    the offset pointer's address equals the original address plus the
    //    offset, and CBMC encodes every pointer-to-address conversion with
    //    a case split over the objects of the program, so a harness that
    //    reads or compares bytes through slices in unrolled loops produces
    //    SAT instances of tens of millions of clauses. The `retain`
    //    harness and its validator stub therefore work on fixed arrays
    //    (plain array operations for CBMC) and compare results with
    //    constant indices.
    // 3. The 10-minute budget of the macOS autoharness job (3 vCPU, 7 GB,
    //    three harnesses in flight, 2–3× slower than this machine) sets
    //    the remaining bounds: `MAX_MATCHES_UNBOUNDED`, `REPLACE_EDIT_BYTES`,
    //    `RETAIN_CHARS` and `UTF16_BYTES`, each measured and stated where
    //    it is defined.
    // =================================================================

    /// Upper bound, in bytes, on the size of any allocation a harness makes. This is not a
    /// bound of the proof: it mirrors CBMC's memory model, whose objects are addressed with
    /// `64 - object_bits` offset bits (`--object-bits 12` in `scripts/run-kani.sh`), so every
    /// capacity whose allocation the model can back is explored and the constant only excludes
    /// allocations no real machine could back either. Same constant and rationale as the
    /// `VecDeque` proofs (#681).
    const MAX_ALLOCATION_BYTES: usize = 1 << 48;

    /// Length bound of the exhaustive-content harnesses (capacity stays symbolic). 64 bytes
    /// holds the two-character window at every position with room on both sides.
    const CONTENT_BYTES: usize = 64;

    /// A `String` of capacity `cap` and length `len <= cap`, every byte NUL, on a zeroed
    /// allocation (`alloc_zeroed`, which CBMC models as one zero-filled object) rather than
    /// `with_capacity` plus a `write_bytes` of symbolic length: at the pinned CBMC, once every
    /// property of a harness is decided, materialising the model of a region written by a
    /// symbolic-length `memset` runs out of memory whenever the solver happened to pick a
    /// large length (the same harness then passes or dies from one run to the next), whereas
    /// the zeroed object costs nothing. A capacity of zero gives `String::new()`, the same
    /// dangling-pointer state `with_capacity(0)` produces.
    fn nul_string(cap: usize, len: usize) -> String {
        if cap == 0 {
            return String::new();
        }
        let layout = core::alloc::Layout::array::<u8>(cap).unwrap();
        // SAFETY: `layout` has a non-zero size; the allocation is zero-filled, so its first
        // `len <= cap` bytes are initialized and valid UTF-8; it was made by the global
        // allocator with the layout `Vec<u8>` will free it with.
        let vec = unsafe {
            let ptr = crate::alloc::alloc_zeroed(layout);
            if ptr.is_null() {
                crate::alloc::handle_alloc_error(layout);
            }
            Vec::from_raw_parts(ptr, len, cap)
        };
        String { vec }
    }

    /// A `String` of symbolic capacity and symbolic length (both bounded only by the
    /// allocation model and `max_len`), every byte NUL. The capacity is a real allocation, so
    /// the reallocating and in-place paths of the functions are both reachable. No cover asks
    /// for a witness with a huge length: a `cover(len > 1 << 40)` forces a model with a 2^40-byte
    /// initialized region, which the pinned CBMC cannot materialise either.
    fn any_nul_string(max_len: usize) -> String {
        let cap: usize = kani::any_where(|c: &usize| *c <= MAX_ALLOCATION_BYTES);
        let len: usize = kani::any_where(|l: &usize| *l <= cap && *l <= max_len);
        let s = nul_string(cap, len);
        kani::cover(cap > len, "generator: spare capacity");
        kani::cover(cap == len && len > 0, "generator: full buffer");
        s
    }

    /// Up to two arbitrary `char`s (symbolic value, hence symbolic UTF-8 width) encoded at a
    /// symbolic char boundary inside an otherwise-NUL string.
    struct Window {
        c: [char; 2],
        /// UTF-8 widths of `c` (0 for a character that is not present).
        w: [usize; 2],
        /// Number of window characters present.
        n: usize,
        /// Byte offset of the window; always a char boundary.
        off: usize,
        /// Total width of the window in bytes.
        bytes: usize,
    }

    /// The window of a NUL-only string: empty, at offset 0. With it, `any_boundary` ranges
    /// over every index of the string, all of which are boundaries.
    const NO_WINDOW: Window = Window { c: ['\0'; 2], w: [0; 2], n: 0, off: 0, bytes: 0 };

    /// Builds the string described at [`Window`]: symbolic capacity (up to the allocation
    /// model), total length up to `max_len`. `n_min..=n_max` bounds the number of window
    /// characters, `at_end` places the window at the very end of the string, and
    /// `multibyte_first` makes the first window character at least two bytes wide.
    fn any_string_with_window(
        max_len: usize,
        n_min: usize,
        n_max: usize,
        at_end: bool,
        multibyte_first: bool,
    ) -> (String, Window) {
        let c0: char = if multibyte_first {
            kani::any_where(|c: &char| c.len_utf8() > 1)
        } else {
            kani::any()
        };
        let c1: char = kani::any();
        let n: usize = kani::any_where(|n: &usize| *n >= n_min && *n <= n_max);
        let w0 = if n >= 1 { c0.len_utf8() } else { 0 };
        let w1 = if n >= 2 { c1.len_utf8() } else { 0 };
        let bytes = w0 + w1;
        let cap: usize = kani::any_where(|c: &usize| *c >= bytes && *c <= MAX_ALLOCATION_BYTES);
        let body: usize = kani::any_where(|b: &usize| {
            b.checked_add(bytes).is_some_and(|total| total <= cap && total <= max_len)
        });
        let off: usize = if at_end { body } else { kani::any_where(|o: &usize| *o <= body) };
        let len = body + bytes;
        let mut s = nul_string(cap, len);
        // The window bytes overwrite NULs in place with the UTF-8 encodings of `c0`/`c1`
        // through safe slice indexing, so the string stays valid UTF-8 at every step.
        if n >= 1 {
            c0.encode_utf8(&mut s.vec[off..off + w0]);
        }
        if n >= 2 {
            c1.encode_utf8(&mut s.vec[off + w0..off + bytes]);
        }
        kani::cover(cap > len, "generator: spare capacity");
        (s, Window { c: [c0, c1], w: [w0, w1], n, off, bytes })
    }

    /// An arbitrary char boundary of `s`, chosen constructively from the three regions where
    /// one can lie (the NUL prefix, the start of a window character or the window's end, the
    /// NUL suffix) and asserted, never assumed. With `NO_WINDOW`, every index of `s`.
    fn any_boundary(s: &str, w: &Window) -> usize {
        let region: u8 = kani::any();
        let idx = match region % 3 {
            0 => kani::any_where(|i: &usize| *i <= w.off),
            1 => {
                let j: usize = kani::any_where(|j: &usize| *j <= w.n);
                w.off + if j >= 1 { w.w[0] } else { 0 } + if j >= 2 { w.w[1] } else { 0 }
            }
            _ => kani::any_where(|i: &usize| *i >= w.off + w.bytes && *i <= s.len()),
        };
        assert!(s.is_char_boundary(idx), "generator: the chosen index is a char boundary");
        idx
    }

    /// Two arbitrary char boundaries of `s`, in order.
    fn any_boundary_pair(s: &str, w: &Window) -> (usize, usize) {
        let a = any_boundary(s, w);
        let b = any_boundary(s, w);
        if a <= b { (a, b) } else { (b, a) }
    }

    /// Every `RangeBounds<usize>` encoding of `start..end` within a string of length `len`
    /// (unbounded start, unbounded end, inclusive end), with a cover per variant.
    fn any_bounds(start: usize, end: usize, len: usize) -> (Bound<usize>, Bound<usize>) {
        let lo = if start == 0 && kani::any() {
            kani::cover(true, "bounds: unbounded start");
            Bound::Unbounded
        } else {
            Bound::Included(start)
        };
        let sel: u8 = kani::any();
        let hi = if end == len && sel % 3 == 0 {
            kani::cover(true, "bounds: unbounded end");
            Bound::Unbounded
        } else if end > start && sel % 3 == 1 {
            kani::cover(true, "bounds: inclusive end");
            Bound::Included(end - 1)
        } else {
            Bound::Excluded(end)
        };
        (lo, hi)
    }

    /// An arbitrary valid UTF-8 string of at most `max_bytes <= 4` bytes, built as a
    /// concatenation of up to four symbolic `char`s (every valid string of that size is one
    /// input, multi-byte characters included): the replacement of `replace_range`, returned
    /// as a buffer and a length so that no allocation is involved.
    fn any_utf8_upto4(max_bytes: usize) -> ([u8; 4], usize) {
        let mut buf = [0u8; 4];
        let mut len = 0usize;
        let mut step = || {
            if kani::any() {
                let c: char = kani::any();
                let w = c.len_utf8();
                if len + w <= max_bytes {
                    c.encode_utf8(&mut buf[len..]);
                    len += w;
                }
            }
        };
        step();
        step();
        step();
        step();
        drop(step);
        (buf, len)
    }

    // -----------------------------------------------------------------
    // Unbounded length and capacity (NUL content), no unwind bound
    // unless noted.
    // -----------------------------------------------------------------

    /// `pop` on a string of symbolic length and capacity.
    #[kani::proof]
    fn check_pop() {
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES);
        let old = s.len();
        let r = s.pop();
        if old == 0 {
            assert!(r.is_none());
        } else {
            assert_eq!(r, Some('\0'));
            assert_eq!(s.len(), old - 1);
        }
        kani::cover(old == 0, "pop: empty string");
    }

    /// `remove` at a symbolic index of a string of symbolic length and capacity. The explicit
    /// unwind bound only stops the infeasible non-boundary panic path (`str` indexing's
    /// `slice_error_fail`, which walks to the next boundary) from being unrolled further; the
    /// verified path is loop-free.
    #[kani::proof]
    #[kani::unwind(4)]
    fn check_remove() {
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES);
        let old = s.len();
        let idx: usize = kani::any_where(|i: &usize| *i < old);
        let r = s.remove(idx);
        assert_eq!(r, '\0');
        assert_eq!(s.len(), old - 1);
        kani::cover(idx > 0 && idx + 1 < old, "remove: in the middle");
        kani::cover(idx + 1 == old && old > 1, "remove: the last byte");
    }

    /// `insert` of an arbitrary `char` at an arbitrary index of a string of symbolic length
    /// and capacity.
    #[kani::proof]
    fn check_insert() {
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES - 4);
        let old = s.len();
        let cap = s.capacity();
        let idx: usize = kani::any_where(|i: &usize| *i <= old);
        let ch: char = kani::any();
        s.insert(idx, ch);
        assert_eq!(s.len(), old + ch.len_utf8());
        kani::cover(cap == old, "insert: reallocates");
        kani::cover(cap >= old + 4 && old > 0, "insert: in place");
        kani::cover(idx > 0 && idx < old && ch.len_utf8() == 4, "insert: 4-byte character inside");
    }

    /// `insert_str` of a string of symbolic length at an arbitrary index, both of symbolic
    /// capacity.
    #[kani::proof]
    fn check_insert_str() {
        let t = any_nul_string(MAX_ALLOCATION_BYTES / 2);
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES / 2);
        let old = s.len();
        let cap = s.capacity();
        let idx: usize = kani::any_where(|i: &usize| *i <= old);
        s.insert_str(idx, &t);
        assert_eq!(s.len(), old + t.len());
        kani::cover(cap < old + t.len(), "insert_str: reallocates");
        kani::cover(cap >= old + t.len() && !t.is_empty(), "insert_str: in place");
        kani::cover(idx > 0 && idx < old && t.len() > 1 << 16, "insert_str: long insert inside");
        kani::cover(t.is_empty(), "insert_str: empty insert");
    }

    /// `split_off` at an arbitrary index of a string of symbolic length and capacity.
    #[kani::proof]
    fn check_split_off() {
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES);
        let old = s.len();
        let at: usize = kani::any_where(|i: &usize| *i <= old);
        let other = s.split_off(at);
        assert_eq!(s.len(), at);
        assert_eq!(other.len(), old - at);
        assert!(other.capacity() >= old - at);
        kani::cover(at > 0 && at < old, "split_off: in the middle");
        kani::cover(at == old && old > 0, "split_off: at the end");
        kani::cover(at == 0 && old > 0, "split_off: everything");
    }

    /// `drain` of an arbitrary range, in every `RangeBounds` encoding, of a string of symbolic
    /// length and capacity, dropped without iterating.
    #[kani::proof]
    fn check_drain_drop() {
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES);
        let old = s.len();
        let (start, end) = any_boundary_pair(&s, &NO_WINDOW);
        let bounds = any_bounds(start, end, old);
        drop(s.drain(bounds));
        assert_eq!(s.len(), old - (end - start));
        kani::cover(start > 0 && end < old && end - start > 1, "drain: interior range");
        kani::cover(start == end, "drain: empty range");
        kani::cover(start == 0 && end == old && old > 0, "drain: everything");
    }

    /// `into_boxed_str` with and without spare capacity (the latter reaches `shrink_to_fit`'s
    /// reallocation).
    #[kani::proof]
    fn check_into_boxed_str() {
        let s = any_nul_string(MAX_ALLOCATION_BYTES);
        let len = s.len();
        let cap = s.capacity();
        let b = s.into_boxed_str();
        assert_eq!(b.len(), len);
        kani::cover(cap > len, "into_boxed_str: shrinks");
        kani::cover(cap == len && len > 0, "into_boxed_str: already exact");
    }

    /// `leak`.
    #[kani::proof]
    fn check_leak() {
        let s = any_nul_string(MAX_ALLOCATION_BYTES);
        let len = s.len();
        let r: &mut str = s.leak();
        assert_eq!(r.len(), len);
        kani::cover(len > 1 << 16, "leak: long string");
    }

    /// Largest edit `replace_range` makes: the removed range and the replacement are each at
    /// most this many bytes. `Vec::splice`'s loops run once per *edited* byte, never per
    /// receiver byte, so this bounds the edit, not the string. Two bytes rather than four for
    /// the 10-minute budget of the macOS autoharness job (four bytes take 145 s here, two
    /// 58 s); a content twin with four-byte edits on the 64-byte receiver and the result
    /// asserted byte for byte exceeded the budget (the solver has to see through `splice`'s
    /// reallocation and two tail moves) and is not included.
    const REPLACE_EDIT_BYTES: usize = 2;

    /// `replace_range` on a receiver of symbolic length and capacity: an arbitrary range of at
    /// most `REPLACE_EDIT_BYTES` bytes, in every `RangeBounds` encoding, replaced by every
    /// valid UTF-8 string of at most `REPLACE_EDIT_BYTES` bytes.
    #[kani::proof]
    #[kani::unwind(3)]
    fn check_replace_range() {
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES - REPLACE_EDIT_BYTES);
        let old = s.len();
        let cap = s.capacity();
        let start: usize = kani::any_where(|i: &usize| *i <= old);
        let k: usize = kani::any_where(|k: &usize| *k <= REPLACE_EDIT_BYTES && start + *k <= old);
        let end = start + k;
        let (buf, n) = any_utf8_upto4(REPLACE_EDIT_BYTES);
        // SAFETY: `buf[..n]` is a concatenation of UTF-8 encodings of `char`s.
        let repl: &str = unsafe { core::str::from_utf8_unchecked(&buf[..n]) };
        let bounds = any_bounds(start, end, old);
        s.replace_range(bounds, repl);
        assert_eq!(s.len(), old - k + repl.len());
        kani::cover(
            repl.len() > k && cap < old + repl.len() - k,
            "replace_range: grows, reallocates",
        );
        kani::cover(repl.len() > k && cap >= old + repl.len() - k, "replace_range: grows in place");
        kani::cover(repl.len() < k, "replace_range: shrinks");
        kani::cover(start == old && !repl.is_empty(), "replace_range: appends");
        kani::cover(repl.len() == 2 && repl.chars().count() == 1, "replace_range: one 2-byte char");
        kani::cover(start > 0 && end < old && k > 0, "replace_range: interior");
    }

    /// Largest number of matches the general searcher model reports in one `remove_matches`
    /// call on the 64-byte content receiver. Each match is one iteration of the two per-match
    /// loops in `remove_matches` (`from_fn(..).collect()` and the compaction loop).
    const MAX_MATCHES: usize = 5;

    /// The same bound for the receiver of symbolic length and capacity. Every match there is
    /// one `ptr::copy` of a symbolic-length region of a 2^48-byte object, chained on the
    /// previous one; at the pinned CBMC three such copies solve in a few minutes and five exceed
    /// the 10-minute budget, so the unbounded harness reports at most two matches (three copies,
    /// including the tail) and the content harness five.
    const MAX_MATCHES_UNBOUNDED: usize = 2;

    /// The most general `Searcher` the (unsafe) `Searcher` contract admits over a haystack:
    /// up to `max_matches` matches, each an arbitrary char-boundary range at or after the end
    /// of the previous one (empty ranges allowed, as the contract allows), then `None`. The
    /// boundaries are chosen with `any_boundary`, so they land on real character boundaries
    /// of the window content; every one is asserted. `remove_matches` only calls
    /// `next_match`; `next` is implemented consistently (a `Reject` for the gap, then the
    /// `Match`). The model records the number of bytes it reported as matched.
    struct AnyPattern<'c> {
        w: &'c Window,
        removed: &'c Cell<usize>,
        count: &'c Cell<usize>,
        max_matches: usize,
    }

    struct AnySearcher<'a, 'c> {
        haystack: &'a str,
        w: &'c Window,
        removed: &'c Cell<usize>,
        count: &'c Cell<usize>,
        left: usize,
        front: usize,
        pending: Option<(usize, usize)>,
    }

    impl<'c> Pattern for AnyPattern<'c> {
        type Searcher<'a> = AnySearcher<'a, 'c>;

        fn into_searcher(self, haystack: &str) -> AnySearcher<'_, 'c> {
            AnySearcher {
                haystack,
                w: self.w,
                removed: self.removed,
                count: self.count,
                left: self.max_matches,
                front: 0,
                pending: None,
            }
        }
    }

    impl<'a, 'c> AnySearcher<'a, 'c> {
        fn choose(&mut self) -> Option<(usize, usize)> {
            if self.left == 0 {
                return None;
            }
            self.left -= 1;
            let a0 = any_boundary(self.haystack, self.w);
            let a = if a0 < self.front { self.front } else { a0 };
            let b0 = any_boundary(self.haystack, self.w);
            let b = if b0 < a { a } else { b0 };
            assert!(self.haystack.is_char_boundary(a) && self.haystack.is_char_boundary(b));
            self.front = b;
            self.removed.set(self.removed.get() + (b - a));
            self.count.set(self.count.get() + 1);
            Some((a, b))
        }
    }

    // SAFETY: every reported range lies on char boundaries of the haystack, ranges are
    // reported in increasing order and do not overlap (each starts at or after the end of the
    // previous one), and `Reject`s cover exactly the gaps between them.
    unsafe impl<'a, 'c> Searcher<'a> for AnySearcher<'a, 'c> {
        fn haystack(&self) -> &'a str {
            self.haystack
        }

        fn next(&mut self) -> SearchStep {
            if let Some((a, b)) = self.pending.take() {
                return SearchStep::Match(a, b);
            }
            let front = self.front;
            match self.choose() {
                Some((a, b)) if a > front => {
                    self.pending = Some((a, b));
                    SearchStep::Reject(front, a)
                }
                Some((a, b)) => SearchStep::Match(a, b),
                None if front < self.haystack.len() => {
                    self.front = self.haystack.len();
                    SearchStep::Reject(front, self.haystack.len())
                }
                None => SearchStep::Done,
            }
        }

        fn next_match(&mut self) -> Option<(usize, usize)> {
            if let Some(m) = self.pending.take() {
                return Some(m);
            }
            self.choose()
        }
    }

    /// Runs `remove_matches` against the general searcher model and checks the length.
    fn remove_matches_against_model(
        s: &mut String,
        w: &Window,
        max_matches: usize,
    ) -> (usize, usize) {
        let old = s.len();
        let removed = Cell::new(0usize);
        let count = Cell::new(0usize);
        s.remove_matches(AnyPattern { w, removed: &removed, count: &count, max_matches });
        assert_eq!(s.len(), old - removed.get());
        (removed.get(), count.get())
    }

    /// `remove_matches` on a receiver of symbolic length and capacity against the general
    /// searcher model: every pattern whose searcher respects the `Searcher` contract and
    /// reports at most `MAX_MATCHES_UNBOUNDED` matches, at any positions, is one input. (The
    /// loops run a concrete number of times, the model's match count; the unwind bound is
    /// that number plus one.)
    #[kani::proof]
    #[kani::unwind(4)]
    fn check_remove_matches() {
        let mut s = any_nul_string(MAX_ALLOCATION_BYTES);
        let (removed, count) =
            remove_matches_against_model(&mut s, &NO_WINDOW, MAX_MATCHES_UNBOUNDED);
        kani::cover(count == MAX_MATCHES_UNBOUNDED && removed > 0, "remove_matches: two matches");
        kani::cover(removed > 0 && s.len() > 1 << 16, "remove_matches: long remainder");
        kani::cover(count > 0 && removed == 0, "remove_matches: only empty matches");
    }

    // -----------------------------------------------------------------
    // Exhaustive content, bounded length (`CONTENT_BYTES`), symbolic
    // capacity.
    // -----------------------------------------------------------------

    /// `pop` on a string whose last (up to two) characters are arbitrary.
    #[kani::proof]
    fn check_pop_content() {
        let (mut s, w) = any_string_with_window(CONTENT_BYTES, 0, 2, true, false);
        let old = s.len();
        let r = s.pop();
        if old == 0 {
            assert!(r.is_none());
        } else if w.n >= 1 {
            assert_eq!(r, Some(w.c[w.n - 1]));
            assert_eq!(s.len(), old - w.w[w.n - 1]);
        } else {
            assert_eq!(r, Some('\0'));
            assert_eq!(s.len(), old - 1);
        }
        if w.n == 2 {
            assert_eq!(s.pop(), Some(w.c[0]));
            assert_eq!(s.len(), old - w.bytes);
        }
        kani::cover(w.n == 2 && w.bytes == 8, "pop: two 4-byte characters");
    }

    /// `remove` of one of the window characters (see `check_remove` for the unwind bound).
    #[kani::proof]
    #[kani::unwind(4)]
    fn check_remove_content() {
        let (mut s, w) = any_string_with_window(CONTENT_BYTES, 1, 2, false, false);
        let j: usize = kani::any_where(|j: &usize| *j < w.n);
        let idx = w.off + if j == 1 { w.w[0] } else { 0 };
        let old = s.len();
        let r = s.remove(idx);
        assert_eq!(r, w.c[j]);
        assert_eq!(s.len(), old - w.w[j]);
        kani::cover(
            idx > 0 && idx + w.w[j] < old && w.w[j] == 4,
            "remove: 4-byte character inside",
        );
        kani::cover(j == 1, "remove: the second window character");
        kani::cover(w.n == 2 && w.bytes == 8, "remove: two 4-byte characters");
        kani::cover(w.off > 0 && w.off + w.bytes < old, "remove: window strictly inside");
    }

    /// `drain` iterated: the range starts at the window, so the first drained character is
    /// the first window character; the range end is an arbitrary boundary after it.
    #[kani::proof]
    fn check_drain_next_content() {
        let (mut s, w) = any_string_with_window(CONTENT_BYTES, 0, 2, false, false);
        let start = w.off;
        let e = any_boundary(&s, &w);
        let end = if e < start { start } else { e };
        let old = s.len();
        let mut d = s.drain(start..end);
        if end > start && w.n >= 1 {
            assert_eq!(d.next(), Some(w.c[0]));
            if w.n == 2 && end == w.off + w.bytes {
                assert_eq!(d.next_back(), Some(w.c[1]));
            } else if w.n == 2 && end > w.off + w.bytes {
                assert_eq!(d.next_back(), Some('\0'));
            }
        } else if end > start {
            assert_eq!(d.next(), Some('\0'));
        } else {
            assert!(d.next().is_none());
        }
        drop(d);
        assert_eq!(s.len(), old - (end - start));
        kani::cover(w.n == 2 && end == w.off + w.bytes && w.bytes == 8, "drain: two 4-byte chars");
        kani::cover(w.off > 0 && w.off + w.bytes < old, "drain: window strictly inside");
    }

    /// `remove_matches` against the general searcher model on arbitrary content: the
    /// reported ranges land on the window's real character boundaries.
    #[kani::proof]
    #[kani::unwind(7)]
    fn check_remove_matches_content() {
        let (mut s, w) = any_string_with_window(CONTENT_BYTES, 0, 2, false, false);
        let (removed, count) = remove_matches_against_model(&mut s, &w, MAX_MATCHES);
        kani::cover(w.n == 2 && removed == w.bytes, "remove_matches: exactly the window");
        kani::cover(count == MAX_MATCHES, "remove_matches: five matches");
        kani::cover(w.n == 2 && w.bytes == 8, "remove_matches: two 4-byte characters");
        kani::cover(w.off > 0 && removed == 0, "remove_matches: window inside, nothing removed");
    }

    // -----------------------------------------------------------------
    // Bounded functions (tool limits documented on each harness).
    // -----------------------------------------------------------------

    /// Character bound of the `retain` harness: `retain`'s two loops in `string.rs` run once
    /// per character. A loop contract would need the invariant "the unread suffix is valid
    /// UTF-8 on a havocked buffer", a quantifier with a symbolic bound (which the pinned Kani
    /// rejects, kani#4719) or a fixed backing size (a byte bound by another name), and the
    /// loop body's temporaries are outside `loop_modifies` (kani#4906). Four characters for
    /// the exact-content harness: proving the result byte for byte means reasoning through one
    /// symbolic-position `ptr::copy` per character (48 s at four characters, 407 s at six, past
    /// the 10-minute budget of the macOS autoharness job at eight); the visiting discipline
    /// and the length are checked on longer strings by `check_retain_visits_bounded`.
    const RETAIN_CHARS: usize = 4;

    /// Replacement for `core::str::from_utf8` in the `retain` harnesses only. `retain`'s
    /// `PanicGuard::drop` calls `from_utf8` inside a `debug_assert!`; under CI's
    /// `-Z loop-contracts` the invariants on `run_utf8_validation`'s loops abstract that
    /// validator, which makes the harness both unsound as a functional check and far too
    /// expensive. This stub is a per-character validator with the byte rules of
    /// `run_utf8_validation` (RFC 3629: lead-byte classes, the `E0`/`ED`/`F0`/`F4` second-byte
    /// restrictions, continuation bytes), unrolled over at most `RETAIN_CHARS` characters by
    /// the harness's unwind bound. It returns `Ok` exactly when the real validator does and
    /// panics otherwise: `Utf8Error` has no public constructor, so the stub cannot return
    /// `Err`, and a panic is what the `debug_assert!` that calls it would raise. Checked by
    /// mutation locally: making it panic on a valid multi-byte prefix fails the harness.
    ///
    /// It validates a copy of the input in a fixed array: an array access is a plain array
    /// operation for CBMC, whereas every slice access goes through pointer arithmetic and, at
    /// the pinned Kani, through the `offset` model's address checks, whose encoding grows
    /// with the number of objects in the harness — the dominant cost of these harnesses.
    fn utf8_validate_unrolled(v: &[u8]) -> Result<&str, core::str::Utf8Error> {
        const CAP: usize = 4 * RETAIN_CHARS;
        let n = v.len();
        assert!(n <= CAP, "utf8_validate_unrolled: input longer than the harness bound");
        let mut a = [0u8; CAP];
        a[..n].copy_from_slice(v);
        let cont = |b: u8| b >= 0x80 && b <= 0xBF;
        let mut i = 0;
        while i < n {
            let b0 = a[i];
            let w = if b0 < 0x80 {
                1
            } else if b0 >= 0xC2 && b0 <= 0xDF {
                2
            } else if b0 >= 0xE0 && b0 <= 0xEF {
                3
            } else if b0 >= 0xF0 && b0 <= 0xF4 {
                4
            } else {
                panic!("utf8_validate_unrolled: invalid lead byte")
            };
            if i + w > n {
                panic!("utf8_validate_unrolled: truncated sequence");
            }
            if w >= 2 {
                let b1 = a[i + 1];
                let second_ok = match b0 {
                    0xE0 => b1 >= 0xA0,
                    0xED => b1 <= 0x9F,
                    0xF0 => b1 >= 0x90,
                    0xF4 => b1 <= 0x8F,
                    _ => true,
                };
                let rest_ok = (w < 3 || cont(a[i + 2])) && (w < 4 || cont(a[i + 3]));
                if !(cont(b1) && second_ok && rest_ok) {
                    panic!("utf8_validate_unrolled: invalid continuation byte");
                }
            }
            i += w;
        }
        // SAFETY: every byte sequence was checked against the UTF-8 rules above.
        Ok(unsafe { core::str::from_utf8_unchecked(v) })
    }

    /// `retain` on every string of at most `K` arbitrary characters, with an arbitrary
    /// (nondeterministic per call) predicate: the predicate sees exactly the string's
    /// characters, in order, and the result is exactly the kept characters, in order. The
    /// input and the expected output live in fixed arrays (the encodings laid out back to
    /// back; the predicate copies the bytes of each kept character across), and the result is
    /// copied into a fixed array by one `copy_from_slice` and compared with constant indices —
    /// no per-byte slice access in the harness, for the reason given at
    /// `utf8_validate_unrolled`.
    /// Replacement for `core::str::from_utf8` in the `retain` harness that agrees with the real
    /// function on every input the harness produces, without re-reading the bytes: the
    /// harness proves that the result of `retain` is, byte for byte, a concatenation of UTF-8
    /// encodings of `char`s (and on the unwind path the guard sees the kept prefix, another
    /// such concatenation), so the real validator returns `Ok` on all of them. Re-validating
    /// those bytes in the stub costs the solver as much as the proof itself (the bytes are the
    /// result of a chain of symbolic-length `ptr::copy`s), hence this form.
    fn from_utf8_as_proved(v: &[u8]) -> Result<&str, core::str::Utf8Error> {
        // SAFETY: see above — the harness asserts that `v` is valid UTF-8.
        Ok(unsafe { core::str::from_utf8_unchecked(v) })
    }

    macro_rules! retain_harness {
        ($name:ident, $k:expr, $unwind:literal, $stub:ident) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::stub(core::str::from_utf8, $stub)]
            fn $name() {
                const K: usize = $k;
                const CAP: usize = 4 * K;
                let chars: [char; K] = kani::any();
                let n: usize = kani::any_where(|n: &usize| *n <= K);
                let mut input = [0u8; CAP];
                let mut widths = [0usize; K];
                let mut len = 0usize;
                for i in 0..K {
                    if i < n {
                        let mut enc = [0u8; 4];
                        let w = chars[i].encode_utf8(&mut enc).len();
                        for j in 0..4 {
                            if j < w {
                                input[len + j] = enc[j];
                            }
                        }
                        widths[i] = w;
                        len += w;
                    }
                }
                let mut s = String::with_capacity(CAP);
                // SAFETY: `input[..len]` is a concatenation of UTF-8 encodings of `char`s and
                // fits the capacity; the bytes are initialized before the length is set.
                unsafe {
                    ptr::copy_nonoverlapping(input.as_ptr(), s.vec.as_mut_ptr(), len);
                    s.vec.set_len(len);
                }
                let mut expected = [0u8; CAP];
                let mut expected_len = 0usize;
                let mut seen = 0usize;
                let mut kept = 0usize;
                let mut pos = 0usize;
                let mut moved_4byte = false;
                s.retain(|c| {
                    assert!(seen < n && c == chars[seen], "retain: visits the characters in order");
                    let w = widths[seen];
                    let keep: bool = kani::any();
                    if keep {
                        // A kept character preceded by a removed one is moved by `ptr::copy`.
                        if seen > kept && w == 4 {
                            moved_4byte = true;
                        }
                        for j in 0..4 {
                            if j < w {
                                expected[expected_len + j] = input[pos + j];
                            }
                        }
                        expected_len += w;
                        kept += 1;
                    }
                    seen += 1;
                    pos += w;
                    keep
                });
                assert!(seen == n, "retain: visits every character exactly once");
                assert!(s.len() == expected_len, "retain: the result has the kept bytes");
                let mut got = [0u8; CAP];
                got[..expected_len].copy_from_slice(s.as_bytes());
                // Compared with constant indices: an array equality lowers to `memcmp`, a loop
                // in CBMC's library that the unwind bound would have to cover byte by byte.
                for i in 0..K {
                    for j in 0..4 {
                        assert!(
                            got[4 * i + j] == expected[4 * i + j],
                            "retain: the result is exactly the kept characters, in order"
                        );
                    }
                }
                kani::cover(kept == n && n > 0, "retain: nothing removed (fast path)");
                kani::cover(kept == 0 && n > 0, "retain: everything removed");
                kani::cover(moved_4byte, "retain: 4-byte character moved after a removal");
            }
        };
    }

    retain_harness!(check_retain_bounded, RETAIN_CHARS, 5, utf8_validate_unrolled);

    /// Character bound of `check_retain_visits_bounded`: five characters take 47 s and 1.9 GB
    /// here, six 124 s, eight 469 s (the solver reasons about the decoding of every later
    /// character through the earlier symbolic-position copies); the macOS autoharness job runs
    /// three harnesses in 7 GB, 2–3× slower than this machine.
    const RETAIN_VISITS_CHARS: usize = 5;

    /// `retain`'s visiting discipline and the length of its result on every string of at most
    /// `K` arbitrary characters: the predicate sees exactly the string's characters, in order,
    /// and the result has exactly the kept bytes. The exact content of the result — hence the
    /// claim of `PanicGuard::drop`'s `debug_assert!`, which the `from_utf8_as_proved` stub
    /// returns without re-checking here — is asserted by `check_retain_bounded`, on strings of
    /// at most `RETAIN_CHARS` characters.
    macro_rules! retain_visits_harness {
        ($name:ident, $k:expr, $unwind:literal) => {
            #[kani::proof]
            #[kani::unwind($unwind)]
            #[kani::stub(core::str::from_utf8, from_utf8_as_proved)]
            fn $name() {
                const K: usize = $k;
                const CAP: usize = 4 * K;
                let chars: [char; K] = kani::any();
                let n: usize = kani::any_where(|n: &usize| *n <= K);
                let mut input = [0u8; CAP];
                let mut len = 0usize;
                for i in 0..K {
                    if i < n {
                        let mut enc = [0u8; 4];
                        let w = chars[i].encode_utf8(&mut enc).len();
                        for j in 0..4 {
                            if j < w {
                                input[len + j] = enc[j];
                            }
                        }
                        len += w;
                    }
                }
                let mut s = String::with_capacity(CAP);
                // SAFETY: `input[..len]` is a concatenation of UTF-8 encodings of `char`s and
                // fits the capacity; the bytes are initialized before the length is set.
                unsafe {
                    ptr::copy_nonoverlapping(input.as_ptr(), s.vec.as_mut_ptr(), len);
                    s.vec.set_len(len);
                }
                let mut seen = 0usize;
                let mut kept = 0usize;
                let mut kept_bytes = 0usize;
                let mut moved_4byte = false;
                s.retain(|c| {
                    assert!(seen < n && c == chars[seen], "retain: visits the characters in order");
                    let keep: bool = kani::any();
                    if keep {
                        if seen > kept && c.len_utf8() == 4 {
                            moved_4byte = true;
                        }
                        kept_bytes += c.len_utf8();
                        kept += 1;
                    }
                    seen += 1;
                    keep
                });
                assert!(seen == n, "retain: visits every character exactly once");
                assert!(s.len() == kept_bytes, "retain: the result has exactly the kept bytes");
                kani::cover(kept == n && n > 0, "retain: nothing removed (fast path)");
                kani::cover(kept == 0 && n > 0, "retain: everything removed");
                kani::cover(moved_4byte, "retain: 4-byte character moved after a removal");
            }
        };
    }

    retain_visits_harness!(check_retain_visits_bounded, RETAIN_VISITS_CHARS, 6);

    /// Byte bound of the `from_utf16*` harnesses: the strict variants loop once per code unit
    /// in `from_utf16_units` (a `for` over `DecodeUtf16`, which Kani's loop contracts cannot
    /// reach, kani#4907) and the lossy ones inside `Iterator::fold`. Twelve bytes (six code
    /// units) for the big-endian functions, which have one code path; eight for the
    /// little-endian ones, which have three (aligned, aligned with an odd trailing byte,
    /// unaligned), each collecting into a growing `String`: `from_utf16le_lossy` takes 94 s and
    /// 7.4 GB here at fourteen bytes, 68 s and 6.2 GB at twelve, 53 s and 4.6 GB at ten, against
    /// 7 GB shared by three harnesses on the macOS autoharness runner. Four code units still
    /// reach every case the covers ask for (both alignments, an odd byte count, a decoded
    /// surrogate pair, an unpaired surrogate).
    const UTF16_BYTES: usize = 12;
    const UTF16_BYTES_LE: usize = 8;

    /// An arbitrary sub-slice of an arbitrary `N`-byte array: both alignments of the start,
    /// both parities of the length.
    fn any_utf16_bytes<const N: usize>() -> ([u8; N], usize, usize) {
        let arr: [u8; N] = kani::any();
        let to: usize = kani::any_where(|t: &usize| *t <= N);
        let from: usize = kani::any_where(|f: &usize| *f <= to);
        (arr, from, to)
    }

    /// Loop-free reference over the code units of `v` (unrolled over at most
    /// `N / 2` units): whether a surrogate is unpaired, and whether a pair occurs.
    fn utf16_shape<const N: usize>(v: &[u8], little_endian: bool) -> (bool, bool) {
        let units = v.len() / 2;
        let mut lone = false;
        let mut pair = false;
        let mut expect_low = false;
        for i in 0..N / 2 {
            if i < units {
                let bytes = [v[2 * i], v[2 * i + 1]];
                let u = if little_endian {
                    u16::from_le_bytes(bytes)
                } else {
                    u16::from_be_bytes(bytes)
                };
                let high = (0xD800..=0xDBFF).contains(&u);
                let low = (0xDC00..=0xDFFF).contains(&u);
                if expect_low {
                    if low {
                        pair = true;
                        expect_low = false;
                    } else {
                        lone = true;
                        expect_low = high;
                    }
                } else if high {
                    expect_low = true;
                } else if low {
                    lone = true;
                }
            }
        }
        (lone || expect_low, pair)
    }

    macro_rules! utf16_strict_harness {
        ($name:ident, $f:ident, $le:expr, $n:expr, $unwind:literal) => {
            /// BOUNDED: input at most `$n` bytes. Functional specification: `Ok` iff
            /// the byte count is even and no surrogate is unpaired; the decoded string has
            /// between one and three bytes per code unit.
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $name() {
                let (arr, from, to) = any_utf16_bytes::<$n>();
                let v = &arr[from..to];
                let units = v.len() / 2;
                let odd = v.len() % 2 == 1;
                let (lone, pair) = utf16_shape::<$n>(v, $le);
                match String::$f(v) {
                    Ok(s) => {
                        assert!(!odd && !lone);
                        assert!(s.len() >= units && s.len() <= 3 * units);
                    }
                    Err(_) => assert!(odd || lone),
                }
                kani::cover(
                    v.as_ptr().addr() % 2 == 1 && units >= 2,
                    "from_utf16: unaligned input",
                );
                kani::cover(v.as_ptr().addr() % 2 == 0 && units >= 2, "from_utf16: aligned input");
                kani::cover(odd, "from_utf16: odd byte count");
                kani::cover(pair && !lone && !odd, "from_utf16: surrogate pair decoded");
                kani::cover(lone, "from_utf16: unpaired surrogate");
            }
        };
    }

    macro_rules! utf16_lossy_harness {
        ($name:ident, $f:ident, $le:expr, $n:expr, $unwind:literal) => {
            /// BOUNDED: input at most `$n` bytes. Functional specification: the
            /// decoded string has between one and three bytes per code unit, plus a
            /// three-byte replacement character for an odd trailing byte.
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $name() {
                let (arr, from, to) = any_utf16_bytes::<$n>();
                let v = &arr[from..to];
                let units = v.len() / 2;
                let odd = (v.len() % 2) as usize;
                let (lone, pair) = utf16_shape::<$n>(v, $le);
                let s = String::$f(v);
                assert!(s.len() >= units + odd && s.len() <= 3 * units + 3 * odd);
                kani::cover(
                    v.as_ptr().addr() % 2 == 1 && units >= 2,
                    "from_utf16_lossy: unaligned input",
                );
                kani::cover(
                    v.as_ptr().addr() % 2 == 0 && units >= 2,
                    "from_utf16_lossy: aligned input",
                );
                kani::cover(odd == 1, "from_utf16_lossy: odd byte count");
                kani::cover(pair && !lone, "from_utf16_lossy: surrogate pair decoded");
                kani::cover(lone, "from_utf16_lossy: unpaired surrogate replaced");
            }
        };
    }

    utf16_strict_harness!(check_from_utf16le, from_utf16le, true, UTF16_BYTES_LE, 5);
    utf16_strict_harness!(check_from_utf16be, from_utf16be, false, UTF16_BYTES, 7);
    utf16_lossy_harness!(check_from_utf16le_lossy, from_utf16le_lossy, true, UTF16_BYTES_LE, 5);
    utf16_lossy_harness!(check_from_utf16be_lossy, from_utf16be_lossy, false, UTF16_BYTES, 7);

    // -----------------------------------------------------------------
    // Documented panics, one cause per harness: an index inside a
    // multi-byte character (bounded-length content model), and an index
    // past the end (unbounded length). Each `should_panic` harness admits
    // only inputs of its cause, so passing means that cause alone makes
    // every input panic.
    // -----------------------------------------------------------------

    /// A string whose window is one multi-byte character, and an index strictly inside it.
    fn string_and_index_inside_char() -> (String, usize) {
        let (s, w) = any_string_with_window(CONTENT_BYTES, 1, 1, false, true);
        let idx: usize = kani::any_where(|i: &usize| *i > w.off && *i < w.off + w.w[0]);
        kani::cover(w.off > 0 && w.off + w.bytes < s.len(), "panic: window strictly inside");
        kani::cover(w.w[0] == 4 && idx == w.off + 3, "panic: last byte of a 4-byte character");
        (s, idx)
    }

    /// A string of symbolic length and an index strictly past its end.
    fn string_and_index_past_end() -> (String, usize) {
        let s = any_nul_string(MAX_ALLOCATION_BYTES - 4);
        let idx: usize = kani::any_where(|i: &usize| *i > s.len());
        (s, idx)
    }

    macro_rules! panic_harnesses {
        ($inside:ident, $past:ident, $unwind:literal, |$s:ident, $idx:ident| $call:expr) => {
            #[kani::proof]
            #[kani::should_panic]
            #[kani::unwind($unwind)]
            fn $inside() {
                let (mut $s, $idx) = string_and_index_inside_char();
                let _ = $call;
            }

            #[kani::proof]
            #[kani::should_panic]
            #[kani::unwind($unwind)]
            fn $past() {
                let (mut $s, $idx) = string_and_index_past_end();
                let _ = $call;
            }
        };
    }

    panic_harnesses!(check_insert_panics_inside_char, check_insert_panics_past_end, 2, |s, idx| s
        .insert(idx, 'x'));
    panic_harnesses!(
        check_insert_str_panics_inside_char,
        check_insert_str_panics_past_end,
        2,
        |s, idx| s.insert_str(idx, "x")
    );
    panic_harnesses!(
        check_split_off_panics_inside_char,
        check_split_off_panics_past_end,
        2,
        |s, idx| s.split_off(idx)
    );
    panic_harnesses!(check_drain_panics_inside_char, check_drain_panics_past_end, 2, |s, idx| s
        .drain(idx..));
    panic_harnesses!(
        check_replace_range_panics_inside_char,
        check_replace_range_panics_past_end,
        2,
        |s, idx| s.replace_range(idx.., "x")
    );
    panic_harnesses!(check_remove_panics_inside_char, check_remove_panics_past_end, 4, |s, idx| s
        .remove(idx));
}
