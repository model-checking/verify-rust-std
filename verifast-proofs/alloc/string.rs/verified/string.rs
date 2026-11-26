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

#[cfg(not(no_global_oom_handling))]
use core::ascii;
use core::error::Error;
use core::iter::FusedIterator;
#[cfg(not(no_global_oom_handling))]
use core::iter::from_fn;
#[cfg(not(no_global_oom_handling))]
use core::mem::MaybeUninit;
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

/*@

lem close_foreach_u8_own(t: thread_id_t, bs: list<u8>)
    req true;
    ens foreach(bs, own::<u8>(t));
{
    match bs {
        nil => { close foreach(nil, own::<u8>(t)); }
        cons(b, rest) => {
            close_foreach_u8_own(t, rest);
            close u8_own(t, b);
            close own::<u8>(t)(b);
            close foreach(bs, own::<u8>(t));
        }
    }
}

lem append_utf8(left: list<u8>, right: list<u8>)
    req is_valid_utf8(left) == true &*& is_valid_utf8(right) == true;
    ens is_valid_utf8(append(left, right)) == true;
{
    match left {
        nil => {}
        cons(b0, rest0) => {
            if b0 <= 0x7F {
                append_utf8(rest0, right);
            } else {
                match rest0 {
                    nil => {}
                    cons(b1, rest1) => {
                        if b0 <= 0xDF {
                            append_utf8(rest1, right);
                        } else {
                            match rest1 {
                                nil => {}
                                cons(b2, rest2) => {
                                    if b0 <= 0xEF {
                                        append_utf8(rest2, right);
                                    } else {
                                        match rest2 {
                                            nil => {}
                                            cons(b3, rest3) => {
                                                append_utf8(rest3, right);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}


lem own_utf16_units_result(t: thread_id_t, value: std::result::Result<String, FromUtf16Error>)
    req match value {
        Result::Ok(s) => <String>.own(t, s),
        Result::Err(e) => e == FromUtf16Error { kind: FromUtf16ErrorKind::LoneSurrogate }
    };
    ens <std::result::Result<String, FromUtf16Error>>.own(t, value);
{
    match value {
        Result::Ok(s) => {}
        Result::Err(e) => {
            close <FromUtf16ErrorKind>.own(t, FromUtf16ErrorKind::LoneSurrogate);
            close <FromUtf16Error>.own(t, e);
        }
    }
    close <std::result::Result<String, FromUtf16Error>>.own(t, value);
}

lem switch_utf8_rest(rest0: list<u8>, b0: u8)
    req b0 >= 0x80 &*& is_valid_utf8(cons(b0, rest0)) == true;
    ens !is_utf8_tail(b0) &*& utf8_seq_len(b0) <= 1 + length(rest0) &*&
        is_valid_utf8(take(utf8_seq_len(b0), cons(b0, rest0))) == true &*&
        is_valid_utf8(drop(utf8_seq_len(b0), cons(b0, rest0))) == true;
{
    match rest0 {
        nil => {}
        cons(b1, rest1) => {
            if b0 >= 0xE0 {
                match rest1 {
                    nil => {}
                    cons(b2, rest2) => {
                        if b0 >= 0xF0 {
                            match rest2 {
                                nil => {}
                                cons(b3, rest3) => {}
                            }
                        }
                    }
                }
            }
        }
    }
}

lem utf8_first_scalar(bs: list<u8>)
    req bs != nil &*& is_valid_utf8(bs) == true;
    ens !is_utf8_tail(head(bs)) &*&
        utf8_seq_len(head(bs)) <= length(bs) &*&
        is_valid_utf8(take(utf8_seq_len(head(bs)), bs)) == true &*&
        is_valid_utf8(drop(utf8_seq_len(head(bs)), bs)) == true;
{
    match bs {
        nil => {}
        cons(b0, rest0) => {
            if b0 >= 0x80 {
                switch_utf8_rest(rest0, b0);
            }
        }
    }
}

lem is_char_boundary_cons(b: u8, bs: list<u8>, idx: i32)
    req 1 <= idx &*& idx <= 1 + length(bs) &*& is_char_boundary(cons(b, bs), idx) == true;
    ens is_char_boundary(bs, idx - 1) == true;
{
    if idx == 1 {
    } else if idx == 1 + length(bs) {
    } else {
        assert nth(idx, cons(b, bs)) == nth(idx - 1, bs);
    }
}

lem is_char_boundary_drop(bs: list<u8>, start: i32, end: i32)
    req 0 <= start &*& start <= end &*& end <= length(bs) &*& is_char_boundary(bs, end) == true;
    ens is_char_boundary(drop(start, bs), end - start) == true;
{
    match bs {
        nil => {}
        cons(b0, rest0) => {
            if start > 0 {
                is_char_boundary_cons(b0, rest0, end);
                is_char_boundary_drop(rest0, start - 1, end - 1);
            }
        }
    }
}

lem split_utf8_at_boundary(bs: list<u8>, idx: i32)
    req is_valid_utf8(bs) == true &*& 0 <= idx &*& idx <= length(bs) &*& is_char_boundary(bs, idx) == true;
    ens is_valid_utf8(take(idx, bs)) == true &*& is_valid_utf8(drop(idx, bs)) == true;
{
    match bs {
        nil => {}
        cons(b0, rest0) => {
            if idx == 0 {
            } else if idx == length(bs) {
                take_length(bs);
                drop_length(bs);
            } else {
                is_char_boundary_cons(b0, rest0, idx);
                if b0 <= 0x7F {
                    split_utf8_at_boundary(rest0, idx - 1);
                } else {
                    match rest0 {
                        nil => {}
                        cons(b1, rest1) => {
                            is_char_boundary_cons(b1, rest1, idx - 1);
                            if b0 <= 0xDF {
                                split_utf8_at_boundary(rest1, idx - 2);
                            } else {
                                match rest1 {
                                    nil => {}
                                    cons(b2, rest2) => {
                                        is_char_boundary_cons(b2, rest2, idx - 2);
                                        if b0 <= 0xEF {
                                            split_utf8_at_boundary(rest2, idx - 3);
                                        } else {
                                            match rest2 {
                                                nil => {}
                                                cons(b3, rest3) => {
                                                    is_char_boundary_cons(b3, rest3, idx - 3);
                                                    split_utf8_at_boundary(rest3, idx - 4);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

lem drop_twice<T>(first: i32, second: i32, xs: list<T>)
    req 0 <= first &*& 0 <= second &*& first + second <= length(xs);
    ens drop(second, drop(first, xs)) == drop(first + second, xs);
{
    match xs {
        nil => {}
        cons(x, tail) => {
            if first > 0 {
                drop_twice(first - 1, second, tail);
            }
        }
    }
}

lem take_twice<T>(first: i32, second: i32, xs: list<T>)
    req 0 <= first &*& first <= second &*& second <= length(xs);
    ens take(first, take(second, xs)) == take(first, xs);
{
    match xs {
        nil => {}
        cons(x, tail) => {
            if first > 0 {
                take_twice(first - 1, second - 1, tail);
            }
        }
    }
}

lem first_is_head<T>(xs: list<T>)
    req xs != nil;
    ens nth(0, xs) == head(xs);
{
    match xs {
        nil => {}
        cons(x, rest) => {}
    }
}

lem drop_take_commute<T>(k: i32, n: i32, xs: list<T>)
    req 0 <= k &*& k <= n &*& n <= length(xs);
    ens drop(k, take(n, xs)) == take(n - k, drop(k, xs));
{
    match xs {
        nil => {}
        cons(x, tail) => {
            if k > 0 {
                drop_take_commute(k - 1, n - 1, tail);
            }
        }
    }
}

lem drop_mapped<T, U>(n: i32, xs: list<T>, apply: fix(T, U))
    req 0 <= n &*& n <= length(xs);
    ens drop(n, map(apply, xs)) == map(apply, drop(n, xs));
{
    match xs {
        nil => {}
        cons(x, rest) => {
            if n > 0 {
                drop_mapped(n - 1, rest, apply);
            }
        }
    }
}

lem split_appended<T>(prefix: list<T>, suffix: list<T>)
    req true;
    ens take(length(prefix), append(prefix, suffix)) == prefix &*&
        drop(length(prefix), append(prefix, suffix)) == suffix;
{
    match prefix {
        nil => {}
        cons(byte, rest) => {
            split_appended(rest, suffix);
        }
    }
}

fix ordered_rejections(bytes: list<u8>, cursor: usize, ranges: list<(usize, usize)>) -> bool {
    match ranges {
        nil => cursor <= length(bytes),
        cons(range, rest) => cursor <= range.0 && range.0 <= range.1 && range.1 <= length(bytes) &&
            is_char_boundary(bytes, range.0) && is_char_boundary(bytes, range.1) &&
            ordered_rejections(bytes, range.1, rest)
    }
}

// A collected prefix ends at or before the back of the last match, which
// is the start of the next rejection (or of the final suffix).
fix ordered_rejection_prefix(bytes: list<u8>, cursor: usize, front: usize,
    ranges: list<(usize, usize)>) -> bool {
    match ranges {
        nil => cursor <= front,
        cons(range, rest) => cursor <= range.0 && range.0 <= range.1 && range.1 <= length(bytes) &&
            is_char_boundary(bytes, range.0) && is_char_boundary(bytes, range.1) &&
            ordered_rejection_prefix(bytes, range.1, front, rest)
    }
}

lem record_rejection(bytes: list<u8>, cursor: usize, front: usize, matched_end: usize,
    ranges: list<(usize, usize)>, rejected: (usize, usize))
    req ordered_rejection_prefix(bytes, cursor, front, ranges) == true &*&
        rejected.0 == front &*& is_char_boundary(bytes, front) == true &*&
        front <= rejected.1 &*& rejected.1 <= matched_end &*& matched_end <= length(bytes) &*&
        is_char_boundary(bytes, rejected.1) == true;
    ens ordered_rejection_prefix(bytes, cursor, matched_end, append(ranges, [rejected])) == true;
{
    match ranges {
        nil => {}
        cons(range, rest) => {
            record_rejection(bytes, range.1, front, matched_end, rest, rejected);
        }
    }
}

lem record_rejection_suffix(bytes: list<u8>, cursor: usize, front: usize,
    ranges: list<(usize, usize)>, suffix: (usize, usize))
    req ordered_rejection_prefix(bytes, cursor, front, ranges) == true &*&
        suffix.0 == front &*& suffix.1 == length(bytes) &*&
        front <= length(bytes) &*& is_char_boundary(bytes, front) == true;
    ens ordered_rejections(bytes, cursor, append(ranges, [suffix])) == true;
{
    match ranges {
        nil => {
            assert is_char_boundary(bytes, length(bytes)) == true;
        }
        cons(range, rest) => {
            record_rejection_suffix(bytes, range.1, front, rest, suffix);
        }
    }
}

inductive RemoveMatchesContext = RemoveMatchesContext(lifetime_t, *str, list<u8>, i32);
inductive ByteCopyRange = ByteCopyRange(base: *u8, start: usize, target: usize);

lem usize_pair_own_of_fields(t: thread_id_t, value: (usize, usize))
    req usize_own(t, value.0) &*& usize_own(t, value.1);
    ens <(usize, usize)>.own(t, value);
{
    close <(usize, usize)>.own(t, value);
}

lem record_next_rejection(bytes: list<u8>, cursor: *str, cell: i32, front: usize,
    ranges: list<(usize, usize)>, rejected: (usize, usize), next_front: usize)
    req ordered_rejection_prefix(bytes, 0, front, ranges) == true &*& rejected.0 == front &*&
        std::str::pattern::front_agrees(std::str::pattern::PositionedSearcher(cursor, bytes, cell, front), front) == true &*&
        std::str::pattern::next_match_range(std::str::pattern::PositionedSearcher(cursor, bytes, cell, front),
            rejected.1, next_front) == true;
    ens ordered_rejection_prefix(bytes, 0, next_front, append(ranges, [rejected])) == true;
{
    record_rejection(bytes, 0, front, next_front, ranges, rejected);
}

lem rejection_range_utf8(bytes: list<u8>, start: usize, end: usize)
    req is_valid_utf8(bytes) == true &*& start <= end &*& end <= length(bytes) &*&
        is_char_boundary(bytes, start) == true &*& is_char_boundary(bytes, end) == true;
    ens is_valid_utf8(take(end - start, drop(start, bytes))) == true;
{
    split_utf8_at_boundary(bytes, start);
    is_char_boundary_drop(bytes, start, end);
    split_utf8_at_boundary(drop(start, bytes), end - start);
}

lem is_char_boundary_from_valid_suffix(bs: list<u8>, idx: i32)
    req 0 <= idx &*& idx <= length(bs) &*& is_valid_utf8(drop(idx, bs)) == true;
    ens is_char_boundary(bs, idx) == true;
{
    if idx < length(bs) {
        let suf = drop(idx, bs);
        length_drop(idx, bs);
        utf8_first_scalar(suf);
        first_is_head(suf);
        drop_n_plus_one(idx, bs);
    }
}

lem take_append_exact<T>(n: i32, xs: list<T>, ys: list<T>)
    req n == length(xs);
    ens take(n, append(xs, ys)) == xs;
{
    match xs {
        nil => {}
        cons(x, tail) => { take_append_exact(n - 1, tail, ys); }
    }
}

lem drop_append_ge<T>(n: i32, xs: list<T>, ys: list<T>)
    req length(xs) <= n &*& n <= length(xs) + length(ys);
    ens drop(n, append(xs, ys)) == drop(n - length(xs), ys);
{
    match xs {
        nil => {}
        cons(x, tail) => { drop_append_ge(n - 1, tail, ys); }
    }
}

lem take_split_join<T>(a: i32, b: i32, xs: list<T>)
    req 0 <= a &*& a <= b &*& b <= length(xs);
    ens take(b, xs) == append(take(a, xs), take(b - a, drop(a, xs)));
{
    match xs {
        nil => {}
        cons(x, tail) => {
            if a > 0 {
                take_split_join(a - 1, b - 1, tail);
            }
        }
    }
}

pred <String>.own(t, s) =
    std::vec::Vec(s.vec, ?cap, ?bs) &*& is_valid_utf8(bs) == true;

pred<'a> <String::retain::SetLenOnDrop<'a>>.own(t, guard) =
    (*guard.s).vec |-> ?v &*& std::vec::Vec(v, ?cap, ?bytes) &*&
    guard.del_bytes <= guard.idx &*& guard.idx <= length(bytes) &*&
    is_valid_utf8(take(guard.idx - guard.del_bytes, bytes)) == true;

lem String::retain::SetLenOnDrop_own_mono<'a0, 'a1>()
    req <String::retain::SetLenOnDrop<'a0>>.own(?t, ?g) &*& lifetime_inclusion('a1, 'a0) == true;
    ens <String::retain::SetLenOnDrop<'a1>>.own(t, String::retain::SetLenOnDrop::<'a1> {
        s: g.s, idx: upcast(g.idx), del_bytes: upcast(g.del_bytes)
    });
{
    open <String::retain::SetLenOnDrop<'a0>>.own(t, g);
    std::str::usize_upcast(g.idx);
    std::str::usize_upcast(g.del_bytes);
    close <String::retain::SetLenOnDrop<'a1>>.own(t, String::retain::SetLenOnDrop::<'a1> {
        s: g.s, idx: upcast(g.idx), del_bytes: upcast(g.del_bytes)
    });
}

lem String_drop()
    req String_own(?_t, ?_v);
    ens <std::vec::Vec<u8, std::alloc::Global>>.own(_t, _v.vec);
{
    open <String>.own(_t, _v);
    std::vec::Vec_u8_to_own(_t, _v.vec);
}

lem String_send(t1: thread_id_t)
    req String_own(?t0, ?v);
    ens String_own(t1, v);
{
    open <String>.own(t0, v);
    close <String>.own(t1, v);
}

pred_ctor String_header_fbc(l: *String, v: std::vec::Vec<u8, std::alloc::Global>, cap: usize, len: usize, buf: *u8)(;) =
    (*l).vec |-> v &*&
    std::vec::Vec_minus_elems(v, cap, len, buf);

lem close_String_mut_str_borrow(k: lifetime_t, klong: lifetime_t, t: thread_id_t, l: *String, r: *str)
    nonghost_callers_only
    req close_full_borrow_token_strong(klong, String_full_borrow_content(t, l), ?q, k) &*&
        lifetime_inclusion(k, klong) == true &*& (*l).vec |-> ?v &*&
        std::vec::Vec_minus_elems(v, ?cap, r.len(), r as *u8) &*&
        (r as *u8)[..r.len()] |-> ?bs &*& is_valid_utf8(bs) == true;
    ens [q]lifetime_token(k) &*& full_borrow(k, str_full_borrow_content(t, r));
{
    let header = String_header_fbc(l, v, cap, r.len(), r as *u8);
    let bytes = str_full_borrow_content(t, r);
    close String_header_fbc(l, v, cap, r.len(), r as *u8)();
    close str_full_borrow_content(t, r)();
    close sep(header, bytes)();
    produce_lem_ptr_chunk full_borrow_convert_strong(True, sep(header, bytes), klong, String_full_borrow_content(t, l))() {
        open sep(header, bytes)();
        open String_header_fbc(l, v, cap, r.len(), r as *u8)();
        open str_full_borrow_content(t, r)();
        std::vec::Vec_unseparate_elems(v);
        close <String>.own(t, String { vec: v });
        close String_full_borrow_content(t, l)();
    } {
        close_full_borrow_strong(klong, String_full_borrow_content(t, l), sep(header, bytes));
    }
    full_borrow_mono(klong, k, sep(header, bytes));
    full_borrow_split(k, header, bytes);
    leak full_borrow(k, header);
}

inductive String_share_info = String_share_info(v: std::vec::Vec<u8, std::alloc::Global>, cap: usize, buf: *u8, bs: list<u8>);

pred <String>.share(k, t, l) =
    exists(String_share_info(?v, ?cap, ?buf, ?bs)) &*&
    [_]frac_borrow(k, String_header_fbc(l, v, cap, length(bs), buf)) &*&
    [_]frac_borrow(k, mk_array::<u8>(buf, length(bs), bs)) &*&
    is_valid_utf8(bs) == true;

lem String_share_full(k: lifetime_t, t: thread_id_t, l: *String)
    req atomic_mask(MaskTop) &*& full_borrow(k, String_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(MaskTop) &*& [_]String_share(k, t, l) &*& [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, String_full_borrow_content(t, l), q);
    open String_full_borrow_content(t, l)();
    assert (*l).vec |-> ?v;
    open <String>.own(t, String { vec: v });
    assert std::vec::Vec(v, ?cap, ?bs);
    let buf = std::vec::Vec_separate_elems(v);
    close String_header_fbc(l, v, cap, length(bs), buf)();
    close mk_array::<u8>(buf, length(bs), bs)();
    close sep(String_header_fbc(l, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
    {
        pred Ctx() = is_valid_utf8(bs) == true;
        produce_lem_ptr_chunk full_borrow_convert_strong(Ctx, sep(String_header_fbc(l, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)), klong, String_full_borrow_content(t, l))() {
            open Ctx();
            open sep(String_header_fbc(l, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
            open String_header_fbc(l, v, cap, length(bs), buf)();
            open mk_array::<u8>(buf, length(bs), bs)();
            std::vec::Vec_unseparate_elems(v);
            close <String>.own(t, String { vec: v });
            close String_full_borrow_content(t, l)();
        } {
            close Ctx();
            close_full_borrow_strong_m(klong, String_full_borrow_content(t, l), sep(String_header_fbc(l, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)));
            full_borrow_mono(klong, k, sep(String_header_fbc(l, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)));
            full_borrow_split_m(k, String_header_fbc(l, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs));
            full_borrow_into_frac_m(k, String_header_fbc(l, v, cap, length(bs), buf));
            full_borrow_into_frac_m(k, mk_array::<u8>(buf, length(bs), bs));
        }
    }
    close exists(String_share_info(v, cap, buf, bs));
    close <String>.share(k, t, l);
    leak <String>.share(k, t, l);
}

lem String_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *String)
    req lifetime_inclusion(k1, k) == true &*& [_]String_share(k, t, l);
    ens [_]String_share(k1, t, l);
{
    open String_share(k, t, l);
    assert [_]exists(String_share_info(?v, ?cap, ?buf, ?bs));
    frac_borrow_mono(k, k1, String_header_fbc(l, v, cap, length(bs), buf));
    frac_borrow_mono(k, k1, mk_array::<u8>(buf, length(bs), bs));
    close exists(String_share_info(v, cap, buf, bs));
    close String_share(k1, t, l);
    leak String_share(k1, t, l);
}

lem init_ref_String_header(p: *String, v: std::vec::Vec<u8, std::alloc::Global>, cap: usize, len: usize, buf: *u8)
    req atomic_mask(?mask) &*& mask_le(Nlft, mask) == true &*& ref_init_perm(p, ?x) &*&
        [_]frac_borrow(?k, String_header_fbc(x, v, cap, len, buf)) &*& [?q]lifetime_token(k);
    ens atomic_mask(mask) &*& [q]lifetime_token(k) &*&
        [_]frac_borrow(k, String_header_fbc(p, v, cap, len, buf)) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    let klong = open_frac_borrow_strong_m(k, String_header_fbc(x, v, cap, len, buf), q);
    open [?f]String_header_fbc(x, v, cap, len, buf)();
    open_ref_init_perm_String(p);
    std::vec::init_ref_Vec(&(*p).vec);
    close [f/2]String_header_fbc(x, v, cap, len, buf)();
    close [f/2]String_header_fbc(p, v, cap, len, buf)();
    close_ref_initialized_String(p, 1);
    close ref_initialized_::<String>(p)();
    {
        pred Ctx() = ref_end_token(&(*p).vec, &(*x).vec, f/2) &*& [f/2]String_header_fbc(x, v, cap, len, buf)();
        let header = String_header_fbc(p, v, cap, len, buf);
        let fields = scaledp(f/2, header);
        let initialized = sep(fields, ref_initialized_(p));
        produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, initialized, klong, f, String_header_fbc(x, v, cap, len, buf))() {
            open Ctx();
            open sep(fields, ref_initialized_(p))();
            open scaledp(f/2, header)();
            open ref_initialized_::<String>(p)();
            open_ref_initialized_String(p);
            open [f/2]String_header_fbc(p, v, cap, len, buf)();
            open [f/2]String_header_fbc(x, v, cap, len, buf)();
            std::vec::end_ref_Vec(&(*p).vec);
            close [f]String_header_fbc(x, v, cap, len, buf)();
        } {
            close Ctx();
            close scaledp(f/2, header)();
            close sep(fields, ref_initialized_(p))();
            close_frac_borrow_strong_m();
            full_borrow_mono(klong, k, initialized);
            full_borrow_split_m(k, fields, ref_initialized_(p));
            full_borrow_into_frac_m(k, fields);
            frac_borrow_implies_scaled(k, f/2, header);
            full_borrow_into_frac_m(k, ref_initialized_(p));
        }
    }
}

lem init_ref_String(p: *String)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]String_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]String_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open String_share(k, t, x);
    assert [_]exists(String_share_info(?v, ?cap, ?buf, ?bs));
    init_ref_String_header(p, v, cap, length(bs), buf);
    close exists(String_share_info(v, cap, buf, bs));
    close String_share(k, t, p);
    leak String_share(k, t, p);
}

lem init_ref_String_header_for_call(p: *String, k: lifetime_t, v: std::vec::Vec<u8, std::alloc::Global>,
    cap: usize, len: usize, buf: *u8)
    nonghost_callers_only
    req ref_init_perm(p, ?x) &*& [_]frac_borrow(k, String_header_fbc(x, v, cap, len, buf)) &*& [?q]lifetime_token(k);
    ens [_]frac_borrow(k, String_header_fbc(p, v, cap, len, buf)) &*&
        [_]frac_borrow(k, ref_initialized_(p)) &*& [q]lifetime_token(k);
{
    {
        pred Pre() = ref_init_perm(p, x) &*& [_]frac_borrow(k, String_header_fbc(x, v, cap, len, buf)) &*& [q]lifetime_token(k);
        pred Post() = [_]frac_borrow(k, String_header_fbc(p, v, cap, len, buf)) &*&
            [_]frac_borrow(k, ref_initialized_(p)) &*& [q]lifetime_token(k);
        produce_lem_ptr_chunk atomic_block(Pre, Post)() {
            open Pre();
            init_ref_String_header(p, v, cap, len, buf);
            close Post();
        } {
            close Pre();
            perform_atomically();
            open Post();
        }
    }
}

lem String_sync(t1: thread_id_t)
    req [_]String_share(?k, ?t0, ?l);
    ens [_]String_share(k, t1, l);
{
    open String_share(k, t0, l);
    assert [_]exists(String_share_info(?v, ?cap, ?buf, ?bs));
    close exists(String_share_info(v, cap, buf, bs));
    close String_share(k, t1, l);
    leak String_share(k, t1, l);
}

lem init_ref_String_raw(p: *String)
    req ref_init_perm(p, ?x) &*& [?f](*x).vec |-> ?v;
    ens ref_end_token(&(*p).vec, &(*x).vec, f/2) &*& [f/2](*x).vec |-> v &*& [f/2](*p).vec |-> v &*& ref_initialized(p);
{
    open_ref_init_perm_String(p);
    std::vec::init_ref_Vec(&(*p).vec);
    close_ref_initialized_String(p, 1);
}

lem end_ref_String_raw(p: *String)
    req ref_end_token(&(*p).vec, ?xvec, ?f) &*& [f](*p).vec |-> ?v &*& ref_initialized(p);
    ens [f](*xvec |-> v);
{
    open_ref_initialized_String(p);
    std::vec::end_ref_Vec(&(*p).vec);
}

@*/

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

/*@
pred <FromUtf16Error>.own(t, e) = <FromUtf16ErrorKind>.own(t, e.kind);

lem FromUtf16Error_drop()
    req FromUtf16Error_own(?t, ?e);
    ens <FromUtf16ErrorKind>.own(t, e.kind);
{
    open <FromUtf16Error>.own(t, e);
}

lem FromUtf16Error_send(t1: thread_id_t)
    req FromUtf16Error_own(?t0, ?e);
    ens FromUtf16Error_own(t1, e);
{
    open <FromUtf16Error>.own(t0, e);
    open <FromUtf16ErrorKind>.own(t0, e.kind);
    close <FromUtf16ErrorKind>.own(t1, e.kind);
    close <FromUtf16Error>.own(t1, e);
}
@*/

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
    pub fn with_capacity(capacity: usize) -> String
    //@ req true;
    //@ ens std::vec::Vec(result.vec, ?cap, []) &*& capacity <= cap;
    //@ on_unwind_ens true;
    /*@
    safety_proof {
        let outcome = call();
        if ignore_unwind_paths() {
            close <String>.own(_t, outcome);
        } else {
            match outcome {
                returning(result) => { close <String>.own(_t, result); }
                unwinding => {}
            }
        }
    }
    @*/
    {
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
    pub fn from_utf16(v: &[u16]) -> Result<String, FromUtf16Error>
    //@ req thread_token(?t) &*& [_](<[u16]>.share(?k, t, v)) &*& [?q]lifetime_token(k);
    //@ ens thread_token(t) &*& [q]lifetime_token(k) &*& <std::result::Result<String, FromUtf16Error>>.own(t, result);
    //@ on_unwind_ens thread_token(t) &*& [q]lifetime_token(k);
    {
        let output = Self::from_utf16_units(v.iter().cloned(), v.len());
        //@ own_utf16_units_result(t, output);
        output
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
    ) -> Result<String, FromUtf16Error>
    //@ req thread_token(?t) &*& <VfImplTrait$0>.own(t, units);
    /*@
    ens thread_token(t) &*& match result {
        Result::Ok(s) => <String>.own(t, s),
        Result::Err(e) => e == FromUtf16Error { kind: FromUtf16ErrorKind::LoneSurrogate }
    };
    @*/
    //@ on_unwind_ens thread_token(t);
    /*@
    safety_proof {
        let result = call();
        if ignore_unwind_paths() {
            own_utf16_units_result(_t, result);
        } else {
            match result {
                returning(output) => { own_utf16_units_result(_t, output); }
                unwinding => {}
            }
        }
    }
    @*/
    {
        let mut ret = String::with_capacity(capacity);
        //@ close_points_to(&ret);
        //@ assert ret |-> ?initial;
        //@ close <String>.own(t, initial);
        for c in char::decode_utf16(units) {
            //@ inv thread_token(t) &*& iter |-> ?d &*& <std::char::DecodeUtf16<VfImplTrait$0>>.own(t, d) &*& ret |-> ?s &*& <String>.own(t, s);
            //@ open <std::result::Result<char, std::char::DecodeUtf16Error>>.own(t, c);
            let Ok(decoded) = c else {
                //@ assert <std::char::DecodeUtf16Error>.own(t, ?decode_error);
                //@ open <std::char::DecodeUtf16Error>.own(t, decode_error);
                return Err(FromUtf16Error { kind: FromUtf16ErrorKind::LoneSurrogate });
            };
            //@ assert ret |-> ?before;
            //@ open <String>.own(t, before);
            //@ open char_own(t, decoded);
            ret.push(decoded)/*@~unwind {
                close_points_to(&ret);
                assert ret |-> ?restored;
                close <String>.own(t, restored);
            } @*/;
            //@ assert ret |-> ?after;
            //@ close <String>.own(t, after);
        }
        //@ open_points_to(&ret);
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
    pub fn from_utf16_lossy(v: &[u16]) -> String
    //@ req thread_token(?t) &*& [_](<[u16]>.share(?k, t, v)) &*& [?q]lifetime_token(k);
    /*@
    ens thread_token(t) &*& [q]lifetime_token(k) &*&
        std::vec::Vec(result.vec, ?capacity, ?bytes) &*& is_valid_utf8(bytes) == true;
    @*/
    //@ on_unwind_ens thread_token(t) &*& [q]lifetime_token(k);
    /*@
    safety_proof {
        let result = call();
        if ignore_unwind_paths() {
            close <String>.own(_t, result);
        } else {
            match result {
                returning(output) => { close <String>.own(_t, output); }
                unwinding => {}
            }
        }
    }
    @*/
    {
        //@ let replace_invalid = VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3afrom_5futf16_5flossy_3a_3a_7bclosure_230_7d {};
        //@ close <VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3afrom_5futf16_5flossy_3a_3a_7bclosure_230_7d>.own(t, replace_invalid);
        let output = char::decode_utf16(v.iter().cloned())
            .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect();
        //@ open <String>.own(t, output);
        output
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
    pub fn from_utf16le(v: &[u8]) -> Result<String, FromUtf16Error>
    //@ req thread_token(?t) &*& [?q]lifetime_token(?k) &*& [_](<[u8]>.share(k, t, v));
    //@ ens thread_token(t) &*& [q]lifetime_token(k) &*& <std::result::Result<String, FromUtf16Error>>.own(t, result);
    //@ on_unwind_ens thread_token(t) &*& [q]lifetime_token(k);
    {
        let (chunks, []) = v.as_chunks::<2>() else {
            //@ let error = FromUtf16Error { kind: FromUtf16ErrorKind::OddBytes };
            //@ close <FromUtf16ErrorKind>.own(t, FromUtf16ErrorKind::OddBytes);
            //@ close <FromUtf16Error>.own(t, error);
            //@ close <std::result::Result<String, FromUtf16Error>>.own(t, std::result::Result::Err(error));
            return Err(FromUtf16Error { kind: FromUtf16ErrorKind::OddBytes });
        };
        // SAFETY: The aligned part of `v` can be transmuted into a valid u16 slice.
        match (cfg!(target_endian = "little"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16(v), //~allow_dead_code
            _ => {
                //@ close <VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fle_5fbytes>.own(t, VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fle_5fbytes {});
                let output = Self::from_utf16_units(chunks.iter().copied().map(u16::from_le_bytes), chunks.len());
                //@ own_utf16_units_result(t, output);
                output
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
    pub fn from_utf16le_lossy(v: &[u8]) -> String
    //@ req thread_token(?t) &*& [_](<[u8]>.share(?k, t, v)) &*& [?q]lifetime_token(k);
    /*@
    ens thread_token(t) &*& [q]lifetime_token(k) &*&
        std::vec::Vec(result.vec, ?capacity, ?bytes) &*& is_valid_utf8(bytes) == true;
    @*/
    //@ on_unwind_ens thread_token(t) &*& [q]lifetime_token(k);
    /*@
    safety_proof {
        let result = call();
        if ignore_unwind_paths() {
            close <String>.own(_t, result);
        } else {
            match result {
                returning(output) => { close <String>.own(_t, output); }
                unwinding => {}
            }
        }
    }
    @*/
    {
        // SAFETY: The aligned part of `v` can be transmuted into a valid u16 slice.
        match (cfg!(target_endian = "little"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v), //~allow_dead_code
            (true, ([], v, [_remainder])) => Self::from_utf16_lossy(v) + "\u{FFFD}", //~allow_dead_code
            _ => {
                let (chunks, remainder) = v.as_chunks::<2>();
                //@ close <VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fle_5fbytes>.own(t, VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fle_5fbytes {});
                //@ close <VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3afrom_5futf16le_5flossy_3a_3a_7bclosure_230_7d>.own(t, VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3afrom_5futf16le_5flossy_3a_3a_7bclosure_230_7d {});
                let string = char::decode_utf16(chunks.iter().copied().map(u16::from_le_bytes))
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect();
                //@ open <String>.own(t, string);
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
    pub fn from_utf16be(v: &[u8]) -> Result<String, FromUtf16Error>
    //@ req thread_token(?t) &*& [?q]lifetime_token(?k) &*& [_](<[u8]>.share(k, t, v));
    //@ ens thread_token(t) &*& [q]lifetime_token(k) &*& <std::result::Result<String, FromUtf16Error>>.own(t, result);
    //@ on_unwind_ens thread_token(t) &*& [q]lifetime_token(k);
    {
        let (chunks, []) = v.as_chunks::<2>() else {
            //@ let error = FromUtf16Error { kind: FromUtf16ErrorKind::OddBytes };
            //@ close <FromUtf16ErrorKind>.own(t, FromUtf16ErrorKind::OddBytes);
            //@ close <FromUtf16Error>.own(t, error);
            //@ close <std::result::Result<String, FromUtf16Error>>.own(t, std::result::Result::Err(error));
            return Err(FromUtf16Error { kind: FromUtf16ErrorKind::OddBytes });
        };
        // SAFETY: The aligned part of `v` can be transmuted into a valid u16 slice.
        match (cfg!(target_endian = "big"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16(v), //~allow_dead_code
            _ => {
                //@ close <VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fbe_5fbytes>.own(t, VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fbe_5fbytes {});
                let output = Self::from_utf16_units(chunks.iter().copied().map(u16::from_be_bytes), chunks.len());
                //@ own_utf16_units_result(t, output);
                output
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
    pub fn from_utf16be_lossy(v: &[u8]) -> String
    //@ req thread_token(?t) &*& [_](<[u8]>.share(?k, t, v)) &*& [?q]lifetime_token(k);
    /*@
    ens thread_token(t) &*& [q]lifetime_token(k) &*&
        std::vec::Vec(result.vec, ?capacity, ?bytes) &*& is_valid_utf8(bytes) == true;
    @*/
    //@ on_unwind_ens thread_token(t) &*& [q]lifetime_token(k);
    /*@
    safety_proof {
        let result = call();
        if ignore_unwind_paths() {
            close <String>.own(_t, result);
        } else {
            match result {
                returning(output) => { close <String>.own(_t, output); }
                unwinding => {}
            }
        }
    }
    @*/
    {
        // SAFETY: The aligned part of `v` can be transmuted into a valid u16 slice.
        match (cfg!(target_endian = "big"), unsafe { v.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v), //~allow_dead_code
            (true, ([], v, [_remainder])) => Self::from_utf16_lossy(v) + "\u{FFFD}", //~allow_dead_code
            _ => {
                let (chunks, remainder) = v.as_chunks::<2>();
                //@ close <VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fbe_5fbytes>.own(t, VfFunctionItem$core_3a_3anum_3a_3a_3cimpl_20u16_3e_3a_3afrom_5fbe_5fbytes {});
                //@ close <VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3afrom_5futf16be_5flossy_3a_3a_7bclosure_230_7d>.own(t, VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3afrom_5futf16be_5flossy_3a_3a_7bclosure_230_7d {});
                let string = char::decode_utf16(chunks.iter().copied().map(u16::from_be_bytes))
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect();
                //@ open <String>.own(t, string);
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
    /// If `capacity == 0`, then `pointer` may be dangling. Otherwise,
    /// it will always be valid for reads and writes over `capacity`
    /// bytes, and point to the start of the string.
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
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> String
    //@ req std::vec::Vec(bytes, ?cap, ?bs) &*& is_valid_utf8(bs) == true;
    //@ ens std::vec::Vec(result.vec, cap, bs) &*& is_valid_utf8(bs) == true;
    //@ on_unwind_ens false;
    {
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
    pub const fn as_str(&self) -> &str
    /*@
    req [?f](*self).vec |-> ?v &*& [?fv]std::vec::Vec_minus_elems(v, ?cap, ?len, ?buf) &*&
        [?fb]buf[..len] |-> ?bytes;
    @*/
    /*@
    ens [f](*self).vec |-> v &*& [fv]std::vec::Vec_minus_elems(v, cap, len, buf) &*&
        [fb]buf[..len] |-> bytes &*& result as *u8 == buf &*& result.len() == len;
    @*/
    //@ on_unwind_ens false;
    /*@
    safety_proof {
        assert [?q]lifetime_token(?k);
        open <String>.share(k, _t, self);
        assert [_]exists(String_share_info(?v, ?cap, ?buf, ?bs));
        frac_borrow_sep(k, String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs));
        open_frac_borrow(k, sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)), q);
        open [?f]sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
        open [f]String_header_fbc(self, v, cap, length(bs), buf)();
        open [f]mk_array::<u8>(buf, length(bs), bs)();
        let result = call();
        close [f]mk_array::<u8>(buf, length(bs), bs)();
        close [f]String_header_fbc(self, v, cap, length(bs), buf)();
        close [f]sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
        close_frac_borrow(f, sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)));
        close exists(bs);
        if ignore_unwind_paths() {
            close str_share(k, _t, result);
            leak str_share(k, _t, result);
        } else {
            let reference = fn_outcome_result(result);
            close str_share(k, _t, reference);
            leak str_share(k, _t, reference);
        }
    }
    @*/
    {
        // SAFETY: String contents are stipulated to be valid UTF-8, invalid contents are an error
        // at construction.
        //@ let vec_ref = precreate_ref(&(*self).vec);
        //@ std::vec::init_ref_Vec(vec_ref);
        let r = unsafe { str::from_utf8_unchecked/*@~byte_slice_view@*/(self.vec.as_slice()) };
        //@ std::vec::end_ref_Vec(vec_ref);
        r
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
    pub const fn as_mut_str(&mut self) -> &mut str
    /*@
    req (*self).vec |-> ?v &*& std::vec::Vec_minus_elems(v, ?cap, ?len, ?buf) &*& buf[..len] |-> ?bytes;
    @*/
    /*@
    ens (*self).vec |-> v &*& std::vec::Vec_minus_elems(v, cap, len, buf) &*&
        buf[..len] |-> bytes &*& result as *u8 == buf &*& result.len() == len;
    @*/
    //@ on_unwind_ens false;
    /*@
    safety_proof {
        assert [?q]lifetime_token(?k);
        let klong = open_full_borrow_strong(k, String_full_borrow_content(_t, self), q);
        open String_full_borrow_content(_t, self)();
        assert (*self).vec |-> ?v;
        open <String>.own(_t, String { vec: v });
        let buf = std::vec::Vec_separate_elems(v);
        let result = call();
        if ignore_unwind_paths() {
            close_String_mut_str_borrow(k, klong, _t, self, result);
        } else {
            close_String_mut_str_borrow(k, klong, _t, self, fn_outcome_result(result));
        }
    }
    @*/
    {
        // SAFETY: String contents are stipulated to be valid UTF-8, invalid contents are an error
        // at construction.
        unsafe { str::from_utf8_unchecked_mut/*@~byte_slice_view@*/(self.vec.as_mut_slice()) }
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
    pub fn push_str(&mut self, string: &str)
    /*@
    req *self |-> ?s0 &*& std::vec::Vec(s0.vec, _, ?bs) &*& is_valid_utf8(bs) == true &*&
        [?fs](string as *u8)[..string.len()] |-> ?sbs &*& is_valid_utf8(sbs) == true;
    @*/
    /*@
    ens *self |-> ?s1 &*& std::vec::Vec(s1.vec, _, append(bs, sbs)) &*& is_valid_utf8(append(bs, sbs)) == true &*&
        [fs](string as *u8)[..string.len()] |-> sbs;
    @*/
    /*@
    on_unwind_ens (*self).vec |-> ?v &*& std::vec::Vec(v, _, bs) &*&
        [fs](string as *u8)[..string.len()] |-> sbs;
    @*/
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        open str_share(?k, _t, string);
        assert [_]exists(?sbs);
        assert [?q]lifetime_token(k);
        open_frac_borrow(k, mk_array::<u8>(string as *u8, string.len(), sbs), q);
        open [?fs]mk_array::<u8>(string as *u8, string.len(), sbs)();
        let outcome = call();
        close [fs]mk_array::<u8>(string as *u8, string.len(), sbs)();
        close_frac_borrow(fs, mk_array::<u8>(string as *u8, string.len(), sbs));
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => { close_points_to(self); }
            }
        }
        assert *self |-> ?s1;
        close <String>.own(_t, s1);
    }
    @*/
    {
        //@ open_points_to(self);
        let r = self.vec.extend_from_slice(string.as_bytes());
        //@ close_points_to(self);
        //@ append_utf8(bs, sbs);
        r
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
        // SAFETY: `self` have reserved enough space for strs in `slice`, and we are copying from valid UTF-8 slices.
        // Therefore all unsafe operations are safe.
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
    pub fn reserve(&mut self, additional: usize)
    //@ req *self |-> ?s0 &*& std::vec::Vec(s0.vec, _, ?bs);
    //@ ens *self |-> ?s1 &*& std::vec::Vec(s1.vec, ?cap, bs) &*& length(bs) + additional <= cap;
    //@ on_unwind_ens (*self).vec |-> ?v &*& std::vec::Vec(v, _, bs);
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => { close_points_to(self); }
            }
        }
        assert *self |-> ?s1;
        close <String>.own(_t, s1);
    }
    @*/
    {
        //@ open_points_to(self);
        let r = self.vec.reserve(additional);
        //@ close_points_to(self);
        r
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
    pub fn push(&mut self, ch: char)
    /*@
    req *self |-> ?s0 &*& std::vec::Vec(s0.vec, _, ?bs) &*& is_valid_utf8(bs) == true &*&
        is_unicode_scalar_value(ch) == true;
    @*/
    /*@
    ens *self |-> ?s1 &*& std::vec::Vec(s1.vec, _, append(bs, char_utf8(ch))) &*&
        is_valid_utf8(append(bs, char_utf8(ch))) == true;
    @*/
    //@ on_unwind_ens (*self).vec |-> ?v &*& std::vec::Vec(v, _, bs);
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        open char_own(_t, ch);
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => { close_points_to(self); }
            }
        }
        assert *self |-> ?s1;
        close <String>.own(_t, s1);
    }
    @*/
    {
        //@ let self_ref = precreate_ref(self);
        //@ open_points_to(self);
        //@ init_ref_String_raw(self_ref);
        let len = self.len();
        //@ end_ref_String_raw(self_ref);
        //@ close_points_to(self);
        let ch_len = ch.len_utf8();
        self.reserve(ch_len);

        //@ open_points_to(self);
        //@ let buf = std::vec::Vec_separate_buffer((*self).vec);
        //@ array__split(buf + len, ch_len);
        // SAFETY: Just reserved capacity for at least the length needed to encode `ch`.
        unsafe {
            core::char::encode_utf8_raw_unchecked(ch as u32, self.vec.as_mut_ptr().add(len));
            self.vec.set_len(len + ch_len);
        }
        //@ array_join(buf);
        //@ std::vec::Vec_unseparate_buffer((*self).vec);
        //@ close_points_to(self);
        //@ append_utf8(bs, char_utf8(ch));
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
    /// If `new_len` is greater than or equal to the string's current length,
    /// this has no effect.
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
        if new_len >= self.len() {
            return;
        }
        assert!(self.is_char_boundary(new_len));
        self.vec.truncate(new_len)
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
    pub fn pop(&mut self) -> Option<char>
    //@ req thread_token(?t) &*& *self |-> ?s0 &*& <String>.own(t, s0);
    //@ ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1) &*& <std::option::Option<char>>.own(t, result);
    //@ on_unwind_ens false;
    {
        //@ open <String>.own(t, s0);
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v0 &*& std::vec::Vec(v0, ?cap, ?bs);
        //@ let buf = std::vec::Vec_separate_elems(v0);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_String_raw(self_ref);
        let ch_opt = self.chars().rev().next();
        //@ end_ref_String_raw(self_ref);
        //@ std::vec::Vec_unseparate_elems(v0);
        /*@
        if ch_opt == std::option::Option::None {
            close_points_to(self);
            close <String>.own(t, s0);
            close <std::option::Option<char>>.own(t, std::option::Option::None);
        }
        @*/
        let ch = ch_opt?;
        //@ let self_ref2 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref2);
        let newlen = self.len() - ch.len_utf8();
        //@ end_ref_String_raw(self_ref2);
        //@ let buf2 = std::vec::Vec_separate_buffer(v0);
        //@ array_split(buf2, newlen);
        //@ array_to_array_(buf2 + newlen);
        //@ array__join(buf2 + newlen);
        // SAFETY: `newlen` is less than old length.
        unsafe {
            self.vec.set_len(newlen);
        }
        //@ std::vec::Vec_unseparate_buffer((*self).vec);
        //@ close_points_to(self);
        //@ assert *self |-> ?s1;
        //@ close <String>.own(t, s1);
        //@ close char_own(t, ch);
        //@ close <std::option::Option<char>>.own(t, std::option::Option::Some(ch));
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
    pub fn remove(&mut self, idx: usize) -> char
    /*@
    req thread_token(?t) &*& *self |-> ?s0 &*&
        std::vec::Vec(s0.vec, ?capacity, ?bytes) &*& is_valid_utf8(bytes) == true;
    @*/
    //@ ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1) &*& char_own(t, result);
    /*@
    on_unwind_ens thread_token(t) &*&
        if is_char_boundary(bytes, idx) {
            *self |-> s0 &*& <String>.own(t, s0)
        } else {
            exists::<*String>(?r) &*& ref_end_token(&(*r).vec, &(*self).vec, 1/2) &*& ref_initialized(r) &*&
            [1/2](*r).vec |-> s0.vec &*& [1/2](*self).vec |-> s0.vec &*&
            std::vec::Vec_minus_elems(s0.vec, capacity, length(bytes), ?buf) &*& buf[..length(bytes)] |-> bytes
        };
    @*/
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        assert std::vec::Vec(s0.vec, _, ?bytes);
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    if !is_char_boundary(bytes, idx) {
                        open exists(?r);
                        end_ref_String_raw(r);
                        std::vec::Vec_unseparate_elems(s0.vec);
                        close_points_to(self);
                        close <String>.own(_t, s0);
                    }
                }
            }
        }
    }
    @*/
    {
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v &*& std::vec::Vec(v, capacity, bytes);
        //@ let buf = std::vec::Vec_separate_elems(v);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_String_raw(self_ref);
        //@ close exists(self_ref);
        let suffix = &self[idx..];
        //@ open exists(self_ref);
        //@ end_ref_String_raw(self_ref);
        //@ split_utf8_at_boundary(bytes, idx);
        let ch = match suffix.chars().next() {
            Some(ch) => ch,
            None => {
                //@ array_join(buf);
                //@ std::vec::Vec_unseparate_elems(v);
                //@ close_points_to(self);
                //@ close <String>.own(t, s0);
                panic!("cannot remove a char from the end of a string")
            }
        };

        //@ length_drop(idx, bytes);
        //@ utf8_first_scalar(drop(idx, bytes));
        //@ array_join(buf);
        //@ std::vec::Vec_unseparate_elems(v);
        //@ let len_ref = precreate_ref(self);
        //@ init_ref_String_raw(len_ref);
        let next = idx + ch.len_utf8();
        let len = self.len();
        //@ end_ref_String_raw(len_ref);
        //@ drop_twice(idx, char_len_utf8(ch), bytes);
        //@ let ptr = std::vec::Vec_separate_buffer(v);
        // SAFETY:
        // * Since `next` is not bigger than `len`, `self.vec.as_ptr().add(next)`
        //   is valid for reads and `self.vec.as_mut_ptr().add(idx)` is valid for writes.
        //   Both pointers are valid for `len - next` bytes.
        // * new length is less than old length.
        unsafe {
            //@ let vec_ref = precreate_ref(&(*self).vec);
            //@ std::vec::init_ref_Vec(vec_ref);
            let src = self.vec.as_ptr().add(next);
            //@ std::vec::end_ref_Vec(vec_ref);
            //@ std::vec::Vec_minus_buffer_merge(v);
            //@ close exists(ByteCopyRange(ptr, next, idx));
            copy_bytes_left__VeriFast_wrapper(src, self.vec.as_mut_ptr().add(idx), len - next);
            /*@ {
                open exists::<list<u8>>(?middle);
                let prefix = take(idx, bytes);
                let tail = drop(next, bytes);
                let output = append(prefix, tail);
                length_take(idx, bytes);
                length_drop(next, bytes);
                append_assoc(prefix, tail, middle);
                split_appended(output, middle);
                append_utf8(prefix, tail);
            } @*/
            //@ let output_len = len - (next - idx);
            //@ array_split(ptr, output_len);
            //@ array_to_array_(ptr + output_len);
            //@ array__join(ptr + output_len);
            self.vec.set_len(len - (next - idx));
        }
        //@ std::vec::Vec_unseparate_buffer((*self).vec);
        //@ close_points_to(self);
        //@ assert *self |-> ?s1;
        //@ close <String>.own(t, s1);
        //@ close char_own(t, ch);
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
    pub fn remove_matches<P: Pattern>(&mut self, pat: P)
    //@ req thread_token(?t) &*& *self |-> ?s0 &*& <String>.own(t, s0) &*& <P>.own(t, pat);
    //@ ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1);
    /*@
    on_unwind_ens thread_token(t) &*&
        exists(RemoveMatchesHaystack(?h, ?cap, ?buf, ?bytes, ?pending)) &*&
        borrow_end_token(h, String_header_fbc(self, s0.vec, cap, length(bytes), buf)) &*&
        borrow_end_token(h, mk_array::<u8>(buf, length(bytes), bytes)) &*& is_valid_utf8(bytes) == true &*&
        match pending {
            none => lifetime_token(h),
            some(r) => [?q]lifetime_token(h) &*&
                [?f]ref_initialized(r) &*& close_frac_borrow_token(?opened, ref_initialized_(r), ?restore, h) &*&
                opened == f &*& q + restore == 1 &*&
                str_share(h, t, ?haystack)
        };
    @*/
    /*@
    safety_proof {
        assert *self |-> ?s0;
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    open exists(RemoveMatchesHaystack(?h, ?cap, ?buf, ?bytes, ?pending));
                    match pending {
                        none => {}
                        some(r) => {
                            assert [?f]ref_initialized(r);
                            close [f]ref_initialized_::<String>(r)();
                            close_frac_borrow(f, ref_initialized_(r));
                            merge_fractions lifetime_token(h);
                            leak str_share(h, _t, _);
                        }
                    }
                    end_lifetime(h);
                    borrow_end(h, String_header_fbc(self, s0.vec, cap, length(bytes), buf));
                    borrow_end(h, mk_array::<u8>(buf, length(bytes), bytes));
                    open String_header_fbc(self, s0.vec, cap, length(bytes), buf)();
                    open mk_array::<u8>(buf, length(bytes), bytes)();
                    std::vec::Vec_unseparate_elems(s0.vec);
                    close_points_to(self);
                    close <String>.own(_t, s0);
                }
            }
        }
    }
    @*/
    {
        use core::str::pattern::Searcher;

        //@ let h = begin_lifetime();
        //@ open_points_to(self);
        //@ open <String>.own(t, s0);
        //@ assert std::vec::Vec(s0.vec, ?original_cap, ?original_bytes);
        //@ let original_buf = std::vec::Vec_separate_elems(s0.vec);
        //@ close String_header_fbc(self, s0.vec, original_cap, length(original_bytes), original_buf)();
        //@ close mk_array::<u8>(original_buf, length(original_bytes), original_bytes)();
        //@ let original_header = String_header_fbc(self, s0.vec, original_cap, length(original_bytes), original_buf);
        //@ let original_storage = mk_array::<u8>(original_buf, length(original_bytes), original_bytes);
        //@ borrow(h, original_header);
        //@ full_borrow_into_frac(h, original_header);
        //@ borrow(h, original_storage);
        //@ full_borrow_into_frac(h, original_storage);
        let local_rejections;
        {
        //@ let_lft 'haystack = h;
        //@ lft_of_typeid_of_lft(h);
        {
            //@ let self_ref = precreate_ref(self);
            //@ let shared_vec = s0.vec;
            //@ let shared_cap = original_cap;
            //@ let shared_buf = original_buf;
            //@ let shared_bytes = original_bytes;
            //@ init_ref_String_header_for_call(self_ref, h, shared_vec, shared_cap, length(shared_bytes), shared_buf);
            //@ close exists(String_share_info(shared_vec, shared_cap, shared_buf, shared_bytes));
            //@ assert [?available]lifetime_token(h);
            //@ open_frac_borrow(h, ref_initialized_(self_ref), available/2);
            //@ open [?f_ref]ref_initialized_::<String>(self_ref)();
            //@ assert lft_of(typeid_of_lft(h)) == h;
            //@ assert [available/2]lifetime_token(h);
            //@ close exists(RemoveMatchesHaystack(h, original_cap, original_buf, original_bytes, some(self_ref)));
            let mut searcher = unsafe { remove_matches_searcher__VeriFast_wrapper/*@::<P, 'haystack>@*/(pat, self) };
            //@ open exists(RemoveMatchesHaystack(h, original_cap, original_buf, original_bytes, some(self_ref)));
            //@ close [f_ref]ref_initialized_::<String>(self_ref)();
            //@ close_frac_borrow(f_ref, ref_initialized_(self_ref));
            //@ merge_fractions lifetime_token(h);
            //@ assert *&searcher |-> ?initial_searcher;
            //@ assert std::str::pattern::SearcherPosition::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(t, initial_searcher, ?haystack, shared_bytes, 0);
            //@ leak str_share('haystack, t, haystack);
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
            let rejections: Vec<_>;
            //@ let captures = begin_lifetime();
            //@ let cursor = create_ghost_cell::<usize>(0);
            {
            let next_rejection = || { //~verify_closure
                /*@~contract
                req thread_token(?_t) &*& *closure_env |-> ?environment &*&
                    exists(?loan) &*&
                    std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher>
                        (?searcher_lft, _t, environment.0, loan) &*& [?qs]lifetime_token(searcher_lft) &*&
                    *environment.1 |-> ?previous &*& usize_own(_t, previous) &*&
                    std::str::pattern::front_agrees(loan, previous) == true;
                @*/
                /*@~contract
                ens thread_token(_t) &*& [qs]lifetime_token(searcher_lft) &*& *closure_env |-> environment &*&
                    <std::option::Option<(usize, usize)>>.own(_t, result) &*&
                    match result {
                        Option::None => *environment.1 |-> previous &*& usize_own(_t, previous) &*&
                            std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher>
                                (searcher_lft, _t, environment.0, loan),
                        Option::Some(rejected) => *environment.1 |-> ?last &*& usize_own(_t, last) &*&
                            rejected.0 == previous &*&
                            std::str::pattern::next_match_range(loan, rejected.1, last) == true &*&
                            std::str::pattern::front_agrees(std::str::pattern::after_match(loan, last), last) == true &*&
                            std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher>
                                (searcher_lft, _t, environment.0, std::str::pattern::after_match(loan, last))
                    };
                @*/
                /*@~contract
                on_unwind_ens thread_token(_t) &*& [qs]lifetime_token(searcher_lft) &*&
                    *closure_env |-> environment &*& *environment.1 |-> previous &*& usize_own(_t, previous) &*&
                    std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher>
                        (searcher_lft, _t, environment.0, loan);
                @*/
                /*@~contract
                safety_proof {
                    assert *closure_env |-> ?environment;
                    open <VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3aremove_5fmatches_3a_3a_7bclosure_230_7d<P, '_VfCapture_1, '_VfCapture_2, <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher, usize>>.own(_t, environment);
                    let front_cell = environment.1;
                    let front_content = (<usize>.full_borrow_content)(_t, front_cell);
                    assert [?qf]lifetime_token('_VfCapture_2);
                    open_full_borrow(qf, '_VfCapture_2, front_content);
                    open_full_borrow_content(_t, front_cell);
                    // Use exactly the ordinary exclusive borrow supplied by
                    // closure ownership in the generic RustBelt obligation.
                    close std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher>
                        ('_VfCapture_1, _t, environment.0, std::str::pattern::OrdinarySearcher);
                    close exists(std::str::pattern::OrdinarySearcher);
                    call();
                    open std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher>
                        ('_VfCapture_1, _t, environment.0, std::str::pattern::OrdinarySearcher);
                    close_full_borrow_content(_t, front_cell);
                    close_full_borrow(front_content);
                    close <VfFunctionItem$closure_3a_3astring_3a_3aString_3a_3aremove_5fmatches_3a_3a_7bclosure_230_7d<P, '_VfCapture_1, '_VfCapture_2, <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher, usize>>.own(_t, environment);
                }
                @*/
                //@ close exists(loan);
                let next = searcher.next_match/*@::< <P as std::str::pattern::Pattern<'_VfCapture_0>>::Searcher,
                    '_VfCapture_0, '_VfCapture_1> @*/();
                //@ open <std::option::Option<(usize, usize)>>.own(_t, next);
                /*@
                match next {
                    Option::None => {
                        close <std::option::Option<(usize, usize)>>.own(_t, std::option::Option::None);
                    }
                    Option::Some(pair) => {
                        leak <(usize, usize)>.own(_t, pair);
                    }
                }
                @*/
                let (start, end) = next?;
                //@ assert next == std::option::Option::Some(?matched);
                //@ assert start == matched.0 &*& end == matched.1;
                //@ std::str::pattern::next_match_advances_front(loan, start, end);
                let prev_front = front;
                //@ assert prev_front == previous;
                front = end;
                //@ assert *environment.1 |-> matched.1;
                //@ open usize_own(_t, prev_front);
                //@ close usize_own(_t, end);
                let range = (prev_front, start);
                let rejection = Some(range);
                //@ assert rejection == std::option::Option::Some(?emitted);
                //@ assert emitted.0 == prev_front &*& emitted.1 == matched.0;
                //@ close usize_own(_t, prev_front);
                //@ close usize_own(_t, start);
                //@ usize_pair_own_of_fields(_t, range);
                //@ close <std::option::Option<(usize, usize)>>.own(_t, rejection);
                rejection
            };
            //@ let searcher_ref = next_rejection.0;
            //@ let front_ref = next_rejection.1;
            //@ assert *front_ref |-> 0;
            //@ close usize_own(t, 0);
            //@ close std::str::pattern::SearcherCursorContent::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(t, searcher_ref, haystack, shared_bytes, cursor)();
            //@ let position_content = std::str::pattern::SearcherCursorContent::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(t, searcher_ref, haystack, shared_bytes, cursor);
            //@ borrow(captures, position_content);
            //@ let loan = std::str::pattern::PositionedSearcher(haystack, shared_bytes, cursor, 0);
            //@ close std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(captures, t, searcher_ref, loan);
            //@ close exists(RemoveMatchesContext(captures, haystack, shared_bytes, cursor));
            //@ close exists(RemoveMatchesHaystack(h, original_cap, original_buf, original_bytes, none));
            rejections = from_fn(next_rejection).collect/*@~verify_vec_collect::<P, 'haystack, 'static, 'static, 'static>@*/()/*@~unwind {
                assert *front_ref |-> ?collected_front;
                open std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(
                    captures, t, searcher_ref, std::str::pattern::PositionedSearcher(haystack, shared_bytes, cursor, collected_front));
                leak full_borrow(captures, position_content);
                merge_fractions lifetime_token(captures);
                end_lifetime(captures);
                borrow_end(captures, position_content);
                open std::str::pattern::SearcherCursorContent::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(
                    t, searcher_ref, haystack, shared_bytes, cursor)();
                merge_fractions ghost_cell::<usize>(cursor, _);
                leak ghost_cell::<usize>(cursor, _);
                leak std::str::pattern::SearcherPosition::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(
                    t, _, haystack, shared_bytes, _);
                leak usize_own(t, collected_front);
            } @*/;
            //@ assert *front_ref |-> ?collected_front;
            //@ open std::str::pattern::SearcherBorrow::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(captures, t, searcher_ref, std::str::pattern::PositionedSearcher(haystack, shared_bytes, cursor, collected_front));
            //@ leak full_borrow(captures, position_content);
            //@ close exists::<*<P as std::str::pattern::Pattern<'haystack>>::Searcher>(searcher_ref);
            //@ close exists::<*usize>(front_ref);
            }
            //@ end_lifetime(captures);
            //@ open exists::<*<P as std::str::pattern::Pattern<'haystack>>::Searcher>(?released_searcher);
            //@ open exists::<*usize>(?released_front);
            //@ borrow_end(captures, std::str::pattern::SearcherCursorContent::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(t, released_searcher, haystack, shared_bytes, cursor));
            //@ open std::str::pattern::SearcherCursorContent::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(t, released_searcher, haystack, shared_bytes, cursor)();
            //@ merge_fractions ghost_cell::<usize>(cursor, _);
            //@ leak ghost_cell::<usize>(cursor, _);
            //@ assert released_searcher == &searcher;
            //@ assert released_front == &front;
            //@ leak std::str::pattern::SearcherPosition::< <P as std::str::pattern::Pattern<'haystack>>::Searcher>(t, _, haystack, shared_bytes, _);
            let iter = rejections.into_iter();
            //@ close exists(String_share_info(shared_vec, shared_cap, shared_buf, shared_bytes));
            //@ let tail_ref = precreate_ref(self);
            //@ init_ref_String_header_for_call(tail_ref, h, shared_vec, shared_cap, length(shared_bytes), shared_buf);
            //@ assert [?before_chain]lifetime_token(h);
            //@ open_frac_borrow(h, ref_initialized_(tail_ref), before_chain/2);
            //@ open [?chain_fraction]ref_initialized_::<String>(tail_ref)();
            local_rejections = unsafe { remove_matches_chain__VeriFast_wrapper/*@::<'haystack>@*/(iter, front, self) };
            //@ close [chain_fraction]ref_initialized_::<String>(tail_ref)();
            //@ close_frac_borrow(chain_fraction, ref_initialized_(tail_ref));
            //@ merge_fractions lifetime_token(h);
        }
        }
        //@ open exists(RemoveMatchesHaystack(h, original_cap, original_buf, original_bytes, none));
        //@ merge_fractions lifetime_token(h);
        //@ end_lifetime(h);
        //@ borrow_end(h, original_header);
        //@ borrow_end(h, original_storage);
        //@ open String_header_fbc(self, s0.vec, original_cap, length(original_bytes), original_buf)();
        //@ open mk_array::<u8>(original_buf, length(original_bytes), original_bytes)();
        //@ std::vec::Vec_unseparate_elems(s0.vec);
        //@ close_points_to(self);
        let rejections = local_rejections;

        unsafe {
            remove_matches_compact_rejections__VeriFast_wrapper(self, rejections);
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
    //@ req thread_token(?t) &*& *self |-> ?s0 &*& <String>.own(t, s0) &*& <F>.own(t, f);
    //@ ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1);
    //@ on_unwind_ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1);
    {
        struct SetLenOnDrop<'a> {
            s: &'a mut String,
            idx: usize,
            del_bytes: usize,
        }

        impl<'a> Drop for SetLenOnDrop<'a> {
            fn drop(&mut self)
            /*@
            req thread_token(?t) &*& (*self).s |-> ?target &*& (*self).idx |-> ?idx &*& (*self).del_bytes |-> ?del &*&
                (*target).vec |-> ?v &*& std::vec::Vec(v, ?cap, ?bytes) &*&
                del <= idx &*& idx <= length(bytes) &*& is_valid_utf8(take(idx - del, bytes)) == true;
            @*/
            /*@
            ens thread_token(t) &*& (*self).s |-> target &*& (*self).idx |-> idx &*& (*self).del_bytes |-> del &*&
                *target |-> ?restored &*& <String>.own(t, restored);
            @*/
            //@ on_unwind_ens false;
            /*@
            safety_proof {
                open String::retain::SetLenOnDrop_full_borrow_content::<'a>(_t, self)();
                assert (*self).s |-> ?target &*& (*self).idx |-> ?idx &*& (*self).del_bytes |-> ?del;
                open <String::retain::SetLenOnDrop<'a>>.own(_t, String::retain::SetLenOnDrop::<'a> { s: target, idx, del_bytes: del });
                call();
                open_points_to(target);
                close String_full_borrow_content(_t, target)();
                borrow('a, String_full_borrow_content(_t, target));
                leak borrow_end_token('a, String_full_borrow_content(_t, target));
            }
            @*/
            {
                let new_len = self.idx - self.del_bytes;
                //@ let string_ref = precreate_ref(target);
                //@ init_ref_String_raw(string_ref);
                debug_assert!(new_len <= self.s.len()); //~allow_dead_code
                //@ end_ref_String_raw(string_ref);
                //@ let buf = std::vec::Vec_separate_buffer(v);
                //@ array_split(buf, new_len);
                //@ array_to_array_(buf + new_len);
                //@ array__join(buf + new_len);
                // SAFETY: Restore the string length to the number of bytes written so far.
                unsafe { self.s.vec.set_len(new_len) };
                //@ std::vec::Vec_unseparate_buffer((*target).vec);
                //@ close_points_to(target);
                //@ assert *target |-> ?restored;
                //@ close <String>.own(t, restored);
            }
        }

        //@ open <String>.own(t, s0);
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v0 &*& std::vec::Vec(v0, ?cap, ?bs0);
        //@ let self_ref0 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref0);
        let len = self.len();
        //@ end_ref_String_raw(self_ref0);
        let mut guard = SetLenOnDrop { s: self, idx: 0, del_bytes: 0 };
        //@ let buf = std::vec::Vec_separate_elems(v0);

        while guard.idx < len {
            /*@
            inv thread_token(t) &*& f |-> ?f_cur &*& <F>.own(t, f_cur) &*&
                guard.s |-> self &*& guard.idx |-> ?idx &*& guard.del_bytes |-> ?del &*&
                (*self).vec |-> v0 &*& std::vec::Vec_minus_elems(v0, cap, len, buf) &*&
                buf[..len] |-> ?cur_bs &*&
                del <= idx &*& idx <= len &*&
                is_valid_utf8(take(idx - del, cur_bs)) == true &*&
                is_valid_utf8(drop(idx, cur_bs)) == true;
            @*/
            //@ let gs_ref = precreate_ref(guard.s);
            //@ init_ref_String_raw(gs_ref);
            let ch =
                // SAFETY: `guard.idx` is positive-or-zero and less that len so the `get_unchecked`
                // is in bound. `self` is valid UTF-8 like string and the returned slice starts at
                // a unicode code point so the `Chars` always return one character.
                unsafe { retain_next_char__VeriFast_wrapper(guard.s, guard.idx, len) };
            //@ end_ref_String_raw(gs_ref);
            let ch_len = ch.len_utf8();
            //@ drop_twice(idx, ch_len, cur_bs);
            if !retain_call_predicate__VeriFast_wrapper(&mut f, ch) {
                guard.del_bytes += ch_len;
            } else if guard.del_bytes > 0 {
                // SAFETY: `guard.idx` is in bound and `guard.del_bytes` represent the number of
                // bytes that are erased from the string so the resulting `guard.idx -
                // guard.del_bytes` always represent a valid unicode code point.
                //
                // `guard.del_bytes` >= `ch.len_utf8()`, so taking a slice with `ch.len_utf8()` len
                // is safe.
                //@ let dst_off = idx - del;
                unsafe {
                    retain_write_char__VeriFast_wrapper(ch, guard.s.as_mut_ptr(), guard.idx, guard.del_bytes);
                }
                //@ let pref = take(dst_off, cur_bs);
                //@ let written = char_utf8(ch);
                //@ let tail = drop(ch_len, drop(dst_off, cur_bs));
                //@ drop_twice(dst_off, ch_len, cur_bs);
                //@ append_assoc(pref, written, tail);
                //@ take_append_exact(dst_off + ch_len, append(pref, written), tail);
                //@ append_utf8(pref, written);
                //@ drop_append_ge(idx + ch_len, append(pref, written), tail);
                //@ drop_twice(dst_off + ch_len, (idx + ch_len) - (dst_off + ch_len), cur_bs);
            }

            /*@
            if del == 0 && guard.del_bytes == 0 {
                take_split_join(idx, idx + ch_len, cur_bs);
                append_utf8(take(idx, cur_bs), take(ch_len, drop(idx, cur_bs)));
            }
            @*/

            // Point idx to the next char
            guard.idx += ch_len;
        }

        //@ std::vec::Vec_unseparate_elems(v0);
        //@ close <String::retain::SetLenOnDrop<'static>>.own(t, guard);
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
    pub fn insert(&mut self, idx: usize, ch: char)
    /*@
    req thread_token(?t) &*& *self |-> ?s0 &*& std::vec::Vec(s0.vec, ?capacity, ?bs) &*&
        is_valid_utf8(bs) == true &*& char_own(t, ch);
    @*/
    //@ ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1);
    /*@
    on_unwind_ens thread_token(t) &*&
        if is_char_boundary(bs, idx) {
            (*self).vec |-> ?v &*& std::vec::Vec(v, _, bs)
        } else {
            exists::<*String>(?r) &*& ref_end_token(&(*r).vec, &(*self).vec, 1/2) &*& ref_initialized(r) &*&
            [1/2](*r).vec |-> s0.vec &*& [1/2](*self).vec |-> s0.vec &*&
            std::vec::Vec_minus_elems(s0.vec, capacity, length(bs), ?buf) &*& buf[..length(bs)] |-> bs
        };
    @*/
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        assert std::vec::Vec(s0.vec, _, ?bs);
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    if !is_char_boundary(bs, idx) {
                        open exists(?r);
                        end_ref_String_raw(r);
                        std::vec::Vec_unseparate_elems(s0.vec);
                    }
                    close_points_to(self);
                    assert *self |-> ?s1;
                    close <String>.own(_t, s1);
                }
            }
        }
    }
    @*/
    {
        //@ open char_own(t, ch);
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v0 &*& std::vec::Vec(v0, capacity, bs);
        //@ let buf0 = std::vec::Vec_separate_elems(v0);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_String_raw(self_ref);
        //@ close exists(self_ref);
        assert!(self.is_char_boundary(idx));
        //@ open exists(self_ref);
        //@ end_ref_String_raw(self_ref);
        //@ std::vec::Vec_unseparate_elems(v0);
        //@ split_utf8_at_boundary(bs, idx);

        //@ let self_ref2 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref2);
        let len = self.len();
        //@ end_ref_String_raw(self_ref2);
        //@ close_points_to(self);
        let ch_len = ch.len_utf8();
        self.reserve(ch_len);

        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v1 &*& std::vec::Vec(v1, ?cap1, bs);
        //@ let buf = std::vec::Vec_separate_buffer(v1);
        //@ array_split(buf, idx);
        //@ array_to_array_(buf + idx);
        //@ array__split(buf + len, ch_len);
        //@ close exists::<option<isize>>(some(ch_len));
        // Move the bytes starting from `idx` to their new location `ch_len` bytes ahead.
        // SAFETY: Sufficient capacity was reserved, and `idx` is a char boundary.
        unsafe {
            //@ let vref = precreate_ref(&(*self).vec);
            //@ std::vec::init_ref_Vec(vref);
            let src = self.vec.as_ptr().add(idx);
            //@ std::vec::end_ref_Vec(vref);
            //@ std::vec::Vec_minus_buffer_merge((*self).vec);
            ptr::copy(
                src,
                self.vec.as_mut_ptr().add(idx + ch_len),
                len - idx,
            );
        }

        // Encode the character into the vacated region if `idx != len`,
        // or into the uninitialized spare capacity otherwise.
        // SAFETY: `idx + ch_len` is in bounds in either case, and `idx` is a char boundary.
        unsafe {
            core::char::encode_utf8_raw_unchecked(ch as u32, self.vec.as_mut_ptr().add(idx));
        }

        // Update the length to include the newly added bytes.
        // SAFETY: We just wrote to all locations in the range `idx..len + ch_len`.
        unsafe {
            self.vec.set_len(len + ch_len);
        }
        //@ array__to_array(buf + idx + ch_len, drop(idx, bs));
        //@ array_join(buf + idx);
        //@ array_join(buf);
        //@ std::vec::Vec_unseparate_buffer((*self).vec);
        //@ append_utf8(char_utf8(ch), drop(idx, bs));
        //@ append_utf8(take(idx, bs), append(char_utf8(ch), drop(idx, bs)));
        //@ close_points_to(self);
        //@ assert *self |-> ?s1;
        //@ close <String>.own(t, s1);
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
    pub fn insert_str(&mut self, idx: usize, string: &str)
    /*@
    req thread_token(?t) &*& *self |-> ?s0 &*& std::vec::Vec(s0.vec, ?capacity, ?bs) &*& is_valid_utf8(bs) == true &*&
        [_]str_share(?k, t, string) &*& [?q]lifetime_token(k);
    @*/
    /*@
    ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1) &*&
        [q]lifetime_token(k);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& [q]lifetime_token(k) &*&
        if is_char_boundary(bs, idx) {
            (*self).vec |-> ?v &*& std::vec::Vec(v, _, bs)
        } else {
            exists::<*String>(?r) &*& ref_end_token(&(*r).vec, &(*self).vec, 1/2) &*& ref_initialized(r) &*&
            [1/2](*r).vec |-> s0.vec &*& [1/2](*self).vec |-> s0.vec &*&
            std::vec::Vec_minus_elems(s0.vec, capacity, length(bs), ?buf) &*& buf[..length(bs)] |-> bs
        };
    @*/
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        assert std::vec::Vec(s0.vec, _, ?bs);
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    if !is_char_boundary(bs, idx) {
                        open exists(?r);
                        end_ref_String_raw(r);
                        std::vec::Vec_unseparate_elems(s0.vec);
                    }
                    close_points_to(self);
                    assert *self |-> ?s1;
                    close <String>.own(_t, s1);
                }
            }
        }
    }
    @*/
    {
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v0 &*& std::vec::Vec(v0, capacity, bs);
        //@ let buf0 = std::vec::Vec_separate_elems(v0);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_String_raw(self_ref);
        //@ close exists(self_ref);
        assert!(self.is_char_boundary(idx));
        //@ open exists(self_ref);
        //@ end_ref_String_raw(self_ref);
        //@ std::vec::Vec_unseparate_elems(v0);
        //@ split_utf8_at_boundary(bs, idx);

        //@ let self_ref2 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref2);
        let len = self.len();
        //@ end_ref_String_raw(self_ref2);
        //@ close_points_to(self);
        let amt = string.len();
        self.reserve(amt);

        //@ open str_share(k, t, string);
        //@ assert [_]exists(?sbs);
        //@ open_frac_borrow(k, mk_array::<u8>(string as *u8, string.len(), sbs), q);
        //@ open [?fs]mk_array::<u8>(string as *u8, string.len(), sbs)();
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v1 &*& std::vec::Vec(v1, ?cap1, bs);
        //@ let buf = std::vec::Vec_separate_buffer(v1);
        //@ array_split(buf, idx);
        //@ array_to_array_(buf + idx);
        //@ if amt > 0 { array__split(buf + len, amt); }
        //@ close exists::<option<isize>>(some(amt));
        // Move the bytes starting from `idx` to their new location `amt` bytes ahead.
        // SAFETY: Sufficient capacity was just reserved, and `idx` is a char boundary.
        unsafe {
            //@ let vref = precreate_ref(&(*self).vec);
            //@ std::vec::init_ref_Vec(vref);
            let src = self.vec.as_ptr().add(idx);
            //@ std::vec::end_ref_Vec(vref);
            //@ std::vec::Vec_minus_buffer_merge((*self).vec);
            ptr::copy(src, self.vec.as_mut_ptr().add(idx + amt), len - idx);
        }

        //@ if amt == 0 { array__split(buf + idx, 0); }
        // Copy the new string slice into the vacated region if `idx != len`,
        // or into the uninitialized spare capacity otherwise.
        // SAFETY: The borrow checker ensures that the source and destination do not overlap.
        unsafe {
            ptr::copy_nonoverlapping(string.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
        }

        // Update the length to include the newly added bytes.
        // SAFETY: We just wrote to all locations in the range `idx..len + amt`.
        unsafe {
            self.vec.set_len(len + amt);
        }
        //@ array__to_array(buf + idx + amt, drop(idx, bs));
        /*@
        if amt == 0 {
            open array(buf + idx, 0, sbs);
        } else {
            array_join(buf + idx);
        }
        @*/
        //@ array_join(buf);
        //@ std::vec::Vec_unseparate_buffer((*self).vec);
        //@ append_utf8(sbs, drop(idx, bs));
        //@ append_utf8(take(idx, bs), append(sbs, drop(idx, bs)));
        //@ close_points_to(self);
        //@ assert *self |-> ?s1;
        //@ close <String>.own(t, s1);
        //@ close [fs]mk_array::<u8>(string as *u8, string.len(), sbs)();
        //@ close_frac_borrow(fs, mk_array::<u8>(string as *u8, string.len(), sbs));
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
    pub const unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8>
    //@ req true;
    //@ ens result == &(*self).vec;
    //@ on_unwind_ens false;
    {
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
    pub const fn len(&self) -> usize
    //@ req [?f](*self).vec |-> ?v &*& [?fv]std::vec::Vec(v, ?cap, ?bs);
    //@ ens [f](*self).vec |-> v &*& [fv]std::vec::Vec(v, cap, bs) &*& result == length(bs);
    //@ on_unwind_ens false;
    /*@
    safety_proof {
        assert [?q]lifetime_token(?k);
        open <String>.share(k, _t, self);
        assert [_]exists(String_share_info(?v, ?cap, ?buf, ?bs));
        frac_borrow_sep(k, String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs));
        open_frac_borrow(k, sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)), q);
        open [?f]sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
        open [f]String_header_fbc(self, v, cap, length(bs), buf)();
        open [f]mk_array::<u8>(buf, length(bs), bs)();
        std::vec::Vec_unseparate_elems(v);
        call();
        let buf_ = std::vec::Vec_separate_elems(v);
        close [f]mk_array::<u8>(buf, length(bs), bs)();
        close [f]String_header_fbc(self, v, cap, length(bs), buf)();
        close [f]sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
        close_frac_borrow(f, sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)));
    }
    @*/
    {
        //@ let vec_ref = precreate_ref(&(*self).vec);
        //@ std::vec::init_ref_Vec(vec_ref);
        let r = self.vec.len();
        //@ std::vec::end_ref_Vec(vec_ref);
        r
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
    pub fn split_off(&mut self, at: usize) -> String
    /*@
    req thread_token(?t) &*& *self |-> ?s0 &*& std::vec::Vec(s0.vec, ?capacity, ?bs) &*& is_valid_utf8(bs) == true;
    @*/
    //@ ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1) &*& <String>.own(t, result);

    /*@
    on_unwind_ens thread_token(t) &*&
        if is_char_boundary(bs, at) {
            (*self).vec |-> ?v &*& std::vec::Vec(v, _, bs)
        } else {
            exists::<*String>(?r) &*& ref_end_token(&(*r).vec, &(*self).vec, 1/2) &*& ref_initialized(r) &*&
            [1/2](*r).vec |-> s0.vec &*& [1/2](*self).vec |-> s0.vec &*&
            std::vec::Vec_minus_elems(s0.vec, capacity, length(bs), ?buf) &*& buf[..length(bs)] |-> bs
        };
    @*/
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        assert std::vec::Vec(s0.vec, _, ?bs);
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    if !is_char_boundary(bs, at) {
                        open exists(?r);
                        end_ref_String_raw(r);
                        std::vec::Vec_unseparate_elems(s0.vec);
                    }
                    close_points_to(self);
                    assert *self |-> ?s1;
                    close <String>.own(_t, s1);
                }
            }
        }
    }
    @*/
    {
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v0 &*& std::vec::Vec(v0, capacity, bs);
        //@ let buf = std::vec::Vec_separate_elems(v0);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_String_raw(self_ref);
        //@ close exists(self_ref);
        assert!(self.is_char_boundary(at));
        //@ open exists(self_ref);
        //@ end_ref_String_raw(self_ref);
        //@ std::vec::Vec_unseparate_elems(v0);
        //@ split_utf8_at_boundary(bs, at);
        let other = self.vec.split_off(at);
        // SAFETY: `other` contains only valid UTF-8 because `at` is on a `UTF-8` code point boundary.
        let r = unsafe { String::from_utf8_unchecked(other) };
        //@ close_points_to(self);
        //@ assert *self |-> ?s1;
        //@ close <String>.own(t, s1);
        //@ close <String>.own(t, r);
        r
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
    pub fn drain<'a, R>(&'a mut self, range: R) -> Drain<'a>
    where
        R: RangeBounds<usize>,
    /*@
    req thread_token(?t) &*& [?q]lifetime_token('a) &*&
        full_borrow('a, <String>.full_borrow_content(t, self)) &*&
        <R>.own(t, range);
    @*/
    /*@
    ens thread_token(t) &*& [q]lifetime_token('a) &*&
        <Drain<'a>>.own(t, result);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*&
        close_full_borrow_token_strong(?klong, String_full_borrow_content(t, self), q, 'a) &*&
        lifetime_inclusion('a, klong) == true &*& exists::<option<*String>>(?read_ref) &*&
        match read_ref {
            none => (*self).vec |-> ?v &*& std::vec::Vec(v, _, ?bs) &*& is_valid_utf8(bs) == true,
            some(r) => ref_end_token(&(*r).vec, &(*self).vec, 1/2) &*& ref_initialized(r) &*&
                [1/2](*self).vec |-> ?v &*& [1/2](*r).vec |-> v &*&
                std::vec::Vec_minus_elems(v, _, ?len, ?buf) &*& buf[..len] |-> ?bs &*& is_valid_utf8(bs) == true
        };
    @*/
    /*@
    safety_proof {
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    assert close_full_borrow_token_strong(?klong, String_full_borrow_content(_t, self), _, 'a);
                    open exists::<option<*String>>(?read_ref);
                    match read_ref {
                        none => {}
                        some(r) => {
                            end_ref_String_raw(r);
                            std::vec::Vec_unseparate_elems((*self).vec);
                        }
                    }
                    assert (*self).vec |-> ?v;
                    close <String>.own(_t, String { vec: v });
                    let original = String_full_borrow_content(_t, self);
                    close String_full_borrow_content(_t, self)();
                    produce_lem_ptr_chunk full_borrow_convert_strong(True, original, klong, original)() {
                        open True();
                    } {
                        close_full_borrow_strong(klong, original, original);
                    }
                    full_borrow_mono(klong, 'a, original);
                    leak full_borrow('a, original);
                }
            }
        }
    }
    @*/
    {
        //@ let klong = open_full_borrow_strong('a, <String>.full_borrow_content(t, self), q);
        //@ open String_full_borrow_content(t, self)();
        //@ assert (*self).vec |-> ?v0;
        //@ open <String>.own(t, String { vec: v0 });
        //@ assert std::vec::Vec(v0, ?cap, ?bs);
        // Memory safety
        //
        // The String version of Drain does not have the memory safety issues
        // of the vector version. The data is just plain bytes.
        // Because the range removal happens in Drop, if the Drain iterator is leaked,
        // the removal will not happen.
        //@ let self_ref0 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref0);
        let len = self.len();
        //@ end_ref_String_raw(self_ref0);
        //@ close exists::<option<*String>>(none);
        let Range { start, end } = slice::range(range, ..len);
        //@ open exists::<option<*String>>(none);
        //@ let buf = std::vec::Vec_separate_elems(v0);
        //@ let self_ref1 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref1);
        //@ close exists::<option<*String>>(some(self_ref1));
        assert!(self.is_char_boundary(start));
        //@ open exists::<option<*String>>(some(self_ref1));
        //@ end_ref_String_raw(self_ref1);
        //@ let self_ref2 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref2);
        //@ close exists::<option<*String>>(some(self_ref2));
        assert!(self.is_char_boundary(end));
        //@ open exists::<option<*String>>(some(self_ref2));
        //@ end_ref_String_raw(self_ref2);

        //@ split_utf8_at_boundary(bs, start);
        //@ split_utf8_at_boundary(bs, end);
        //@ drop_twice(start, end - start, bs);
        // Take out two simultaneous borrows. The &mut String won't be accessed
        // until iteration is over, in Drop.
        let self_ptr = self as *mut _;
        //@ let self_ref3 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref3);
        // SAFETY: `slice::range` and `is_char_boundary` do the appropriate bounds checks.
        let chars_iter = unsafe { self.get_unchecked(start..end) }.chars();
        //@ array_join(buf + start);
        //@ array_join(buf);
        //@ append_take_drop_n(drop(start, bs), end - start);
        //@ append_take_drop_n(bs, start);
        //@ end_ref_String_raw(self_ref3);
        //@ std::vec::Vec_unseparate_elems(v0);
        //@ let gid = create_ghost_cell::<Drain_state>(Drain_active(v0, cap, buf, bs, start, end));
        //@ close Drain_fbc(gid, self_ptr)();
        /*@
        {
            pred Ctx() = true;
            produce_lem_ptr_chunk full_borrow_convert_strong(Ctx, Drain_fbc(gid, self_ptr), klong, <String>.full_borrow_content(t, self))() {
                open Ctx();
                open Drain_fbc(gid, self_ptr)();
                assert [1/2]ghost_cell::<Drain_state>(gid, ?st);
                match st {
                    Drain_active(va, capa, bufa, bsa, sa, ea) => {
                        close <String>.own(t, String { vec: va });
                        close String_full_borrow_content(t, self)();
                        leak [1/2]ghost_cell::<Drain_state>(gid, _);
                    }
                    Drain_dropped => {
                        assert (*self).vec |-> ?vd;
                        close <String>.own(t, String { vec: vd });
                        close String_full_borrow_content(t, self)();
                        leak [1/2]ghost_cell::<Drain_state>(gid, _);
                    }
                }
            } {
                close Ctx();
                close_full_borrow_strong(klong, <String>.full_borrow_content(t, self), Drain_fbc(gid, self_ptr));
                full_borrow_mono(klong, 'a, Drain_fbc(gid, self_ptr));
            }
        }
        @*/
        //@ is_char_boundary_drop(bs, start, end);
        //@ split_utf8_at_boundary(drop(start, bs), end - start);
        let r = Drain { start, end, iter: chars_iter, string: self_ptr };
        //@ std::str::Chars_as_str_lft::<'static, 'a>(chars_iter);
        //@ close exists::<pair<i32, usize>>(pair(gid, start));
        //@ close <Drain<'a>>.own(t, r);
        r
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
    #[stable(feature = "string_into_chars", since = "1.101.0")]
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
    /*@
    req thread_token(?t) &*& *self |-> ?s0 &*& std::vec::Vec(s0.vec, ?capacity, ?bs) &*& is_valid_utf8(bs) == true &*&
        <R>.own(t, range) &*& [_]str_share(?k, t, replace_with) &*& [?q]lifetime_token(k);
    @*/
    /*@
    ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1) &*&
        [q]lifetime_token(k);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& [q]lifetime_token(k) &*& exists::<option<*String>>(?read_ref) &*&
        match read_ref {
            none => (*self).vec |-> ?v &*& std::vec::Vec(v, _, bs),
            some(r) => ref_end_token(&(*r).vec, &(*self).vec, 1/2) &*& ref_initialized(r) &*&
                [1/2](*r).vec |-> s0.vec &*& [1/2](*self).vec |-> s0.vec &*&
                std::vec::Vec_minus_elems(s0.vec, capacity, length(bs), ?buf) &*& buf[..length(bs)] |-> bs
        };
    @*/
    /*@
    safety_proof {
        open <String>.own(_t, ?s0);
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    open exists::<option<*String>>(?read_ref);
                    match read_ref {
                        none => {}
                        some(r) => {
                            end_ref_String_raw(r);
                            std::vec::Vec_unseparate_elems(s0.vec);
                        }
                    }
                    close_points_to(self);
                    assert *self |-> ?s1;
                    close <String>.own(_t, s1);
                }
            }
        }
    }
    @*/
    {
        //@ open_points_to(self);
        //@ assert (*self).vec |-> ?v0 &*& std::vec::Vec(v0, capacity, bs);
        // We avoid #81138 (nondeterministic RangeBounds impls) because we only use `range` once, here.
        //@ let self_ref0 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref0);
        let len0 = self.len();
        //@ end_ref_String_raw(self_ref0);
        //@ close exists::<option<*String>>(none);
        let checked_range = slice::range(range, ..len0);
        //@ open exists::<option<*String>>(none);

        //@ let buf = std::vec::Vec_separate_elems(v0);
        //@ let self_ref1 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref1);
        //@ close exists::<option<*String>>(some(self_ref1));
        assert!(
            self.is_char_boundary(checked_range.start),
            "start of range should be a character boundary"
        );
        //@ open exists::<option<*String>>(some(self_ref1));
        //@ end_ref_String_raw(self_ref1);
        //@ let self_ref2 = precreate_ref(self);
        //@ init_ref_String_raw(self_ref2);
        //@ close exists::<option<*String>>(some(self_ref2));
        assert!(
            self.is_char_boundary(checked_range.end),
            "end of range should be a character boundary"
        );
        //@ open exists::<option<*String>>(some(self_ref2));
        //@ end_ref_String_raw(self_ref2);
        //@ std::vec::Vec_unseparate_elems(v0);
        //@ split_utf8_at_boundary(bs, checked_range.start);
        //@ split_utf8_at_boundary(bs, checked_range.end);
        //@ close_points_to(self);

        //@ open str_share(k, t, replace_with);
        //@ assert [_]exists(?rep_bs);
        //@ let replacement = mk_array::<u8>(replace_with as *u8, replace_with.len(), rep_bs);
        //@ open_frac_borrow(k, replacement, q);
        //@ open [?f]mk_array::<u8>(replace_with as *u8, replace_with.len(), rep_bs)();
        //@ array_inv::<u8>();
        //@ close [f]mk_array::<u8>(replace_with as *u8, replace_with.len(), rep_bs)();
        //@ close_frac_borrow(f, replacement);
        //@ close exists::<option<*String>>(none);
        if replace_with.len() > checked_range.len() {
            self.reserve(replace_with.len() - checked_range.len());
        }
        //@ open exists::<option<*String>>(none);
        //@ open_frac_borrow(k, mk_array::<u8>(replace_with as *u8, replace_with.len(), rep_bs), q);
        //@ open [?fs]mk_array::<u8>(replace_with as *u8, replace_with.len(), rep_bs)();
        //@ open_points_to(self);
        // SAFETY: We ensure that we're not replacing across a char boundary and
        // that the new contents are valid UTF-8. The only potentially-unsound
        // unwind from `splice` that would leave the string in an invalid state
        // would be from an error growing the allocation, which we protect against
        // by reserving it preemptively.
        unsafe { self.as_mut_vec() }.splice(checked_range, replace_with.bytes());
        //@ append_utf8(rep_bs, drop(checked_range.end, bs));
        //@ append_utf8(take(checked_range.start, bs), append(rep_bs, drop(checked_range.end, bs)));
        //@ close_points_to(self);
        //@ assert *self |-> ?s1;
        //@ close <String>.own(t, s1);
        //@ close [fs]mk_array::<u8>(replace_with as *u8, replace_with.len(), rep_bs)();
        //@ close_frac_borrow(fs, mk_array::<u8>(replace_with as *u8, replace_with.len(), rep_bs));
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
    pub fn into_boxed_str(self) -> Box<str>
    //@ req thread_token(?t) &*& <String>.own(t, self);
    //@ ens thread_token(t) &*& <std::boxed::Box<str, std::alloc::Global>>.own(t, result);
    //@ on_unwind_ens thread_token(t);
    {
        let slice = string_vec__VeriFast_wrapper(self).into_boxed_slice();
        // SAFETY: `slice` contains only valid UTF-8 because `String` is guaranteed to be valid UTF-8.
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
    pub fn leak<'a>(self) -> &'a mut str
    //@ req thread_token(?t) &*& <String>.own(t, self);
    //@ ens thread_token(t) &*& full_borrow('a, <str>.full_borrow_content(t, result));
    //@ on_unwind_ens false;
    {
        let slice = string_vec__VeriFast_wrapper(self).leak();
        // SAFETY: `slice` contains only valid UTF-8 because `String` is guaranteed to be valid UTF-8.
        let r = unsafe { from_utf8_unchecked_mut(slice) };
        //@ close str_full_borrow_content(t, r)();
        //@ borrow('a, str_full_borrow_content(t, r));
        //@ leak borrow_end_token('a, str_full_borrow_content(t, r));
        r
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
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> String
    //@ req thread_token(?t) &*& <I>.own(t, iter);
    //@ ens thread_token(t) &*& <String>.own(t, result);
    //@ on_unwind_ens thread_token(t);
    {
        FromCharIterSpec::to_string_spec(iter.into_iter())
    }
}

#[cfg(not(no_global_oom_handling))]
trait FromCharIterSpec: Iterator<Item = char> {
    fn to_string_spec(self) -> String;
}

#[cfg(not(no_global_oom_handling))]
impl<T> FromCharIterSpec for T
where
    T: Iterator<Item = char>,
{
    default fn to_string_spec(/*@~mut@*/ self) -> String
    //@ req thread_token(?t) &*& <T>.own(t, self);
    //@ ens thread_token(t) &*& <String>.own(t, result);
    //@ on_unwind_ens thread_token(t);
    {
        //@ let hint_ref = precreate_ref(&self);
        //@ init_ref_readonly(hint_ref, 1/2);
        let mut buf = String::with_capacity(self.size_hint().0);
        //@ close <String>.own(t, buf);
        //@ close_points_to(&buf);
        buf.extend(self);
        //@ open_points_to(&buf);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl FromCharIterSpec for core::str::EscapeDefault<'_> {
    fn to_string_spec(self) -> String {
        // go through the ToString specialization
        self.to_string()
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
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I)
    //@ req thread_token(?t) &*& *self |-> ?s0 &*& <String>.own(t, s0) &*& <I>.own(t, iter);
    //@ ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1);
    //@ on_unwind_ens thread_token(t) &*& *self |-> ?s1 &*& <String>.own(t, s1);
    {
        SpecExtendChars::spec_extend_into(iter, self);
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
trait SpecExtendChars {
    fn spec_extend_into(self, s: &mut String);
}

#[cfg(not(no_global_oom_handling))]
impl<T: IntoIterator<Item = char>> SpecExtendChars for T {
    default fn spec_extend_into(self, target: &mut String)
    //@ req thread_token(?t) &*& *target |-> ?s0 &*& <String>.own(t, s0) &*& <T>.own(t, self);
    //@ ens thread_token(t) &*& *target |-> ?s1 &*& <String>.own(t, s1);
    /*@
    on_unwind_ens thread_token(t) &*& exists::<option<lifetime_t>>(?pending) &*&
        match pending {
            none => *target |-> ?s1 &*& <String>.own(t, s1),
            some(k) => lifetime_token(k) &*& borrow_end_token(k, String_full_borrow_content(t, target))
        };
    @*/
    /*@
    safety_proof {
        let outcome = call();
        if !ignore_unwind_paths() {
            match outcome {
                returning(value) => {}
                unwinding => {
                    open exists::<option<lifetime_t>>(?pending);
                    match pending {
                        none => {}
                        some(k) => {
                            end_lifetime(k);
                            borrow_end(k, String_full_borrow_content(_t, target));
                            open String_full_borrow_content(_t, target)();
                            close_points_to(target);
                        }
                    }
                }
            }
        }
    }
    @*/
    {
        //@ close exists::<option<lifetime_t>>(none);
        let /*@~mut@*/ iterator = self.into_iter();
        //@ let hint_ref = precreate_ref(&iterator);
        //@ init_ref_readonly(hint_ref, 1/2);
        let (lower_bound, _) = iterator.size_hint();
        //@ open <String>.own(t, s0);
        target.reserve(lower_bound)/*@~unwind {
            close_points_to(target);
            assert *target |-> ?restored;
            close <String>.own(t, restored);
        } @*/;
        //@ assert *target |-> ?reserved;
        //@ close <String>.own(t, reserved);
        //@ open exists::<option<lifetime_t>>(none);
        //@ let builder = begin_lifetime();
        {
        //@ let_lft 'builder = builder;
        //@ let content = String_full_borrow_content(t, target);
        //@ open_points_to(target);
        //@ close String_full_borrow_content(t, target)();
        //@ borrow(builder, content);
        let push = move |c| { //~verify_closure
            /*@~contract
            req thread_token(?_t) &*& *closure_env |-> ?env &*& *env.0 |-> ?s0 &*&
                <String>.own(_t, s0) &*& char_own(_t, c);
            @*/
            /*@~contract
            ens thread_token(_t) &*& *closure_env |-> env &*& *env.0 |-> ?s1 &*& <String>.own(_t, s1);
            @*/
            /*@~contract
            on_unwind_ens thread_token(_t) &*& *closure_env |-> env &*& *env.0 |-> ?s1 &*& <String>.own(_t, s1);
            @*/
            /*@~contract
            safety_proof {
                assert *closure_env |-> ?env;
                open <VfFunctionItem$closure_3a_3a_3cT_20as_20string_3a_3aSpecExtendChars_3e_3a_3aspec_5fextend_5finto_3a_3a_7bclosure_230_7d<T, '_VfCapture_0, String>>.own(_t, env);
                let capture = env.0;
                let content = String_full_borrow_content(_t, capture);
                assert [?q]lifetime_token('_VfCapture_0);
                open_full_borrow(q, '_VfCapture_0, content);
                open String_full_borrow_content(_t, capture)();
                close_points_to(capture);
                call();
                open_points_to(capture);
                close String_full_borrow_content(_t, capture)();
                close_full_borrow(content);
                close <VfFunctionItem$closure_3a_3a_3cT_20as_20string_3a_3aSpecExtendChars_3e_3a_3aspec_5fextend_5finto_3a_3a_7bclosure_230_7d<T, '_VfCapture_0, String>>.own(_t, env);
            }
            @*/
            //@ assert *closure_env |-> ?current_env;
            //@ let target_ptr = current_env.0;
            //@ assert *target_ptr |-> ?before;
            //@ open <String>.own(_t, before);
            //@ open char_own(_t, c);
            let result = target.push(c)/*@~unwind {
                close_points_to(target_ptr);
                assert *target_ptr |-> ?restored;
                close <String>.own(_t, restored);
            } @*/;
            //@ assert *target_ptr |-> ?after;
            //@ close <String>.own(_t, after);
            result
        };
        //@ close <VfFunctionItem$closure_3a_3a_3cT_20as_20string_3a_3aSpecExtendChars_3e_3a_3aspec_5fextend_5finto_3a_3a_7bclosure_230_7d<T, 'builder, String>>.own(t, push);
        //@ close exists::<option<lifetime_t>>(some(builder));
        iterator.for_each(push);
        //@ open exists::<option<lifetime_t>>(some(builder));
        }
        //@ end_lifetime(builder);
        //@ borrow_end(builder, String_full_borrow_content(t, target));
        //@ open String_full_borrow_content(t, target)();
        //@ close_points_to(target);
    }
}

#[cfg(not(no_global_oom_handling))]
impl SpecExtendChars for core::str::EscapeDefault<'_> {
    fn spec_extend_into(self, target: &mut String) {
        target.extend_from_escape_default(self);
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
unsafe impl<'b> Pattern for &'b String {
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
    fn add(mut self, other: &str) -> String
    /*@
    req thread_token(?t) &*& std::vec::Vec(self.vec, _, ?bs) &*& is_valid_utf8(bs) == true &*&
        [?fs](other as *u8)[..other.len()] |-> ?sbs &*& is_valid_utf8(sbs) == true;
    @*/
    /*@
    ens thread_token(t) &*& std::vec::Vec(result.vec, _, ?bytes) &*& is_valid_utf8(bytes) == true &*&
        [fs](other as *u8)[..other.len()] |-> sbs;
    @*/
    //@ on_unwind_ens thread_token(t) &*& [fs](other as *u8)[..other.len()] |-> sbs;
    /*@
    safety_proof {
        open <String>.own(_t, self);
        open str_share(?k, _t, other);
        assert [_]exists(?sbs);
        assert [?q]lifetime_token(k);
        open_frac_borrow(k, mk_array::<u8>(other as *u8, other.len(), sbs), q);
        open [?fs]mk_array::<u8>(other as *u8, other.len(), sbs)();
        let result = call();
        close [fs]mk_array::<u8>(other as *u8, other.len(), sbs)();
        close_frac_borrow(fs, mk_array::<u8>(other as *u8, other.len(), sbs));
        if ignore_unwind_paths() {
            close <String>.own(_t, result);
        } else {
            match result {
                returning(output) => { close <String>.own(_t, output); }
                unwinding => {}
            }
        }
    }
    @*/
    {
        self.push_str(other)/*@~unwind {
            close_points_to(&self);
            assert self |-> ?restored;
            close <String>.own(t, restored);
        } @*/;
        //@ open_points_to(&self);
        let r = self;
        //@ close_points_to(&self);
        r
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
    fn deref(&self) -> &str
    /*@
    req [?f](*self).vec |-> ?v &*& [?fv]std::vec::Vec_minus_elems(v, ?cap, ?len, ?buf) &*&
        [?fb]buf[..len] |-> ?bytes;
    @*/
    /*@
    ens [f](*self).vec |-> v &*& [fv]std::vec::Vec_minus_elems(v, cap, len, buf) &*&
        [fb]buf[..len] |-> bytes &*& result as *u8 == buf &*& result.len() == len;
    @*/
    //@ on_unwind_ens false;
    /*@
    safety_proof {
        assert [?q]lifetime_token(?k);
        open <String>.share(k, _t, self);
        assert [_]exists(String_share_info(?v, ?cap, ?buf, ?bs));
        frac_borrow_sep(k, String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs));
        open_frac_borrow(k, sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)), q);
        open [?f]sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
        open [f]String_header_fbc(self, v, cap, length(bs), buf)();
        open [f]mk_array::<u8>(buf, length(bs), bs)();
        let result = call();
        close [f]mk_array::<u8>(buf, length(bs), bs)();
        close [f]String_header_fbc(self, v, cap, length(bs), buf)();
        close [f]sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs))();
        close_frac_borrow(f, sep_(String_header_fbc(self, v, cap, length(bs), buf), mk_array::<u8>(buf, length(bs), bs)));
        close exists(bs);
        if ignore_unwind_paths() {
            close str_share(k, _t, result);
            leak str_share(k, _t, result);
        } else {
            let reference = fn_outcome_result(result);
            close str_share(k, _t, reference);
            leak str_share(k, _t, reference);
        }
    }
    @*/
    {
        self.as_str() //~ignore_ref_creation
    }
}

#[unstable(feature = "deref_pure_trait", issue = "87121")]
unsafe impl ops::DerefPure for String {}

#[stable(feature = "derefmut_for_string", since = "1.3.0")]
impl ops::DerefMut for String {
    #[inline]
    fn deref_mut(&mut self) -> &mut str
    /*@
    req (*self).vec |-> ?v &*& std::vec::Vec_minus_elems(v, ?cap, ?len, ?buf) &*& buf[..len] |-> ?bytes;
    @*/
    /*@
    ens (*self).vec |-> v &*& std::vec::Vec_minus_elems(v, cap, len, buf) &*&
        buf[..len] |-> bytes &*& result as *u8 == buf &*& result.len() == len;
    @*/
    //@ on_unwind_ens false;
    /*@
    safety_proof {
        assert [?q]lifetime_token(?k);
        let klong = open_full_borrow_strong(k, String_full_borrow_content(_t, self), q);
        open String_full_borrow_content(_t, self)();
        assert (*self).vec |-> ?v;
        open <String>.own(_t, String { vec: v });
        let buf = std::vec::Vec_separate_elems(v);
        let result = call();
        if ignore_unwind_paths() {
            close_String_mut_str_borrow(k, klong, _t, self, result);
        } else {
            close_String_mut_str_borrow(k, klong, _t, self, fn_outcome_result(result));
        }
    }
    @*/
    {
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

#[cfg(not(no_global_oom_handling))]
impl SpecToString for core::str::EscapeDefault<'_> {
    fn spec_to_string(&self) -> String {
        let mut s = String::new();
        s.extend_from_escape_default(self.clone());
        s
    }
}

#[cfg(not(no_global_oom_handling))]
impl String {
    #[inline]
    fn extend_from_escape_default(&mut self, escaper: core::str::EscapeDefault<'_>) {
        let (front, middle, tail) = escaper.into_parts();
        let lengths = front.as_ref().map_or_default(|f| f.size_hint().0)
            + middle.as_ref().map_or_default(|m| m.size_hint().0)
            + tail.as_ref().map_or_default(|t| t.size_hint().0);
        self.reserve(lengths);

        if let Some(front) = front {
            self.extend(front);
        }
        if let Some(middle) = middle {
            /// Ensures a spare capacity of N bytes and then passes that as MaybeUninit
            /// slice to a closure that returns the bytes written, then
            /// updates the length.
            ///
            /// # Safety:
            ///
            /// The caller must initialize the number of bytes returned by the closure.
            #[inline]
            unsafe fn with_spare<const N: usize, T>(
                bytes: &mut Vec<u8>,
                then: impl FnOnce(&mut [MaybeUninit<T>; N]) -> usize,
            ) {
                const {
                    assert!(core::mem::size_of::<T>() == 1);
                }
                bytes.reserve(N);
                let old_len = bytes.len();
                // SAFETY: We reserved enough space for the requested number of bytes.
                unsafe {
                    let spare: &mut [MaybeUninit<T>; N] = bytes
                        .spare_capacity_mut()
                        .as_mut_ptr()
                        .cast::<T>()
                        .cast_uninit()
                        .cast_array::<N>()
                        .as_mut_unchecked();
                    let written = then(spare);
                    bytes.set_len(old_len + written);
                }
            }

            for c in middle {
                match c {
                    '\'' | '\"' | '\\' => {
                        self.push('\\');
                        self.push(c);
                    }
                    '\x20'..='\x7e' => self.push(c),
                    '\t' => {
                        self.push('\\');
                        self.push('t');
                    }
                    '\r' => {
                        self.push('\\');
                        self.push('r');
                    }
                    '\n' => {
                        self.push('\\');
                        self.push('n');
                    }
                    c => {
                        // SAFETY: We only let the function write ascii chars, so it remains valid utf8.
                        // and it returns the number of bytes written, so so with_spare ensures the rest for us.
                        unsafe {
                            with_spare::<10, ascii::Char>(self.as_mut_vec(), |spare| {
                                escape_unicode_into(spare, c)
                            });
                        }
                    }
                }
            }
        }

        if let Some(tail) = tail {
            self.extend(tail);
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[inline]
// adapted from core::escape::escape_unicode, but it's left-aligned instead of right-aligned.
fn escape_unicode_into(output: &mut [MaybeUninit<ascii::Char>; 10], c: char) -> usize {
    const HEX_DIGITS: [ascii::Char; 16] = *b"0123456789abcdef".as_ascii().unwrap();

    let c = c as u32;
    // OR-ing `1` ensures that for `c == 0` the code computes that
    // one digit should be printed.
    let prefix_skip = (c | 1).leading_zeros() as usize / 4 - 2;

    // Always write all digits, but for shorter representations the unused
    // digits get overwritten by later writes.
    output[3usize.saturating_sub(prefix_skip)].write(HEX_DIGITS[((c >> 20) & 15) as usize]);
    output[4usize.saturating_sub(prefix_skip)].write(HEX_DIGITS[((c >> 16) & 15) as usize]);
    output[5usize.saturating_sub(prefix_skip)].write(HEX_DIGITS[((c >> 12) & 15) as usize]);
    output[6usize.saturating_sub(prefix_skip)].write(HEX_DIGITS[((c >> 8) & 15) as usize]);
    output[7usize.saturating_sub(prefix_skip)].write(HEX_DIGITS[((c >> 4) & 15) as usize]);
    output[8usize.saturating_sub(prefix_skip)].write(HEX_DIGITS[(c & 15) as usize]);

    output[0].write(ascii::Char::ReverseSolidus);
    output[1].write(ascii::Char::SmallU);
    output[2].write(ascii::Char::LeftCurlyBracket);
    output[9 - prefix_skip].write(ascii::Char::RightCurlyBracket);

    10 - prefix_skip
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

/// Note that all methods of this trait append to the `String`'s existing
/// contents; they never truncate or replace what is already there. In
/// particular, [`fmt::Write::write_str`] uses [`push_str`][String::push_str]
/// and [`fmt::Write::write_char`] uses [`push`][String::push].
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
#[stable(feature = "string_into_chars", since = "1.101.0")]
pub struct IntoChars {
    bytes: vec::IntoIter<u8>,
}

#[stable(feature = "string_into_chars", since = "1.101.0")]
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
    /// let mut chars = String::from("abc").into_chars();
    ///
    /// assert_eq!(chars.as_str(), "abc");
    /// chars.next();
    /// assert_eq!(chars.as_str(), "bc");
    /// chars.next();
    /// chars.next();
    /// assert_eq!(chars.as_str(), "");
    /// ```
    #[stable(feature = "string_into_chars", since = "1.101.0")]
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
    /// let chars = String::from("abc").into_chars();
    /// assert_eq!(chars.into_string(), "abc");
    ///
    /// let mut chars = String::from("def").into_chars();
    /// chars.next();
    /// assert_eq!(chars.into_string(), "ef");
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[stable(feature = "string_into_chars", since = "1.101.0")]
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

#[stable(feature = "string_into_chars", since = "1.101.0")]
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

#[stable(feature = "string_into_chars", since = "1.101.0")]
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

#[stable(feature = "string_into_chars", since = "1.101.0")]
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

/*@

inductive Drain_state =
    Drain_active(v: std::vec::Vec<u8, std::alloc::Global>, cap: usize, buf: *u8, bs: list<u8>, start: usize, end: usize)
  | Drain_dropped;

pred_ctor Drain_fbc(gid: i32, s: *String)() =
    [1/2]ghost_cell::<Drain_state>(gid, ?st) &*&
    match st {
        Drain_active(v, cap, buf, bs, start, end) =>
            (*s).vec |-> v &*&
            std::vec::Vec(v, cap, bs) &*&
            buf == std::vec::Vec_buf(v) &*&
            is_valid_utf8(bs) == true &*&
            0 <= start &*& start <= end &*& end <= length(bs) &*&
            is_char_boundary(bs, start) == true &*&
            is_char_boundary(bs, end) == true,
        Drain_dropped =>
            (*s).vec |-> ?v1 &*& std::vec::Vec(v1, _, ?bs1) &*& is_valid_utf8(bs1) == true
    };

pred<'a> <Drain<'a>>.own(t, d) =
    exists::<pair<i32, usize>>(pair(?gid, ?off)) &*&
    [1/2]ghost_cell::<Drain_state>(gid, Drain_active(?v, ?cap, ?buf, ?bs, d.start, d.end)) &*&
    full_borrow('a, Drain_fbc(gid, d.string)) &*&
    d.start <= off &*&
    0 <= d.iter.as_str().len() &*&
    off + d.iter.as_str().len() <= d.end &*&
    d.iter.as_str() as *u8 == buf + off &*&
    is_valid_utf8(take(d.iter.as_str().len(), drop(off, bs))) == true;

lem Drain_own_mono<'a0, 'a1>()
    req Drain_own::<'a0>(?t, ?v) &*& lifetime_inclusion('a1, 'a0) == true;
    ens Drain_own::<'a1>(t, Drain::<'a1> { string: v.string, start: upcast(v.start), end: upcast(v.end), iter: upcast(v.iter) });
{
    open <Drain<'a0>>.own(t, v);
    assert exists::<pair<i32, usize>>(pair(?gid, ?off));
    full_borrow_mono('a0, 'a1, Drain_fbc(gid, v.string));
    std::str::Chars_as_str_upcast::<'a0, 'a1>(v.iter);
    std::str::usize_upcast(v.start);
    std::str::usize_upcast(v.end);
    close exists::<pair<i32, usize>>(pair(gid, off));
    close <Drain<'a1>>.own(t, Drain::<'a1> { string: v.string, start: upcast(v.start), end: upcast(v.end), iter: upcast(v.iter) });
}

lem Drain_send<'a>(t1: thread_id_t)
    req Drain_own::<'a>(?t0, ?v);
    ens Drain_own::<'a>(t1, v);
{
    open <Drain<'a>>.own(t0, v);
    close <Drain<'a>>.own(t1, v);
}

pred_ctor Drain_share_fbc<'a>(l: *Drain<'a>, d: Drain<'a>)(;) =
    (*l).string |-> d.string &*& (*l).start |-> d.start &*& (*l).end |-> d.end &*& (*l).iter |-> d.iter &*&
    struct_Drain_padding(l);

pred<'a> <Drain<'a>>.share(k, t, l) =
    exists::<Drain<'a>>(?d) &*&
    [_]frac_borrow(k, Drain_share_fbc::<'a>(l, d));

lem Drain_share_full<'a>(k: lifetime_t, t: thread_id_t, l: *Drain<'a>)
    req atomic_mask(MaskTop) &*& full_borrow(k, Drain_full_borrow_content::<'a>(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(MaskTop) &*& [_]Drain_share::<'a>(k, t, l) &*& [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, Drain_full_borrow_content::<'a>(t, l), q);
    open Drain_full_borrow_content::<'a>(t, l)();
    assert (*l).string |-> ?s &*& (*l).start |-> ?st &*& (*l).end |-> ?en &*& (*l).iter |-> ?it;
    let d = Drain::<'a> { string: s, start: st, end: en, iter: it };
    close Drain_share_fbc::<'a>(l, d)();
    {
        pred Ctx() = <Drain<'a>>.own(t, d);
        produce_lem_ptr_chunk full_borrow_convert_strong(Ctx, Drain_share_fbc::<'a>(l, d), klong, Drain_full_borrow_content::<'a>(t, l))() {
            open Ctx();
            open Drain_share_fbc::<'a>(l, d)();
            close Drain_full_borrow_content::<'a>(t, l)();
        } {
            close Ctx();
            close_full_borrow_strong_m(klong, Drain_full_borrow_content::<'a>(t, l), Drain_share_fbc::<'a>(l, d));
            full_borrow_mono(klong, k, Drain_share_fbc::<'a>(l, d));
            full_borrow_into_frac_m(k, Drain_share_fbc::<'a>(l, d));
        }
    }
    close exists::<Drain<'a>>(d);
    close <Drain<'a>>.share(k, t, l);
    leak <Drain<'a>>.share(k, t, l);
}

lem Drain_share_mono<'a>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Drain<'a>)
    req lifetime_inclusion(k1, k) == true &*& [_]Drain_share::<'a>(k, t, l);
    ens [_]Drain_share::<'a>(k1, t, l);
{
    open Drain_share::<'a>(k, t, l);
    assert [_]exists::<Drain<'a>>(?d);
    frac_borrow_mono(k, k1, Drain_share_fbc::<'a>(l, d));
    close exists::<Drain<'a>>(d);
    close Drain_share::<'a>(k1, t, l);
    leak Drain_share::<'a>(k1, t, l);
}

lem init_ref_Drain<'a>(p: *Drain<'a>)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Drain_share::<'a>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Drain_share::<'a>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open Drain_share::<'a>(k, t, x);
    assert [_]exists::<Drain<'a>>(?d);
    let klong = open_frac_borrow_strong_m(k, Drain_share_fbc::<'a>(x, d), q);
    open [?f]Drain_share_fbc::<'a>(x, d)();
    open_ref_init_perm_Drain::<'a>(p);
    init_ref_readonly(&(*p).string, 1/2);
    init_ref_readonly(&(*p).start, 1/2);
    init_ref_readonly(&(*p).end, 1/2);
    init_ref_readonly(&(*p).iter, 1/2);
    init_ref_padding_Drain::<'a>(p, 1/2);
    close [f/2]Drain_share_fbc::<'a>(x, d)();
    close [f/2]Drain_share_fbc::<'a>(p, d)();
    close_ref_initialized_Drain::<'a>(p);
    close ref_initialized_::<Drain<'a>>(p)();
    {
        pred Ctx() =
            ref_readonly_end_token(&(*p).string, &(*x).string, f/2) &*&
            ref_readonly_end_token(&(*p).start, &(*x).start, f/2) &*&
            ref_readonly_end_token(&(*p).end, &(*x).end, f/2) &*&
            ref_readonly_end_token(&(*p).iter, &(*x).iter, f/2) &*&
            ref_padding_end_token(p, x, f/2) &*&
            [f/2]Drain_share_fbc::<'a>(x, d)();
        produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, sep(scaledp(f/2, Drain_share_fbc::<'a>(p, d)), ref_initialized_(p)), klong, f, Drain_share_fbc::<'a>(x, d))() {
            open Ctx();
            open sep(scaledp(f/2, Drain_share_fbc::<'a>(p, d)), ref_initialized_(p))();
            open scaledp(f/2, Drain_share_fbc::<'a>(p, d))();
            open ref_initialized_::<Drain<'a>>(p)();
            open_ref_initialized_Drain::<'a>(p);
            open [f/2]Drain_share_fbc::<'a>(p, d)();
            open [f/2]Drain_share_fbc::<'a>(x, d)();
            end_ref_readonly(&(*p).string);
            end_ref_readonly(&(*p).start);
            end_ref_readonly(&(*p).end);
            end_ref_readonly(&(*p).iter);
            end_ref_padding_Drain::<'a>(p);
            close [f]Drain_share_fbc::<'a>(x, d)();
        } {
            close Ctx();
            close scaledp(f/2, Drain_share_fbc::<'a>(p, d))();
            close sep(scaledp(f/2, Drain_share_fbc::<'a>(p, d)), ref_initialized_(p))();
            close_frac_borrow_strong_m();
            full_borrow_mono(klong, k, sep(scaledp(f/2, Drain_share_fbc::<'a>(p, d)), ref_initialized_(p)));
            full_borrow_split_m(k, scaledp(f/2, Drain_share_fbc::<'a>(p, d)), ref_initialized_(p));
            full_borrow_into_frac_m(k, scaledp(f/2, Drain_share_fbc::<'a>(p, d)));
            frac_borrow_implies_scaled(k, f/2, Drain_share_fbc::<'a>(p, d));
            full_borrow_into_frac_m(k, ref_initialized_(p));
        }
    }
    close exists::<Drain<'a>>(d);
    close Drain_share::<'a>(k, t, p);
    leak Drain_share::<'a>(k, t, p);
}

lem Drain_sync<'a>(t1: thread_id_t)
    req [_]Drain_share::<'a>(?k, ?t0, ?l);
    ens [_]Drain_share::<'a>(k, t1, l);
{
    open Drain_share::<'a>(k, t0, l);
    assert [_]exists::<Drain<'a>>(?d);
    close exists::<Drain<'a>>(d);
    close Drain_share::<'a>(k, t1, l);
    leak Drain_share::<'a>(k, t1, l);
}

@*/

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
        unsafe { Drain_drop__VeriFast_wrapper(self) }
    }
}

fn string_vec__VeriFast_wrapper(s: String) -> Vec<u8>
//@ req thread_token(?t) &*& <String>.own(t, s);
//@ ens thread_token(t) &*& std::vec::Vec(result, _, ?bs) &*& is_valid_utf8(bs) == true;
//@ on_unwind_ens false;
/*@
safety_proof {
    let result = call();
    if ignore_unwind_paths() {
        std::vec::Vec_u8_to_own(_t, result);
    } else {
        std::vec::Vec_u8_to_own(_t, fn_outcome_result(result));
    }
}
@*/
{
    //@ open <String>.own(t, s);
    s.vec
}

unsafe fn retain_next_char__VeriFast_wrapper(s: &str, idx: usize, len: usize) -> char
/*@
req [?f](s as *u8)[..s.len()] |-> ?bs &*& idx < len &*& len == s.len() &*&
    is_valid_utf8(drop(idx, bs)) == true;
@*/
/*@
ens [f](s as *u8)[..s.len()] |-> bs &*& is_unicode_scalar_value(result) == true &*&
    idx + char_len_utf8(result) <= len &*&
    char_utf8(result) == take(char_len_utf8(result), drop(idx, bs)) &*&
    is_valid_utf8(char_utf8(result)) == true &*&
    is_valid_utf8(drop(idx + char_len_utf8(result), bs)) == true;
@*/
//@ on_unwind_ens false;
{
    //@ is_char_boundary_from_valid_suffix(bs, idx);
    //@ length_drop(idx, bs);
    //@ utf8_first_scalar(drop(idx, bs));
    let ch = unsafe { s.get_unchecked(idx..len).chars().next().unwrap_unchecked() };
    //@ open [f]array(s as *u8 + len, 0, _);
    //@ array_join(s as *u8);
    //@ drop_twice(idx, char_len_utf8(ch), bs);
    ch
}

fn retain_call_predicate__VeriFast_wrapper<F: FnMut(char) -> bool>(f: &mut F, ch: char) -> bool
//@ req thread_token(?t) &*& *f |-> ?f0 &*& <F>.own(t, f0) &*& is_unicode_scalar_value(ch) == true;
//@ ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1);
//@ on_unwind_ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1);
/*@
safety_proof {
    open char_own(_t, ch);
    let result = call();
    if ignore_unwind_paths() {
        close bool_own(_t, result);
    } else {
        match result {
            returning(value) => { close bool_own(_t, value); }
            unwinding => {}
        }
    }
}
@*/
{
    //@ close char_own(t, ch);
    //@ close <(char,)>.own(t, std_tuple_1_::<char> { 0: ch });
    let keep = f(ch);
    //@ open bool_own(t, keep);
    keep
}

unsafe fn retain_write_char__VeriFast_wrapper(ch: char, buf: *mut u8, idx: usize, del: usize)
/*@
req buf[..?len] |-> ?bs &*& is_unicode_scalar_value(ch) == true &*&
    del <= idx &*& idx + char_len_utf8(ch) <= len;
@*/
/*@
ens buf[..len] |-> append(take(idx - del, bs),
        append(char_utf8(ch), drop(idx - del + char_len_utf8(ch), bs))) &*&
    is_valid_utf8(char_utf8(ch)) == true;
@*/
//@ on_unwind_ens false;
{
    //@ let ch_len = char_len_utf8(ch);
    //@ let offset = idx - del;
    //@ array_inv::<u8>();
    ch.encode_utf8(unsafe {
        let data = buf.add(idx - del);
        //@ array_split(buf, offset);
        //@ array_split(data, ch_len);
        //@ open array(data, ch_len, ?dst_before);
        //@ close array(data, ch_len, dst_before);
        //@ div_rem_nonneg(data as usize, 1);
        crate::slice::from_raw_parts_mut(data, ch.len_utf8())
    });
    //@ open array(buf + offset + ch_len, 0, _);
    //@ array_join(buf + offset);
    /*@
    if offset == 0 {
        open array(buf, 0, _);
    } else {
        array_join(buf);
    }
    @*/
    //@ drop_twice(offset, ch_len, bs);
}

/*@
inductive RemoveMatchesHaystack = RemoveMatchesHaystack(lifetime_t, usize, *u8, list<u8>, option<*String>);
@*/

unsafe fn remove_matches_searcher__VeriFast_wrapper<'a, P: Pattern>(
    pat: P,
    this: &'a String,
) -> P::Searcher<'a>
/*@
req thread_token(?t) &*& <P>.own(t, pat) &*& [?q]lifetime_token('a) &*&
    [_]frac_borrow('a, ref_initialized_(this)) &*&
    exists(String_share_info(?vec, ?cap, ?buf, ?bytes)) &*&
    [_]frac_borrow('a, String_header_fbc(this, vec, cap, length(bytes), buf)) &*&
    [_]frac_borrow('a, mk_array::<u8>(buf, length(bytes), bytes)) &*&
    is_valid_utf8(bytes) == true;
@*/
/*@
ens thread_token(t) &*& [q]lifetime_token('a) &*& str_share('a, t, ?haystack) &*&
    haystack as *u8 == buf &*& haystack.len() == length(bytes) &*&
    < <P as std::str::pattern::Pattern<'a>>::Searcher>.own(t, result) &*&
    std::str::pattern::SearcherPosition::< <P as std::str::pattern::Pattern<'a>>::Searcher>
        (t, result, haystack, bytes, 0);
@*/
//@ on_unwind_ens thread_token(t) &*& [q]lifetime_token('a) &*& str_share('a, t, ?haystack);
{
    //@ let len = length(bytes);
    //@ let storage = mk_array::<u8>(buf, len, bytes);
    //@ let header = String_header_fbc(this, vec, cap, len, buf);
    //@ frac_borrow_sep('a, header, storage);
    //@ open_frac_borrow('a, sep_(header, storage), q/2);
    //@ open [?f]sep_(header, storage)();
    //@ open [f]String_header_fbc(this, vec, cap, len, buf)();
    //@ open [f]mk_array::<u8>(buf, len, bytes)();
    let haystack: &str = this;
    //@ close [f]mk_array::<u8>(buf, len, bytes)();
    //@ close [f]String_header_fbc(this, vec, cap, len, buf)();
    //@ close [f]sep_(header, storage)();
    //@ close_frac_borrow(f, sep_(header, storage));
    //@ merge_fractions lifetime_token('a);
    //@ close exists(bytes);
    //@ close str_share('a, t, haystack);
    //@ close exists(bytes);
    pat.into_searcher/*@::<P, 'a> @*/(haystack)
}

unsafe fn remove_matches_chain__VeriFast_wrapper<'a>(
    iter: crate::vec::IntoIter<(usize, usize)>,
    front: usize,
    this: &'a String,
) -> core::iter::Chain<crate::vec::IntoIter<(usize, usize)>, core::iter::Once<(usize, usize)>>
/*@
req thread_token(?t) &*& std::iter::VecRejectionIter(t, iter, ?ranges) &*&
    [?q]lifetime_token('a) &*& exists(String_share_info(?vec, ?cap, ?buf, ?bytes)) &*&
    [_]frac_borrow('a, ref_initialized_(this)) &*&
    [_]frac_borrow('a, String_header_fbc(this, vec, cap, length(bytes), buf)) &*&
    [_]frac_borrow('a, mk_array::<u8>(buf, length(bytes), bytes)) &*&
    ordered_rejection_prefix(bytes, 0, front, ranges) == true &*&
    front <= length(bytes) &*& is_char_boundary(bytes, front) == true;
@*/
/*@
ens thread_token(t) &*& [q]lifetime_token('a) &*&
    std::iter::RejectionChain(t, result, ?all) &*& ordered_rejections(bytes, 0, all) == true;
@*/
//@ on_unwind_ens false;
{
    //@ let header = String_header_fbc(this, vec, cap, length(bytes), buf);
    //@ let storage = mk_array::<u8>(buf, length(bytes), bytes);
    //@ frac_borrow_sep('a, header, storage);
    //@ open_frac_borrow('a, sep_(header, storage), q/2);
    //@ open [?f]sep_(header, storage)();
    //@ open [f]String_header_fbc(this, vec, cap, length(bytes), buf)();
    //@ open [f]mk_array::<u8>(buf, length(bytes), bytes)();
    //@ std::vec::Vec_unseparate_elems(vec);
    let len = this.len();
    //@ std::vec::Vec_separate_elems(vec);
    //@ close [f]mk_array::<u8>(buf, length(bytes), bytes)();
    //@ close [f]String_header_fbc(this, vec, cap, length(bytes), buf)();
    //@ close [f]sep_(header, storage)();
    //@ close_frac_borrow(f, sep_(header, storage));
    //@ merge_fractions lifetime_token('a);
    let suffix = (front, len);
    //@ let terminal = suffix;
    //@ assert terminal.0 == front &*& terminal.1 == length(bytes);
    //@ close usize_own(t, front);
    //@ close usize_own(t, len);
    //@ usize_pair_own_of_fields(t, terminal);
    //@ record_rejection_suffix(bytes, 0, front, ranges, terminal);
    iter.chain(core::iter::once(suffix))
}

unsafe fn remove_matches_compact_rejections__VeriFast_wrapper(
    this: &mut String,
    rejections: core::iter::Chain<crate::vec::IntoIter<(usize, usize)>, core::iter::Once<(usize, usize)>>,
)
/*@
req thread_token(?t) &*& *this |-> ?s0 &*& std::vec::Vec(s0.vec, ?capacity, ?original) &*&
    is_valid_utf8(original) == true &*& std::iter::RejectionChain(t, rejections, ?ranges) &*&
    ordered_rejections(original, 0, ranges) == true;
@*/
//@ ens thread_token(t) &*& *this |-> ?s1 &*& <String>.own(t, s1);
//@ on_unwind_ens false;
{
    //@ open_points_to(this);
    //@ let buffer = std::vec::Vec_separate_buffer((*this).vec);
    let mut len = 0;
    let ptr = this.vec.as_mut_ptr();
    //@ close_points_to(this);
    //@ close exists::<usize>(0);

    for (start, end) in rejections {
        /*@
        inv thread_token(t) &*& *this |-> s0 &*&
            std::vec::Vec_minus_buffer(s0.vec, capacity, length(original), buffer) &*&
            buffer[..length(original)] |-> ?current &*& buffer[length(original)..capacity] |-> _ &*&
            iter |-> ?state &*& std::iter::RejectionChain(t, state, ?remaining) &*&
            exists::<usize>(?cursor) &*& ordered_rejections(original, cursor, remaining) == true &*&
            len <= cursor &*& cursor <= length(original) &*&
            is_valid_utf8(take(len, current)) == true &*& drop(cursor, current) == drop(cursor, original);
        @*/
        //@ open exists::<usize>(cursor);
        //@ assert remaining == cons(?range, ?tail);
        //@ leak <(usize, usize)>.own(t, range);
        //@ rejection_range_utf8(original, start, end);
        //@ drop_twice(cursor, start - cursor, original);
        //@ drop_twice(cursor, start - cursor, current);
        //@ drop_twice(cursor, end - cursor, original);
        //@ drop_twice(cursor, end - cursor, current);
        len = unsafe { remove_matches_compact__VeriFast_wrapper(ptr, len, start, end) };
        //@ close exists::<usize>(end);
    }
    //@ open exists::<usize>(_);
    //@ std::vec::Vec_unseparate_buffer(s0.vec);
    // SAFETY: `len` is less than or equal to the original length of the string.
    unsafe {
        remove_matches_set_len__VeriFast_wrapper(this, len);
    }
}

unsafe fn remove_matches_compact__VeriFast_wrapper(ptr: *mut u8, len: usize, start: usize, end: usize) -> usize
/*@
req ptr[..?n] |-> ?before &*& len <= start &*& start <= end &*& end <= n &*&
    is_valid_utf8(take(len, before)) == true &*& is_valid_utf8(take(end - start, drop(start, before))) == true;
@*/
/*@
ens ptr[..n] |-> ?after &*& result == len + (end - start) &*& result <= end &*&
    take(result, after) == append(take(len, before), take(end - start, drop(start, before))) &*&
    is_valid_utf8(take(result, after)) == true &*& drop(end, after) == drop(end, before);
@*/
//@ on_unwind_ens false;
{
    let count = end - start;
    //@ let prefix = take(len, before);
    //@ let payload = take(count, drop(start, before));
    //@ let output_prefix = append(prefix, payload);
    if start != len {
        // SAFETY: per Searcher::next:
        //
        // The stream of Match and Reject values up to a Done will
        // contain index ranges that are adjacent, non-overlapping,
        // covering the whole haystack, and laying on utf8
        // boundaries.
        unsafe {
            remove_matches_copy__VeriFast_wrapper(ptr, start, len, count);
        }
        //@ open exists::<list<u8>>(?middle);
        //@ append_assoc(prefix, payload, append(middle, drop(end, before)));
        //@ append_assoc(output_prefix, middle, drop(end, before));
        //@ split_appended(output_prefix, append(middle, drop(end, before)));
        //@ split_appended(append(output_prefix, middle), drop(end, before));
    } else {
        //@ append_take_drop_n(before, len);
        //@ append_take_drop_n(drop(len, before), count);
        //@ drop_twice(len, count, before);
        //@ append_assoc(prefix, payload, drop(end, before));
        //@ split_appended(output_prefix, drop(end, before));
    }
    //@ append_utf8(prefix, payload);
    let mut len = len;
    len += count;
    len
}

unsafe fn remove_matches_set_len__VeriFast_wrapper(this: &mut String, len: usize)
/*@
req thread_token(?t) &*& *this |-> ?s0 &*& std::vec::Vec(s0.vec, ?capacity, ?bytes) &*&
    len <= length(bytes) &*& is_valid_utf8(take(len, bytes)) == true;
@*/
//@ ens thread_token(t) &*& *this |-> ?s1 &*& <String>.own(t, s1);
//@ on_unwind_ens false;
{
    //@ open_points_to(this);
    //@ let buf = std::vec::Vec_separate_buffer((*this).vec);
    /*@
    if len < length(bytes) {
        array_split(buf, len);
        array_to_array_(buf + len);
        array__join(buf + len);
    }
    @*/
    unsafe { this.vec.set_len(len) };
    //@ std::vec::Vec_unseparate_buffer((*this).vec);
    //@ close_points_to(this);
    //@ assert *this |-> ?s1;
    //@ close <String>.own(t, s1);
}

unsafe fn remove_matches_copy__VeriFast_wrapper(ptr: *mut u8, start: usize, written: usize, count: usize)
/*@
req ptr[..?n] |-> ?before &*& written < start &*& start + count <= n;
@*/
/*@
ens ptr[..n] |-> ?after &*& exists::<list<u8>>(?middle) &*& length(middle) == start - written &*&
    after == append(take(written, before), append(take(count, drop(start, before)),
        append(middle, drop(start + count, before))));
@*/
//@ on_unwind_ens false;
{
    //@ close exists(ByteCopyRange(ptr, start, written));
    unsafe { copy_bytes_left__VeriFast_wrapper(ptr.add(start), ptr.add(written), count) };
}

unsafe fn copy_bytes_left__VeriFast_wrapper(src: *const u8, dst: *mut u8, count: usize)
/*@
req exists(ByteCopyRange(?ptr, ?start, ?written)) &*&
    ptr[..?n] |-> ?before &*& 0 <= written &*& written < start &*& start + count <= n &*&
    src == ptr + start &*& dst == ptr + written;
@*/
/*@
ens ptr[..n] |-> ?after &*& exists::<list<u8>>(?middle) &*& length(middle) == start - written &*&
    after == append(take(written, before), append(take(count, drop(start, before)),
        append(middle, drop(start + count, before))));
@*/
//@ on_unwind_ens false;
{
    //@ let distance = start - written;
    //@ let payload = take(count, drop(start, before));
    //@ array_split(ptr, written);
    /*@
    if distance <= count {
        array_split(ptr + written, distance);
        drop_twice(written, distance, before);
        array_split(ptr + start, count);
        close exists::<option<isize>>(some(-distance));
    } else {
        array_split(ptr + written, count);
        array_split(ptr + written + count, distance - count);
        drop_twice(written, count, before);
        drop_twice(written + count, distance - count, before);
        array_split(ptr + start, count);
        close exists::<option<isize>>(none);
    }
    @*/
    //@ drop_twice(start, count, before);
    //@ array_to_array_(ptr + start);
    //@ array_to_array_(ptr + written);
    unsafe { ptr::copy(src, dst, count) };
    //@ array__to_array(ptr + written, payload);
    /*@
    if distance <= count {
        let middle = drop(count - distance, payload);
        drop_mapped(count - distance, payload, some);
        array__to_array(ptr + written + count, middle);
        array_join(ptr + written + count);
        array_join(ptr + written);
        close exists(middle);
    } else {
        let gap = take(distance - count, drop(written + count, before));
        array__to_array(ptr + start, payload);
        if count == 0 {
            open array(ptr + start, 0, payload);
            open array(ptr + written, 0, payload);
        } else {
            array_join(ptr + start);
        }
        array_join(ptr + written + count);
        append_assoc(gap, payload, drop(start + count, before));
        if count != 0 {
            array_join(ptr + written);
        }
        close exists(append(gap, payload));
    }
    @*/
    /*@
    if written == 0 {
        open array(ptr, 0, take(written, before));
    } else {
        array_join(ptr);
    }
    @*/
}

unsafe fn Drain_drop__VeriFast_wrapper<'a>(this: &mut Drain<'a>)
/*@
req thread_token(?t) &*& [?q]lifetime_token('a) &*&
    Drain_full_borrow_content::<'a>(t, this)();
@*/
/*@
ens thread_token(t) &*& [q]lifetime_token('a) &*&
    (*this).string |-> ?s &*& (*this).start |-> ?st &*& (*this).end |-> ?en &*& (*this).iter |-> ?it &*&
    struct_Drain_padding(this);
@*/
//@ on_unwind_ens false;
{
    //@ open Drain_full_borrow_content::<'a>(t, this)();
    //@ assert (*this).string |-> ?s &*& (*this).start |-> ?st &*& (*this).end |-> ?en &*& (*this).iter |-> ?it;
    //@ open <Drain<'a>>.own(t, Drain::<'a> { string: s, start: st, end: en, iter: it });
    //@ assert exists::<pair<i32, usize>>(pair(?gid, ?off));
    //@ assert [1/2]ghost_cell::<Drain_state>(gid, Drain_active(?v, ?cap, ?buf, ?bs, st, en));
    //@ open_full_borrow(q, 'a, Drain_fbc(gid, s));
    //@ open Drain_fbc(gid, s)();
    // Use Vec::drain. "Reaffirm" the bounds checks to avoid
    // panic code being inserted again.
    // SAFETY: We only use the returned Vec to call drain.
    let self_vec = unsafe { &mut *(*this.string).as_mut_vec() };
    if this.start <= this.end && this.end <= { //~allow_dead_code
        //@ let vref = precreate_ref(self_vec);
        //@ std::vec::init_ref_Vec(vref);
        let vec_len = self_vec.len();
        //@ std::vec::end_ref_Vec(vref);
        vec_len
    } { //~allow_dead_code
        self_vec.drain(this.start..this.end);
        //@ split_utf8_at_boundary(bs, st);
        //@ split_utf8_at_boundary(bs, en);
        //@ append_utf8(take(st, bs), drop(en, bs));
    }
    //@ ghost_cell_mutate(gid, Drain_dropped);
    //@ close Drain_fbc(gid, s)();
    //@ close_full_borrow(Drain_fbc(gid, s));
    //@ leak full_borrow('a, Drain_fbc(gid, s)) &*& [1/2]ghost_cell::<Drain_state>(gid, Drain_dropped);
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
    fn next(&mut self) -> Option<char>
    //@ req thread_token(?t) &*& [?q]lifetime_token('_0) &*& *self |-> ?d0 &*& <Drain<'_0>>.own(t, d0);
    //@ ens thread_token(t) &*& [q]lifetime_token('_0) &*& *self |-> ?d1 &*& <Drain<'_0>>.own(t, d1) &*& <std::option::Option<char>>.own(t, result);
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        //@ open <Drain<'_0>>.own(t, d0);
        //@ assert exists::<pair<i32, usize>>(pair(?gid, ?off));
        //@ assert [1/2]ghost_cell::<Drain_state>(gid, Drain_active(?v, ?cap, ?buf, ?bs, d0.start, d0.end));
        //@ open_full_borrow(q, '_0, Drain_fbc(gid, d0.string));
        //@ open Drain_fbc(gid, d0.string)();
        //@ assert ghost_cell::<Drain_state>(gid, _);
        //@ let iter_len = d0.iter.as_str().len();
        //@ let buf_ = std::vec::Vec_separate_elems(v);
        //@ array_split(buf, off);
        //@ array_split(buf + off, iter_len);
        //@ drop_twice(off, iter_len, bs);
        //@ std::str::points_to_Chars_lft::<'_0, 'static>(&(*self).iter);
        let r = self.iter.next();
        //@ std::str::points_to_Chars_lft::<'static, '_0>(&(*self).iter as *std::str::Chars<'static>);
        //@ array_join(buf + off);
        //@ array_join(buf);
        //@ append_take_drop_n(drop(off, bs), iter_len);
        //@ append_take_drop_n(bs, off);
        //@ std::vec::Vec_unseparate_elems(v);
        //@ close Drain_fbc(gid, d0.string)();
        //@ close_full_borrow(Drain_fbc(gid, d0.string));
        //@ close_points_to(self);
        //@ assert *self |-> ?d1;
        /*@
        match r {
            Option::None => {
                close exists::<pair<i32, usize>>(pair(gid, off));
                close <std::option::Option<char>>.own(t, std::option::Option::None);
            }
            Option::Some(ch) => {
                let iter_bs = take(iter_len, drop(off, bs));
                utf8_first_scalar(iter_bs);
                let step = utf8_seq_len(head(iter_bs));
                drop_twice(off, step, bs);
                drop_take_commute(step, iter_len, drop(off, bs));
                close exists::<pair<i32, usize>>(pair(gid, off + step));
                close char_own(t, ch);
                close <std::option::Option<char>>.own(t, std::option::Option::Some(ch));
            }
        }
        @*/
        //@ close <Drain<'_0>>.own(t, d1);
        r
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
    fn next_back(&mut self) -> Option<char>
    //@ req thread_token(?t) &*& [?q]lifetime_token('_0) &*& *self |-> ?d0 &*& <Drain<'_0>>.own(t, d0);
    //@ ens thread_token(t) &*& [q]lifetime_token('_0) &*& *self |-> ?d1 &*& <Drain<'_0>>.own(t, d1) &*& <std::option::Option<char>>.own(t, result);
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        //@ open <Drain<'_0>>.own(t, d0);
        //@ assert exists::<pair<i32, usize>>(pair(?gid, ?off));
        //@ assert [1/2]ghost_cell::<Drain_state>(gid, Drain_active(?v, ?cap, ?buf, ?bs, d0.start, d0.end));
        //@ open_full_borrow(q, '_0, Drain_fbc(gid, d0.string));
        //@ open Drain_fbc(gid, d0.string)();
        //@ assert ghost_cell::<Drain_state>(gid, _);
        //@ let iter_len = d0.iter.as_str().len();
        //@ let buf_ = std::vec::Vec_separate_elems(v);
        //@ array_split(buf, off);
        //@ array_split(buf + off, iter_len);
        //@ drop_twice(off, iter_len, bs);
        //@ std::str::points_to_Chars_lft::<'_0, 'static>(&(*self).iter);
        let r = self.iter.next_back();
        //@ std::str::points_to_Chars_lft::<'static, '_0>(&(*self).iter as *std::str::Chars<'static>);
        //@ array_join(buf + off);
        //@ array_join(buf);
        //@ append_take_drop_n(drop(off, bs), iter_len);
        //@ append_take_drop_n(bs, off);
        //@ std::vec::Vec_unseparate_elems(v);
        //@ close Drain_fbc(gid, d0.string)();
        //@ close_full_borrow(Drain_fbc(gid, d0.string));
        //@ close_points_to(self);
        //@ assert *self |-> ?d1;
        /*@
        match r {
            Option::None => {
                close <std::option::Option<char>>.own(t, std::option::Option::None);
            }
            Option::Some(ch) => {
                take_twice(iter_len - char_len_utf8(ch), iter_len, drop(off, bs));
                close char_own(t, ch);
                close <std::option::Option<char>>.own(t, std::option::Option::Some(ch));
            }
        }
        @*/
        //@ close exists::<pair<i32, usize>>(pair(gid, off));
        //@ close <Drain<'_0>>.own(t, d1);
        r
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
    use core::kani;

    use super::String;
    const MAX_BYTES: usize = 8;
    const MAX_CAPACITY: usize = MAX_BYTES + 1;

    fn bounded_string(first: Option<char>, second: Option<char>) -> String {
        let len = first.map_or(0, char::len_utf8) + second.map_or(0, char::len_utf8);
        let spare = usize::from(kani::any::<u8>()).min(MAX_CAPACITY - len);
        let mut string = String::with_capacity(len + spare);
        if let Some(first) = first {
            string.push(first);
        }
        if let Some(second) = second {
            string.push(second);
        }
        string
    }

    #[inline(always)]
    fn check_remove(input: &str, idx: usize, removed: char, expected: &[u8]) {
        let mut string = String::from(input);
        kani::assert(string.remove(idx) == removed, "remove returns the selected scalar");
        kani::assert(string.as_bytes() == expected, "remove preserves the remaining bytes");
        kani::cover(true, "remove completes the selected case");
    }

    #[kani::proof]
    fn harness_string_remove() {
        match kani::any::<u8>() % 8 {
            0 => check_remove("abc", 0, 'a', b"bc"),
            1 => check_remove("aébc", 1, 'é', b"abc"),
            2 => check_remove("€ab", 0, '€', b"ab"),
            3 => check_remove("a🦀", 1, '🦀', b"a"),
            4 => check_remove("a", 0, 'a', b""),
            5 => check_remove("\0🐱é", 1, '🐱', "\0é".as_bytes()),
            6 => check_remove("xé€🦀", 3, '€', "xé🦀".as_bytes()),
            _ => check_remove("\u{10ffff}β", 0, '\u{10ffff}', "β".as_bytes()),
        }
    }

    #[kani::proof]
    fn harness_string_remove_arbitrary_scalar() {
        let scalar: char = kani::any();
        let mut bytes = kani::any::<[u8; 6]>().map(|byte| byte & 0x7f);
        let index = usize::from(kani::any::<u8>()).min(bytes.len() - 4);
        let width = scalar.encode_utf8(&mut bytes[index..index + 4]).len();
        // SAFETY: encode_utf8 writes one complete scalar. Every other byte is initialized ASCII.
        let mut string = unsafe { String::from_utf8_unchecked(bytes.to_vec()) };

        kani::assert(string.remove(index) == scalar, "remove returns the arbitrary scalar");
        kani::assert(string.len() == bytes.len() - width, "remove shortens by the scalar width");
        let output_index = usize::from(kani::any::<u8>()) % bytes.len();
        if let Some(&byte) = string.as_bytes().get(output_index) {
            let input_index =
                if output_index < index { output_index } else { output_index + width };
            kani::assert(byte == bytes[input_index], "remove preserves the remaining bytes");
        }
        kani::cover(output_index < string.len(), "check a byte in the result");
        kani::cover(width == 1, "remove a one-byte scalar");
        kani::cover(width == 2, "remove a two-byte scalar");
        kani::cover(width == 3, "remove a three-byte scalar");
        kani::cover(width == 4, "remove a four-byte scalar");
    }

    #[kani::proof]
    #[kani::should_panic]
    fn harness_string_remove_inside_char() {
        let scalar: char = kani::any();
        let scalar = if scalar.is_ascii() { 'é' } else { scalar };
        let mut string = bounded_string(Some(scalar), None);
        let index = 1 + usize::from(kani::any::<u8>()).min(string.len() - 2);
        kani::cover(index < string.len() && !string.is_char_boundary(index), "inside a scalar");
        string.remove(index);
    }

    #[kani::proof]
    #[kani::should_panic]
    fn harness_string_remove_at_end() {
        let mut string = bounded_string(kani::any(), None);
        let index = string.len();
        kani::cover(index == 0, "at the end of an empty string");
        kani::cover(index > 0, "at the end of a non-empty string");
        string.remove(index);
    }

    #[kani::proof]
    #[kani::should_panic]
    fn harness_string_remove_past_end() {
        let mut string = bounded_string(Some(kani::any()), None);
        let len = string.len();
        let index = (len + 1).saturating_add(kani::any::<usize>());
        kani::cover(index > len, "past the end of the string");
        string.remove(index);
    }

    #[kani::proof]
    fn harness_string_into_boxed_str() {
        let string = bounded_string(kani::any(), kani::any());
        let capacity = string.capacity();
        let len = string.len();
        let index = usize::from(kani::any::<u8>()) % MAX_BYTES;
        let byte = string.as_bytes().get(index).copied();
        let boxed = string.into_boxed_str();

        kani::assert(boxed.len() == len, "boxing preserves the length");
        kani::assert(boxed.as_bytes().get(index).copied() == byte, "boxing preserves the bytes");
        kani::cover(index < len, "check an initialized byte after boxing");
        kani::cover(capacity == 0, "box an empty allocation");
        kani::cover(capacity == len && len > 0, "box a full allocation");
        kani::cover(capacity > len && len > 0, "shrink the allocation before boxing");
    }
}
