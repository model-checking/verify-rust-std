//! Utilities for the `str` primitive type.
//!
//! *[See also the `str` primitive type](str).*

#![stable(feature = "rust1", since = "1.0.0")]
// Many of the usings in this module are only used in the test configuration.
// It's cleaner to just turn off the unused_imports warning than to fix them.
#![allow(unused_imports)]

use core::borrow::{Borrow, BorrowMut};
use core::iter::FusedIterator;
use core::mem::MaybeUninit;
#[stable(feature = "encode_utf16", since = "1.8.0")]
pub use core::str::EncodeUtf16;
#[stable(feature = "split_ascii_whitespace", since = "1.34.0")]
pub use core::str::SplitAsciiWhitespace;
#[stable(feature = "split_inclusive", since = "1.51.0")]
pub use core::str::SplitInclusive;
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::SplitWhitespace;
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::pattern;
use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher, Utf8Pattern};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{Bytes, CharIndices, Chars, from_utf8, from_utf8_mut};
#[stable(feature = "str_escape", since = "1.34.0")]
pub use core::str::{EscapeDebug, EscapeDefault, EscapeUnicode};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{FromStr, Utf8Error};
#[allow(deprecated)]
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{Lines, LinesAny};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{MatchIndices, RMatchIndices};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{Matches, RMatches};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{ParseBoolError, from_utf8_unchecked, from_utf8_unchecked_mut};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{RSplit, Split};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{RSplitN, SplitN};
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::str::{RSplitTerminator, SplitTerminator};
#[stable(feature = "utf8_chunks", since = "1.79.0")]
pub use core::str::{Utf8Chunk, Utf8Chunks};
#[unstable(feature = "str_from_raw_parts", issue = "119206")]
pub use core::str::{from_raw_parts, from_raw_parts_mut};
use core::unicode::conversions;
use core::{mem, ptr};

use crate::borrow::ToOwned;
use crate::boxed::Box;
use crate::slice::{Concat, Join, SliceIndex};
use crate::string::String;
use crate::vec::Vec;

/// Note: `str` in `Concat<str>` is not meaningful here.
/// This type parameter of the trait only exists to enable another impl.
#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "slice_concat_ext", issue = "27747")]
impl<S: Borrow<str>> Concat<str> for [S] {
    type Output = String;

    fn concat(slice: &Self) -> String {
        Join::join(slice, "")
    }
}

#[cfg(not(no_global_oom_handling))]
#[unstable(feature = "slice_concat_ext", issue = "27747")]
impl<S: Borrow<str>> Join<&str> for [S] {
    type Output = String;

    fn join(slice: &Self, sep: &str) -> String {
        // ignore-tidy-undocumented-unsafe
        unsafe { String::from_utf8_unchecked(join_generic_copy(slice, sep.as_bytes())) }
    }
}

#[cfg(not(no_global_oom_handling))]
macro_rules! specialize_for_lengths {
    ($separator:expr, $target:expr, $iter:expr; $($num:expr),*) => {{
        let mut target = $target;
        let iter = $iter;
        let sep_bytes = $separator;
        match $separator.len() {
            $(
                // loops with hardcoded sizes run much faster
                // specialize the cases with small separator lengths
                $num => {
                    for s in iter {
                        copy_slice_and_advance!(target, sep_bytes);
                        let content_bytes = s.borrow().as_ref();
                        copy_slice_and_advance!(target, content_bytes);
                    }
                },
            )*
            _ => {
                // arbitrary non-zero size fallback
                for s in iter {
                    copy_slice_and_advance!(target, sep_bytes);
                    let content_bytes = s.borrow().as_ref();
                    copy_slice_and_advance!(target, content_bytes);
                }
            }
        }
        target
    }}
}

#[cfg(not(no_global_oom_handling))]
macro_rules! copy_slice_and_advance {
    ($target:expr, $bytes:expr) => {
        let len = $bytes.len();
        let (head, tail) = { $target }.split_at_mut(len);
        head.copy_from_slice($bytes);
        $target = tail;
    };
}

// Optimized join implementation that works for both Vec<T> (T: Copy) and String's inner vec
// Currently (2018-05-13) there is a bug with type inference and specialization (see issue #36262)
// For this reason SliceConcat<T> is not specialized for T: Copy and SliceConcat<str> is the
// only user of this function. It is left in place for the time when that is fixed.
//
// the bounds for String-join are S: Borrow<str> and for Vec-join Borrow<[T]>
// [T] and str both impl AsRef<[T]> for some T
// => s.borrow().as_ref() and we always have slices
//
// # Safety notes
//
// `Borrow` is a safe trait, and implementations are not required
// to be deterministic. An inconsistent `Borrow` implementation could return slices
// of different lengths on consecutive calls (e.g. by using interior mutability).
//
// This implementation calls `borrow()` multiple times:
// 1. To calculate `reserved_len`, all elements are borrowed once.
// 2. All elements, except the first, are borrowed a second time when building the mapped iterator.
//
// Risks and Mitigations:
// - If elements 2..N GROW on their second borrow, the target slice bounds set by `checked_sub`
//   means that `split_at_mut` inside `copy_slice_and_advance!` will correctly panic.
// - If elements SHRINK on their second borrow, the spare space is never written, and the final
//   length set via `set_len` masks trailing uninitialized bytes.
#[cfg(not(no_global_oom_handling))]
fn join_generic_copy<B, T, S>(slice: &[S], sep: &[T]) -> Vec<T>
where
    T: Copy,
    B: AsRef<[T]> + ?Sized,
    S: Borrow<B>,
{
    let sep_len = sep.len();
    let mut iter = slice.iter();

    // the first slice is the only one without a separator preceding it
    // we take care to only borrow this once during the length calculation
    // to avoid inconsistent Borrow implementations from breaking our assumptions
    let first = match iter.next() {
        Some(first) => first.borrow().as_ref(),
        None => return vec![],
    };

    // compute the exact total length of the joined Vec
    // if the `len` calculation overflows, we'll panic
    // we would have run out of memory anyway and the rest of the function requires
    // the entire Vec pre-allocated for safety
    let reserved_len = sep_len
        .checked_mul(iter.len())
        .and_then(|n| n.checked_add(first.len()))
        .and_then(|n| {
            // iter starts from the second element as we've already taken the first
            // it's cloned so we can reuse the same iterator below
            iter.clone().map(|s| s.borrow().as_ref().len()).try_fold(n, usize::checked_add)
        })
        .expect("attempt to join into collection with len > usize::MAX");

    // prepare an uninitialized buffer
    let mut result = Vec::with_capacity(reserved_len);
    debug_assert!(result.capacity() >= reserved_len);

    result.extend_from_slice(first);

    let pos = result.len();
    debug_assert!(reserved_len >= pos);
    // ignore-tidy-undocumented-unsafe
    unsafe {
        let target = result.spare_capacity_mut().get_unchecked_mut(..reserved_len - pos);

        // Convert the separator and slices to slices of MaybeUninit
        // to simplify implementation in specialize_for_lengths.
        let sep_uninit = core::slice::from_raw_parts(sep.as_ptr().cast(), sep.len());
        let iter_uninit = iter.map(|it| {
            let it = it.borrow().as_ref();
            core::slice::from_raw_parts(it.as_ptr().cast(), it.len())
        });

        // copy separator and slices over without bounds checks.
        // `specialize_for_lengths!` internally calls `s.borrow()`, but because it uses
        // the bounds-checked `split_at_mut` any misbehaving implementation
        // will not write out of bounds.
        let remain = specialize_for_lengths!(sep_uninit, target, iter_uninit; 0, 1, 2, 3, 4);

        // A weird borrow implementation may return different
        // slices for the length calculation and the actual copy.
        // Make sure we don't expose uninitialized bytes to the caller.
        let result_len = reserved_len - remain.len();
        result.set_len(result_len);
    }
    result
}

/// Helper for final sigma lowercase
#[cfg(not(no_global_oom_handling))]
fn map_uppercase_sigma(from: &str, i: usize) -> char {
    fn case_ignorable_then_cased<I: Iterator<Item = char>>(iter: I) -> bool {
        match iter.skip_while(|&c| c.is_case_ignorable()).next() {
            Some(c) => c.is_cased(),
            None => false,
        }
    }

    // See https://www.unicode.org/versions/latest/core-spec/chapter-3/#G54277
    // for the definition of `Final_Sigma`.
    let is_word_final = case_ignorable_then_cased(from[..i].chars().rev())
        && !case_ignorable_then_cased(from[i + const { 'Σ'.len_utf8() }..].chars());
    if is_word_final { 'ς' } else { 'σ' }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Borrow<str> for String {
    #[inline]
    fn borrow(&self) -> &str {
        &self[..]
    }
}

#[stable(feature = "string_borrow_mut", since = "1.36.0")]
impl BorrowMut<str> for String {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        &mut self[..]
    }
}

#[cfg(not(no_global_oom_handling))]
#[stable(feature = "rust1", since = "1.0.0")]
impl ToOwned for str {
    type Owned = String;

    #[inline]
    fn to_owned(&self) -> String {
        // ignore-tidy-undocumented-unsafe
        unsafe { String::from_utf8_unchecked(self.as_bytes().to_owned()) }
    }

    #[inline]
    fn clone_into(&self, target: &mut String) {
        target.clear();
        target.push_str(self);
    }
}

/// Methods for string slices.
impl str {
    /// Converts a `Box<str>` into a `Box<[u8]>` without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = "this is a string";
    /// let boxed_str = s.to_owned().into_boxed_str();
    /// let boxed_bytes = boxed_str.into_boxed_bytes();
    /// assert_eq!(*boxed_bytes, *s.as_bytes());
    /// ```
    #[rustc_allow_incoherent_impl]
    #[stable(feature = "str_box_extras", since = "1.20.0")]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[inline]
    pub fn into_boxed_bytes(self: Box<Self>) -> Box<[u8]> {
        self.into()
    }

    /// Replaces all matches of a pattern with another string.
    ///
    /// `replace` creates a new [`String`], and copies the data from this string slice into it.
    /// While doing so, it attempts to find matches of a pattern. If it finds any, it
    /// replaces them with the replacement string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = "this is old";
    ///
    /// assert_eq!("this is new", s.replace("old", "new"));
    /// assert_eq!("than an old", s.replace("is", "an"));
    /// ```
    ///
    /// When the pattern doesn't match, it returns this string slice as [`String`]:
    ///
    /// ```
    /// let s = "this is old";
    /// assert_eq!(s, s.replace("cookie monster", "little lamb"));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use = "this returns the replaced string as a new allocation, \
                  without modifying the original"]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn replace<P: Pattern>(&self, from: P, to: &str) -> String {
        // Fast path for replacing a single ASCII character with another.
        if let Some(from_byte) = match from.as_utf8_pattern() {
            Some(Utf8Pattern::StringPattern(s)) => match s.as_bytes() {
                [from_byte] => Some(*from_byte),
                _ => None,
            },
            Some(Utf8Pattern::CharPattern(c)) => c.as_ascii().map(|ascii_char| ascii_char.to_u8()),
            _ => None,
        } {
            if let [to_byte] = to.as_bytes() {
                // ignore-tidy-undocumented-unsafe
                return unsafe { replace_ascii(self.as_bytes(), from_byte, *to_byte) };
            }
        }
        // Set result capacity to self.len() when from.len() <= to.len()
        let default_capacity = match from.as_utf8_pattern() {
            Some(Utf8Pattern::StringPattern(s)) if s.len() <= to.len() => self.len(),
            Some(Utf8Pattern::CharPattern(c)) if c.len_utf8() <= to.len() => self.len(),
            _ => 0,
        };
        let mut result = String::with_capacity(default_capacity);
        let mut last_end = 0;
        for (start, part) in self.match_indices(from) {
            // ignore-tidy-undocumented-unsafe
            result.push_str(unsafe { self.get_unchecked(last_end..start) });
            result.push_str(to);
            last_end = start + part.len();
        }
        // ignore-tidy-undocumented-unsafe
        result.push_str(unsafe { self.get_unchecked(last_end..self.len()) });
        result
    }

    /// Replaces first N matches of a pattern with another string.
    ///
    /// `replacen` creates a new [`String`], and copies the data from this string slice into it.
    /// While doing so, it attempts to find matches of a pattern. If it finds any, it
    /// replaces them with the replacement string slice at most `count` times.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = "foo foo 123 foo";
    /// assert_eq!("new new 123 foo", s.replacen("foo", "new", 2));
    /// assert_eq!("faa fao 123 foo", s.replacen('o', "a", 3));
    /// assert_eq!("foo foo new23 foo", s.replacen(char::is_numeric, "new", 1));
    /// ```
    ///
    /// When the pattern doesn't match, it returns this string slice as [`String`]:
    ///
    /// ```
    /// let s = "this is old";
    /// assert_eq!(s, s.replacen("cookie monster", "little lamb", 10));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[doc(alias = "replace_first")]
    #[must_use = "this returns the replaced string as a new allocation, \
                  without modifying the original"]
    #[stable(feature = "str_replacen", since = "1.16.0")]
    pub fn replacen<P: Pattern>(&self, pat: P, to: &str, count: usize) -> String {
        // Hope to reduce the times of re-allocation
        let mut result = String::with_capacity(32);
        let mut last_end = 0;
        for (start, part) in self.match_indices(pat).take(count) {
            // ignore-tidy-undocumented-unsafe
            result.push_str(unsafe { self.get_unchecked(last_end..start) });
            result.push_str(to);
            last_end = start + part.len();
        }
        // ignore-tidy-undocumented-unsafe
        result.push_str(unsafe { self.get_unchecked(last_end..self.len()) });
        result
    }

    /// Returns the lowercase equivalent of this string slice, as a new [`String`].
    ///
    /// 'Lowercase' is defined according to the terms of
    /// [Chapter 3 (Conformance)](https://www.unicode.org/versions/latest/core-spec/chapter-3/#G34432)
    /// of the Unicode standard.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [`String`] instead of modifying the
    /// parameter in-place.
    ///
    /// Unlike [`char::to_lowercase()`], this method fully handles the context-dependent
    /// casing of Greek sigma. However, like that method, it does not handle locale-specific
    /// casing, like Turkish and Azeri I/ı/İ/i. See its documentation
    /// for more information.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = "HELLO WORLD";
    ///
    /// assert_eq!("hello world", s.to_lowercase());
    /// ```
    ///
    /// Tricky examples, with sigma:
    ///
    /// ```
    /// let sigma = "Σ";
    ///
    /// assert_eq!("σ", sigma.to_lowercase());
    ///
    /// // but at the end of a word, it's ς, not σ:
    /// let odysseus = "ὈΔΥΣΣΕΎΣ";
    ///
    /// assert_eq!("ὀδυσσεύς", odysseus.to_lowercase());
    ///
    /// let odysseus_king_of_ithaca = "Ο ΟΔΥΣΣΈΑΣ ΒΑΣΙΛΙΆΣ ΤΗΣ ΙΘΆΚΗΣ";
    ///
    /// assert_eq!("ο οδυσσέας βασιλιάς της ιθάκης", odysseus_king_of_ithaca.to_lowercase());
    /// ```
    ///
    /// Languages without case are not changed:
    ///
    /// ```
    /// let new_year = "农历新年";
    ///
    /// assert_eq!(new_year, new_year.to_lowercase());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use = "this returns the lowercase string as a new String, \
                  without modifying the original"]
    #[stable(feature = "unicode_case_mapping", since = "1.2.0")]
    pub fn to_lowercase(&self) -> String {
        // SAFETY: `to_ascii_lowercase` preserves ASCII bytes, so the converted
        // prefix remains valid UTF-8.
        let (mut s, rest) = unsafe { convert_while_ascii(self, u8::to_ascii_lowercase) };

        let prefix_len = s.len();

        for (i, c) in rest.char_indices() {
            if c == 'Σ' {
                // Σ maps to σ, except at the end of a word where it maps to ς.
                // This is the only conditional (contextual) but language-independent mapping
                // in `SpecialCasing.txt`,
                // so hard-code it rather than have a generic "condition" mechanism.
                // See https://github.com/rust-lang/rust/issues/26035
                let sigma_lowercase = map_uppercase_sigma(self, prefix_len + i);
                s.push(sigma_lowercase);
            } else {
                match conversions::to_lower(c) {
                    [a, '\0', _] => s.push(a),
                    [a, b, '\0'] => {
                        s.push(a);
                        s.push(b);
                    }
                    [a, b, c] => {
                        s.push(a);
                        s.push(b);
                        s.push(c);
                    }
                }
            }
        }
        s
    }

    /// Returns the titlecase equivalent of this string slice,
    /// which is assumed to represent a single word,
    /// as a new [`String`].
    ///
    /// Essentially, this consists of uppercasing the first cased letter
    /// (with [`char::to_titlecase()`]), and lowercasing everything that follows.
    ///
    /// 'Titlecase' is defined according to the terms of
    /// [Chapter 3 (Conformance)](https://www.unicode.org/versions/latest/core-spec/chapter-3/#G34082)
    /// of the Unicode standard.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [`String`] instead of modifying the
    /// parameter in-place.
    ///
    /// Unlike [`char::to_lowercase()`], this method fully handles the context-dependent
    /// casing of Greek sigma. However, like that method, it does not handle locale-specific
    /// casing, like Turkish and Azeri I/ı/İ/i. See its documentation
    /// for more information.
    ///
    /// This method does not perform any kind of word segmentation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(titlecase)]
    /// let s = "HELLO WORLD";
    ///
    /// assert_eq!("Hello world", s.word_to_titlecase());
    /// ```
    ///
    /// The first *cased* letter is uppercased:
    ///
    /// ```
    /// #![feature(titlecase)]
    /// let the_night_before_christmas = "'twas";
    ///
    /// assert_eq!("'Twas", the_night_before_christmas.word_to_titlecase());
    /// ```
    ///
    /// Languages without case are not changed:
    ///
    /// ```
    /// #![feature(titlecase)]
    /// let new_year = "农历新年";
    ///
    /// assert_eq!(new_year, new_year.word_to_titlecase());
    /// ```
    ///
    /// Georgian uppercase ("Mtavruli") letters are not used in titlecase:
    ///
    /// ```
    /// #![feature(titlecase)]
    /// let georgian = "ერთობაშია";
    ///
    /// assert_eq!(georgian, georgian.word_to_titlecase());
    /// ```
    ///
    /// No word segmentation is performed,
    /// so only the first cased letter in the whole string gets uppercased:
    ///
    /// ```
    /// #![feature(titlecase)]
    /// let blazingly_fast = "ferris and I";
    ///
    /// assert_eq!("Ferris and i", blazingly_fast.word_to_titlecase());
    /// ```
    ///
    /// Tricky examples, with sigma:
    ///
    /// ```
    /// #![feature(titlecase)]
    /// let odysseus = "ὈΔΥΣΣΕΎΣ";
    ///
    /// assert_eq!("Ὀδυσσεύς", odysseus.word_to_titlecase());
    ///
    /// let odysseus_king_of_ithaca = "Ο ΟΔΥΣΣΈΑΣ ΒΑΣΙΛΙΆΣ ΤΗΣ ΙΘΆΚΗΣ";
    ///
    /// assert_eq!("Ο οδυσσέας βασιλιάς της ιθάκης", odysseus_king_of_ithaca.word_to_titlecase());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use = "this returns the titlecase word as a new String, \
                  without modifying the original"]
    #[unstable(feature = "titlecase", issue = "153892")]
    pub fn word_to_titlecase(&self) -> String {
        let mut s = String::with_capacity(self.len());
        let mut chars = self.char_indices();

        // The first cased character is title-cased; leading uncased characters pass through.
        'until_first_cased_char: for (_, c) in chars.by_ref() {
            if c.is_cased() {
                s.extend(c.to_titlecase());
                break 'until_first_cased_char;
            } else {
                s.push(c);
            }
        }

        // Everything after the first cased character is lower-cased. Use the ASCII fast
        // path (auto-vectorized) for its ASCII prefix, mirroring `to_lowercase`.
        let remainder = chars.as_str();
        let rest_start = self.len() - remainder.len();
        // SAFETY: `to_ascii_lowercase` preserves ASCII bytes, so the prefix stays valid UTF-8.
        let (ascii, rest) = unsafe { convert_while_ascii(remainder, u8::to_ascii_lowercase) };
        s.push_str(&ascii);
        let prefix_len = rest_start + ascii.len();

        for (i, c) in rest.char_indices() {
            if c == 'Σ' {
                // Σ maps to σ, except at the end of a word where it maps to ς.
                // This is the only conditional (contextual) but language-independent mapping
                // in `SpecialCasing.txt`,
                // so hard-code it rather than have a generic "condition" mechanism.
                // See https://github.com/rust-lang/rust/issues/26035
                let sigma_lowercase = map_uppercase_sigma(self, prefix_len + i);
                s.push(sigma_lowercase);
            } else {
                match conversions::to_lower(c) {
                    [a, '\0', _] => s.push(a),
                    [a, b, '\0'] => {
                        s.push(a);
                        s.push(b);
                    }
                    [a, b, c] => {
                        s.push(a);
                        s.push(b);
                        s.push(c);
                    }
                }
            }
        }

        s
    }

    /// Returns the uppercase equivalent of this string slice, as a new [`String`].
    ///
    /// 'Uppercase' is defined according to the terms of
    /// [Chapter 3 (Conformance)](https://www.unicode.org/versions/latest/core-spec/chapter-3/#G34431)
    /// of the Unicode standard.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [`String`] instead of modifying the
    /// parameter in-place.
    ///
    /// Like [`char::to_uppercase()`] this method does not handle language-specific
    /// casing, like Turkish and Azeri I/ı/İ/i. See that method's documentation
    /// for more information.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = "hello world";
    ///
    /// assert_eq!("HELLO WORLD", s.to_uppercase());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// let new_year = "农历新年";
    ///
    /// assert_eq!(new_year, new_year.to_uppercase());
    /// ```
    ///
    /// One character can become multiple:
    /// ```
    /// let s = "tschüß";
    ///
    /// assert_eq!("TSCHÜSS", s.to_uppercase());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use = "this returns the uppercase string as a new String, \
                  without modifying the original"]
    #[stable(feature = "unicode_case_mapping", since = "1.2.0")]
    pub fn to_uppercase(&self) -> String {
        // SAFETY: `to_ascii_uppercase` preserves ASCII bytes, so the converted
        // prefix remains valid UTF-8.
        let (mut s, rest) = unsafe { convert_while_ascii(self, u8::to_ascii_uppercase) };

        for c in rest.chars() {
            match conversions::to_upper(c) {
                [a, '\0', _] => s.push(a),
                [a, b, '\0'] => {
                    s.push(a);
                    s.push(b);
                }
                [a, b, c] => {
                    s.push(a);
                    s.push(b);
                    s.push(c);
                }
            }
        }
        s
    }

    /// Returns the case-folded equivalent of this string slice, as a new [`String`].
    ///
    /// Case folding is a transformation, mostly matching lowercase, that is meant to be used
    /// for case-insensitive string comparisons. Case-folded strings should not usually
    /// be exposed directly to users.
    ///
    /// For the precise specification of case folding, see
    /// [Chapter 3 (Conformance)](https://www.unicode.org/versions/latest/core-spec/chapter-3/#G63737)
    /// of the Unicode standard.
    ///
    /// Since some characters can expand into multiple characters when case folding,
    /// this function returns a [`String`] instead of modifying the parameter in-place.
    ///
    /// No [normalization] (e.g. NFC) is performed, so visually and semantically identical strings
    /// might still casefold differently. For example, `"Å"` (U+00C5 LATIN CAPITAL LETTER A WITH RING ABOVE)
    /// is considered distinct from `"Å"` (A followed by U+030A COMBINING RING ABOVE),
    /// even though Unicode considers them canonically equivalent.
    ///
    /// Like [`char::to_casefold_unnormalized()`] this method does not handle language-specific
    /// casing, like Turkish and Azeri I/ı/İ/i. See that method's documentation
    /// for more information.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(casefold)]
    /// let s0 = "HELLO";
    /// let s1 = "Hello";
    ///
    /// assert_eq!(s0.to_casefold_unnormalized(), s1.to_casefold_unnormalized());
    /// assert_eq!(s0.to_casefold_unnormalized(), "hello")
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// #![feature(casefold)]
    /// let new_year = "农历新年";
    ///
    /// assert_eq!(new_year, new_year.to_casefold_unnormalized());
    /// ```
    ///
    /// One character can become multiple:
    ///
    /// ```
    /// #![feature(casefold)]
    /// let s0 = "TSCHÜẞ";
    /// let s1 = "TSCHÜSS";
    /// let s2 = "tschüß";
    ///
    /// assert_eq!(s0.to_casefold_unnormalized(), s1.to_casefold_unnormalized());
    /// assert_eq!(s0.to_casefold_unnormalized(), s2.to_casefold_unnormalized());
    /// assert_eq!(s0.to_casefold_unnormalized(), "tschüss");
    /// ```
    ///
    /// No NFC [normalization] is performed:
    ///
    /// ```rust
    /// #![feature(casefold)]
    /// // These two strings are visually and semantically identical...
    /// let comp = "Å";
    /// let decomp = "Å";
    ///
    /// // ... but not codepoint-for-codepoint equal.
    /// assert_eq!(comp, "\u{C5}");
    /// assert_eq!(decomp, "A\u{030A}");
    ///
    /// // Their case-foldings are likewise unequal:
    /// assert_eq!(comp.to_casefold_unnormalized(), "\u{E5}");
    /// assert_eq!(decomp.to_casefold_unnormalized(), "a\u{030A}");
    /// ```
    ///
    /// [normalization]: https://www.unicode.org/faq/normalization.html
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use = "this returns the case-folded string as a new String, \
                  without modifying the original"]
    #[unstable(feature = "casefold", issue = "157000")]
    pub fn to_casefold_unnormalized(&self) -> String {
        // SAFETY: `to_ascii_lowercase` preserves ASCII bytes, so the converted
        // prefix remains valid UTF-8.
        let (mut s, rest) = unsafe { convert_while_ascii(self, u8::to_ascii_lowercase) };

        for c in rest.chars() {
            match conversions::to_casefold(c) {
                [a, '\0', _] => s.push(a),
                [a, b, '\0'] => {
                    s.push(a);
                    s.push(b);
                }
                [a, b, c] => {
                    s.push(a);
                    s.push(b);
                    s.push(c);
                }
            }
        }
        s
    }

    /// Converts a [`Box<str>`] into a [`String`] without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// let string = String::from("birthday gift");
    /// let boxed_str = string.clone().into_boxed_str();
    ///
    /// assert_eq!(boxed_str.into_string(), string);
    /// ```
    #[stable(feature = "box_str", since = "1.4.0")]
    #[rustc_allow_incoherent_impl]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[inline]
    pub fn into_string(self: Box<Self>) -> String {
        let slice = Box::<[u8]>::from(self);
        // ignore-tidy-undocumented-unsafe
        unsafe { String::from_utf8_unchecked(slice.into_vec()) }
    }

    /// Creates a new [`String`] by repeating a string `n` times.
    ///
    /// # Panics
    ///
    /// This function will panic if the capacity would overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// assert_eq!("abc".repeat(4), String::from("abcabcabcabc"));
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// // this will panic at runtime
    /// let huge = "0123456789abcdef".repeat(usize::MAX);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use]
    #[stable(feature = "repeat_str", since = "1.16.0")]
    #[inline]
    pub fn repeat(&self, n: usize) -> String {
        // ignore-tidy-undocumented-unsafe
        unsafe { String::from_utf8_unchecked(self.as_bytes().repeat(n)) }
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII upper case equivalent.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To uppercase the value in-place, use [`make_ascii_uppercase`].
    ///
    /// To uppercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_uppercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// let s = "Grüße, Jürgen ❤";
    ///
    /// assert_eq!("GRüßE, JüRGEN ❤", s.to_ascii_uppercase());
    /// ```
    ///
    /// [`make_ascii_uppercase`]: str::make_ascii_uppercase
    /// [`to_uppercase`]: #method.to_uppercase
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use = "to uppercase the value in-place, use `make_ascii_uppercase()`"]
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[inline]
    pub fn to_ascii_uppercase(&self) -> String {
        let bytes = self.as_bytes().to_ascii_uppercase();
        // SAFETY: ASCII case conversion only maps a-z to A-Z and leaves
        // all other bytes unchanged as valid UTF-8
        unsafe { String::from_utf8_unchecked(bytes) }
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// To lowercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_lowercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// let s = "Grüße, Jürgen ❤";
    ///
    /// assert_eq!("grüße, jürgen ❤", s.to_ascii_lowercase());
    /// ```
    ///
    /// [`make_ascii_lowercase`]: str::make_ascii_lowercase
    /// [`to_lowercase`]: #method.to_lowercase
    #[cfg(not(no_global_oom_handling))]
    #[rustc_allow_incoherent_impl]
    #[must_use = "to lowercase the value in-place, use `make_ascii_lowercase()`"]
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[inline]
    pub fn to_ascii_lowercase(&self) -> String {
        let bytes = self.as_bytes().to_ascii_lowercase();
        // SAFETY: ASCII case conversion only maps A-Z to a-z and leaves
        // all other bytes unchanged as valid UTF-8
        unsafe { String::from_utf8_unchecked(bytes) }
    }
}

/// Converts a boxed slice of bytes to a boxed string slice without checking
/// that the string contains valid UTF-8.
///
/// # Safety
///
/// * The provided bytes must contain a valid UTF-8 sequence.
///
/// # Examples
///
/// ```
/// let smile_utf8 = Box::new([226, 152, 186]);
/// let smile = unsafe { std::str::from_boxed_utf8_unchecked(smile_utf8) };
///
/// assert_eq!("☺", &*smile);
/// ```
#[stable(feature = "str_box_extras", since = "1.20.0")]
#[must_use]
#[inline]
pub unsafe fn from_boxed_utf8_unchecked(v: Box<[u8]>) -> Box<str> {
    // SAFETY: Upheld by caller.
    unsafe { Box::from_raw(Box::into_raw(v) as *mut str) }
}

/// Internal; same as `from_boxed_utf8_unchecked` but allocator-generic. Name
/// probably not suitable for being made `pub` as-is.
#[must_use]
#[inline]
#[cfg(not(no_global_oom_handling))]
pub(crate) unsafe fn from_boxed_utf8_unchecked_in<A: crate::alloc::Allocator>(
    v: Box<[u8], A>,
) -> Box<str, A> {
    let (ptr, alloc) = Box::into_raw_with_allocator(v);
    // SAFETY: Upheld by caller.
    unsafe { Box::from_raw_in(ptr as *mut str, alloc) }
}

/// Converts leading ascii bytes in `s` by calling the `convert` function.
///
/// For better average performance, this happens in chunks of `2*size_of::<usize>()`.
///
/// Returns a tuple of the converted prefix and the remainder starting from
/// the first non-ascii character.
///
/// This function is only public so that it can be verified in a codegen test,
/// see `issue-123712-str-to-lower-autovectorization.rs`.
///
/// # Safety
///
/// `convert` must return an ASCII byte for every ASCII input byte.
#[unstable(feature = "str_internals", issue = "none")]
#[doc(hidden)]
#[inline]
#[cfg(not(no_global_oom_handling))]
pub unsafe fn convert_while_ascii(s: &str, convert: fn(&u8) -> u8) -> (String, &str) {
    // Process the input in chunks of 16 bytes to enable auto-vectorization.
    // Previously the chunk size depended on the size of `usize`,
    // but on 32-bit platforms with sse or neon is also the better choice.
    // The only downside on other platforms would be a bit more loop-unrolling.
    const N: usize = 16;

    let mut slice = s.as_bytes();
    let mut out = Vec::with_capacity(slice.len());
    let mut out_slice = out.spare_capacity_mut();

    let mut ascii_prefix_len = 0_usize;
    let mut is_ascii = [false; N];

    while slice.len() >= N {
        // SAFETY: checked in loop condition
        let chunk = unsafe { slice.get_unchecked(..N) };
        // SAFETY: out_slice has at least same length as input slice and gets sliced with the same offsets
        let out_chunk = unsafe { out_slice.get_unchecked_mut(..N) };

        for j in 0..N {
            is_ascii[j] = chunk[j] <= 127;
        }

        // Auto-vectorization for this check is a bit fragile, sum and comparing against the chunk
        // size gives the best result, specifically a pmovmsk instruction on x86.
        // See https://github.com/llvm/llvm-project/issues/96395 for why llvm currently does not
        // currently recognize other similar idioms.
        if is_ascii.iter().map(|x| *x as u8).sum::<u8>() as usize != N {
            break;
        }

        for j in 0..N {
            out_chunk[j] = MaybeUninit::new(convert(&chunk[j]));
        }

        ascii_prefix_len += N;
        // ignore-tidy-undocumented-unsafe
        slice = unsafe { slice.get_unchecked(N..) };
        // ignore-tidy-undocumented-unsafe
        out_slice = unsafe { out_slice.get_unchecked_mut(N..) };
    }

    // handle the remainder as individual bytes
    while !slice.is_empty() {
        let byte = slice[0];
        if byte > 127 {
            break;
        }
        // SAFETY: out_slice has at least same length as input slice
        unsafe {
            *out_slice.get_unchecked_mut(0) = MaybeUninit::new(convert(&byte));
        }
        ascii_prefix_len += 1;
        // ignore-tidy-undocumented-unsafe
        slice = unsafe { slice.get_unchecked(1..) };
        // ignore-tidy-undocumented-unsafe
        out_slice = unsafe { out_slice.get_unchecked_mut(1..) };
    }

    // SAFETY: ascii_prefix_len bytes have been initialized above
    unsafe { out.set_len(ascii_prefix_len) };

    // SAFETY: We have written only valid ascii to the output vec
    let ascii_string = unsafe { String::from_utf8_unchecked(out) };

    // SAFETY: we know this is a valid char boundary
    // since we only skipped over leading ascii bytes
    let rest = unsafe { core::str::from_utf8_unchecked(slice) };

    (ascii_string, rest)
}
#[inline]
#[cfg(not(no_global_oom_handling))]
#[allow(dead_code)]
/// Faster implementation of string replacement for ASCII to ASCII cases.
/// Should produce fast vectorized code.
unsafe fn replace_ascii(utf8_bytes: &[u8], from: u8, to: u8) -> String {
    let result: Vec<u8> = utf8_bytes.iter().map(|b| if *b == from { to } else { *b }).collect();
    // SAFETY: We replaced ascii with ascii on valid utf8 strings.
    unsafe { String::from_utf8_unchecked(result) }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::kani;
    use core::str::pattern::{Pattern, ReverseSearcher, SearchStep, Searcher, StrSearcher};
    use core::ub_checks::Invariant;

    use crate::alloc::{Layout, alloc};

    // Challenge 21 harnesses (str::pattern StrSearcher safety). They live in this crate,
    // not core, because arbitrary-length inputs need the global allocator as HARNESS
    // infrastructure: `symbolic_str` below builds a haystack/needle of genuinely symbolic
    // length. Backing provenance (heap) is immaterial to the properties proven — every
    // read goes through the same `&str` the real callers use.

    /// A `&str` of symbolic length in `[1, 2^40]` with valid (nondet-content) backing.
    /// The 2^40 cap is the pointer-offset budget at `--object-bits 12` (offsets get
    /// ~52 bits); it is an encoding parameter, not a proof bound — a larger cap would
    /// need a larger `--object-bits`. The floor is 1 because `alloc` forbids zero-size
    /// allocations; the zero-length haystack is pinned by `ch21_bounded_empty_haystack`.
    fn symbolic_str() -> &'static str {
        let n: usize = kani::any();
        kani::assume(n > 0 && n <= 1usize << 40);
        // SAFETY: align 1 is a nonzero power of two and n <= 2^40 < isize::MAX; the
        // checked constructor's unwrap would add panic-formatting to every harness.
        let layout = unsafe { Layout::from_size_align_unchecked(n, 1) };
        let ptr = unsafe { alloc(layout) };
        kani::assume(!ptr.is_null());
        // SAFETY: freshly allocated, n bytes, alignment 1; content is nondeterministic.
        // UTF-8 properties of the content are assumed pointwise at use sites only where
        // the challenge's assumptions grant them (see the per-harness notes).
        unsafe { core::str::from_utf8_unchecked(core::slice::from_raw_parts(ptr, n)) }
    }

    // Criterion 1, empty-needle arm: creating a searcher from any valid UTF-8 haystack of
    // UNBOUNDED (symbolic) length establishes the type invariant. The empty-needle
    // constructor sets position=0/end=haystack.len() and performs no slicing, so
    // `is_char_boundary(0)` and `is_char_boundary(len)` take their O(1) fast paths.
    #[kani::proof]
    #[kani::unwind(5)]
    fn ch21_into_searcher_establishes_c_empty() {
        let haystack = symbolic_str();
        let s = "".into_searcher(haystack);
        kani::cover(true, "ch21 empty ctor state live");
        kani::assert(s.is_safe(), "C established at creation (empty arm)");
    }

    /// A 1-byte `&str` with a symbolic ASCII byte — the needle class `StrSearcher::new`
    /// routes to the single-byte searcher arm. ASCII is forced: a one-byte str is valid
    /// UTF-8 exactly when its byte is ASCII.
    fn symbolic_ascii_needle() -> &'static str {
        let needle = symbolic_str();
        kani::assume(needle.len() == 1 && needle.as_bytes()[0] <= 0x7F);
        needle
    }

    // Criterion 1, single-byte arm: creating a searcher from ANY 1-byte needle over a valid
    // UTF-8 haystack of UNBOUNDED (symbolic) length establishes the type invariant
    // (`StrSearcher::new` routes every one-byte needle to the single-byte arm). The
    // constructor sets position=0/end=haystack.len() and performs no slicing, so the
    // boundary checks take their O(1) fast paths.
    #[kani::proof]
    #[kani::unwind(5)]
    fn ch21_into_searcher_establishes_c_byte() {
        let haystack = symbolic_str();
        let needle = symbolic_ascii_needle();
        let s = needle.into_searcher(haystack);
        kani::cover(true, "ch21 byte ctor state live");
        kani::assert(s.is_safe(), "C established at creation (byte arm)");
    }

    // UNBOUNDED stepping, single-byte arm: from ANY invariant-satisfying state over a
    // SYMBOLIC-length haystack (assumption 3 encoded as a 1-char valid-UTF-8 window at the
    // cursor), one real `next()` preserves the invariant. The byte-arm step is O(1): one
    // byte compare plus `ceil_char_boundary`, whose scan ends inside the window's char.
    #[kani::proof]
    #[kani::unwind(5)]
    fn ch21_byte_next_preserves() {
        let haystack = symbolic_str();
        let needle = symbolic_ascii_needle();
        let mut s = StrSearcher::kani_arbitrary_byte_step(haystack, needle);
        let _step = s.next();
        kani::assert(s.is_safe(), "byte next: C preserved (unbounded haystack)");
    }

    // UNBOUNDED stepping, single-byte arm: every span `next()` returns lies on UTF-8
    // boundaries of the symbolic-length haystack.
    #[kani::proof]
    #[kani::unwind(5)]
    fn ch21_byte_next_boundaries() {
        let haystack = symbolic_str();
        let needle = symbolic_ascii_needle();
        let mut s = StrSearcher::kani_arbitrary_byte_step(haystack, needle);
        match s.next() {
            SearchStep::Match(a, b) => {
                kani::cover(true, "ch21 byte next match span returned");
                kani::assert(haystack.is_char_boundary(a), "byte next match: start on boundary");
                kani::assert(haystack.is_char_boundary(b), "byte next match: end on boundary");
            }
            SearchStep::Reject(a, b) => {
                kani::cover(true, "ch21 byte next reject span returned");
                kani::assert(haystack.is_char_boundary(a), "byte next reject: start on boundary");
                kani::assert(haystack.is_char_boundary(b), "byte next reject: end on boundary");
            }
            SearchStep::Done => kani::cover(true, "ch21 byte next done arm"),
        }
    }

    // The single-byte arm's match scans (`next_match`/`next_match_back`) call
    // `memchr`/`memrchr`, whose functional correctness the challenge grants (the slice
    // module assumption). The UNBOUNDED match proofs stub both with this nondeterministic
    // model of that granted contract: it may report any in-range position holding the
    // sought byte, or report no occurrence — a superset of the real scans' behaviors
    // (minimality of the reported hit is dropped; the safety proofs do not consume it).
    // When the sought byte is ASCII, a valid UTF-8 haystack also places a char boundary
    // (or the end) immediately after a hit — the same locally granted window as the step
    // builders. The real forward scan still runs end to end in the `ch21_bounded_next_match`
    // companion; a bounded reverse-scan companion is a disclosed residual (see the
    // reverse-method note below).
    #[cfg(kani)]
    fn ch21_stub_mem_scan(x: u8, text: &[u8]) -> Option<usize> {
        if kani::any() {
            let i: usize = kani::any();
            kani::assume(i < text.len() && text[i] == x);
            // The post-hit window holds only for an ASCII hit; the `x > 0x7F` disjunct keeps
            // the model sound if ever reused for a non-ASCII byte (inert here — a single-byte
            // needle is always ASCII).
            kani::assume(x > 0x7F || i + 1 == text.len() || !matches!(text[i + 1], 0x80..=0xBF));
            kani::cover(true, "ch21 mem-scan hit modeled");
            Some(i)
        } else {
            None
        }
    }

    // UNBOUNDED match scanning, single-byte arm: from ANY invariant-satisfying state over
    // a SYMBOLIC-length haystack, one real `next_match()` preserves the invariant, with
    // the `memchr` scan modeled by its granted contract (`ch21_stub_mem_scan`).
    #[kani::proof]
    #[kani::stub(core::slice::memchr::memchr, ch21_stub_mem_scan)]
    #[kani::unwind(5)]
    fn ch21_byte_next_match_preserves() {
        let haystack = symbolic_str();
        let needle = symbolic_ascii_needle();
        let mut s = StrSearcher::kani_arbitrary_byte_state(haystack, needle);
        let _m = s.next_match();
        kani::assert(s.is_safe(), "byte next_match: C preserved (unbounded haystack)");
    }

    // UNBOUNDED match scanning, single-byte arm: every span `next_match()` returns lies on
    // UTF-8 boundaries of the symbolic-length haystack.
    #[kani::proof]
    #[kani::stub(core::slice::memchr::memchr, ch21_stub_mem_scan)]
    #[kani::unwind(5)]
    fn ch21_byte_next_match_boundaries() {
        let haystack = symbolic_str();
        let needle = symbolic_ascii_needle();
        let mut s = StrSearcher::kani_arbitrary_byte_state(haystack, needle);
        if let Some((a, b)) = s.next_match() {
            kani::cover(true, "ch21 byte next_match span returned");
            kani::assert(haystack.is_char_boundary(a), "byte next_match: start on boundary");
            kani::assert(haystack.is_char_boundary(b), "byte next_match: end on boundary");
        } else {
            kani::cover(true, "ch21 byte next_match none arm");
        }
    }

    // UNBOUNDED reverse match scanning, single-byte arm: from ANY invariant-satisfying
    // state, one real `next_match_back()` preserves the invariant, with the `memrchr`
    // scan modeled by the same granted contract. Unlike the reverse step methods, this
    // path performs no boundary walk — the found byte itself carries the boundary facts.
    #[kani::proof]
    #[kani::stub(core::slice::memchr::memrchr, ch21_stub_mem_scan)]
    #[kani::unwind(5)]
    fn ch21_byte_next_match_back_preserves() {
        let haystack = symbolic_str();
        let needle = symbolic_ascii_needle();
        let mut s = StrSearcher::kani_arbitrary_byte_state(haystack, needle);
        let _m = s.next_match_back();
        kani::assert(s.is_safe(), "byte next_match_back: C preserved (unbounded haystack)");
    }

    // UNBOUNDED reverse match scanning, single-byte arm: every span `next_match_back()`
    // returns lies on UTF-8 boundaries — the span end lands either strictly inside the
    // scanned prefix (the window after the hit) or exactly on the backward cursor (a
    // boundary by the invariant).
    #[kani::proof]
    #[kani::stub(core::slice::memchr::memrchr, ch21_stub_mem_scan)]
    #[kani::unwind(5)]
    fn ch21_byte_next_match_back_boundaries() {
        let haystack = symbolic_str();
        let needle = symbolic_ascii_needle();
        let mut s = StrSearcher::kani_arbitrary_byte_state(haystack, needle);
        if let Some((a, b)) = s.next_match_back() {
            kani::cover(true, "ch21 byte next_match_back span returned");
            kani::assert(haystack.is_char_boundary(a), "byte next_match_back: start on boundary");
            kani::assert(haystack.is_char_boundary(b), "byte next_match_back: end on boundary");
        } else {
            kani::cover(true, "ch21 byte next_match_back none arm");
        }
    }

    // UNBOUNDED stepping, empty-needle arm: from ANY invariant-satisfying state over a
    // SYMBOLIC-length haystack (assumption 3 encoded as a 1-char valid-UTF-8 window at the
    // cursor), one real `next()` preserves the invariant. The empty-arm step is O(1), so no
    // loop contract is involved.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(5)]
    fn ch21_empty_next_preserves() {
        let haystack = symbolic_str();
        let mut s = StrSearcher::kani_arbitrary_empty_step(haystack, 1);
        let _step = s.next();
        kani::assert(s.is_safe(), "empty next: C preserved (unbounded haystack)");
    }

    // UNBOUNDED stepping, empty-needle arm: every span `next()` returns lies on UTF-8
    // boundaries of the symbolic-length haystack.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(5)]
    fn ch21_empty_next_boundaries() {
        let haystack = symbolic_str();
        let mut s = StrSearcher::kani_arbitrary_empty_step(haystack, 1);
        match s.next() {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                kani::cover(true, "ch21 empty next span returned");
                kani::assert(haystack.is_char_boundary(a), "empty next: start on boundary");
                kani::assert(haystack.is_char_boundary(b), "empty next: end on boundary");
            }
            SearchStep::Done => kani::cover(true, "ch21 empty next done arm"),
        }
    }

    // UNBOUNDED stepping: on the empty arm `next_match` returns after <=2 internal `next`
    // steps (Match/Reject strictly alternate), so a 2-char cursor window covers it — the
    // iteration bound is structural, independent of haystack length.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(4)]
    fn ch21_empty_next_match_preserves() {
        let haystack = symbolic_str();
        let mut s = StrSearcher::kani_arbitrary_empty_step(haystack, 2);
        let _m = s.next_match();
        kani::assert(s.is_safe(), "empty next_match: C preserved (unbounded haystack)");
    }

    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(4)]
    fn ch21_empty_next_match_boundaries() {
        let haystack = symbolic_str();
        let mut s = StrSearcher::kani_arbitrary_empty_step(haystack, 2);
        if let Some((a, b)) = s.next_match() {
            kani::cover(true, "ch21 empty next_match span returned");
            kani::assert(haystack.is_char_boundary(a), "empty next_match: start on boundary");
            kani::assert(haystack.is_char_boundary(b), "empty next_match: end on boundary");
        } else {
            kani::cover(true, "ch21 empty next_match exhausted arm");
        }
    }

    // Same structural <=2-step argument for the provided method `next_reject`.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(4)]
    fn ch21_empty_next_reject_preserves() {
        let haystack = symbolic_str();
        let mut s = StrSearcher::kani_arbitrary_empty_step(haystack, 2);
        let _r = s.next_reject();
        kani::assert(s.is_safe(), "empty next_reject: C preserved (unbounded haystack)");
    }

    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(4)]
    fn ch21_empty_next_reject_boundaries() {
        let haystack = symbolic_str();
        let mut s = StrSearcher::kani_arbitrary_empty_step(haystack, 2);
        if let Some((a, b)) = s.next_reject() {
            kani::cover(true, "ch21 empty next_reject span returned");
            kani::assert(haystack.is_char_boundary(a), "empty next_reject: start on boundary");
            kani::assert(haystack.is_char_boundary(b), "empty next_reject: end on boundary");
        } else {
            kani::cover(true, "ch21 empty next_reject exhausted arm");
        }
    }

    // The str indexing in these methods carries a diverging panic-formatter path
    // (`core::str::slice_error_fail`) that is DEAD under the type invariant — every index the
    // methods produce is in-bounds and on a char boundary — but which CBMC still symbolically
    // explores, exploding the object count (the reject methods loop internally, multiplying
    // the cost). We stub it with a diverging no-op so the dead path is pruned;
    // `ch21_stub_falsifier` proves the stub is divergence-preserving (a path that actually
    // reaches it still halts verification — nothing is silently masked).
    #[cfg(kani)]
    fn ch21_stub_sef(_s: &str, _begin: usize, _end: usize) -> ! {
        kani::panic("slice_error_fail stubbed: unreachable under the StrSearcher type invariant")
    }

    // Soundness falsifier for the stub: a deliberately out-of-range slice REACHES the stubbed
    // path; `should_panic` requires it to panic (via the stub's divergence), proving the stub
    // does not silently accept a bad slice. Passes in CI by panicking — machine-checked.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::should_panic]
    fn ch21_stub_falsifier() {
        let h = "aé";
        let i: usize = kani::any();
        kani::assume(i > h.len());
        let _ = &h[i..];
    }

    // Bounded companions: drive the real StrSearcher methods to completion on a concrete
    // fixture containing a multi-byte char, asserting the type invariant is preserved after
    // every step and that every returned span lies on UTF-8 char boundaries. Bounded by
    // construction (concrete inputs); one loop per searcher arm: needle "" (empty arm),
    // "a" (one byte, single-byte arm), "é" (two bytes, Two-Way arm). Fixture "aé" =
    // 'a' (1 byte) + 'é' (2 bytes): char boundaries at 0, 1, 3; offset 2 is mid-character.
    // unwind 10: each arm's loop drives at most 5 steps + Done (sequences traced in the
    // count asserts below); 10 leaves slack for the unwind check itself.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(10)]
    fn ch21_bounded_next() {
        let h = "aé";
        let (mut m, mut r) = (0, 0);
        let mut e = "".into_searcher(h);
        loop {
            match e.next() {
                SearchStep::Match(a, b) => {
                    m += 1;
                    kani::assert(h.is_char_boundary(a), "next empty: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next empty: span end on boundary");
                    kani::assert(e.is_safe(), "next empty: C preserved");
                }
                SearchStep::Reject(a, b) => {
                    r += 1;
                    kani::assert(h.is_char_boundary(a), "next empty: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next empty: span end on boundary");
                    kani::assert(e.is_safe(), "next empty: C preserved");
                }
                SearchStep::Done => break,
            }
        }
        // "" over "aé": Match(0,0) Reject(0,1) Match(1,1) Reject(1,3) Match(3,3) Done.
        kani::assert(m == 3 && r == 2, "next empty: exact step counts (3 matches, 2 rejects)");
        let (mut m, mut r) = (0, 0);
        let mut by = "a".into_searcher(h);
        loop {
            match by.next() {
                SearchStep::Match(a, b) => {
                    m += 1;
                    kani::assert(h.is_char_boundary(a), "next byte: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next byte: span end on boundary");
                    kani::assert(by.is_safe(), "next byte: C preserved");
                }
                SearchStep::Reject(a, b) => {
                    r += 1;
                    kani::assert(h.is_char_boundary(a), "next byte: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next byte: span end on boundary");
                    kani::assert(by.is_safe(), "next byte: C preserved");
                }
                SearchStep::Done => break,
            }
        }
        // "a" over "aé" (one-byte needle, single-byte arm): Match(0,1) Reject(1,3) Done.
        kani::assert(m == 1 && r == 1, "next byte: exact step counts (1 match, 1 reject)");
        let (mut m, mut r) = (0, 0);
        let mut tw = "é".into_searcher(h);
        // Criterion 1, Two-Way arm (bounded): creation establishes C. The empty and
        // single-byte arms have dedicated unbounded creation harnesses above; the Two-Way
        // constructor is only reachable on a concrete fixture at this pin, so its
        // creation check lives here, before the first step.
        kani::assert(tw.is_safe(), "creation twoway: C established at creation");
        loop {
            match tw.next() {
                SearchStep::Match(a, b) => {
                    m += 1;
                    kani::assert(h.is_char_boundary(a), "next twoway: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next twoway: span end on boundary");
                    kani::assert(tw.is_safe(), "next twoway: C preserved");
                }
                SearchStep::Reject(a, b) => {
                    r += 1;
                    kani::assert(h.is_char_boundary(a), "next twoway: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next twoway: span end on boundary");
                    kani::assert(tw.is_safe(), "next twoway: C preserved");
                }
                SearchStep::Done => break,
            }
        }
        // "é" over "aé" (two-byte needle, Two-Way arm): Reject(0,1) Match(1,3) Done.
        kani::assert(m == 1 && r == 1, "next twoway: exact step counts (1 match, 1 reject)");
        kani::cover(true, "ch21 next: all three arms driven to Done");
    }

    // unwind 10: at most 3 yields + exhaustion per arm (counts asserted below).
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(10)]
    fn ch21_bounded_next_match() {
        let h = "aé";
        let mut n = 0;
        let mut e = "".into_searcher(h);
        while let Some((a, b)) = e.next_match() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_match empty: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_match empty: end on boundary");
            kani::assert(e.is_safe(), "next_match empty: C preserved");
        }
        kani::assert(e.is_safe(), "next_match empty: C preserved at Done");
        // "" matches at every boundary of "aé": 0, 1, 3.
        kani::assert(n == 3, "next_match empty: exactly 3 matches");
        let mut n = 0;
        let mut by = "a".into_searcher(h);
        while let Some((a, b)) = by.next_match() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_match byte: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_match byte: end on boundary");
            kani::assert(by.is_safe(), "next_match byte: C preserved");
        }
        kani::assert(by.is_safe(), "next_match byte: C preserved at Done");
        // "a" occurs once in "aé", at (0,1).
        kani::assert(n == 1, "next_match byte: exactly 1 match");
        let mut n = 0;
        let mut tw = "é".into_searcher(h);
        while let Some((a, b)) = tw.next_match() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_match twoway: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_match twoway: end on boundary");
            kani::assert(tw.is_safe(), "next_match twoway: C preserved");
        }
        kani::assert(tw.is_safe(), "next_match twoway: C preserved at Done");
        // "é" occurs once in "aé", at (1,3).
        kani::assert(n == 1, "next_match twoway: exactly 1 match");
        kani::cover(true, "ch21 next_match: all three arms exhausted");
    }

    // unwind 10: at most 2 yields + exhaustion per arm (counts asserted below); exercises the
    // provided-method path (`next_reject` is a `Searcher` default method looping `next`).
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(10)]
    fn ch21_bounded_next_reject() {
        let h = "aé";
        let mut n = 0;
        let mut e = "".into_searcher(h);
        while let Some((a, b)) = e.next_reject() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_reject empty: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_reject empty: end on boundary");
            kani::assert(e.is_safe(), "next_reject empty: C preserved");
        }
        kani::assert(e.is_safe(), "next_reject empty: C preserved at Done");
        // "" rejects each char of "aé": (0,1) and (1,3).
        kani::assert(n == 2, "next_reject empty: exactly 2 rejects");
        let mut n = 0;
        let mut by = "a".into_searcher(h);
        while let Some((a, b)) = by.next_reject() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_reject byte: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_reject byte: end on boundary");
            kani::assert(by.is_safe(), "next_reject byte: C preserved");
        }
        kani::assert(by.is_safe(), "next_reject byte: C preserved at Done");
        // After the match at (0,1), the remaining "é" is rejected as (1,3).
        kani::assert(n == 1, "next_reject byte: exactly 1 reject");
        let mut n = 0;
        let mut tw = "é".into_searcher(h);
        while let Some((a, b)) = tw.next_reject() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_reject twoway: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_reject twoway: end on boundary");
            kani::assert(tw.is_safe(), "next_reject twoway: C preserved");
        }
        kani::assert(tw.is_safe(), "next_reject twoway: C preserved at Done");
        // The leading 'a' is rejected as (0,1); the match at (1,3) is skipped.
        kani::assert(n == 1, "next_reject twoway: exactly 1 reject");
        kani::cover(true, "ch21 next_reject: all three arms exhausted");
    }

    // Reverse bounded companions: the direction-symmetric mirror of the three forward
    // companions above, driving the real reverse methods to completion on the same fixture.
    // A reverse scan visits the same spans as the forward scan in the opposite order, so the
    // step counts match their forward counterparts. unwind 10 as above.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(10)]
    fn ch21_bounded_next_back() {
        let h = "aé";
        let (mut m, mut r) = (0, 0);
        let mut e = "".into_searcher(h);
        loop {
            match e.next_back() {
                SearchStep::Match(a, b) => {
                    m += 1;
                    kani::assert(h.is_char_boundary(a), "next_back empty: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next_back empty: span end on boundary");
                    kani::assert(e.is_safe(), "next_back empty: C preserved");
                }
                SearchStep::Reject(a, b) => {
                    r += 1;
                    kani::assert(h.is_char_boundary(a), "next_back empty: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next_back empty: span end on boundary");
                    kani::assert(e.is_safe(), "next_back empty: C preserved");
                }
                SearchStep::Done => break,
            }
        }
        // "" over "aé", reverse: Match(3,3) Reject(1,3) Match(1,1) Reject(0,1) Match(0,0) Done.
        kani::assert(m == 3 && r == 2, "next_back empty: exact step counts (3 matches, 2 rejects)");
        let (mut m, mut r) = (0, 0);
        let mut by = "a".into_searcher(h);
        loop {
            match by.next_back() {
                SearchStep::Match(a, b) => {
                    m += 1;
                    kani::assert(h.is_char_boundary(a), "next_back byte: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next_back byte: span end on boundary");
                    kani::assert(by.is_safe(), "next_back byte: C preserved");
                }
                SearchStep::Reject(a, b) => {
                    r += 1;
                    kani::assert(h.is_char_boundary(a), "next_back byte: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next_back byte: span end on boundary");
                    kani::assert(by.is_safe(), "next_back byte: C preserved");
                }
                SearchStep::Done => break,
            }
        }
        // "a" over "aé", reverse (single-byte arm): Reject(1,3) Match(0,1) Done.
        kani::assert(m == 1 && r == 1, "next_back byte: exact step counts (1 match, 1 reject)");
        let (mut m, mut r) = (0, 0);
        let mut tw = "é".into_searcher(h);
        loop {
            match tw.next_back() {
                SearchStep::Match(a, b) => {
                    m += 1;
                    kani::assert(h.is_char_boundary(a), "next_back twoway: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next_back twoway: span end on boundary");
                    kani::assert(tw.is_safe(), "next_back twoway: C preserved");
                }
                SearchStep::Reject(a, b) => {
                    r += 1;
                    kani::assert(h.is_char_boundary(a), "next_back twoway: span start on boundary");
                    kani::assert(h.is_char_boundary(b), "next_back twoway: span end on boundary");
                    kani::assert(tw.is_safe(), "next_back twoway: C preserved");
                }
                SearchStep::Done => break,
            }
        }
        // "é" over "aé", reverse (Two-Way arm): Match(1,3) Reject(0,1) Done.
        kani::assert(m == 1 && r == 1, "next_back twoway: exact step counts (1 match, 1 reject)");
        kani::cover(true, "ch21 next_back: all three arms driven to Done");
    }

    // unwind 10: at most 3 yields + exhaustion per arm (counts asserted below).
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(10)]
    fn ch21_bounded_next_match_back() {
        let h = "aé";
        let mut n = 0;
        let mut e = "".into_searcher(h);
        while let Some((a, b)) = e.next_match_back() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_match_back empty: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_match_back empty: end on boundary");
            kani::assert(e.is_safe(), "next_match_back empty: C preserved");
        }
        kani::assert(e.is_safe(), "next_match_back empty: C preserved at Done");
        // "" matches at every boundary of "aé": 3, 1, 0.
        kani::assert(n == 3, "next_match_back empty: exactly 3 matches");
        let mut n = 0;
        let mut by = "a".into_searcher(h);
        while let Some((a, b)) = by.next_match_back() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_match_back byte: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_match_back byte: end on boundary");
            kani::assert(by.is_safe(), "next_match_back byte: C preserved");
        }
        kani::assert(by.is_safe(), "next_match_back byte: C preserved at Done");
        // "a" occurs once in "aé", at (0,1).
        kani::assert(n == 1, "next_match_back byte: exactly 1 match");
        let mut n = 0;
        let mut tw = "é".into_searcher(h);
        while let Some((a, b)) = tw.next_match_back() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_match_back twoway: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_match_back twoway: end on boundary");
            kani::assert(tw.is_safe(), "next_match_back twoway: C preserved");
        }
        kani::assert(tw.is_safe(), "next_match_back twoway: C preserved at Done");
        // "é" occurs once in "aé", at (1,3).
        kani::assert(n == 1, "next_match_back twoway: exactly 1 match");
        kani::cover(true, "ch21 next_match_back: all three arms exhausted");
    }

    // unwind 10: at most 2 yields + exhaustion per arm; exercises the provided-method path
    // (`next_reject_back` is a `ReverseSearcher` default method looping `next_back`).
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(10)]
    fn ch21_bounded_next_reject_back() {
        let h = "aé";
        let mut n = 0;
        let mut e = "".into_searcher(h);
        while let Some((a, b)) = e.next_reject_back() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_reject_back empty: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_reject_back empty: end on boundary");
            kani::assert(e.is_safe(), "next_reject_back empty: C preserved");
        }
        kani::assert(e.is_safe(), "next_reject_back empty: C preserved at Done");
        // "" rejects each char of "aé": (1,3) and (0,1).
        kani::assert(n == 2, "next_reject_back empty: exactly 2 rejects");
        let mut n = 0;
        let mut by = "a".into_searcher(h);
        while let Some((a, b)) = by.next_reject_back() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_reject_back byte: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_reject_back byte: end on boundary");
            kani::assert(by.is_safe(), "next_reject_back byte: C preserved");
        }
        kani::assert(by.is_safe(), "next_reject_back byte: C preserved at Done");
        // The "é" at (1,3) is rejected; the match at (0,1) is skipped.
        kani::assert(n == 1, "next_reject_back byte: exactly 1 reject");
        let mut n = 0;
        let mut tw = "é".into_searcher(h);
        while let Some((a, b)) = tw.next_reject_back() {
            n += 1;
            kani::assert(h.is_char_boundary(a), "next_reject_back twoway: start on boundary");
            kani::assert(h.is_char_boundary(b), "next_reject_back twoway: end on boundary");
            kani::assert(tw.is_safe(), "next_reject_back twoway: C preserved");
        }
        kani::assert(tw.is_safe(), "next_reject_back twoway: C preserved at Done");
        // The trailing 'a' is rejected as (0,1); the match at (1,3) is skipped.
        kani::assert(n == 1, "next_reject_back twoway: exactly 1 reject");
        kani::cover(true, "ch21 next_reject_back: all three arms exhausted");
    }

    // Zero-length-haystack companion: the symbolic harnesses float the haystack length in
    // [1, 2^40] (`alloc` forbids zero-size allocations), so this pins the one excluded
    // length concretely. All six methods on all three arms over `""`: the empty-needle
    // searcher yields exactly one Match(0, 0) per direction (0 is the sole char boundary
    // of `""`), and the single-byte and Two-Way searchers terminate immediately. The
    // needle blocks are written out straight-line (no needle array) so every searcher
    // kind stays a compile-time constant for the solver.
    // unwind 10: the provided reject methods loop internally; every sequence here is at
    // most one yield.
    #[kani::proof]
    #[kani::stub(core::str::slice_error_fail, ch21_stub_sef)]
    #[kani::unwind(10)]
    fn ch21_bounded_empty_haystack() {
        let h = "";
        let mut e = "".into_searcher(h);
        kani::assert(e.is_safe(), "empty haystack: C established at creation (empty arm)");
        kani::assert(
            matches!(e.next(), SearchStep::Match(0, 0)),
            "empty/empty: next is Match(0,0)",
        );
        kani::assert(e.is_safe(), "empty/empty: C preserved after next");
        kani::assert(matches!(e.next(), SearchStep::Done), "empty/empty: next then Done");
        let mut e = "".into_searcher(h);
        kani::assert(
            matches!(e.next_back(), SearchStep::Match(0, 0)),
            "empty/empty: next_back is Match(0,0)",
        );
        kani::assert(e.is_safe(), "empty/empty: C preserved after next_back");
        kani::assert(matches!(e.next_back(), SearchStep::Done), "empty/empty: next_back then Done");
        let mut e = "".into_searcher(h);
        kani::assert(matches!(e.next_match(), Some((0, 0))), "empty/empty: one match at (0,0)");
        kani::assert(matches!(e.next_match(), None), "empty/empty: next_match exhausted");
        let mut e = "".into_searcher(h);
        kani::assert(matches!(e.next_reject(), None), "empty/empty: no rejects");
        let mut e = "".into_searcher(h);
        kani::assert(
            matches!(e.next_match_back(), Some((0, 0))),
            "empty/empty: one back-match at (0,0)",
        );
        kani::assert(matches!(e.next_match_back(), None), "empty/empty: next_match_back exhausted");
        let mut e = "".into_searcher(h);
        kani::assert(matches!(e.next_reject_back(), None), "empty/empty: no back-rejects");
        kani::assert(e.is_safe(), "empty/empty: C preserved at exhaustion");
        // "a" routes to the single-byte arm; over "" every method terminates on the
        // first call.
        let mut s = "a".into_searcher(h);
        kani::assert(s.is_safe(), "empty/byte: C established at creation");
        kani::assert(matches!(s.next(), SearchStep::Done), "empty/byte: next is Done");
        kani::assert(s.is_safe(), "empty/byte: C preserved after next");
        let mut s = "a".into_searcher(h);
        kani::assert(matches!(s.next_back(), SearchStep::Done), "empty/byte: next_back is Done");
        kani::assert(s.is_safe(), "empty/byte: C preserved after next_back");
        let mut s = "a".into_searcher(h);
        kani::assert(matches!(s.next_match(), None), "empty/byte: no matches");
        let mut s = "a".into_searcher(h);
        kani::assert(matches!(s.next_reject(), None), "empty/byte: no rejects");
        let mut s = "a".into_searcher(h);
        kani::assert(matches!(s.next_match_back(), None), "empty/byte: no back-matches");
        let mut s = "a".into_searcher(h);
        kani::assert(matches!(s.next_reject_back(), None), "empty/byte: no back-rejects");
        kani::assert(s.is_safe(), "empty/byte: C preserved at exhaustion");
        // "é" (two bytes) routes to the Two-Way arm.
        let mut s = "é".into_searcher(h);
        kani::assert(s.is_safe(), "empty/twoway: C established at creation");
        kani::assert(matches!(s.next(), SearchStep::Done), "empty/twoway: next is Done");
        kani::assert(s.is_safe(), "empty/twoway: C preserved after next");
        let mut s = "é".into_searcher(h);
        kani::assert(matches!(s.next_back(), SearchStep::Done), "empty/twoway: next_back is Done");
        kani::assert(s.is_safe(), "empty/twoway: C preserved after next_back");
        let mut s = "é".into_searcher(h);
        kani::assert(matches!(s.next_match(), None), "empty/twoway: no matches");
        let mut s = "é".into_searcher(h);
        kani::assert(matches!(s.next_reject(), None), "empty/twoway: no rejects");
        let mut s = "é".into_searcher(h);
        kani::assert(matches!(s.next_match_back(), None), "empty/twoway: no back-matches");
        let mut s = "é".into_searcher(h);
        kani::assert(matches!(s.next_reject_back(), None), "empty/twoway: no back-rejects");
        kani::assert(s.is_safe(), "empty/twoway: C preserved at exhaustion");
        kani::cover(true, "ch21 empty haystack: all three arms exercised");
    }

    // Unbounded reverse coverage is staged, not blocked by technique. `next_back`'s Reject
    // branch calls `str::floor_char_boundary`, which reads the haystack's first byte and
    // walks back up to four bytes, resting on global UTF-8 well-formedness that the
    // symbolic-length technique does not supply at the cursor. (`next_match_back` avoids
    // this: `memrchr` returns an exact ASCII position, already a boundary — hence its
    // unbounded proof above.) The loop-contract upgrade that lifts the Two-Way rows to
    // unbounded lifts these too.
}
