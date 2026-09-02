//! The string Pattern API.
//!
//! The Pattern API provides a generic mechanism for using different pattern
//! types when searching through a string.
//!
//! For more details, see the traits [`Pattern`], [`Searcher`],
//! [`ReverseSearcher`], and [`DoubleEndedSearcher`].
//!
//! Although this API is unstable, it is exposed via stable APIs on the
//! [`str`] type.
//!
//! # Examples
//!
//! [`Pattern`] is [implemented][pattern-impls] in the stable API for
//! [`&str`][`str`], [`char`], slices of [`char`], and functions and closures
//! implementing `FnMut(char) -> bool`.
//!
//! ```
//! let s = "Can you find a needle in a haystack?";
//!
//! // &str pattern
//! assert_eq!(s.find("you"), Some(4));
//! // char pattern
//! assert_eq!(s.find('n'), Some(2));
//! // array of chars pattern
//! assert_eq!(s.find(&['a', 'e', 'i', 'o', 'u']), Some(1));
//! // slice of chars pattern
//! assert_eq!(s.find(&['a', 'e', 'i', 'o', 'u'][..]), Some(1));
//! // closure pattern
//! assert_eq!(s.find(|c: char| c.is_ascii_punctuation()), Some(35));
//! ```
//!
//! [pattern-impls]: Pattern#implementors

#![unstable(
    feature = "pattern",
    reason = "API not fully fleshed out and ready to be stabilized",
    issue = "27721"
)]

#[cfg(all(target_arch = "x86_64", any(kani, target_feature = "sse2")))]
use safety::{loop_invariant, requires};

use crate::cmp::Ordering;
use crate::convert::TryInto as _;
#[cfg(kani)]
use crate::kani;
use crate::slice::memchr;
use crate::{cmp, fmt};

// Pattern

/// A string pattern.
///
/// A `Pattern` expresses that the implementing type
/// can be used as a string pattern for searching in a [`&str`][str].
///
/// For example, both `'a'` and `"aa"` are patterns that
/// would match at index `1` in the string `"baaaab"`.
///
/// The trait itself acts as a builder for an associated
/// [`Searcher`] type, which does the actual work of finding
/// occurrences of the pattern in a string.
///
/// Depending on the type of the pattern, the behavior of methods like
/// [`str::find`] and [`str::contains`] can change. The table below describes
/// some of those behaviors.
///
/// | Pattern type             | Match condition                           |
/// |--------------------------|-------------------------------------------|
/// | `&str`                   | is substring                              |
/// | `char`                   | is contained in string                    |
/// | `&[char]`                | any char in slice is contained in string  |
/// | `F: FnMut(char) -> bool` | `F` returns `true` for a char in string   |
/// | `&&str`                  | is substring                              |
/// | `&String`                | is substring                              |
///
/// # Examples
///
/// ```
/// // &str
/// assert_eq!("abaaa".find("ba"), Some(1));
/// assert_eq!("abaaa".find("bac"), None);
///
/// // char
/// assert_eq!("abaaa".find('a'), Some(0));
/// assert_eq!("abaaa".find('b'), Some(1));
/// assert_eq!("abaaa".find('c'), None);
///
/// // &[char; N]
/// assert_eq!("ab".find(&['b', 'a']), Some(0));
/// assert_eq!("abaaa".find(&['a', 'z']), Some(0));
/// assert_eq!("abaaa".find(&['c', 'd']), None);
///
/// // &[char]
/// assert_eq!("ab".find(&['b', 'a'][..]), Some(0));
/// assert_eq!("abaaa".find(&['a', 'z'][..]), Some(0));
/// assert_eq!("abaaa".find(&['c', 'd'][..]), None);
///
/// // FnMut(char) -> bool
/// assert_eq!("abcdef_z".find(|ch| ch > 'd' && ch < 'y'), Some(4));
/// assert_eq!("abcddd_z".find(|ch| ch > 'd' && ch < 'y'), None);
/// ```
pub trait Pattern: Sized {
    /// Associated searcher for this pattern
    type Searcher<'a>: Searcher<'a>;

    /// Constructs the associated searcher from
    /// `self` and the `haystack` to search in.
    fn into_searcher(self, haystack: &str) -> Self::Searcher<'_>;

    /// Checks whether the pattern matches anywhere in the haystack
    #[inline]
    fn is_contained_in(self, haystack: &str) -> bool {
        self.into_searcher(haystack).next_match().is_some()
    }

    /// Checks whether the pattern matches at the front of the haystack
    #[inline]
    fn is_prefix_of(self, haystack: &str) -> bool {
        matches!(self.into_searcher(haystack).next(), SearchStep::Match(0, _))
    }

    /// Checks whether the pattern matches at the back of the haystack
    #[inline]
    fn is_suffix_of<'a>(self, haystack: &'a str) -> bool
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        matches!(self.into_searcher(haystack).next_back(), SearchStep::Match(_, j) if haystack.len() == j)
    }

    /// Removes the pattern from the front of haystack, if it matches.
    #[inline]
    fn strip_prefix_of(self, haystack: &str) -> Option<&str> {
        if let SearchStep::Match(start, len) = self.into_searcher(haystack).next() {
            debug_assert_eq!(
                start, 0,
                "The first search step from Searcher \
                 must include the first character"
            );
            // SAFETY: `Searcher` is known to return valid indices.
            unsafe { Some(haystack.get_unchecked(len..)) }
        } else {
            None
        }
    }

    /// Removes the pattern from the back of haystack, if it matches.
    #[inline]
    fn strip_suffix_of<'a>(self, haystack: &'a str) -> Option<&'a str>
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        if let SearchStep::Match(start, end) = self.into_searcher(haystack).next_back() {
            debug_assert_eq!(
                end,
                haystack.len(),
                "The first search step from ReverseSearcher \
                 must include the last character"
            );
            // SAFETY: `Searcher` is known to return valid indices.
            unsafe { Some(haystack.get_unchecked(..start)) }
        } else {
            None
        }
    }

    /// Returns the pattern as utf-8 bytes if possible.
    fn as_utf8_pattern(&self) -> Option<Utf8Pattern<'_>> {
        None
    }
}
/// Result of calling [`Pattern::as_utf8_pattern()`].
/// Can be used for inspecting the contents of a [`Pattern`] in cases
/// where the underlying representation can be represented as UTF-8.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Utf8Pattern<'a> {
    /// Type returned by String and str types.
    StringPattern(&'a [u8]),
    /// Type returned by char types.
    CharPattern(char),
}

// Searcher

/// Result of calling [`Searcher::next()`] or [`ReverseSearcher::next_back()`].
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SearchStep {
    /// Expresses that a match of the pattern has been found at
    /// `haystack[a..b]`.
    Match(usize, usize),
    /// Expresses that `haystack[a..b]` has been rejected as a possible match
    /// of the pattern.
    ///
    /// Note that there might be more than one `Reject` between two `Match`es,
    /// there is no requirement for them to be combined into one.
    Reject(usize, usize),
    /// Expresses that every byte of the haystack has been visited, ending
    /// the iteration.
    Done,
}

/// A searcher for a string pattern.
///
/// This trait provides methods for searching for non-overlapping
/// matches of a pattern starting from the front (left) of a string.
///
/// It will be implemented by associated `Searcher`
/// types of the [`Pattern`] trait.
///
/// The trait is marked unsafe because the indices returned by the
/// [`next()`][Searcher::next] methods are required to lie on valid utf8
/// boundaries in the haystack. This enables consumers of this trait to
/// slice the haystack without additional runtime checks.
pub unsafe trait Searcher<'a> {
    /// Getter for the underlying string to be searched in
    ///
    /// Will always return the same [`&str`][str].
    fn haystack(&self) -> &'a str;

    /// Performs the next search step starting from the front.
    ///
    /// - Returns [`Match(a, b)`][SearchStep::Match] if `haystack[a..b]` matches
    ///   the pattern.
    /// - Returns [`Reject(a, b)`][SearchStep::Reject] if `haystack[a..b]` can
    ///   not match the pattern, even partially.
    /// - Returns [`Done`][SearchStep::Done] if every byte of the haystack has
    ///   been visited.
    ///
    /// The stream of [`Match`][SearchStep::Match] and
    /// [`Reject`][SearchStep::Reject] values up to a [`Done`][SearchStep::Done]
    /// will contain index ranges that are adjacent, non-overlapping,
    /// covering the whole haystack, and laying on utf8 boundaries.
    ///
    /// A [`Match`][SearchStep::Match] result needs to contain the whole matched
    /// pattern, however [`Reject`][SearchStep::Reject] results may be split up
    /// into arbitrary many adjacent fragments. Both ranges may have zero length.
    ///
    /// As an example, the pattern `"aaa"` and the haystack `"cbaaaaab"`
    /// might produce the stream
    /// `[Reject(0, 1), Reject(1, 2), Match(2, 5), Reject(5, 8)]`
    fn next(&mut self) -> SearchStep;

    /// Finds the next [`Match`][SearchStep::Match] result. See [`next()`][Searcher::next].
    ///
    /// Unlike [`next()`][Searcher::next], there is no guarantee that the returned ranges
    /// of this and [`next_reject`][Searcher::next_reject] will overlap. This will return
    /// `(start_match, end_match)`, where start_match is the index of where
    /// the match begins, and end_match is the index after the end of the match.
    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }

    /// Finds the next [`Reject`][SearchStep::Reject] result. See [`next()`][Searcher::next]
    /// and [`next_match()`][Searcher::next_match].
    ///
    /// Unlike [`next()`][Searcher::next], there is no guarantee that the returned ranges
    /// of this and [`next_match`][Searcher::next_match] will overlap.
    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }
}

/// A reverse searcher for a string pattern.
///
/// This trait provides methods for searching for non-overlapping
/// matches of a pattern starting from the back (right) of a string.
///
/// It will be implemented by associated [`Searcher`]
/// types of the [`Pattern`] trait if the pattern supports searching
/// for it from the back.
///
/// The index ranges returned by this trait are not required
/// to exactly match those of the forward search in reverse.
///
/// For the reason why this trait is marked unsafe, see the
/// parent trait [`Searcher`].
pub unsafe trait ReverseSearcher<'a>: Searcher<'a> {
    /// Performs the next search step starting from the back.
    ///
    /// - Returns [`Match(a, b)`][SearchStep::Match] if `haystack[a..b]`
    ///   matches the pattern.
    /// - Returns [`Reject(a, b)`][SearchStep::Reject] if `haystack[a..b]`
    ///   can not match the pattern, even partially.
    /// - Returns [`Done`][SearchStep::Done] if every byte of the haystack
    ///   has been visited
    ///
    /// The stream of [`Match`][SearchStep::Match] and
    /// [`Reject`][SearchStep::Reject] values up to a [`Done`][SearchStep::Done]
    /// will contain index ranges that are adjacent, non-overlapping,
    /// covering the whole haystack, and laying on utf8 boundaries.
    ///
    /// A [`Match`][SearchStep::Match] result needs to contain the whole matched
    /// pattern, however [`Reject`][SearchStep::Reject] results may be split up
    /// into arbitrary many adjacent fragments. Both ranges may have zero length.
    ///
    /// As an example, the pattern `"aaa"` and the haystack `"cbaaaaab"`
    /// might produce the stream
    /// `[Reject(7, 8), Match(4, 7), Reject(1, 4), Reject(0, 1)]`.
    fn next_back(&mut self) -> SearchStep;

    /// Finds the next [`Match`][SearchStep::Match] result.
    /// See [`next_back()`][ReverseSearcher::next_back].
    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }

    /// Finds the next [`Reject`][SearchStep::Reject] result.
    /// See [`next_back()`][ReverseSearcher::next_back].
    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }
}

/// A marker trait to express that a [`ReverseSearcher`]
/// can be used for a [`DoubleEndedIterator`] implementation.
///
/// For this, the impl of [`Searcher`] and [`ReverseSearcher`] need
/// to follow these conditions:
///
/// - All results of `next()` need to be identical
///   to the results of `next_back()` in reverse order.
/// - `next()` and `next_back()` need to behave as
///   the two ends of a range of values, that is they
///   can not "walk past each other".
///
/// # Examples
///
/// `char::Searcher` is a `DoubleEndedSearcher` because searching for a
/// [`char`] only requires looking at one at a time, which behaves the same
/// from both ends.
///
/// `(&str)::Searcher` is not a `DoubleEndedSearcher` because
/// the pattern `"aa"` in the haystack `"aaa"` matches as either
/// `"[aa]a"` or `"a[aa]"`, depending on which side it is searched.
pub trait DoubleEndedSearcher<'a>: ReverseSearcher<'a> {}

/////////////////////////////////////////////////////////////////////////////
// Impl for char
/////////////////////////////////////////////////////////////////////////////

/// Associated type for `<char as Pattern>::Searcher<'a>`.
#[derive(Clone, Debug)]
pub struct CharSearcher<'a> {
    haystack: &'a str,
    // safety invariant: `finger`/`finger_back` must be a valid utf8 byte index of `haystack`
    // This invariant can be broken *within* next_match and next_match_back, however
    // they must exit with fingers on valid code point boundaries.
    /// `finger` is the current byte index of the forward search.
    /// Imagine that it exists before the byte at its index, i.e.
    /// `haystack[finger]` is the first byte of the slice we must inspect during
    /// forward searching
    finger: usize,
    /// `finger_back` is the current byte index of the reverse search.
    /// Imagine that it exists after the byte at its index, i.e.
    /// haystack[finger_back - 1] is the last byte of the slice we must inspect during
    /// forward searching (and thus the first byte to be inspected when calling next_back()).
    finger_back: usize,
    /// The character being searched for
    needle: char,

    // safety invariant: `utf8_size` must be less than 5
    /// The number of bytes `needle` takes up when encoded in utf8.
    utf8_size: u8,
    /// A utf8 encoded copy of the `needle`
    utf8_encoded: [u8; 4],
}

impl CharSearcher<'_> {
    fn utf8_size(&self) -> usize {
        self.utf8_size.into()
    }
}

unsafe impl<'a> Searcher<'a> for CharSearcher<'a> {
    #[inline]
    fn haystack(&self) -> &'a str {
        self.haystack
    }
    #[inline]
    fn next(&mut self) -> SearchStep {
        let old_finger = self.finger;
        // SAFETY: 1-4 guarantee safety of `get_unchecked`
        // 1. `self.finger` and `self.finger_back` are kept on unicode boundaries
        //    (this is invariant)
        // 2. `self.finger >= 0` since it starts at 0 and only increases
        // 3. `self.finger < self.finger_back` because otherwise the char `iter`
        //    would return `SearchStep::Done`
        // 4. `self.finger` comes before the end of the haystack because `self.finger_back`
        //    starts at the end and only decreases
        let slice = unsafe { self.haystack.get_unchecked(old_finger..self.finger_back) };
        let mut iter = slice.chars();
        let old_len = iter.iter.len();
        if let Some(ch) = iter.next() {
            // add byte offset of current character
            // without re-encoding as utf-8
            self.finger += old_len - iter.iter.len();
            if ch == self.needle {
                SearchStep::Match(old_finger, self.finger)
            } else {
                SearchStep::Reject(old_finger, self.finger)
            }
        } else {
            SearchStep::Done
        }
    }
    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        loop {
            // get the haystack after the last character found
            let bytes = self.haystack.as_bytes().get(self.finger..self.finger_back)?;
            // the last byte of the utf8 encoded needle
            // SAFETY: we have an invariant that `utf8_size < 5`
            let last_byte = unsafe { *self.utf8_encoded.get_unchecked(self.utf8_size() - 1) };
            if let Some(index) = memchr::memchr(last_byte, bytes) {
                // The new finger is the index of the byte we found,
                // plus one, since we memchr'd for the last byte of the character.
                //
                // Note that this doesn't always give us a finger on a UTF8 boundary.
                // If we *didn't* find our character
                // we may have indexed to the non-last byte of a 3-byte or 4-byte character.
                // We can't just skip to the next valid starting byte because a character like
                // ꁁ (U+A041 YI SYLLABLE PA), utf-8 `EA 81 81` will have us always find
                // the second byte when searching for the third.
                //
                // However, this is totally okay. While we have the invariant that
                // self.finger is on a UTF8 boundary, this invariant is not relied upon
                // within this method (it is relied upon in CharSearcher::next()).
                //
                // We only exit this method when we reach the end of the string, or if we
                // find something. When we find something the `finger` will be set
                // to a UTF8 boundary.
                self.finger += index + 1;
                if self.finger >= self.utf8_size() {
                    let found_char = self.finger - self.utf8_size();
                    if let Some(slice) = self.haystack.as_bytes().get(found_char..self.finger) {
                        if slice == &self.utf8_encoded[0..self.utf8_size()] {
                            return Some((found_char, self.finger));
                        }
                    }
                }
            } else {
                // found nothing, exit
                self.finger = self.finger_back;
                return None;
            }
        }
    }

    // let next_reject use the default implementation from the Searcher trait
}

unsafe impl<'a> ReverseSearcher<'a> for CharSearcher<'a> {
    #[inline]
    fn next_back(&mut self) -> SearchStep {
        let old_finger = self.finger_back;
        // SAFETY: see the comment for next() above
        let slice = unsafe { self.haystack.get_unchecked(self.finger..old_finger) };
        let mut iter = slice.chars();
        let old_len = iter.iter.len();
        if let Some(ch) = iter.next_back() {
            // subtract byte offset of current character
            // without re-encoding as utf-8
            self.finger_back -= old_len - iter.iter.len();
            if ch == self.needle {
                SearchStep::Match(self.finger_back, old_finger)
            } else {
                SearchStep::Reject(self.finger_back, old_finger)
            }
        } else {
            SearchStep::Done
        }
    }
    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        let haystack = self.haystack.as_bytes();
        loop {
            // get the haystack up to but not including the last character searched
            let bytes = haystack.get(self.finger..self.finger_back)?;
            // the last byte of the utf8 encoded needle
            // SAFETY: we have an invariant that `utf8_size < 5`
            let last_byte = unsafe { *self.utf8_encoded.get_unchecked(self.utf8_size() - 1) };
            if let Some(index) = memchr::memrchr(last_byte, bytes) {
                // we searched a slice that was offset by self.finger,
                // add self.finger to recoup the original index
                let index = self.finger + index;
                // memrchr will return the index of the byte we wish to
                // find. In case of an ASCII character, this is indeed
                // were we wish our new finger to be ("after" the found
                // char in the paradigm of reverse iteration). For
                // multibyte chars we need to skip down by the number of more
                // bytes they have than ASCII
                let shift = self.utf8_size() - 1;
                if index >= shift {
                    let found_char = index - shift;
                    if let Some(slice) = haystack.get(found_char..(found_char + self.utf8_size())) {
                        if slice == &self.utf8_encoded[0..self.utf8_size()] {
                            // move finger to before the character found (i.e., at its start index)
                            self.finger_back = found_char;
                            return Some((self.finger_back, self.finger_back + self.utf8_size()));
                        }
                    }
                }
                // We can't use finger_back = index - size + 1 here. If we found the last char
                // of a different-sized character (or the middle byte of a different character)
                // we need to bump the finger_back down to `index`. This similarly makes
                // `finger_back` have the potential to no longer be on a boundary,
                // but this is OK since we only exit this function on a boundary
                // or when the haystack has been searched completely.
                //
                // Unlike next_match this does not
                // have the problem of repeated bytes in utf-8 because
                // we're searching for the last byte, and we can only have
                // found the last byte when searching in reverse.
                self.finger_back = index;
            } else {
                self.finger_back = self.finger;
                // found nothing, exit
                return None;
            }
        }
    }

    // let next_reject_back use the default implementation from the Searcher trait
}

impl<'a> DoubleEndedSearcher<'a> for CharSearcher<'a> {}

/// Searches for chars that are equal to a given [`char`].
///
/// # Examples
///
/// ```
/// assert_eq!("Hello world".find('o'), Some(4));
/// ```
impl Pattern for char {
    type Searcher<'a> = CharSearcher<'a>;

    #[inline]
    fn into_searcher<'a>(self, haystack: &'a str) -> Self::Searcher<'a> {
        let mut utf8_encoded = [0; char::MAX_LEN_UTF8];
        let utf8_size = self
            .encode_utf8(&mut utf8_encoded)
            .len()
            .try_into()
            .expect("char len should be less than 255");

        CharSearcher {
            haystack,
            finger: 0,
            finger_back: haystack.len(),
            needle: self,
            utf8_size,
            utf8_encoded,
        }
    }

    #[inline]
    fn is_contained_in(self, haystack: &str) -> bool {
        if (self as u32) < 128 {
            haystack.as_bytes().contains(&(self as u8))
        } else {
            let mut buffer = [0u8; 4];
            self.encode_utf8(&mut buffer).is_contained_in(haystack)
        }
    }

    #[inline]
    fn is_prefix_of(self, haystack: &str) -> bool {
        self.encode_utf8(&mut [0u8; 4]).is_prefix_of(haystack)
    }

    #[inline]
    fn strip_prefix_of(self, haystack: &str) -> Option<&str> {
        self.encode_utf8(&mut [0u8; 4]).strip_prefix_of(haystack)
    }

    #[inline]
    fn is_suffix_of<'a>(self, haystack: &'a str) -> bool
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        self.encode_utf8(&mut [0u8; 4]).is_suffix_of(haystack)
    }

    #[inline]
    fn strip_suffix_of<'a>(self, haystack: &'a str) -> Option<&'a str>
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        self.encode_utf8(&mut [0u8; 4]).strip_suffix_of(haystack)
    }

    #[inline]
    fn as_utf8_pattern(&self) -> Option<Utf8Pattern<'_>> {
        Some(Utf8Pattern::CharPattern(*self))
    }
}

/////////////////////////////////////////////////////////////////////////////
// Impl for a MultiCharEq wrapper
/////////////////////////////////////////////////////////////////////////////

#[doc(hidden)]
trait MultiCharEq {
    fn matches(&mut self, c: char) -> bool;
}

impl<F> MultiCharEq for F
where
    F: FnMut(char) -> bool,
{
    #[inline]
    fn matches(&mut self, c: char) -> bool {
        (*self)(c)
    }
}

impl<const N: usize> MultiCharEq for [char; N] {
    #[inline]
    fn matches(&mut self, c: char) -> bool {
        self.contains(&c)
    }
}

impl<const N: usize> MultiCharEq for &[char; N] {
    #[inline]
    fn matches(&mut self, c: char) -> bool {
        self.contains(&c)
    }
}

impl MultiCharEq for &[char] {
    #[inline]
    fn matches(&mut self, c: char) -> bool {
        self.contains(&c)
    }
}

struct MultiCharEqPattern<C: MultiCharEq>(C);

#[derive(Clone, Debug)]
struct MultiCharEqSearcher<'a, C: MultiCharEq> {
    char_eq: C,
    haystack: &'a str,
    char_indices: super::CharIndices<'a>,
}

impl<C: MultiCharEq> Pattern for MultiCharEqPattern<C> {
    type Searcher<'a> = MultiCharEqSearcher<'a, C>;

    #[inline]
    fn into_searcher(self, haystack: &str) -> MultiCharEqSearcher<'_, C> {
        MultiCharEqSearcher { haystack, char_eq: self.0, char_indices: haystack.char_indices() }
    }
}

unsafe impl<'a, C: MultiCharEq> Searcher<'a> for MultiCharEqSearcher<'a, C> {
    #[inline]
    fn haystack(&self) -> &'a str {
        self.haystack
    }

    #[inline]
    fn next(&mut self) -> SearchStep {
        let s = &mut self.char_indices;
        // Compare lengths of the internal byte slice iterator
        // to find length of current char
        let pre_len = s.iter.iter.len();
        if let Some((i, c)) = s.next() {
            let len = s.iter.iter.len();
            let char_len = pre_len - len;
            if self.char_eq.matches(c) {
                return SearchStep::Match(i, i + char_len);
            } else {
                return SearchStep::Reject(i, i + char_len);
            }
        }
        SearchStep::Done
    }
}

unsafe impl<'a, C: MultiCharEq> ReverseSearcher<'a> for MultiCharEqSearcher<'a, C> {
    #[inline]
    fn next_back(&mut self) -> SearchStep {
        let s = &mut self.char_indices;
        // Compare lengths of the internal byte slice iterator
        // to find length of current char
        let pre_len = s.iter.iter.len();
        if let Some((i, c)) = s.next_back() {
            let len = s.iter.iter.len();
            let char_len = pre_len - len;
            if self.char_eq.matches(c) {
                return SearchStep::Match(i, i + char_len);
            } else {
                return SearchStep::Reject(i, i + char_len);
            }
        }
        SearchStep::Done
    }
}

impl<'a, C: MultiCharEq> DoubleEndedSearcher<'a> for MultiCharEqSearcher<'a, C> {}

/////////////////////////////////////////////////////////////////////////////

macro_rules! pattern_methods {
    ($a:lifetime, $t:ty, $pmap:expr, $smap:expr) => {
        type Searcher<$a> = $t;

        #[inline]
        fn into_searcher<$a>(self, haystack: &$a str) -> $t {
            ($smap)(($pmap)(self).into_searcher(haystack))
        }

        #[inline]
        fn is_contained_in<$a>(self, haystack: &$a str) -> bool {
            ($pmap)(self).is_contained_in(haystack)
        }

        #[inline]
        fn is_prefix_of<$a>(self, haystack: &$a str) -> bool {
            ($pmap)(self).is_prefix_of(haystack)
        }

        #[inline]
        fn strip_prefix_of<$a>(self, haystack: &$a str) -> Option<&$a str> {
            ($pmap)(self).strip_prefix_of(haystack)
        }

        #[inline]
        fn is_suffix_of<$a>(self, haystack: &$a str) -> bool
        where
            $t: ReverseSearcher<$a>,
        {
            ($pmap)(self).is_suffix_of(haystack)
        }

        #[inline]
        fn strip_suffix_of<$a>(self, haystack: &$a str) -> Option<&$a str>
        where
            $t: ReverseSearcher<$a>,
        {
            ($pmap)(self).strip_suffix_of(haystack)
        }
    };
}

macro_rules! searcher_methods {
    (forward) => {
        #[inline]
        fn haystack(&self) -> &'a str {
            self.0.haystack()
        }
        #[inline]
        fn next(&mut self) -> SearchStep {
            self.0.next()
        }
        #[inline]
        fn next_match(&mut self) -> Option<(usize, usize)> {
            self.0.next_match()
        }
        #[inline]
        fn next_reject(&mut self) -> Option<(usize, usize)> {
            self.0.next_reject()
        }
    };
    (reverse) => {
        #[inline]
        fn next_back(&mut self) -> SearchStep {
            self.0.next_back()
        }
        #[inline]
        fn next_match_back(&mut self) -> Option<(usize, usize)> {
            self.0.next_match_back()
        }
        #[inline]
        fn next_reject_back(&mut self) -> Option<(usize, usize)> {
            self.0.next_reject_back()
        }
    };
}

/// Associated type for `<[char; N] as Pattern>::Searcher<'a>`.
#[derive(Clone, Debug)]
pub struct CharArraySearcher<'a, const N: usize>(
    <MultiCharEqPattern<[char; N]> as Pattern>::Searcher<'a>,
);

/// Associated type for `<&[char; N] as Pattern>::Searcher<'a>`.
#[derive(Clone, Debug)]
pub struct CharArrayRefSearcher<'a, 'b, const N: usize>(
    <MultiCharEqPattern<&'b [char; N]> as Pattern>::Searcher<'a>,
);

/// Searches for chars that are equal to any of the [`char`]s in the array.
///
/// # Examples
///
/// ```
/// assert_eq!("Hello world".find(['o', 'l']), Some(2));
/// assert_eq!("Hello world".find(['h', 'w']), Some(6));
/// ```
impl<const N: usize> Pattern for [char; N] {
    pattern_methods!('a, CharArraySearcher<'a, N>, MultiCharEqPattern, CharArraySearcher);
}

unsafe impl<'a, const N: usize> Searcher<'a> for CharArraySearcher<'a, N> {
    searcher_methods!(forward);
}

unsafe impl<'a, const N: usize> ReverseSearcher<'a> for CharArraySearcher<'a, N> {
    searcher_methods!(reverse);
}

impl<'a, const N: usize> DoubleEndedSearcher<'a> for CharArraySearcher<'a, N> {}

/// Searches for chars that are equal to any of the [`char`]s in the array.
///
/// # Examples
///
/// ```
/// assert_eq!("Hello world".find(&['o', 'l']), Some(2));
/// assert_eq!("Hello world".find(&['h', 'w']), Some(6));
/// ```
impl<'b, const N: usize> Pattern for &'b [char; N] {
    pattern_methods!('a, CharArrayRefSearcher<'a, 'b, N>, MultiCharEqPattern, CharArrayRefSearcher);
}

unsafe impl<'a, 'b, const N: usize> Searcher<'a> for CharArrayRefSearcher<'a, 'b, N> {
    searcher_methods!(forward);
}

unsafe impl<'a, 'b, const N: usize> ReverseSearcher<'a> for CharArrayRefSearcher<'a, 'b, N> {
    searcher_methods!(reverse);
}

impl<'a, 'b, const N: usize> DoubleEndedSearcher<'a> for CharArrayRefSearcher<'a, 'b, N> {}

/////////////////////////////////////////////////////////////////////////////
// Impl for &[char]
/////////////////////////////////////////////////////////////////////////////

// Todo: Change / Remove due to ambiguity in meaning.

/// Associated type for `<&[char] as Pattern>::Searcher<'a>`.
#[derive(Clone, Debug)]
pub struct CharSliceSearcher<'a, 'b>(<MultiCharEqPattern<&'b [char]> as Pattern>::Searcher<'a>);

unsafe impl<'a, 'b> Searcher<'a> for CharSliceSearcher<'a, 'b> {
    searcher_methods!(forward);
}

unsafe impl<'a, 'b> ReverseSearcher<'a> for CharSliceSearcher<'a, 'b> {
    searcher_methods!(reverse);
}

impl<'a, 'b> DoubleEndedSearcher<'a> for CharSliceSearcher<'a, 'b> {}

/// Searches for chars that are equal to any of the [`char`]s in the slice.
///
/// # Examples
///
/// ```
/// assert_eq!("Hello world".find(&['o', 'l'][..]), Some(2));
/// assert_eq!("Hello world".find(&['h', 'w'][..]), Some(6));
/// ```
impl<'b> Pattern for &'b [char] {
    pattern_methods!('a, CharSliceSearcher<'a, 'b>, MultiCharEqPattern, CharSliceSearcher);
}

/////////////////////////////////////////////////////////////////////////////
// Impl for F: FnMut(char) -> bool
/////////////////////////////////////////////////////////////////////////////

/// Associated type for `<F as Pattern>::Searcher<'a>`.
#[derive(Clone)]
pub struct CharPredicateSearcher<'a, F>(<MultiCharEqPattern<F> as Pattern>::Searcher<'a>)
where
    F: FnMut(char) -> bool;

impl<F> fmt::Debug for CharPredicateSearcher<'_, F>
where
    F: FnMut(char) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CharPredicateSearcher")
            .field("haystack", &self.0.haystack)
            .field("char_indices", &self.0.char_indices)
            .finish()
    }
}
unsafe impl<'a, F> Searcher<'a> for CharPredicateSearcher<'a, F>
where
    F: FnMut(char) -> bool,
{
    searcher_methods!(forward);
}

unsafe impl<'a, F> ReverseSearcher<'a> for CharPredicateSearcher<'a, F>
where
    F: FnMut(char) -> bool,
{
    searcher_methods!(reverse);
}

impl<'a, F> DoubleEndedSearcher<'a> for CharPredicateSearcher<'a, F> where F: FnMut(char) -> bool {}

/// Searches for [`char`]s that match the given predicate.
///
/// # Examples
///
/// ```
/// assert_eq!("Hello world".find(char::is_uppercase), Some(0));
/// assert_eq!("Hello world".find(|c| "aeiou".contains(c)), Some(1));
/// ```
impl<F> Pattern for F
where
    F: FnMut(char) -> bool,
{
    pattern_methods!('a, CharPredicateSearcher<'a, F>, MultiCharEqPattern, CharPredicateSearcher);
}

/////////////////////////////////////////////////////////////////////////////
// Impl for &&str
/////////////////////////////////////////////////////////////////////////////

/// Delegates to the `&str` impl.
impl<'b, 'c> Pattern for &'c &'b str {
    pattern_methods!('a, StrSearcher<'a, 'b>, |&s| s, |s| s);
}

/////////////////////////////////////////////////////////////////////////////
// Impl for &str
/////////////////////////////////////////////////////////////////////////////

/// Non-allocating substring search.
///
/// Will handle the pattern `""` as returning empty matches at each character
/// boundary.
///
/// # Examples
///
/// ```
/// assert_eq!("Hello world".find("world"), Some(6));
/// ```
impl<'b> Pattern for &'b str {
    type Searcher<'a> = StrSearcher<'a, 'b>;

    #[inline]
    fn into_searcher(self, haystack: &str) -> StrSearcher<'_, 'b> {
        StrSearcher::new(haystack, self)
    }

    /// Checks whether the pattern matches at the front of the haystack.
    #[inline]
    fn is_prefix_of(self, haystack: &str) -> bool {
        haystack.as_bytes().starts_with(self.as_bytes())
    }

    /// Checks whether the pattern matches anywhere in the haystack
    #[inline]
    fn is_contained_in(self, haystack: &str) -> bool {
        if self.len() == 0 {
            return true;
        }

        match self.len().cmp(&haystack.len()) {
            Ordering::Less => {
                if self.len() == 1 {
                    return haystack.as_bytes().contains(&self.as_bytes()[0]);
                }

                #[cfg(any(
                    all(target_arch = "x86_64", target_feature = "sse2"),
                    all(target_arch = "loongarch64", target_feature = "lsx")
                ))]
                if self.len() <= 32 {
                    if let Some(result) = simd_contains(self, haystack) {
                        return result;
                    }
                }

                self.into_searcher(haystack).next_match().is_some()
            }
            _ => self == haystack,
        }
    }

    /// Removes the pattern from the front of haystack, if it matches.
    #[inline]
    fn strip_prefix_of(self, haystack: &str) -> Option<&str> {
        if self.is_prefix_of(haystack) {
            // SAFETY: prefix was just verified to exist.
            unsafe { Some(haystack.get_unchecked(self.as_bytes().len()..)) }
        } else {
            None
        }
    }

    /// Checks whether the pattern matches at the back of the haystack.
    #[inline]
    fn is_suffix_of<'a>(self, haystack: &'a str) -> bool
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        haystack.as_bytes().ends_with(self.as_bytes())
    }

    /// Removes the pattern from the back of haystack, if it matches.
    #[inline]
    fn strip_suffix_of<'a>(self, haystack: &'a str) -> Option<&'a str>
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        if self.is_suffix_of(haystack) {
            let i = haystack.len() - self.as_bytes().len();
            // SAFETY: suffix was just verified to exist.
            unsafe { Some(haystack.get_unchecked(..i)) }
        } else {
            None
        }
    }

    #[inline]
    fn as_utf8_pattern(&self) -> Option<Utf8Pattern<'_>> {
        Some(Utf8Pattern::StringPattern(self.as_bytes()))
    }
}

/////////////////////////////////////////////////////////////////////////////
// Two Way substring searcher
/////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Debug)]
/// Associated type for `<&str as Pattern>::Searcher<'a>`.
pub struct StrSearcher<'a, 'b> {
    haystack: &'a str,
    needle: &'b str,

    searcher: StrSearcherImpl,
}

#[derive(Clone, Debug)]
enum StrSearcherImpl {
    Empty(EmptyNeedle),
    TwoWay(TwoWaySearcher),
}

#[derive(Clone, Debug)]
struct EmptyNeedle {
    position: usize,
    end: usize,
    is_match_fw: bool,
    is_match_bw: bool,
    // Needed in case of an empty haystack, see #85462
    is_finished: bool,
}

impl<'a, 'b> StrSearcher<'a, 'b> {
    fn new(haystack: &'a str, needle: &'b str) -> StrSearcher<'a, 'b> {
        if needle.is_empty() {
            StrSearcher {
                haystack,
                needle,
                searcher: StrSearcherImpl::Empty(EmptyNeedle {
                    position: 0,
                    end: haystack.len(),
                    is_match_fw: true,
                    is_match_bw: true,
                    is_finished: false,
                }),
            }
        } else {
            StrSearcher {
                haystack,
                needle,
                searcher: StrSearcherImpl::TwoWay(TwoWaySearcher::new(
                    needle.as_bytes(),
                    haystack.len(),
                )),
            }
        }
    }
}

unsafe impl<'a, 'b> Searcher<'a> for StrSearcher<'a, 'b> {
    #[inline]
    fn haystack(&self) -> &'a str {
        self.haystack
    }

    #[inline]
    fn next(&mut self) -> SearchStep {
        match self.searcher {
            StrSearcherImpl::Empty(ref mut searcher) => {
                if searcher.is_finished {
                    return SearchStep::Done;
                }
                // empty needle rejects every char and matches every empty string between them
                let is_match = searcher.is_match_fw;
                searcher.is_match_fw = !searcher.is_match_fw;
                let pos = searcher.position;
                match self.haystack[pos..].chars().next() {
                    _ if is_match => SearchStep::Match(pos, pos),
                    None => {
                        searcher.is_finished = true;
                        SearchStep::Done
                    }
                    Some(ch) => {
                        searcher.position += ch.len_utf8();
                        SearchStep::Reject(pos, searcher.position)
                    }
                }
            }
            StrSearcherImpl::TwoWay(ref mut searcher) => {
                // TwoWaySearcher produces valid *Match* indices that split at char boundaries
                // as long as it does correct matching and that haystack and needle are
                // valid UTF-8
                // *Rejects* from the algorithm can fall on any indices, but we will walk them
                // manually to the next character boundary, so that they are utf-8 safe.
                if searcher.position == self.haystack.len() {
                    return SearchStep::Done;
                }
                let is_long = searcher.memory == usize::MAX;
                match searcher.next::<RejectAndMatch>(
                    self.haystack.as_bytes(),
                    self.needle.as_bytes(),
                    is_long,
                ) {
                    SearchStep::Reject(a, mut b) => {
                        // skip to next char boundary
                        while !self.haystack.is_char_boundary(b) {
                            b += 1;
                        }
                        searcher.position = cmp::max(b, searcher.position);
                        SearchStep::Reject(a, b)
                    }
                    otherwise => otherwise,
                }
            }
        }
    }

    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        match self.searcher {
            StrSearcherImpl::Empty(..) => loop {
                match self.next() {
                    SearchStep::Match(a, b) => return Some((a, b)),
                    SearchStep::Done => return None,
                    SearchStep::Reject(..) => {}
                }
            },
            StrSearcherImpl::TwoWay(ref mut searcher) => {
                let is_long = searcher.memory == usize::MAX;
                // write out `true` and `false` cases to encourage the compiler
                // to specialize the two cases separately.
                if is_long {
                    searcher.next::<MatchOnly>(
                        self.haystack.as_bytes(),
                        self.needle.as_bytes(),
                        true,
                    )
                } else {
                    searcher.next::<MatchOnly>(
                        self.haystack.as_bytes(),
                        self.needle.as_bytes(),
                        false,
                    )
                }
            }
        }
    }
}

unsafe impl<'a, 'b> ReverseSearcher<'a> for StrSearcher<'a, 'b> {
    #[inline]
    fn next_back(&mut self) -> SearchStep {
        match self.searcher {
            StrSearcherImpl::Empty(ref mut searcher) => {
                if searcher.is_finished {
                    return SearchStep::Done;
                }
                let is_match = searcher.is_match_bw;
                searcher.is_match_bw = !searcher.is_match_bw;
                let end = searcher.end;
                match self.haystack[..end].chars().next_back() {
                    _ if is_match => SearchStep::Match(end, end),
                    None => {
                        searcher.is_finished = true;
                        SearchStep::Done
                    }
                    Some(ch) => {
                        searcher.end -= ch.len_utf8();
                        SearchStep::Reject(searcher.end, end)
                    }
                }
            }
            StrSearcherImpl::TwoWay(ref mut searcher) => {
                if searcher.end == 0 {
                    return SearchStep::Done;
                }
                let is_long = searcher.memory == usize::MAX;
                match searcher.next_back::<RejectAndMatch>(
                    self.haystack.as_bytes(),
                    self.needle.as_bytes(),
                    is_long,
                ) {
                    SearchStep::Reject(mut a, b) => {
                        // skip to next char boundary
                        while !self.haystack.is_char_boundary(a) {
                            a -= 1;
                        }
                        searcher.end = cmp::min(a, searcher.end);
                        SearchStep::Reject(a, b)
                    }
                    otherwise => otherwise,
                }
            }
        }
    }

    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        match self.searcher {
            StrSearcherImpl::Empty(..) => loop {
                match self.next_back() {
                    SearchStep::Match(a, b) => return Some((a, b)),
                    SearchStep::Done => return None,
                    SearchStep::Reject(..) => {}
                }
            },
            StrSearcherImpl::TwoWay(ref mut searcher) => {
                let is_long = searcher.memory == usize::MAX;
                // write out `true` and `false`, like `next_match`
                if is_long {
                    searcher.next_back::<MatchOnly>(
                        self.haystack.as_bytes(),
                        self.needle.as_bytes(),
                        true,
                    )
                } else {
                    searcher.next_back::<MatchOnly>(
                        self.haystack.as_bytes(),
                        self.needle.as_bytes(),
                        false,
                    )
                }
            }
        }
    }
}

/// The internal state of the two-way substring search algorithm.
#[derive(Clone, Debug)]
struct TwoWaySearcher {
    // constants
    /// critical factorization index
    crit_pos: usize,
    /// critical factorization index for reversed needle
    crit_pos_back: usize,
    period: usize,
    /// `byteset` is an extension (not part of the two way algorithm);
    /// it's a 64-bit "fingerprint" where each set bit `j` corresponds
    /// to a (byte & 63) == j present in the needle.
    byteset: u64,

    // variables
    position: usize,
    end: usize,
    /// index into needle before which we have already matched
    memory: usize,
    /// index into needle after which we have already matched
    memory_back: usize,
}

/*
    This is the Two-Way search algorithm, which was introduced in the paper:
    Crochemore, M., Perrin, D., 1991, Two-way string-matching, Journal of the ACM 38(3):651-675.

    Here's some background information.

    A *word* is a string of symbols. The *length* of a word should be a familiar
    notion, and here we denote it for any word x by |x|.
    (We also allow for the possibility of the *empty word*, a word of length zero).

    If x is any non-empty word, then an integer p with 0 < p <= |x| is said to be a
    *period* for x iff for all i with 0 <= i <= |x| - p - 1, we have x[i] == x[i+p].
    For example, both 1 and 2 are periods for the string "aa". As another example,
    the only period of the string "abcd" is 4.

    We denote by period(x) the *smallest* period of x (provided that x is non-empty).
    This is always well-defined since every non-empty word x has at least one period,
    |x|. We sometimes call this *the period* of x.

    If u, v and x are words such that x = uv, where uv is the concatenation of u and
    v, then we say that (u, v) is a *factorization* of x.

    Let (u, v) be a factorization for a word x. Then if w is a non-empty word such
    that both of the following hold

      - either w is a suffix of u or u is a suffix of w
      - either w is a prefix of v or v is a prefix of w

    then w is said to be a *repetition* for the factorization (u, v).

    Just to unpack this, there are four possibilities here. Let w = "abc". Then we
    might have:

      - w is a suffix of u and w is a prefix of v. ex: ("lolabc", "abcde")
      - w is a suffix of u and v is a prefix of w. ex: ("lolabc", "ab")
      - u is a suffix of w and w is a prefix of v. ex: ("bc", "abchi")
      - u is a suffix of w and v is a prefix of w. ex: ("bc", "a")

    Note that the word vu is a repetition for any factorization (u,v) of x = uv,
    so every factorization has at least one repetition.

    If x is a string and (u, v) is a factorization for x, then a *local period* for
    (u, v) is an integer r such that there is some word w such that |w| = r and w is
    a repetition for (u, v).

    We denote by local_period(u, v) the smallest local period of (u, v). We sometimes
    call this *the local period* of (u, v). Provided that x = uv is non-empty, this
    is well-defined (because each non-empty word has at least one factorization, as
    noted above).

    It can be proven that the following is an equivalent definition of a local period
    for a factorization (u, v): any positive integer r such that x[i] == x[i+r] for
    all i such that |u| - r <= i <= |u| - 1 and such that both x[i] and x[i+r] are
    defined. (i.e., i > 0 and i + r < |x|).

    Using the above reformulation, it is easy to prove that

        1 <= local_period(u, v) <= period(uv)

    A factorization (u, v) of x such that local_period(u,v) = period(x) is called a
    *critical factorization*.

    The algorithm hinges on the following theorem, which is stated without proof:

    **Critical Factorization Theorem** Any word x has at least one critical
    factorization (u, v) such that |u| < period(x).

    The purpose of maximal_suffix is to find such a critical factorization.

    If the period is short, compute another factorization x = u' v' to use
    for reverse search, chosen instead so that |v'| < period(x).

*/
impl TwoWaySearcher {
    fn new(needle: &[u8], end: usize) -> TwoWaySearcher {
        let (crit_pos_false, period_false) = TwoWaySearcher::maximal_suffix(needle, false);
        let (crit_pos_true, period_true) = TwoWaySearcher::maximal_suffix(needle, true);

        let (crit_pos, period) = if crit_pos_false > crit_pos_true {
            (crit_pos_false, period_false)
        } else {
            (crit_pos_true, period_true)
        };

        // A particularly readable explanation of what's going on here can be found
        // in Crochemore and Rytter's book "Text Algorithms", ch 13. Specifically
        // see the code for "Algorithm CP" on p. 323.
        //
        // What's going on is we have some critical factorization (u, v) of the
        // needle, and we want to determine whether u is a suffix of
        // &v[..period]. If it is, we use "Algorithm CP1". Otherwise we use
        // "Algorithm CP2", which is optimized for when the period of the needle
        // is large.
        if needle[..crit_pos] == needle[period..period + crit_pos] {
            // short period case -- the period is exact
            // compute a separate critical factorization for the reversed needle
            // x = u' v' where |v'| < period(x).
            //
            // This is sped up by the period being known already.
            // Note that a case like x = "acba" may be factored exactly forwards
            // (crit_pos = 1, period = 3) while being factored with approximate
            // period in reverse (crit_pos = 2, period = 2). We use the given
            // reverse factorization but keep the exact period.
            let crit_pos_back = needle.len()
                - cmp::max(
                    TwoWaySearcher::reverse_maximal_suffix(needle, period, false),
                    TwoWaySearcher::reverse_maximal_suffix(needle, period, true),
                );

            TwoWaySearcher {
                crit_pos,
                crit_pos_back,
                period,
                byteset: Self::byteset_create(&needle[..period]),

                position: 0,
                end,
                memory: 0,
                memory_back: needle.len(),
            }
        } else {
            // long period case -- we have an approximation to the actual period,
            // and don't use memorization.
            //
            // Approximate the period by lower bound max(|u|, |v|) + 1.
            // The critical factorization is efficient to use for both forward and
            // reverse search.

            TwoWaySearcher {
                crit_pos,
                crit_pos_back: crit_pos,
                period: cmp::max(crit_pos, needle.len() - crit_pos) + 1,
                byteset: Self::byteset_create(needle),

                position: 0,
                end,
                memory: usize::MAX, // Dummy value to signify that the period is long
                memory_back: usize::MAX,
            }
        }
    }

    #[inline]
    fn byteset_create(bytes: &[u8]) -> u64 {
        bytes.iter().fold(0, |a, &b| (1 << (b & 0x3f)) | a)
    }

    #[inline]
    fn byteset_contains(&self, byte: u8) -> bool {
        (self.byteset >> ((byte & 0x3f) as usize)) & 1 != 0
    }

    // One of the main ideas of Two-Way is that we factorize the needle into
    // two halves, (u, v), and begin trying to find v in the haystack by scanning
    // left to right. If v matches, we try to match u by scanning right to left.
    // How far we can jump when we encounter a mismatch is all based on the fact
    // that (u, v) is a critical factorization for the needle.
    #[inline]
    fn next<S>(&mut self, haystack: &[u8], needle: &[u8], long_period: bool) -> S::Output
    where
        S: TwoWayStrategy,
    {
        // `next()` uses `self.position` as its cursor
        let old_pos = self.position;
        let needle_last = needle.len() - 1;
        'search: loop {
            // Check that we have room to search in
            // position + needle_last can not overflow if we assume slices
            // are bounded by isize's range.
            let tail_byte = match haystack.get(self.position + needle_last) {
                Some(&b) => b,
                None => {
                    self.position = haystack.len();
                    return S::rejecting(old_pos, self.position);
                }
            };

            if S::use_early_reject() && old_pos != self.position {
                return S::rejecting(old_pos, self.position);
            }

            // Quickly skip by large portions unrelated to our substring
            if !self.byteset_contains(tail_byte) {
                self.position += needle.len();
                if !long_period {
                    self.memory = 0;
                }
                continue 'search;
            }

            // See if the right part of the needle matches
            let start =
                if long_period { self.crit_pos } else { cmp::max(self.crit_pos, self.memory) };
            for i in start..needle.len() {
                if needle[i] != haystack[self.position + i] {
                    self.position += i - self.crit_pos + 1;
                    if !long_period {
                        self.memory = 0;
                    }
                    continue 'search;
                }
            }

            // See if the left part of the needle matches
            let start = if long_period { 0 } else { self.memory };
            for i in (start..self.crit_pos).rev() {
                if needle[i] != haystack[self.position + i] {
                    self.position += self.period;
                    if !long_period {
                        self.memory = needle.len() - self.period;
                    }
                    continue 'search;
                }
            }

            // We have found a match!
            let match_pos = self.position;

            // Note: add self.period instead of needle.len() to have overlapping matches
            self.position += needle.len();
            if !long_period {
                self.memory = 0; // set to needle.len() - self.period for overlapping matches
            }

            return S::matching(match_pos, match_pos + needle.len());
        }
    }

    // Follows the ideas in `next()`.
    //
    // The definitions are symmetrical, with period(x) = period(reverse(x))
    // and local_period(u, v) = local_period(reverse(v), reverse(u)), so if (u, v)
    // is a critical factorization, so is (reverse(v), reverse(u)).
    //
    // For the reverse case we have computed a critical factorization x = u' v'
    // (field `crit_pos_back`). We need |u| < period(x) for the forward case and
    // thus |v'| < period(x) for the reverse.
    //
    // To search in reverse through the haystack, we search forward through
    // a reversed haystack with a reversed needle, matching first u' and then v'.
    #[inline]
    fn next_back<S>(&mut self, haystack: &[u8], needle: &[u8], long_period: bool) -> S::Output
    where
        S: TwoWayStrategy,
    {
        // `next_back()` uses `self.end` as its cursor -- so that `next()` and `next_back()`
        // are independent.
        let old_end = self.end;
        'search: loop {
            // Check that we have room to search in
            // end - needle.len() will wrap around when there is no more room,
            // but due to slice length limits it can never wrap all the way back
            // into the length of haystack.
            let front_byte = match haystack.get(self.end.wrapping_sub(needle.len())) {
                Some(&b) => b,
                None => {
                    self.end = 0;
                    return S::rejecting(0, old_end);
                }
            };

            if S::use_early_reject() && old_end != self.end {
                return S::rejecting(self.end, old_end);
            }

            // Quickly skip by large portions unrelated to our substring
            if !self.byteset_contains(front_byte) {
                self.end -= needle.len();
                if !long_period {
                    self.memory_back = needle.len();
                }
                continue 'search;
            }

            // See if the left part of the needle matches
            let crit = if long_period {
                self.crit_pos_back
            } else {
                cmp::min(self.crit_pos_back, self.memory_back)
            };
            for i in (0..crit).rev() {
                if needle[i] != haystack[self.end - needle.len() + i] {
                    self.end -= self.crit_pos_back - i;
                    if !long_period {
                        self.memory_back = needle.len();
                    }
                    continue 'search;
                }
            }

            // See if the right part of the needle matches
            let needle_end = if long_period { needle.len() } else { self.memory_back };
            for i in self.crit_pos_back..needle_end {
                if needle[i] != haystack[self.end - needle.len() + i] {
                    self.end -= self.period;
                    if !long_period {
                        self.memory_back = self.period;
                    }
                    continue 'search;
                }
            }

            // We have found a match!
            let match_pos = self.end - needle.len();
            // Note: sub self.period instead of needle.len() to have overlapping matches
            self.end -= needle.len();
            if !long_period {
                self.memory_back = needle.len();
            }

            return S::matching(match_pos, match_pos + needle.len());
        }
    }

    // Compute the maximal suffix of `arr`.
    //
    // The maximal suffix is a possible critical factorization (u, v) of `arr`.
    //
    // Returns (`i`, `p`) where `i` is the starting index of v and `p` is the
    // period of v.
    //
    // `order_greater` determines if lexical order is `<` or `>`. Both
    // orders must be computed -- the ordering with the largest `i` gives
    // a critical factorization.
    //
    // For long period cases, the resulting period is not exact (it is too short).
    #[inline]
    fn maximal_suffix(arr: &[u8], order_greater: bool) -> (usize, usize) {
        let mut left = 0; // Corresponds to i in the paper
        let mut right = 1; // Corresponds to j in the paper
        let mut offset = 0; // Corresponds to k in the paper, but starting at 0
        // to match 0-based indexing.
        let mut period = 1; // Corresponds to p in the paper

        while let Some(&a) = arr.get(right + offset) {
            // `left` will be inbounds when `right` is.
            let b = arr[left + offset];
            if (a < b && !order_greater) || (a > b && order_greater) {
                // Suffix is smaller, period is entire prefix so far.
                right += offset + 1;
                offset = 0;
                period = right - left;
            } else if a == b {
                // Advance through repetition of the current period.
                if offset + 1 == period {
                    right += offset + 1;
                    offset = 0;
                } else {
                    offset += 1;
                }
            } else {
                // Suffix is larger, start over from current location.
                left = right;
                right += 1;
                offset = 0;
                period = 1;
            }
        }
        (left, period)
    }

    // Compute the maximal suffix of the reverse of `arr`.
    //
    // The maximal suffix is a possible critical factorization (u', v') of `arr`.
    //
    // Returns `i` where `i` is the starting index of v', from the back;
    // returns immediately when a period of `known_period` is reached.
    //
    // `order_greater` determines if lexical order is `<` or `>`. Both
    // orders must be computed -- the ordering with the largest `i` gives
    // a critical factorization.
    //
    // For long period cases, the resulting period is not exact (it is too short).
    fn reverse_maximal_suffix(arr: &[u8], known_period: usize, order_greater: bool) -> usize {
        let mut left = 0; // Corresponds to i in the paper
        let mut right = 1; // Corresponds to j in the paper
        let mut offset = 0; // Corresponds to k in the paper, but starting at 0
        // to match 0-based indexing.
        let mut period = 1; // Corresponds to p in the paper
        let n = arr.len();

        while right + offset < n {
            let a = arr[n - (1 + right + offset)];
            let b = arr[n - (1 + left + offset)];
            if (a < b && !order_greater) || (a > b && order_greater) {
                // Suffix is smaller, period is entire prefix so far.
                right += offset + 1;
                offset = 0;
                period = right - left;
            } else if a == b {
                // Advance through repetition of the current period.
                if offset + 1 == period {
                    right += offset + 1;
                    offset = 0;
                } else {
                    offset += 1;
                }
            } else {
                // Suffix is larger, start over from current location.
                left = right;
                right += 1;
                offset = 0;
                period = 1;
            }
            if period == known_period {
                break;
            }
        }
        debug_assert!(period <= known_period);
        left
    }
}

// TwoWayStrategy allows the algorithm to either skip non-matches as quickly
// as possible, or to work in a mode where it emits Rejects relatively quickly.
trait TwoWayStrategy {
    type Output;
    fn use_early_reject() -> bool;
    fn rejecting(a: usize, b: usize) -> Self::Output;
    fn matching(a: usize, b: usize) -> Self::Output;
}

/// Skip to match intervals as quickly as possible
enum MatchOnly {}

impl TwoWayStrategy for MatchOnly {
    type Output = Option<(usize, usize)>;

    #[inline]
    fn use_early_reject() -> bool {
        false
    }
    #[inline]
    fn rejecting(_a: usize, _b: usize) -> Self::Output {
        None
    }
    #[inline]
    fn matching(a: usize, b: usize) -> Self::Output {
        Some((a, b))
    }
}

/// Emit Rejects regularly
enum RejectAndMatch {}

impl TwoWayStrategy for RejectAndMatch {
    type Output = SearchStep;

    #[inline]
    fn use_early_reject() -> bool {
        true
    }
    #[inline]
    fn rejecting(a: usize, b: usize) -> Self::Output {
        SearchStep::Reject(a, b)
    }
    #[inline]
    fn matching(a: usize, b: usize) -> Self::Output {
        SearchStep::Match(a, b)
    }
}

/// SIMD search for short needles based on
/// Wojciech Muła's "SIMD-friendly algorithms for substring searching"[0]
///
/// It skips ahead by the vector width on each iteration (rather than the needle length as two-way
/// does) by probing the first and last byte of the needle for the whole vector width
/// and only doing full needle comparisons when the vectorized probe indicated potential matches.
///
/// Since the x86_64 baseline only offers SSE2 we only use u8x16 here.
/// If we ever ship std with for x86-64-v3 or adapt this for other platforms then wider vectors
/// should be evaluated.
///
/// Similarly, on LoongArch the 128-bit LSX vector extension is the baseline,
/// so we also use `u8x16` there. Wider vector widths may be considered
/// for future LoongArch extensions (e.g., LASX).
///
/// For haystacks smaller than vector-size + needle length it falls back to
/// a naive O(n*m) search so this implementation should not be called on larger needles.
///
/// [0]: http://0x80.pl/articles/simd-strfind.html#sse-avx2
#[cfg(any(
    all(target_arch = "x86_64", target_feature = "sse2"),
    all(target_arch = "loongarch64", target_feature = "lsx")
))]
#[inline]
fn simd_contains(needle: &str, haystack: &str) -> Option<bool> {
    let needle = needle.as_bytes();
    let haystack = haystack.as_bytes();

    debug_assert!(needle.len() > 1);

    use crate::ops::BitAnd;
    use crate::simd::cmp::SimdPartialEq;
    use crate::simd::{mask8x16 as Mask, u8x16 as Block};

    let first_probe = needle[0];
    let last_byte_offset = needle.len() - 1;

    // the offset used for the 2nd vector
    let second_probe_offset = if needle.len() == 2 {
        // never bail out on len=2 needles because the probes will fully cover them and have
        // no degenerate cases.
        1
    } else {
        // try a few bytes in case first and last byte of the needle are the same
        let Some(second_probe_offset) =
            (needle.len().saturating_sub(4)..needle.len()).rfind(|&idx| needle[idx] != first_probe)
        else {
            // fall back to other search methods if we can't find any different bytes
            // since we could otherwise hit some degenerate cases
            return None;
        };
        second_probe_offset
    };

    // do a naive search if the haystack is too small to fit
    if haystack.len() < Block::LEN + last_byte_offset {
        return Some(haystack.windows(needle.len()).any(|c| c == needle));
    }

    let first_probe: Block = Block::splat(first_probe);
    let second_probe: Block = Block::splat(needle[second_probe_offset]);
    // first byte are already checked by the outer loop. to verify a match only the
    // remainder has to be compared.
    let trimmed_needle = &needle[1..];

    // this #[cold] is load-bearing, benchmark before removing it...
    let check_mask = #[cold]
    |idx, mask: u16, skip: bool| -> bool {
        if skip {
            return false;
        }

        // and so is this. optimizations are weird.
        let mut mask = mask;

        while mask != 0 {
            let trailing = mask.trailing_zeros();
            let offset = idx + trailing as usize + 1;
            // SAFETY: mask is between 0 and 15 trailing zeroes, we skip one additional byte that was already compared
            // and then take trimmed_needle.len() bytes. This is within the bounds defined by the outer loop
            unsafe {
                let sub = haystack.get_unchecked(offset..).get_unchecked(..trimmed_needle.len());
                if small_slice_eq(sub, trimmed_needle) {
                    return true;
                }
            }
            mask &= !(1 << trailing);
        }
        false
    };

    let test_chunk = |idx| -> u16 {
        // SAFETY: this requires at least LANES bytes being readable at idx
        // that is ensured by the loop ranges (see comments below)
        let a: Block = unsafe { haystack.as_ptr().add(idx).cast::<Block>().read_unaligned() };
        // SAFETY: this requires LANES + block_offset bytes being readable at idx
        let b: Block = unsafe {
            haystack.as_ptr().add(idx).add(second_probe_offset).cast::<Block>().read_unaligned()
        };
        let eq_first: Mask = a.simd_eq(first_probe);
        let eq_last: Mask = b.simd_eq(second_probe);
        let both = eq_first.bitand(eq_last);
        let mask = both.to_bitmask() as u16;

        mask
    };

    let mut i = 0;
    let mut result = false;
    // The loop condition must ensure that there's enough headroom to read LANE bytes,
    // and not only at the current index but also at the index shifted by block_offset
    const UNROLL: usize = 4;
    while i + last_byte_offset + UNROLL * Block::LEN < haystack.len() && !result {
        let mut masks = [0u16; UNROLL];
        for j in 0..UNROLL {
            masks[j] = test_chunk(i + j * Block::LEN);
        }
        for j in 0..UNROLL {
            let mask = masks[j];
            if mask != 0 {
                result |= check_mask(i + j * Block::LEN, mask, result);
            }
        }
        i += UNROLL * Block::LEN;
    }
    while i + last_byte_offset + Block::LEN < haystack.len() && !result {
        let mask = test_chunk(i);
        if mask != 0 {
            result |= check_mask(i, mask, result);
        }
        i += Block::LEN;
    }

    // Process the tail that didn't fit into LANES-sized steps.
    // This simply repeats the same procedure but as right-aligned chunk instead
    // of a left-aligned one. The last byte must be exactly flush with the string end so
    // we don't miss a single byte or read out of bounds.
    let i = haystack.len() - last_byte_offset - Block::LEN;
    let mask = test_chunk(i);
    if mask != 0 {
        result |= check_mask(i, mask, result);
    }

    Some(result)
}

/// Compares short slices for equality.
///
/// It avoids a call to libc's memcmp which is faster on long slices
/// due to SIMD optimizations but it incurs a function call overhead.
///
/// # Safety
///
/// Both slices must have the same length.
#[cfg(any(
    all(target_arch = "x86_64", any(kani, target_feature = "sse2")),
    all(target_arch = "loongarch64", target_feature = "lsx")
))]
#[inline]
#[requires(x.len() == y.len())]
unsafe fn small_slice_eq(x: &[u8], y: &[u8]) -> bool {
    debug_assert_eq!(x.len(), y.len());
    // This function is adapted from
    // https://github.com/BurntSushi/memchr/blob/8037d11b4357b0f07be2bb66dc2659d9cf28ad32/src/memmem/util.rs#L32

    // If we don't have enough bytes to do 4-byte at a time loads, then
    // fall back to the naive slow version.
    //
    // Potential alternative: We could do a copy_nonoverlapping combined with a mask instead
    // of a loop. Benchmark it.
    if x.len() < 4 {
        for (&b1, &b2) in x.iter().zip(y) {
            if b1 != b2 {
                return false;
            }
        }
        return true;
    }
    // When we have 4 or more bytes to compare, then proceed in chunks of 4 at
    // a time using unaligned loads.
    //
    // Also, why do 4 byte loads instead of, say, 8 byte loads? The reason is
    // that this particular version of memcmp is likely to be called with tiny
    // needles. That means that if we do 8 byte loads, then a higher proportion
    // of memcmp calls will use the slower variant above. With that said, this
    // is a hypothesis and is only loosely supported by benchmarks. There's
    // likely some improvement that could be made here. The main thing here
    // though is to optimize for latency, not throughput.

    // SAFETY: Via the conditional above, we know that both `px` and `py`
    // have the same length, so `px < pxend` implies that `py < pyend`.
    // Thus, dereferencing both `px` and `py` in the loop below is safe.
    //
    // Moreover, we set `pxend` and `pyend` to be 4 bytes before the actual
    // end of `px` and `py`. Thus, the final dereference outside of the
    // loop is guaranteed to be valid. (The final comparison will overlap with
    // the last comparison done in the loop for lengths that aren't multiples
    // of four.)
    //
    // Finally, we needn't worry about alignment here, since we do unaligned
    // loads.
    unsafe {
        let (mut px, mut py) = (x.as_ptr(), y.as_ptr());
        let (pxend, pyend) = (px.add(x.len() - 4), py.add(y.len() - 4));
        #[loop_invariant(crate::ub_checks::same_allocation(on_entry(px), px)
        && crate::ub_checks::same_allocation(on_entry(py), py)
        && px.addr() >= on_entry(px).addr()
        && py.addr() >= on_entry(py).addr()
        && px.addr() - on_entry(px).addr() == py.addr() - on_entry(py).addr())]
        while px < pxend {
            let vx = (px as *const u32).read_unaligned();
            let vy = (py as *const u32).read_unaligned();
            if vx != vy {
                return false;
            }
            px = px.add(4);
            py = py.add(4);
        }
        let vx = (pxend as *const u32).read_unaligned();
        let vy = (pyend as *const u32).read_unaligned();
        vx == vy
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub mod verify {
    use super::*;

    #[cfg(all(kani, target_arch = "x86_64"))] // only called on x86
    #[kani::proof]
    #[kani::unwind(4)]
    pub fn check_small_slice_eq() {
        // TODO: ARR_SIZE can be `std::usize::MAX` with cbmc argument
        // `--arrays-uf-always`
        const ARR_SIZE: usize = 1000;
        let x: [u8; ARR_SIZE] = kani::any();
        let y: [u8; ARR_SIZE] = kani::any();
        let xs = kani::slice::any_slice_of_array(&x);
        let ys = kani::slice::any_slice_of_array(&y);
        kani::assume(xs.len() == ys.len());
        unsafe {
            small_slice_eq(xs, ys);
        }
    }

    #[cfg(all(kani, target_arch = "x86_64"))] // only called on x86
    #[kani::proof]
    #[kani::unwind(4)]
    pub fn check_small_slice_eq_empty() {
        let ptr_x = kani::any_where::<usize, _>(|val| *val != 0) as *const u8;
        let ptr_y = kani::any_where::<usize, _>(|val| *val != 0) as *const u8;
        kani::assume(ptr_x.is_aligned());
        kani::assume(ptr_y.is_aligned());
        assert_eq!(
            unsafe {
                small_slice_eq(
                    crate::slice::from_raw_parts(ptr_x, 0),
                    crate::slice::from_raw_parts(ptr_y, 0),
                )
            },
            true
        );
    }

    // ==================================================================
    // Challenge 20: verify safety of char-related Searcher methods
    //
    // For each searcher type we define a type invariant `C` and prove the
    // challenge's three criteria against the real, unmodified method
    // bodies:
    //   1. `into_searcher` establishes `C` (base-case harnesses);
    //   2. `C` implies the Searcher safety property: every returned index
    //      pair lies on UTF-8 char boundaries (asserted on the values the
    //      real methods return);
    //   3. every method preserves `C` (inductive-step harnesses that admit
    //      an arbitrary `C`-satisfying state — not just reachable ones —
    //      then run the real method and re-assert `C`).
    //
    // Verification is bounded: haystacks are arbitrary UTF-8 of up to
    // HAYSTACK_BYTES bytes (all four UTF-8 width classes are reachable),
    // needles are arbitrary `char`s, and unwind bounds are justified by
    // the fact that every search-loop iteration advances a cursor by at
    // least one byte. The inductive-step harnesses are unbounded in the
    // searcher *state* given the haystack: they cover every state
    // satisfying `C`, whether or not a call sequence reaches it.
    // ==================================================================

    /// Maximum haystack size in bytes. 5 bytes fits a 4-byte (maximum
    /// width) character plus a neighbor, so every UTF-8 width class and
    /// multi-iteration search loops are covered.
    const HAYSTACK_BYTES: usize = 5;

    /// Unwind bound for loops that advance at least one byte per
    /// iteration over a HAYSTACK_BYTES haystack (+1 for the final
    /// iteration that observes the exhausted cursor, +1 for the
    /// unwinding assertion itself).
    const UNWIND: usize = HAYSTACK_BYTES + 2;

    /// An arbitrary UTF-8 string of 0..=N bytes written into a
    /// caller-owned buffer, built constructively as a concatenation of
    /// up to N symbolic `char`s — every valid UTF-8 string of at most N
    /// bytes is reachable, multibyte characters included. Constructive
    /// generation is used instead of filtering `kani::any()` bytes
    /// through `from_utf8`, because under CI's `-Z loop-contracts` the
    /// loop invariants inside `run_utf8_validation` abstract the
    /// validator's loops, making its *functional* result unreliable as
    /// a filter (and the constructive form is cheaper for the solver).
    /// The char-appending steps are unrolled (loop-free) so harnesses can
    /// use tight unwind bounds; those bounds then cheaply truncate the
    /// (infeasible) panic-formatting paths of the code under test,
    /// keeping the CBMC formula within `--object-bits 12`.
    fn symbolic_str<const N: usize>(buf: &mut [u8; N]) -> &str {
        let mut len = 0usize;
        {
            let mut step = || {
                if kani::any() {
                    let c: char = kani::any();
                    let w = c.len_utf8();
                    if len + w <= N {
                        c.encode_utf8(&mut buf[len..]);
                        len += w;
                    }
                }
            };
            // HAYSTACK_BYTES steps cover every string of <= N <= 5 bytes.
            step();
            step();
            step();
            step();
            step();
        }
        // SAFETY: `buf[..len]` is a concatenation of UTF-8 encodings of
        // `char`s, hence valid UTF-8 by construction.
        unsafe { crate::str::from_utf8_unchecked(&buf[..len]) }
    }

    // ------------------------------------------------------------------
    // Stubs for memchr/memrchr.
    //
    // Challenge 20 allows assuming "the safety and functional correctness
    // of all functions in the slice module", which covers
    // `core::slice::memchr::{memchr,memrchr}`. Following the stub pattern
    // accepted in PR #544, these are *semantically identical
    // implementations* of the first/last-occurrence contract — no
    // nondeterminism, no `kani::assume` — replacing only the optimized
    // word-at-a-time scan, which CBMC unwinds poorly. Each harness's
    // unwind bound fully unwinds the linear scan, so the proofs remain
    // exhaustive. They are applied per-harness, only where the real call
    // graph reaches memchr/memrchr (`CharSearcher::next_match` /
    // `next_match_back`).
    // ------------------------------------------------------------------

    fn stub_memchr(x: u8, text: &[u8]) -> Option<usize> {
        let mut i = 0;
        while i < text.len() {
            if text[i] == x {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    fn stub_memrchr(x: u8, text: &[u8]) -> Option<usize> {
        let mut i = text.len();
        while i > 0 {
            i -= 1;
            if text[i] == x {
                return Some(i);
            }
        }
        None
    }

    // ------------------------------------------------------------------
    // CharSearcher
    // ------------------------------------------------------------------

    /// Type invariant `C` for `CharSearcher` (the condition of challenge
    /// criterion 2): both fingers are in-bounds char boundaries of the
    /// haystack in the right order, and the needle metadata is the true
    /// UTF-8 encoding of the needle. (Inside `next_match`/`next_match_back`
    /// the fingers may transiently leave boundaries — the documented
    /// mid-loop state — but every public method must restore `C` on exit,
    /// which is exactly what these harnesses check.)
    fn type_invariant_cs(s: &CharSearcher<'_>) -> bool {
        let mut enc = [0u8; 4];
        let enc_len = s.needle.encode_utf8(&mut enc).len();
        s.finger <= s.finger_back
            && s.finger_back <= s.haystack.len()
            && s.haystack.is_char_boundary(s.finger)
            && s.haystack.is_char_boundary(s.finger_back)
            && s.utf8_size() == enc_len
            && s.utf8_encoded[..enc_len] == enc[..enc_len]
    }

    /// An arbitrary `CharSearcher` state satisfying `C` — the induction
    /// hypothesis for the step harnesses. This covers every
    /// `C`-satisfying state, a superset of the states reachable by call
    /// sequences from `into_searcher` (whose base case is
    /// `verify_cs_into_searcher`).
    fn any_char_searcher(haystack: &str) -> CharSearcher<'_> {
        let needle: char = kani::any();
        let mut utf8_encoded = [0u8; 4];
        let utf8_size = needle.encode_utf8(&mut utf8_encoded).len() as u8;
        let finger: usize = kani::any();
        let finger_back: usize = kani::any();
        kani::assume(finger <= finger_back && finger_back <= haystack.len());
        kani::assume(haystack.is_char_boundary(finger));
        kani::assume(haystack.is_char_boundary(finger_back));
        CharSearcher { haystack, finger, finger_back, needle, utf8_size, utf8_encoded }
    }

    /// Criterion 2's safety property for a returned index pair.
    fn assert_valid_range(haystack: &str, a: usize, b: usize) {
        assert!(a <= b && b <= haystack.len());
        assert!(haystack.is_char_boundary(a));
        assert!(haystack.is_char_boundary(b));
    }

    /// Criterion 1: `char::into_searcher` establishes `C`.
    #[kani::proof]
    #[kani::unwind(8)]
    pub fn verify_cs_into_searcher() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let needle: char = kani::any();
        let searcher = needle.into_searcher(haystack);
        assert!(type_invariant_cs(&searcher));
        assert!(searcher.finger == 0);
        assert!(searcher.finger_back == haystack.len());
    }

    /// Criteria 2+3 for the real `CharSearcher::next`.
    #[kani::proof]
    #[kani::unwind(8)]
    pub fn verify_cs_next() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_char_searcher(haystack);
        match s.next() {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_valid_range(haystack, a, b);
                kani::cover(true, "next returned Match or Reject");
            }
            SearchStep::Done => kani::cover(true, "next returned Done"),
        }
        assert!(type_invariant_cs(&s));
    }

    /// Criteria 2+3 for the real `CharSearcher::next_back`.
    #[kani::proof]
    #[kani::unwind(8)]
    pub fn verify_cs_next_back() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_char_searcher(haystack);
        match s.next_back() {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_valid_range(haystack, a, b);
                kani::cover(true, "next_back returned Match or Reject");
            }
            SearchStep::Done => kani::cover(true, "next_back returned Done"),
        }
        assert!(type_invariant_cs(&s));
    }

    /// Criteria 2+3 for the real `CharSearcher::next_match` — the memchr
    /// loop, with memchr replaced by the semantically identical
    /// `stub_memchr` (see above). Every loop iteration advances `finger`
    /// by at least one byte, so UNWIND fully unwinds the search.
    #[kani::proof]
    #[kani::unwind(7)]
    #[kani::stub(crate::slice::memchr::memchr, stub_memchr)]
    pub fn verify_cs_next_match() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_char_searcher(haystack);
        match s.next_match() {
            Some((a, b)) => {
                assert_valid_range(haystack, a, b);
                assert!(b - a == s.utf8_size());
                kani::cover(true, "next_match found the needle");
            }
            None => kani::cover(true, "next_match found nothing"),
        }
        assert!(type_invariant_cs(&s));
    }

    /// Criteria 2+3 for the real `CharSearcher::next_match_back` — the
    /// memrchr loop, with memrchr replaced by the semantically identical
    /// `stub_memrchr`. Every iteration decreases `finger_back` by at
    /// least one byte.
    #[kani::proof]
    #[kani::unwind(7)]
    #[kani::stub(crate::slice::memchr::memrchr, stub_memrchr)]
    pub fn verify_cs_next_match_back() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_char_searcher(haystack);
        match s.next_match_back() {
            Some((a, b)) => {
                assert_valid_range(haystack, a, b);
                assert!(b - a == s.utf8_size());
                kani::cover(true, "next_match_back found the needle");
            }
            None => kani::cover(true, "next_match_back found nothing"),
        }
        assert!(type_invariant_cs(&s));
    }

    /// Criteria 2+3 for `CharSearcher::next_reject` — the real trait
    /// default, looping over the real `next()`. Each `next()` consumes at
    /// least one byte, so UNWIND fully unwinds the loop.
    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_cs_next_reject() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_char_searcher(haystack);
        if let Some((a, b)) = s.next_reject() {
            assert_valid_range(haystack, a, b);
            kani::cover(true, "next_reject returned a range");
        }
        assert!(type_invariant_cs(&s));
    }

    /// Criteria 2+3 for `CharSearcher::next_reject_back` — the real trait
    /// default over the real `next_back()`.
    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_cs_next_reject_back() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_char_searcher(haystack);
        if let Some((a, b)) = s.next_reject_back() {
            assert_valid_range(haystack, a, b);
            kani::cover(true, "next_reject_back returned a range");
        }
        assert!(type_invariant_cs(&s));
    }

    /// From-creation run to `Done`: every step of the real `next()` on a
    /// freshly created searcher yields boundary-valid ranges and
    /// preserves `C` (criteria 1+2+3 composed).
    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_cs_search_to_done() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let needle: char = kani::any();
        let mut s = needle.into_searcher(haystack);
        loop {
            match s.next() {
                SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                    assert_valid_range(haystack, a, b)
                }
                SearchStep::Done => break,
            }
            assert!(type_invariant_cs(&s));
        }
        kani::cover(true, "searched the whole haystack");
    }

    // ------------------------------------------------------------------
    // MultiCharEqSearcher (and its four delegating wrapper searchers)
    // ------------------------------------------------------------------

    /// Type invariant `C` for `MultiCharEqSearcher`: the `CharIndices`
    /// iterator views exactly the haystack subrange
    /// `[front, front + rem)`, and both endpoints are char boundaries.
    /// This is what makes the real `next`/`next_back` (and the trait
    /// defaults built on them) return boundary-valid indices: `next()`
    /// yields `front` and `next_back()` yields `front + rem` positions,
    /// and `Chars`/`CharIndices` step through whole characters.
    fn type_invariant_mces<C: MultiCharEq>(s: &MultiCharEqSearcher<'_, C>) -> bool {
        let front = s.char_indices.front_offset;
        let rem = s.char_indices.iter.iter.len();
        front + rem <= s.haystack.len()
            && s.haystack.is_char_boundary(front)
            && s.haystack.is_char_boundary(front + rem)
            && s.char_indices.iter.iter.as_slice().as_ptr().addr()
                == s.haystack.as_ptr().addr() + front
    }

    /// An arbitrary `C`-satisfying `MultiCharEqSearcher` state — the
    /// induction hypothesis for the step harnesses. `char_eq.matches` is
    /// a pure, safe predicate, so the safety argument is independent of
    /// the concrete `MultiCharEq` instantiation; harnesses use
    /// `[char; 2]`.
    fn any_mces(haystack: &str) -> MultiCharEqSearcher<'_, [char; 2]> {
        let k: usize = kani::any();
        let j: usize = kani::any();
        kani::assume(k <= j && j <= haystack.len());
        kani::assume(haystack.is_char_boundary(k));
        kani::assume(haystack.is_char_boundary(j));
        // SAFETY: k <= j <= len and both are char boundaries (assumed
        // above); get_unchecked avoids dragging the slice-error panic
        // machinery into the CBMC formula.
        let sub = unsafe { haystack.get_unchecked(k..j) };
        let char_indices = crate::str::CharIndices { front_offset: k, iter: sub.chars() };
        let char_eq: [char; 2] = kani::any();
        MultiCharEqSearcher { char_eq, haystack, char_indices }
    }

    /// Criterion 1: `into_searcher` establishes `C` for
    /// `MultiCharEqSearcher`.
    #[kani::proof]
    pub fn verify_mces_into_searcher() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let chars: [char; 2] = kani::any();
        let searcher = MultiCharEqPattern(chars).into_searcher(haystack);
        assert!(type_invariant_mces(&searcher));
    }

    /// Criteria 2+3 for the real `MultiCharEqSearcher::next`.
    #[kani::proof]
    pub fn verify_mces_next() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_mces(haystack);
        match s.next() {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_valid_range(haystack, a, b);
                kani::cover(true, "mces next returned Match or Reject");
            }
            SearchStep::Done => kani::cover(true, "mces next returned Done"),
        }
        assert!(type_invariant_mces(&s));
    }

    /// Criteria 2+3 for the real `MultiCharEqSearcher::next_back`.
    #[kani::proof]
    pub fn verify_mces_next_back() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_mces(haystack);
        match s.next_back() {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_valid_range(haystack, a, b);
                kani::cover(true, "mces next_back returned Match or Reject");
            }
            SearchStep::Done => kani::cover(true, "mces next_back returned Done"),
        }
        assert!(type_invariant_mces(&s));
    }

    /// Criteria 2+3 for the four trait defaults on `MultiCharEqSearcher`
    /// (`next_match`, `next_reject`, `next_match_back`,
    /// `next_reject_back`) — the real default loops over the real
    /// `next`/`next_back`. Each iteration consumes at least one byte.
    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_mces_next_match() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_mces(haystack);
        if let Some((a, b)) = s.next_match() {
            assert_valid_range(haystack, a, b);
            kani::cover(true, "mces next_match returned a range");
        }
        assert!(type_invariant_mces(&s));
    }

    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_mces_next_reject() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_mces(haystack);
        if let Some((a, b)) = s.next_reject() {
            assert_valid_range(haystack, a, b);
            kani::cover(true, "mces next_reject returned a range");
        }
        assert!(type_invariant_mces(&s));
    }

    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_mces_next_match_back() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_mces(haystack);
        if let Some((a, b)) = s.next_match_back() {
            assert_valid_range(haystack, a, b);
            kani::cover(true, "mces next_match_back returned a range");
        }
        assert!(type_invariant_mces(&s));
    }

    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_mces_next_reject_back() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let mut s = any_mces(haystack);
        if let Some((a, b)) = s.next_reject_back() {
            assert_valid_range(haystack, a, b);
            kani::cover(true, "mces next_reject_back returned a range");
        }
        assert!(type_invariant_mces(&s));
    }

    /// The four remaining challenge searcher types
    /// (`CharArraySearcher`, `CharArrayRefSearcher`, `CharSliceSearcher`,
    /// `CharPredicateSearcher`) are `pattern_methods!` newtype delegations
    /// to `MultiCharEqSearcher`, so their invariant is the wrapped
    /// searcher's `C` and all six methods delegate to the code verified
    /// above. These harnesses check the delegation itself end-to-end for
    /// the array wrapper (the other three wrappers expand from the same
    /// macro with a different `MultiCharEq` instance; `matches` is a pure
    /// safe predicate in all four).
    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_char_array_searcher_delegation() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let chars: [char; 2] = kani::any();
        let mut s = chars.into_searcher(haystack);
        assert!(type_invariant_mces(&s.0));
        match s.next() {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_valid_range(haystack, a, b)
            }
            SearchStep::Done => {}
        }
        if let Some((a, b)) = s.next_match() {
            assert_valid_range(haystack, a, b);
        }
        assert!(type_invariant_mces(&s.0));
    }

    #[kani::proof]
    #[kani::unwind(7)]
    pub fn verify_char_array_searcher_delegation_back() {
        let mut buf = [0u8; HAYSTACK_BYTES];
        let haystack = symbolic_str(&mut buf);
        let chars: [char; 2] = kani::any();
        let mut s = chars.into_searcher(haystack);
        match s.next_back() {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_valid_range(haystack, a, b)
            }
            SearchStep::Done => {}
        }
        if let Some((a, b)) = s.next_match_back() {
            assert_valid_range(haystack, a, b);
        }
        assert!(type_invariant_mces(&s.0));
    }
    // ==================================================================
    // Challenge 21: verify safety of StrSearcher (empty-needle and
    // Two-Way searchers).
    //
    // Same methodology as the Challenge 20 section above: real method
    // bodies, a base-case harness proving the constructor establishes the
    // type invariant `C`, and inductive-step harnesses that admit an
    // arbitrary `C`-satisfying state, run one real method and re-assert
    // `C` and the boundary property on whatever it returned.
    //
    // Inputs are *symbolic-length* byte slices (`any_utf8`), constrained
    // to be valid UTF-8 by the byte-table predicate `utf8_local` instead
    // of being built char by char, so no proof depends on a haystack
    // length: the only size parameter is the backing-array size
    // (`HAY_MAX`/`NDL_MAX`), the same CBMC memory-model limitation as
    // `ARR_SIZE` in `str::validations::verify::check_run_utf8_validation`.
    //
    // Loop bounds. The real `'search` loops are not unwound to the
    // haystack length:
    // - `StrSearcher::next`/`next_back` instantiate them with
    //   `RejectAndMatch`, whose `use_early_reject()` makes the loop
    //   return as soon as the cursor has moved, and every `continue
    //   'search` moves the cursor by at least one byte -- so the loop
    //   runs at most two iterations for any haystack. Only the inner
    //   byte-compare loops scale, with the needle length.
    // - `next_match`/`next_match_back` instantiate them with `MatchOnly`,
    //   whose loop body is the *same code* minus that early exit. The
    //   `verify_twoway_search_step_*` harnesses run one real iteration
    //   (the `RejectAndMatch` instantiation) from an *arbitrary* state
    //   satisfying the loop's invariant `S` and prove it preserves `S`
    //   and that any Match it reports is byte-exact and boundary-valid;
    //   that is the inductive step of the unbounded `MatchOnly` loop,
    //   machine-checked through the real code. The direct
    //   `verify_twoway_step_next_match*` harnesses add end-to-end
    //   coverage of the real `MatchOnly` loop up to the array size.
    //
    // The Two-Way invariant is content-coupled: boundary validity of a
    // returned Match hinges on the match being byte-exact (a byte-exact
    // image of valid UTF-8 starting at a boundary ends at a boundary),
    // which in short-period mode depends on the memorized prefix really
    // matching the haystack and `period` being an exact period of the
    // needle. Those are clauses of `C`, established by `new()` and
    // preserved by the search steps -- not assumptions about the result.
    // Content clauses are stated with `crate::forall!` over the backing
    // array (constant bounds, guarded by the real lengths), which is the
    // form CBMC's SAT backend can instantiate.
    //
    // Loop contracts (`-Z loop-contracts`) on the real `'search` loops
    // were tried and are not usable with the pinned Kani without
    // rewriting the loops themselves: CBMC requires a contract on every
    // nested loop, Kani's `for`-loop contract support hoists the inner
    // range construction to the outer loop head (where `start` is not
    // yet computed) and computes `end - start` for legitimately empty
    // reversed ranges, and Kani's compiler panics on `let start = if ..
    // { .. } else { cmp::max(..) }` inside a contracted loop. Keeping the
    // shipped code byte-identical was preferred.
    // ==================================================================

    /// Backing-array size for haystacks: haystack lengths range over
    /// `0..=HAY_MAX`. No loop is unwound to this size (see the module
    /// comment), so it is a CBMC memory-model parameter, not a proof
    /// bound; 16 keeps every harness well inside CI's per-harness budget.
    const HAY_MAX: usize = 16;
    /// Backing-array size for needles in the Two-Way inductive-step
    /// harnesses: needle lengths range over `1..=NDL_MAX`. The inner
    /// byte-compare loops of the search are unwound to this size.
    const NDL_MAX: usize = 8;
    /// Needle bound for the base case `verify_str_searcher_new`, which
    /// runs the real `maximal_suffix`/`reverse_maximal_suffix` (unwound;
    /// see the harness comment).
    const NEW_NDL_MAX: usize = 8;
    /// Constant bound of the quantifiers in the content predicates
    /// (`prefix_eq`, `suffix_eq`, `has_period`); must cover every needle
    /// array used with them.
    const NDL_QMAX: usize = 8;
    /// Backing-array sizes for the direct `next_match`/`next_match_back`
    /// harnesses, which do unwind the real `MatchOnly` loop to the
    /// haystack length (their unbounded inductive step is
    /// `verify_twoway_search_step_*`, at the full `NDL_MAX`).
    const MATCH_HAY_MAX: usize = 5;
    const MATCH_NDL_MAX: usize = 6;
    /// Extra bytes past the maximum length so the byte-table predicates
    /// may read up to four bytes after any index `< MAX` without leaving
    /// the backing array.
    const PAD: usize = 4;
    const _: () =
        assert!(NEW_NDL_MAX <= NDL_QMAX && NDL_MAX <= NDL_QMAX && MATCH_NDL_MAX <= NDL_QMAX);

    // ------------------------------------------------------------------
    // Symbolic-length UTF-8 inputs
    // ------------------------------------------------------------------

    /// The byte-table definition of "`arr[..len]` is valid UTF-8", as two
    /// facts local to a 4-byte window and quantified over every index of
    /// the backing array (`i >= len` positions are vacuous):
    ///
    /// - U-lead: every non-continuation byte at `i` is a valid leading
    ///   byte (`<0x80`, `0xC2..=0xDF`, `0xE0..=0xEF`, `0xF0..=0xF4`) of
    ///   width `w`, its `w - 1` continuation bytes are present (with the
    ///   second-byte restrictions for `E0`/`ED`/`F0`/`F4`: no overlong
    ///   forms, no surrogates, nothing above U+10FFFF), `i + w <= len`,
    ///   and the byte at `i + w` is a leading byte or the end of the
    ///   string.
    /// - U-cover: every byte lies within three bytes after a
    ///   non-continuation byte (at `i = 0`: the first byte leads).
    ///
    /// Both are properties of every valid UTF-8 string, so assuming them
    /// is sound; together they are equivalent to `from_utf8(..).is_ok()`
    /// (U-cover at 0 starts the parse on a leading byte, U-lead makes
    /// each step a valid sequence that lands on the next leading byte or
    /// exactly on `len`), which justifies `from_utf8_unchecked` in
    /// `any_utf8`. `from_utf8` itself is not used as the filter because
    /// under CI's `-Z loop-contracts` the invariants in
    /// `run_utf8_validation` abstract its loops and its result no longer
    /// constrains the bytes.
    ///
    /// The quantifier bodies are deliberately branch-free (bitwise `&`/`|`,
    /// indicator arithmetic, no helper calls, no nested closures): CBMC
    /// instantiates a quantifier body as one expression, and control flow
    /// or statement expressions inside it are rejected or blow up
    /// instrumentation. Every read stays inside the backing array because
    /// of `PAD`.
    fn utf8_local<const N: usize>(arr: &[u8; N], len: usize) -> bool {
        let p = arr.as_ptr();
        let lead = crate::forall!(|i in (0, N - PAD)| unsafe {
            let i: usize = i;
            let b0 = *p.wrapping_add(i);
            let b1 = *p.wrapping_add(i.wrapping_add(1));
            let b2 = *p.wrapping_add(i.wrapping_add(2));
            let b3 = *p.wrapping_add(i.wrapping_add(3));
            let c0 = (b0 as i8) < -64;
            let c1 = (b1 as i8) < -64;
            let c2 = (b2 as i8) < -64;
            let c3 = (b3 as i8) < -64;
            // width of the sequence led by b0 (0: not a valid leading byte)
            let w: usize = (b0 < 0x80) as usize
                + (((b0 >= 0xC2) & (b0 < 0xE0)) as usize) * 2
                + (((b0 >= 0xE0) & (b0 < 0xF0)) as usize) * 3
                + (((b0 >= 0xF0) & (b0 < 0xF5)) as usize) * 4;
            let cw = (*p.wrapping_add(i.wrapping_add(w)) as i8) < -64;
            let sec = ((b0 != 0xE0) | (b1 >= 0xA0))
                & ((b0 != 0xED) | (b1 < 0xA0))
                & ((b0 != 0xF0) | (b1 >= 0x90))
                & ((b0 != 0xF4) | (b1 < 0x90));
            (i >= len)
                | c0
                | ((w != 0)
                    & (i.wrapping_add(w) <= len)
                    & ((w < 2) | (c1 & sec))
                    & ((w < 3) | c2)
                    & ((w < 4) | c3)
                    & ((i.wrapping_add(w) == len) | !cw))
        });
        let cover = crate::forall!(|i in (0, N - PAD)| unsafe {
            let i: usize = i;
            (i >= len)
                | ((*p.wrapping_add(i) as i8) >= -64)
                | ((i >= 1) & ((*p.wrapping_add(i.saturating_sub(1)) as i8) >= -64))
                | ((i >= 2) & ((*p.wrapping_add(i.saturating_sub(2)) as i8) >= -64))
                | ((i >= 3) & ((*p.wrapping_add(i.saturating_sub(3)) as i8) >= -64))
        });
        lead && cover
    }

    /// An arbitrary valid UTF-8 string of symbolic length `0..=N - PAD`
    /// backed by a caller-owned array of arbitrary content.
    fn any_utf8<const N: usize>(arr: &[u8; N]) -> &str {
        let len: usize = kani::any();
        kani::assume(len <= N - PAD);
        kani::assume(utf8_local(arr, len));
        // SAFETY: `utf8_local` is the byte-table definition of UTF-8
        // validity (see its documentation).
        unsafe { crate::str::from_utf8_unchecked(&arr[..len]) }
    }

    // ------------------------------------------------------------------
    // Content predicates of the Two-Way invariant (constant-bound
    // quantifiers; every read is guarded by the real lengths and stays
    // inside the backing arrays).
    // ------------------------------------------------------------------

    /// `h[pos + j] == nb[j]` for every `j < k`. Callers establish
    /// `k <= nb.len()` and `pos + k <= h.len()`. Out-of-range `j` are
    /// vacuous; their read index is clamped to 0 so every read stays in
    /// bounds (the quantifier body must be branch-free, see `utf8_local`).
    fn prefix_eq(h: &[u8], nb: &[u8], pos: usize, k: usize) -> bool {
        let hp = h.as_ptr();
        let np = nb.as_ptr();
        crate::forall!(|j in (0, NDL_QMAX)| unsafe {
            let j: usize = j;
            let jj = j * ((j < k) as usize);
            (j >= k) | (*hp.wrapping_add(pos.wrapping_add(jj)) == *np.wrapping_add(jj))
        })
    }

    /// `h[start + j] == nb[j]` for every `j` in `m..nb.len()`. Callers
    /// establish `m <= nb.len()` and `start + nb.len() <= h.len()`.
    /// Out-of-range `j` are vacuous; their read index is clamped to `m`.
    fn suffix_eq(h: &[u8], nb: &[u8], start: usize, m: usize) -> bool {
        let n = nb.len();
        let hp = h.as_ptr();
        let np = nb.as_ptr();
        crate::forall!(|j in (0, NDL_QMAX)| unsafe {
            let j: usize = j;
            let inr = (j >= m) & (j < n);
            let jj = m.wrapping_add(j.wrapping_sub(m) * (inr as usize));
            !inr | (*hp.wrapping_add(start.wrapping_add(jj)) == *np.wrapping_add(jj))
        })
    }

    /// `period` is a period of `nb`: `nb[j] == nb[j + period]` whenever
    /// `j + period < nb.len()`. Callers establish `period <= nb.len()`.
    /// Out-of-range `j` are vacuous; their read index is clamped to 0.
    fn has_period(nb: &[u8], period: usize) -> bool {
        let n = nb.len();
        let np = nb.as_ptr();
        crate::forall!(|j in (0, NDL_QMAX)| unsafe {
            let j: usize = j;
            let inr = j.wrapping_add(period) < n;
            let jj = j * (inr as usize);
            !inr | (*np.wrapping_add(jj) == *np.wrapping_add(jj.wrapping_add(period)))
        })
    }

    // ------------------------------------------------------------------
    // Type invariant `C`
    // ------------------------------------------------------------------

    fn type_invariant_empty_needle(en: &EmptyNeedle, haystack: &str) -> bool {
        en.position <= haystack.len()
            && en.end <= haystack.len()
            && haystack.is_char_boundary(en.position)
            && haystack.is_char_boundary(en.end)
    }

    /// Search-state invariant `S` of the Two-Way searcher: everything in
    /// `C` except the char-boundary clauses on the cursors. `S` is what
    /// the real `'search` loops maintain at *every* iteration (the
    /// cursors move by algorithmic shifts and may sit inside a character
    /// between iterations); `C` adds the boundary clauses that hold
    /// between public calls.
    /// - Clauses 1-2: cursors in-bounds (`position <= end` is
    ///   deliberately NOT required -- the two cursors evolve
    ///   independently).
    /// - Clauses 5-9: constructor-established well-formedness the search
    ///   loops need for panic-freedom and strict cursor progress.
    /// - Clauses 10-11 (short-period mode only): `period` is an exact
    ///   period of the needle, and the memorized bytes really match the
    ///   haystack at the current alignment -- the content coupling that
    ///   makes a Match byte-exact and hence boundary-valid.
    fn search_state_two_way(tw: &TwoWaySearcher, haystack: &str, needle: &str) -> bool {
        let n = needle.len();
        let h = haystack.as_bytes();
        let nb = needle.as_bytes();
        tw.position <= haystack.len()                       // 1
            && tw.end <= haystack.len()                     // 2
            && n >= 1                                       // 5
            && tw.crit_pos <= n                             // 6
            && tw.crit_pos_back <= n                        // 7
            && tw.period >= 1                               // 8
            // 8b: the critical factorization theorem's |u| < period(x).
            // This is what justifies the period-shift memorization in the
            // 'search loop: after `position += period; memory = n - period`,
            // the skipped prefix lies inside the previously verified right
            // part (indices >= crit_pos), so clause 11 is preserved.
            && tw.crit_pos < tw.period                      // 8b
            // 8c: the mirror fact for the reverse search (the code
            // comment on next_back: "We need |u| < period(x) for the
            // forward case and thus |v'| < period(x) for the reverse"),
            // justifying the back-shift memorization for clause 11b.
            && n - tw.crit_pos_back < tw.period             // 8c
            && (tw.memory == usize::MAX) == (tw.memory_back == usize::MAX) // 9
            && (if tw.memory == usize::MAX {
                // long-period mode: period = max(crit_pos, n - crit_pos) + 1
                // with crit_pos in [1, n-1] (crit_pos = 0 short-circuits to
                // the short branch via the vacuous prefix comparison, and
                // the maximal suffix is nonempty), so period <= n. The
                // bound is load-bearing: next_back's `end -= period` runs
                // with end >= n and would underflow if period could be
                // n + 1. No memorization in this mode.
                tw.period <= n
            } else {
                tw.period <= n
                    && tw.memory <= n
                    && tw.memory_back <= n
                    // 10: period is an exact period of the needle
                    && has_period(nb, tw.period)
                    // 11: memorized prefix matches at current alignment
                    // (only meaningful while a candidate window fits)
                    && (tw.position + n > h.len()
                        || prefix_eq(h, nb, tw.position, tw.memory))
                    // 11b: memorized suffix matches at the back alignment
                    && (tw.end < n || suffix_eq(h, nb, tw.end - n, tw.memory_back))
            })
    }

    /// Two-Way invariant `C` = `S` plus clauses 3-4: both cursors lie on
    /// char boundaries of the haystack.
    fn type_invariant_two_way(tw: &TwoWaySearcher, haystack: &str, needle: &str) -> bool {
        search_state_two_way(tw, haystack, needle)
            && haystack.is_char_boundary(tw.position)       // 3
            && haystack.is_char_boundary(tw.end) // 4
    }

    /// Per-clause assertion version of `search_state_two_way`, used by
    /// the inductive-step harnesses so a counterexample names the exact
    /// clause it violates.
    fn assert_two_way_s(tw: &TwoWaySearcher, haystack: &str, needle: &str) {
        let n = needle.len();
        let h = haystack.as_bytes();
        let nb = needle.as_bytes();
        assert!(tw.position <= haystack.len(), "c1 position bound");
        assert!(tw.end <= haystack.len(), "c2 end bound");
        assert!(n >= 1, "c5 needle nonempty");
        assert!(tw.crit_pos <= n, "c6 crit_pos bound");
        assert!(tw.crit_pos_back <= n, "c7 crit_pos_back bound");
        assert!(tw.period >= 1, "c8 period positive");
        assert!(tw.crit_pos < tw.period, "c8b crit_pos < period");
        assert!(n - tw.crit_pos_back < tw.period, "c8c n - crit_pos_back < period");
        assert!((tw.memory == usize::MAX) == (tw.memory_back == usize::MAX), "c9 mode coherence");
        if tw.memory == usize::MAX {
            assert!(tw.period <= n, "c10L long period bound");
        } else {
            assert!(tw.period <= n, "c10a short period bound");
            assert!(tw.memory <= n, "c10b memory bound");
            assert!(tw.memory_back <= n, "c10c memory_back bound");
            assert!(has_period(nb, tw.period), "c10 exact period");
            assert!(
                tw.position + n > h.len() || prefix_eq(h, nb, tw.position, tw.memory),
                "c11 memory matches"
            );
            assert!(
                tw.end < n || suffix_eq(h, nb, tw.end - n, tw.memory_back),
                "c11b memory_back matches"
            );
        }
    }

    /// Per-clause assertion version of `type_invariant_two_way`.
    fn assert_two_way_c(tw: &TwoWaySearcher, haystack: &str, needle: &str) {
        assert_two_way_s(tw, haystack, needle);
        assert!(haystack.is_char_boundary(tw.position), "c3 position boundary");
        assert!(haystack.is_char_boundary(tw.end), "c4 end boundary");
    }

    fn type_invariant_str_searcher(s: &StrSearcher<'_, '_>) -> bool {
        match &s.searcher {
            StrSearcherImpl::Empty(en) => {
                s.needle.is_empty() && type_invariant_empty_needle(en, s.haystack)
            }
            StrSearcherImpl::TwoWay(tw) => {
                !s.needle.is_empty() && type_invariant_two_way(tw, s.haystack, s.needle)
            }
        }
    }

    // ------------------------------------------------------------------
    // Criterion 1: creation establishes `C`
    // ------------------------------------------------------------------

    /// `StrSearcher::new` establishes `C` for both the empty-needle and
    /// Two-Way variants (this is also the base case for the
    /// inductive-step harnesses below). The haystack has symbolic length
    /// (only its length reaches `new`). The needle is bounded by
    /// `NEW_NDL_MAX`: `new` runs the real `maximal_suffix` /
    /// `reverse_maximal_suffix`, whose `while let` loops are unwound
    /// here (at most 2n+2 iterations each, hence the unwind bound), and the clauses `C` takes
    /// from them (`crit_pos < period`, `period <= n`, exactness of the
    /// short-mode period) are consequences of the critical factorization
    /// theorem rather than of a loop-local invariant. The inductive steps
    /// assume nothing but `C`, so this bound is confined to the pure
    /// function of the needle.
    #[kani::proof]
    #[kani::unwind(20)]
    pub fn verify_str_searcher_new() {
        let hbuf: [u8; HAY_MAX + PAD] = kani::any();
        let nbuf: [u8; NEW_NDL_MAX + PAD] = kani::any();
        let haystack = any_utf8(&hbuf);
        let needle = any_utf8(&nbuf);
        let s = StrSearcher::new(haystack, needle);
        assert!(type_invariant_str_searcher(&s));
        match &s.searcher {
            StrSearcherImpl::Empty(_) => kani::cover(true, "empty-needle variant created"),
            StrSearcherImpl::TwoWay(tw) => {
                assert!(tw.position == 0 && tw.end == haystack.len());
                kani::cover(tw.memory == usize::MAX, "long-period factorization reached");
                kani::cover(tw.memory != usize::MAX, "short-period factorization reached");
            }
        }
    }

    // ------------------------------------------------------------------
    // Criteria 2+3: inductive steps
    // ------------------------------------------------------------------

    // No Two-Way-arm "from creation" harnesses: composing the real
    // `new()` (whose reachable-state constraint threads through the whole
    // maximal_suffix computation) with the real search loops overflows
    // CBMC's `--object-bits 12` limit at any useful input size. They are
    // also logically redundant: `verify_str_searcher_new` machine-checks
    // that creation establishes `C`, and the `verify_twoway_step_*`
    // harnesses machine-check that from EVERY `C`-satisfying state (a
    // superset of all reachable states) the real methods return
    // boundary-valid ranges and preserve `C` -- so any call sequence from
    // creation is covered by induction. The same composition argument
    // covers the `next_reject`/`next_reject_back` trait defaults on the
    // Two-Way arm: they are `Searcher`-generic loops over `next`/
    // `next_back` that cannot carry a `StrSearcher`-specific loop
    // invariant, and each iteration is one of the steps proven here.
    // Their empty-needle variants are machine-checked below
    // (`verify_empty_step_next_reject`/`_back`).

    /// An arbitrary `C`-satisfying empty-needle searcher (induction
    /// hypothesis; base case in `verify_str_searcher_new`).
    fn any_empty_searcher<'a>(haystack: &'a str) -> StrSearcher<'a, 'static> {
        let position: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(position <= haystack.len() && end <= haystack.len());
        kani::assume(haystack.is_char_boundary(position));
        kani::assume(haystack.is_char_boundary(end));
        StrSearcher {
            haystack,
            needle: "",
            searcher: StrSearcherImpl::Empty(EmptyNeedle {
                position,
                end,
                is_match_fw: kani::any(),
                is_match_bw: kani::any(),
                is_finished: kani::any(),
            }),
        }
    }

    /// An arbitrary `C`-satisfying Two-Way searcher (induction
    /// hypothesis; base case in `verify_str_searcher_new`). All eight
    /// fields are symbolic; `byteset` is unconstrained, so the proofs
    /// also show memory safety does not depend on the fingerprint.
    /// `long_period` selects the factorization mode (`memory ==
    /// usize::MAX` or not); each harness below is instantiated once per
    /// mode, which halves the formula CBMC has to solve at a time while
    /// still covering every `C`-state between the two.
    fn any_twoway_searcher<'a, 'b>(
        haystack: &'a str,
        needle: &'b str,
        long_period: bool,
    ) -> StrSearcher<'a, 'b> {
        let tw = TwoWaySearcher {
            crit_pos: kani::any(),
            crit_pos_back: kani::any(),
            period: kani::any(),
            byteset: kani::any(),
            position: kani::any(),
            end: kani::any(),
            memory: kani::any(),
            memory_back: kani::any(),
        };
        kani::assume((tw.memory == usize::MAX) == long_period);
        let s = StrSearcher { haystack, needle, searcher: StrSearcherImpl::TwoWay(tw) };
        kani::assume(type_invariant_str_searcher(&s));
        s
    }

    /// An arbitrary `S`-satisfying Two-Way search state -- the induction
    /// hypothesis for the single-iteration lemmas below (a superset of
    /// the `C`-states, since `S` drops the boundary clauses).
    fn any_twoway_search_state(haystack: &str, needle: &str, long_period: bool) -> TwoWaySearcher {
        let tw = TwoWaySearcher {
            crit_pos: kani::any(),
            crit_pos_back: kani::any(),
            period: kani::any(),
            byteset: kani::any(),
            position: kani::any(),
            end: kani::any(),
            memory: kani::any(),
            memory_back: kani::any(),
        };
        kani::assume((tw.memory == usize::MAX) == long_period);
        kani::assume(search_state_two_way(&tw, haystack, needle));
        tw
    }

    /// Inductive step for the empty-needle variant: from any
    /// `C`-satisfying state, each real method returns boundary-valid
    /// ranges and preserves `C`. Unbounded in the haystack: the arm is
    /// loop-free per call (`Chars::next`/`next_back` decode one scalar
    /// straight-line) and alternates Match/Reject, so the `next_match`/
    /// `next_reject` default loops run at most two iterations.
    macro_rules! empty_needle_step {
        ($name:ident, $call:ident, step) => {
            #[kani::proof]
            #[kani::unwind(3)]
            pub fn $name() {
                let hbuf: [u8; HAY_MAX + PAD] = kani::any();
                let haystack = any_utf8(&hbuf);
                let mut s = any_empty_searcher(haystack);
                match s.$call() {
                    SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                        assert_valid_range(haystack, a, b);
                        kani::cover(true, "empty-needle step returned a range");
                    }
                    SearchStep::Done => kani::cover(true, "empty-needle step returned Done"),
                }
                assert!(type_invariant_str_searcher(&s));
            }
        };
        ($name:ident, $call:ident, opt) => {
            #[kani::proof]
            #[kani::unwind(3)]
            pub fn $name() {
                let hbuf: [u8; HAY_MAX + PAD] = kani::any();
                let haystack = any_utf8(&hbuf);
                let mut s = any_empty_searcher(haystack);
                match s.$call() {
                    Some((a, b)) => {
                        assert_valid_range(haystack, a, b);
                        kani::cover(true, "empty-needle step returned a range");
                    }
                    None => kani::cover(true, "empty-needle step returned None"),
                }
                assert!(type_invariant_str_searcher(&s));
            }
        };
    }

    empty_needle_step!(verify_empty_step_next, next, step);
    empty_needle_step!(verify_empty_step_next_back, next_back, step);
    empty_needle_step!(verify_empty_step_next_match, next_match, opt);
    empty_needle_step!(verify_empty_step_next_match_back, next_match_back, opt);
    empty_needle_step!(verify_empty_step_next_reject, next_reject, opt);
    empty_needle_step!(verify_empty_step_next_reject_back, next_reject_back, opt);

    /// Inductive step for the Two-Way variant through the public methods
    /// (`next`, `next_back`, `next_match`, `next_match_back`): from any
    /// `C`-satisfying state the real method returns boundary-valid ranges
    /// and re-establishes `C`.
    ///
    /// Unwind bounds. For `next`/`next_back` (`NDL_MAX + 1`) the `'search`
    /// loop runs at most two iterations for *any* haystack (see the
    /// module comment), the inner byte-compare loops at most `NDL_MAX`,
    /// and the char-boundary walks in `StrSearcher::next`/`next_back` at
    /// most 3 (U-cover); the bound covers all of them, and the haystack
    /// length is unconstrained up to the array size. For `next_match`/
    /// `next_match_back` (`MATCH_HAY_MAX + 2 = MATCH_NDL_MAX + 1`) the
    /// `MatchOnly` loop advances the cursor by at least one byte per
    /// iteration, so the bound covers every iteration up to the smaller
    /// array sizes these coverage harnesses use; their unbounded
    /// inductive step is `verify_twoway_search_step_*` below.
    macro_rules! twoway_step {
        ($name:ident, $call:ident, $long:expr, step) => {
            #[kani::proof]
            #[kani::unwind(9)]
            pub fn $name() {
                let hbuf: [u8; HAY_MAX + PAD] = kani::any();
                let nbuf: [u8; NDL_MAX + PAD] = kani::any();
                let haystack = any_utf8(&hbuf);
                let needle = any_utf8(&nbuf);
                kani::assume(!needle.is_empty());
                let mut s = any_twoway_searcher(haystack, needle, $long);
                match s.$call() {
                    SearchStep::Match(a, b) => {
                        assert_valid_range(haystack, a, b);
                        kani::cover(true, "two-way step returned Match");
                    }
                    SearchStep::Reject(a, b) => {
                        assert_valid_range(haystack, a, b);
                        kani::cover(true, "two-way step returned Reject");
                    }
                    SearchStep::Done => kani::cover(true, "two-way step returned Done"),
                }
                if let StrSearcherImpl::TwoWay(ref tw) = s.searcher {
                    assert_two_way_c(tw, haystack, needle);
                } else {
                    unreachable!();
                }
            }
        };
        ($name:ident, $call:ident, $long:expr, opt) => {
            #[kani::proof]
            #[kani::unwind(7)]
            pub fn $name() {
                let hbuf: [u8; MATCH_HAY_MAX + PAD] = kani::any();
                let nbuf: [u8; MATCH_NDL_MAX + PAD] = kani::any();
                let haystack = any_utf8(&hbuf);
                let needle = any_utf8(&nbuf);
                kani::assume(!needle.is_empty());
                let mut s = any_twoway_searcher(haystack, needle, $long);
                match s.$call() {
                    Some((a, b)) => {
                        assert_valid_range(haystack, a, b);
                        kani::cover(true, "two-way step found a match");
                    }
                    None => kani::cover(true, "two-way step found nothing"),
                }
                if let StrSearcherImpl::TwoWay(ref tw) = s.searcher {
                    assert_two_way_c(tw, haystack, needle);
                } else {
                    unreachable!();
                }
            }
        };
    }

    // `_short`: short-period mode (memorization active, content clauses
    // 10/11/11b live); `_long`: long-period mode (`memory == usize::MAX`).
    twoway_step!(verify_twoway_step_next_short, next, false, step);
    twoway_step!(verify_twoway_step_next_long, next, true, step);
    twoway_step!(verify_twoway_step_next_back_short, next_back, false, step);
    twoway_step!(verify_twoway_step_next_back_long, next_back, true, step);
    twoway_step!(verify_twoway_step_next_match_short, next_match, false, opt);
    twoway_step!(verify_twoway_step_next_match_long, next_match, true, opt);
    twoway_step!(verify_twoway_step_next_match_back_short, next_match_back, false, opt);
    twoway_step!(verify_twoway_step_next_match_back_long, next_match_back, true, opt);

    /// One real iteration of the `'search` loops, from an arbitrary
    /// `S`-state: `TwoWaySearcher::next::<RejectAndMatch>` (resp.
    /// `next_back`) returns as soon as the cursor moves (or on the first
    /// iteration), so it *is* the loop body shared with `MatchOnly` (whose
    /// only difference is not taking that early exit). Proves: `S` is
    /// preserved; a `Match(a, b)` is byte-exact (`haystack[a..b] ==
    /// needle`), hence `a` and `b` lie on char boundaries (U-lead on the
    /// needle's last leading byte and on the haystack); a `Reject` spans
    /// `old_cursor..cursor` in bounds. Together with
    /// `verify_str_searcher_new` this is the induction proving
    /// `next_match`/`next_match_back` safe for haystacks of any length.
    /// Instantiated per direction and per factorization mode.
    macro_rules! twoway_search_step {
        ($name:ident, fwd, $long:expr) => {
            #[kani::proof]
            #[kani::unwind(9)]
            pub fn $name() {
                let hbuf: [u8; HAY_MAX + PAD] = kani::any();
                let nbuf: [u8; NDL_MAX + PAD] = kani::any();
                let haystack = any_utf8(&hbuf);
                let needle = any_utf8(&nbuf);
                kani::assume(!needle.is_empty());
                let mut tw = any_twoway_search_state(haystack, needle, $long);
                let old_pos = tw.position;
                match tw.next::<RejectAndMatch>(haystack.as_bytes(), needle.as_bytes(), $long) {
                    SearchStep::Match(a, b) => {
                        assert!(
                            b == a + needle.len() && b <= haystack.len(),
                            "match window in bounds"
                        );
                        assert!(
                            haystack.as_bytes()[a..b] == *needle.as_bytes(),
                            "match is byte-exact"
                        );
                        assert_valid_range(haystack, a, b);
                        assert!(tw.position == b, "cursor moved past the match");
                        kani::cover(true, "forward search step: Match");
                    }
                    SearchStep::Reject(a, b) => {
                        assert!(a == old_pos && a <= b && b <= haystack.len(), "reject window");
                        assert!(tw.position == b, "cursor at reject end");
                        kani::cover(true, "forward search step: Reject");
                    }
                    SearchStep::Done => unreachable!("RejectAndMatch never yields Done"),
                }
                assert_two_way_s(&tw, haystack, needle);
            }
        };
        ($name:ident, bwd, $long:expr) => {
            #[kani::proof]
            #[kani::unwind(9)]
            pub fn $name() {
                let hbuf: [u8; HAY_MAX + PAD] = kani::any();
                let nbuf: [u8; NDL_MAX + PAD] = kani::any();
                let haystack = any_utf8(&hbuf);
                let needle = any_utf8(&nbuf);
                kani::assume(!needle.is_empty());
                let mut tw = any_twoway_search_state(haystack, needle, $long);
                let old_end = tw.end;
                match tw.next_back::<RejectAndMatch>(haystack.as_bytes(), needle.as_bytes(), $long)
                {
                    SearchStep::Match(a, b) => {
                        assert!(
                            b == a + needle.len() && b <= haystack.len(),
                            "match window in bounds"
                        );
                        assert!(
                            haystack.as_bytes()[a..b] == *needle.as_bytes(),
                            "match is byte-exact"
                        );
                        assert_valid_range(haystack, a, b);
                        assert!(tw.end == a, "cursor moved before the match");
                        kani::cover(true, "backward search step: Match");
                    }
                    SearchStep::Reject(a, b) => {
                        assert!(b == old_end && a <= b, "reject window");
                        assert!(tw.end == a, "cursor at reject start");
                        kani::cover(true, "backward search step: Reject");
                    }
                    SearchStep::Done => unreachable!("RejectAndMatch never yields Done"),
                }
                assert_two_way_s(&tw, haystack, needle);
            }
        };
    }

    twoway_search_step!(verify_twoway_search_step_fwd_short, fwd, false);
    twoway_search_step!(verify_twoway_search_step_fwd_long, fwd, true);
    twoway_search_step!(verify_twoway_search_step_bwd_short, bwd, false);
    twoway_search_step!(verify_twoway_search_step_bwd_long, bwd, true);
}
