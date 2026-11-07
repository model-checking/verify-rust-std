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

// Must match the `cfg` on `small_slice_eq`, the only user of these attributes.
#[cfg(any(
    all(target_arch = "x86_64", any(kani, target_feature = "sse2")),
    all(target_arch = "loongarch64", target_feature = "lsx"),
    all(target_arch = "aarch64", target_feature = "neon")
))]
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

    /// Returns the pattern as UTF-8 if possible.
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
    /// This stores `str` rather than bytes so callers cannot describe
    /// non-UTF-8 string patterns through this API.
    StringPattern(&'a str),
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
        #[cfg_attr(kani, kani::loop_modifies(
            verify::FilterLoopContract::cursor(&*self, false),
            verify::FilterLoopContract::word_cursor(&*self, false),
            verify::FilterLoopContract::flag(&*self, false),
            verify::FilterLoopContract::cache(&*self, false),
            verify::FilterLoopContract::finished(&*self)
        ))]
        #[cfg_attr(kani, kani::loop_invariant(verify::FilterLoopContract::valid(&*self)))]
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
        #[cfg_attr(kani, kani::loop_modifies(
            verify::FilterLoopContract::cursor(&*self, true),
            verify::FilterLoopContract::word_cursor(&*self, true),
            verify::FilterLoopContract::flag(&*self, true),
            verify::FilterLoopContract::cache(&*self, true),
            verify::FilterLoopContract::finished(&*self)
        ))]
        #[cfg_attr(kani, kani::loop_invariant(verify::FilterLoopContract::valid(&*self)))]
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
        if self.is_empty() {
            return true;
        }

        match self.len().cmp(&haystack.len()) {
            Ordering::Less => {
                if self.len() == 1 {
                    return haystack.as_bytes().contains(&self.as_bytes()[0]);
                }

                #[cfg(any(
                    all(target_arch = "x86_64", target_feature = "sse2"),
                    all(target_arch = "loongarch64", target_feature = "lsx"),
                    all(target_arch = "aarch64", target_feature = "neon")
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
            unsafe { Some(haystack.get_unchecked(self.len()..)) }
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
            let i = haystack.len() - self.len();
            // SAFETY: suffix was just verified to exist.
            unsafe { Some(haystack.get_unchecked(..i)) }
        } else {
            None
        }
    }

    #[inline]
    fn as_utf8_pattern(&self) -> Option<Utf8Pattern<'_>> {
        Some(Utf8Pattern::StringPattern(self))
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
    Byte(ByteNeedle),
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

/// Fast searcher for a single-byte needle using `memchr`/`memrchr`.
#[derive(Clone, Debug)]
struct ByteNeedle {
    b: u8,
    /// Forward cursor: `haystack[..position]` has already been reported.
    position: usize,
    /// Backward cursor: `haystack[end..]` has already been reported.
    end: usize,
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
        } else if let &[b] = needle.as_bytes() {
            StrSearcher {
                haystack,
                needle,
                searcher: StrSearcherImpl::Byte(ByteNeedle { b, position: 0, end: haystack.len() }),
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
    #[cfg_attr(kani, kani::requires(verify::supported_contract_state(self)))]
    #[cfg_attr(kani, kani::ensures(|step| {
        verify::assume_utf8_at_match(self.haystack, self.needle, *step);
        verify::invariant(self) && verify::step_ok(self.haystack, *step)
    }))]
    #[cfg_attr(
        kani,
        kani::modifies(
            verify::front_cursor(self),
            verify::front_memory(self),
            verify::empty_forward_flag(self),
            verify::empty_finished(self)
        )
    )]
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
            StrSearcherImpl::Byte(ref mut searcher) => {
                let bytes = self.haystack.as_bytes();
                let pos = searcher.position;
                if pos >= bytes.len() {
                    return SearchStep::Done;
                }
                if bytes[pos] == searcher.b {
                    searcher.position = pos + 1;
                    SearchStep::Match(pos, pos + 1)
                } else {
                    // `pos` is always on a char boundary, so this rejects
                    // exactly the char starting at `pos`.
                    let end = self.haystack.ceil_char_boundary(pos + 1);
                    searcher.position = end;
                    SearchStep::Reject(pos, end)
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
                    SearchStep::Reject(a, b) => {
                        // skip to next char boundary
                        let b = self.haystack.ceil_char_boundary(b);
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
            StrSearcherImpl::Empty(..) =>
            #[cfg_attr(kani, kani::loop_invariant(verify::empty_loop_state(&*self)))]
            #[cfg_attr(
                    kani,
                    kani::loop_modifies(
                        verify::front_cursor(self),
                        verify::empty_forward_flag(self),
                        verify::empty_finished(self)
                    )
                )]
            loop {
                match self.next() {
                    SearchStep::Match(a, b) => return Some((a, b)),
                    SearchStep::Done => return None,
                    SearchStep::Reject(..) => {}
                }
            },
            StrSearcherImpl::Byte(ref mut searcher) => {
                let bytes = self.haystack.as_bytes();
                if searcher.position >= bytes.len() {
                    return None;
                }
                match memchr::memchr(searcher.b, &bytes[searcher.position..]) {
                    Some(i) => {
                        let pos = searcher.position + i;
                        searcher.position = pos + 1;
                        Some((pos, pos + 1))
                    }
                    None => {
                        searcher.position = bytes.len();
                        None
                    }
                }
            }
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
    #[cfg_attr(kani, kani::requires(verify::supported_contract_state(self)))]
    #[cfg_attr(kani, kani::ensures(|step| verify::invariant(self)
        && verify::step_ok(self.haystack, *step)))]
    #[cfg_attr(
        kani,
        kani::modifies(
            verify::back_cursor(self),
            verify::back_memory(self),
            verify::empty_backward_flag(self),
            verify::empty_finished(self)
        )
    )]
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
            StrSearcherImpl::Byte(ref mut searcher) => {
                let end = searcher.end;
                if end == 0 {
                    return SearchStep::Done;
                }
                let bytes = self.haystack.as_bytes();
                if bytes[end - 1] == searcher.b {
                    searcher.end = end - 1;
                    SearchStep::Match(end - 1, end)
                } else {
                    let start = self.haystack.floor_char_boundary(end - 1);
                    searcher.end = start;
                    SearchStep::Reject(start, end)
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
                    SearchStep::Reject(a, b) => {
                        // skip to previous char boundary
                        let a = self.haystack.floor_char_boundary(a);
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
            StrSearcherImpl::Empty(..) =>
            #[cfg_attr(kani, kani::loop_invariant(verify::empty_loop_state(&*self)))]
            #[cfg_attr(
                    kani,
                    kani::loop_modifies(
                        verify::back_cursor(self),
                        verify::empty_backward_flag(self),
                        verify::empty_finished(self)
                    )
                )]
            loop {
                match self.next_back() {
                    SearchStep::Match(a, b) => return Some((a, b)),
                    SearchStep::Done => return None,
                    SearchStep::Reject(..) => {}
                }
            },
            StrSearcherImpl::Byte(ref mut searcher) => {
                if searcher.end == 0 {
                    return None;
                }
                let bytes = self.haystack.as_bytes();
                match memchr::memrchr(searcher.b, &bytes[..searcher.end]) {
                    Some(i) => {
                        searcher.end = i;
                        Some((i, i + 1))
                    }
                    None => {
                        searcher.end = 0;
                        None
                    }
                }
            }
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
    #[cfg_attr(kani, kani::ensures(|_| true))]
    #[cfg_attr(kani, kani::modifies())]
    fn byteset_create(bytes: &[u8]) -> u64 {
        bytes.iter().fold(0, |a, &b| (1 << (b & 0x3f)) | a)
    }

    #[inline]
    #[cfg_attr(kani, kani::ensures(|_| true))]
    #[cfg_attr(kani, kani::modifies())]
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
        #[cfg_attr(kani, kani::loop_invariant(
            verify::raw_loop_state(self, haystack, needle, long_period)
                && old_pos <= self.position
                && (self.position != old_pos || self.memory == on_entry(self.memory))))]
        #[cfg_attr(kani, kani::loop_modifies(&self.position, &self.memory))]
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
            #[cfg_attr(kani, kani::loop_invariant(
                verify::raw_scan_state(self, haystack, needle, long_period, true)
                    && verify::long_scan_probes::<S>(self, haystack, needle, long_period, kani::index, 0, old_pos, on_entry(verify::last_scalar_start(needle)))
                    && self.position == on_entry(self.position)
                    && self.memory == on_entry(self.memory)
                    && old_pos <= self.position))]
            #[cfg_attr(kani, kani::loop_modifies(&self.position, &self.memory))]
            for i in start..needle.len() {
                // SAFETY: on every iteration of `'search`, the `haystack.get(self.position + needle_last)`
                // check returned `Some`, so `self.position + needle_last < haystack.len()`.
                // Since `i < needle.len()` implies `i <= needle_last`, we have
                // `self.position + i < haystack.len()`.
                // Every path that mutates `self.position` below either returns or re-enters `'search`,
                // which re-runs the check before reaching the loop again.
                if needle[i] != unsafe { *haystack.get_unchecked(self.position + i) } {
                    self.position += i - self.crit_pos + 1;
                    if !long_period {
                        self.memory = 0;
                    }
                    continue 'search;
                }
            }

            // See if the left part of the needle matches
            let start = if long_period { 0 } else { self.memory };
            #[cfg_attr(kani, kani::loop_invariant(
                verify::raw_scan_state(self, haystack, needle, long_period, true)
                    && verify::long_scan_probes::<S>(self, haystack, needle, long_period, kani::index, 1, old_pos, on_entry(verify::last_scalar_start(needle)))
                    && self.position == on_entry(self.position)
                    && self.memory == on_entry(self.memory)
                    && old_pos <= self.position))]
            #[cfg_attr(kani, kani::loop_modifies(&self.position, &self.memory))]
            for i in (start..self.crit_pos).rev() {
                // SAFETY: on every iteration of `'search`, the `haystack.get(self.position + needle_last)`
                // check returned `Some`, so `self.position + needle_last < haystack.len()`.
                // Since `i < self.crit_pos <= needle.len()`, we have `i <= needle_last`, and thus
                // `self.position + i <= self.position + needle_last < haystack.len()`.
                // Every path that mutates `self.position` below either returns or re-enters `'search`,
                // which re-runs the check before reaching the loop again.
                if needle[i] != unsafe { *haystack.get_unchecked(self.position + i) } {
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
        #[cfg_attr(kani, kani::loop_invariant(
            verify::raw_loop_state(self, haystack, needle, long_period)
                && self.end <= old_end
                && (self.end != old_end || self.memory_back == on_entry(self.memory_back))))]
        #[cfg_attr(kani, kani::loop_modifies(&self.end, &self.memory_back))]
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
            #[cfg_attr(kani, kani::loop_invariant(
                verify::raw_scan_state(self, haystack, needle, long_period, false)
                    && verify::long_scan_probes::<S>(self, haystack, needle, long_period, kani::index, 2, old_end, on_entry(verify::reverse_scan_probe::<S>(needle)))
                    && self.end == on_entry(self.end)
                    && self.memory_back == on_entry(self.memory_back)
                    && self.end <= old_end))]
            #[cfg_attr(kani, kani::loop_modifies(&self.end, &self.memory_back))]
            for i in (0..crit).rev() {
                // SAFETY: On every iteration of `'search`, `haystack.get(self.end.wrapping_sub(needle.len()))`
                //   returned `Some`, so `self.end >= needle.len()` and `self.end - needle.len() < haystack.len()`.
                //   Since `self.end <= haystack.len()` and `i < needle.len()`, we have
                //   `self.end - needle.len() + i < self.end <= haystack.len()`, so
                //   `haystack.get_unchecked(self.end - needle.len() + i)` is safe.
                // - The path that mutates `self.end` either re-enters `'search`, which re-runs the checks
                //   before reaching this loop again, or returns on match, so the invariant holds.
                if needle[i] != unsafe { *haystack.get_unchecked(self.end - needle.len() + i) } {
                    self.end -= self.crit_pos_back - i;
                    if !long_period {
                        self.memory_back = needle.len();
                    }
                    continue 'search;
                }
            }

            // See if the right part of the needle matches
            let needle_end = if long_period { needle.len() } else { self.memory_back };
            #[cfg_attr(kani, kani::loop_invariant(
                verify::raw_scan_state(self, haystack, needle, long_period, false)
                    && verify::long_scan_probes::<S>(self, haystack, needle, long_period, kani::index, 3, old_end, on_entry(verify::reverse_scan_probe::<S>(needle)))
                    && self.end == on_entry(self.end)
                    && self.memory_back == on_entry(self.memory_back)
                    && self.end <= old_end))]
            #[cfg_attr(kani, kani::loop_modifies(&self.end, &self.memory_back))]
            for i in self.crit_pos_back..needle_end {
                // SAFETY: The same `self.end - needle.len() + i < haystack.len()` argument as the
                // left-part loop applies: the `haystack.get(self.end.wrapping_sub(needle.len()))`
                // check at the top of `'search` established the bound for this iteration, and
                // every mutation of `self.end` is followed by `continue 'search` (which re-runs
                // the check) or a `return` (which exits before any further unsafe access).
                if needle[i] != unsafe { *haystack.get_unchecked(self.end - needle.len() + i) } {
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
    #[cfg_attr(kani, kani::requires(!arr.is_empty() && arr.len() <= verify::MAX_ALLOCATION_BYTES))]
    #[cfg_attr(kani, kani::ensures(|result| verify::numeric_suffix_result(arr, *result)))]
    #[cfg_attr(kani, kani::modifies())]
    fn maximal_suffix(arr: &[u8], order_greater: bool) -> (usize, usize) {
        let mut left = 0; // Corresponds to i in the paper
        let mut right = 1; // Corresponds to j in the paper
        let mut offset = 0; // Corresponds to k in the paper, but starting at 0
        // to match 0-based indexing.
        let mut period = 1; // Corresponds to p in the paper

        #[cfg_attr(kani, kani::loop_invariant(verify::suffix_loop_state(arr, left, right, offset, period)))]
        #[cfg_attr(kani, kani::loop_modifies(&left, &right, &offset, &period))]
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

        #[cfg_attr(kani, kani::loop_invariant(
            verify::reverse_suffix_loop_state(arr, known_period, left, right, offset, period)))]
        #[cfg_attr(kani, kani::loop_modifies(&left, &right, &offset, &period))]
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
    all(target_arch = "loongarch64", target_feature = "lsx"),
    all(target_arch = "aarch64", target_feature = "neon")
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
        both.to_bitmask() as u16
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
    all(target_arch = "loongarch64", target_feature = "lsx"),
    all(target_arch = "aarch64", target_feature = "neon")
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

    // A cover immediately after each positive assumption and assertion checks reachability
    // of that program point under the same assumptions and stubs. `true` is
    // intentional: the predicate has already been evaluated by the assertion;
    // evaluating it again could repeat a function call or quantified check.
    // These probes add no assumptions. Negative fixtures remain separate.

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
        kani::cover(true, "assume #1");
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
        kani::cover(true, "assume #2");
        kani::assume(ptr_y.is_aligned());
        kani::cover(true, "assume #3");
        assert_eq!(
            unsafe {
                small_slice_eq(
                    crate::slice::from_raw_parts(ptr_x, 0),
                    crate::slice::from_raw_parts(ptr_y, 0),
                )
            },
            true
        );
        kani::cover(true, "assert #1");
    }

    // Challenge 21: symbolic-length proofs for the real substring searcher.

    // CI's --object-bits 12 leaves 52 signed pointer offset bits. The largest
    // byte allocation with a representable one-past-the-end pointer therefore
    // has 2^51 - 1 bytes, as in Challenge 20 PR #740. This is the pointer-model
    // limit, not a bound on search iterations. Haystack and needle lengths are
    // independently symbolic throughout this domain.
    pub(super) const MAX_ALLOCATION_BYTES: usize = (1 << 51) - 1;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut u8;
        fn __CPROVER_havoc_object(ptr: *mut u8);
    }

    // Start with initialized storage, then choose arbitrary defined bytes.
    // Havoc changes this fresh byte object's contents, not its allocation size
    // or any other object. It imposes no restriction on the input bytes.
    fn initialized_symbolic_allocation(len: usize) -> *mut u8 {
        assert!(len > 0 && len <= MAX_ALLOCATION_BYTES);
        kani::cover(true, "assert #2");
        let ptr = unsafe { malloc(len) };
        kani::assume(!ptr.is_null());
        kani::cover(true, "assume #4");
        unsafe {
            crate::ptr::write_bytes(ptr, 0, len);
            __CPROVER_havoc_object(ptr);
        }
        ptr
    }

    #[kani::proof]
    pub fn harness_initialized_symbolic_bytes() {
        let len: usize = kani::any();
        kani::assume(len > 0 && len <= MAX_ALLOCATION_BYTES);
        kani::cover(true, "assume #5");
        let ptr = initialized_symbolic_allocation(len);
        let bytes = unsafe { crate::slice::from_raw_parts(ptr, len) };
        let i: usize = kani::any();
        let j: usize = kani::any();
        kani::assume(i < len && j < len);
        kani::cover(true, "assume #6");
        kani::cover(
            len > 4096 && i != j && bytes[i] != bytes[j],
            "independent arbitrary initialized bytes at symbolic length",
        );
        kani::cover(
            bytes[i] == 0x80 && bytes[j] == 0xff,
            "initialized byte input has no UTF-8 restriction",
        );
        kani::cover(
            len == MAX_ALLOCATION_BYTES,
            "the largest initialized allocation in the CI pointer model",
        );
    }

    fn any_str() -> &'static str {
        let len: usize = kani::any();
        kani::assume(len <= MAX_ALLOCATION_BYTES);
        kani::cover(true, "assume #7");
        let ptr = if len == 0 {
            crate::ptr::NonNull::<u8>::dangling().as_ptr()
        } else {
            initialized_symbolic_allocation(len)
        };
        // SAFETY: the allocation lives for the proof. As in Challenge 20, UTF-8
        // validity is modeled by its local consequences rather than a scan.
        unsafe { crate::str::from_utf8_unchecked(crate::slice::from_raw_parts(ptr, len)) }
    }

    // Preprocessing has a non-empty domain. Constrain that before allocation
    // so its quantified array facts do not carry a dead dangling-pointer case.
    // This produces exactly the non-empty part of any_str's input domain.
    fn any_nonempty_str() -> &'static str {
        let len: usize = kani::any();
        kani::assume(len > 0 && len <= MAX_ALLOCATION_BYTES);
        kani::cover(true, "assume #8");
        let ptr = initialized_symbolic_allocation(len);
        unsafe { crate::str::from_utf8_unchecked(crate::slice::from_raw_parts(ptr, len)) }
    }

    // Word-combinatorics lemmas apply to arbitrary byte sequences, including
    // reversed UTF-8 bytes. Avoid constructing a str view in these harnesses.
    fn any_nonempty_bytes() -> &'static [u8] {
        let len: usize = kani::any();
        kani::assume(len > 0 && len <= MAX_ALLOCATION_BYTES);
        kani::cover(true, "assume #9");
        let ptr = initialized_symbolic_allocation(len);
        unsafe { crate::slice::from_raw_parts(ptr, len) }
    }

    // Basic state check used by the Empty and Byte proofs below. The TwoWay
    // branch records numeric constraints only, not the full search invariant.
    pub(super) fn invariant(s: &StrSearcher<'_, '_>) -> bool {
        let (position, end) = match &s.searcher {
            StrSearcherImpl::Empty(e) => {
                if !s.needle.is_empty() {
                    return false;
                }
                (e.position, e.end)
            }
            StrSearcherImpl::Byte(b) => {
                if s.needle.len() != 1 || s.needle.as_bytes()[0] != b.b || b.b >= 128 {
                    return false;
                }
                (b.position, b.end)
            }
            StrSearcherImpl::TwoWay(t) => {
                let n = s.needle.len();
                if n < 2 || t.period == 0 || t.period > n || t.crit_pos > n || t.crit_pos_back > n {
                    return false;
                }
                if t.memory == usize::MAX {
                    if t.memory_back != usize::MAX
                        || !long_preprocessing_state(t, s.needle.as_bytes())
                    {
                        return false;
                    }
                } else if !short_state(t, s.haystack.as_bytes(), s.needle.as_bytes()) {
                    return false;
                }
                (t.position, t.end)
            }
        };
        // Forward and reverse searches are independent, so do not order them.
        position <= s.haystack.len()
            && end <= s.haystack.len()
            && s.haystack.is_char_boundary(position)
            && s.haystack.is_char_boundary(end)
    }

    fn lead_width(b: u8) -> usize {
        match b {
            0..=0x7f => 1,
            0xc2..=0xdf => 2,
            0xe0..=0xef => 3,
            0xf0..=0xf4 => 4,
            _ => 0,
        }
    }

    fn continuation(b: u8) -> bool {
        b & 0xc0 == 0x80
    }

    /// A complete Unicode scalar at `i`, including the next boundary if present.
    /// This is a local UTF-8 rule, not an assumption about search results.
    fn character_at(bytes: &[u8], i: usize) -> bool {
        if i >= bytes.len() {
            return false;
        }
        let lead = bytes[i];
        let width = lead_width(lead);
        if width == 0 || width > bytes.len() - i {
            return false;
        }
        let second_ok = if width == 1 {
            true
        } else {
            let second = bytes[i + 1];
            match lead {
                0xe0 => (0xa0..=0xbf).contains(&second),
                0xed => (0x80..=0x9f).contains(&second),
                0xf0 => (0x90..=0xbf).contains(&second),
                0xf4 => (0x80..=0x8f).contains(&second),
                _ => continuation(second),
            }
        };
        second_ok
            && (width < 3 || continuation(bytes[i + 2]))
            && (width < 4 || continuation(bytes[i + 3]))
            && (i + width == bytes.len() || !continuation(bytes[i + width]))
    }

    /// Every byte of a valid UTF-8 string belongs to a complete scalar. For a
    /// continuation byte, its lead is at most three bytes earlier. The predicate
    /// holds at every index of every valid string, including indices a buggy
    /// algorithm might produce; it does not require `i` to be a boundary.
    fn utf8_at(bytes: &[u8], i: usize) -> bool {
        i >= bytes.len()
            || character_at(bytes, i)
            || (i >= 1 && lead_width(bytes[i - 1]) >= 2 && character_at(bytes, i - 1))
            || (i >= 2 && lead_width(bytes[i - 2]) >= 3 && character_at(bytes, i - 2))
            || (i >= 3 && lead_width(bytes[i - 3]) == 4 && character_at(bytes, i - 3))
    }

    /// Local consequences of valid UTF-8 needed by boundary rounding. The
    /// first-byte condition also justifies floor_char_boundary's debug check.
    /// No returned search index is assumed to be a boundary here.
    pub(crate) fn nearby_boundary(s: &str, index: usize, forward: bool) -> bool {
        if s.len() > isize::MAX as usize || (!s.is_empty() && continuation(s.as_bytes()[0])) {
            return false;
        }
        if index >= s.len() {
            return true;
        }
        if forward {
            s.is_char_boundary(index)
                || s.is_char_boundary(index + 1)
                || s.is_char_boundary(index + 2)
                || s.is_char_boundary(index + 3)
        } else {
            s.is_char_boundary(index)
                || (index >= 1 && s.is_char_boundary(index - 1))
                || (index >= 2 && s.is_char_boundary(index - 2))
                || (index >= 3 && s.is_char_boundary(index - 3))
        }
    }

    pub(crate) fn boundary_result(s: &str, index: usize, result: usize, forward: bool) -> bool {
        result <= s.len()
            && s.is_char_boundary(result)
            && if index >= s.len() {
                result == s.len()
            } else if forward {
                index <= result && result - index <= 3
            } else {
                result <= index && index - result <= 3
            }
    }

    // A UTF-8 scalar contains at most four bytes. `nearby_boundary` therefore
    // bounds this particular rounding loop independently of the string length.
    // Keep unwinding assertions enabled to prove this is a complete expansion.
    #[kani::proof_for_contract(str::ceil_char_boundary)]
    #[kani::unwind(5)]
    pub fn harness_ceil_char_boundary() {
        let s = any_str();
        let index: usize = kani::any();
        kani::assume(nearby_boundary(s, index, true));
        kani::cover(true, "assume #10");
        let result = s.ceil_char_boundary(index);
        kani::cover(
            index > 4096 && result > index,
            "round forward at a distant continuation byte",
        );
        kani::cover(index >= s.len(), "clamp at the end");
        kani::cover(true, "contract proof returns: harness_ceil_char_boundary");
    }

    #[kani::proof_for_contract(str::floor_char_boundary)]
    pub fn harness_floor_char_boundary() {
        let s = any_str();
        let index: usize = kani::any();
        kani::assume(nearby_boundary(s, index, false));
        kani::cover(true, "assume #11");
        let result = s.floor_char_boundary(index);
        kani::cover(
            index > 4096 && result < index && index < s.len(),
            "round backward at a distant continuation byte",
        );
        kani::cover(index >= s.len(), "clamp at the end");
        kani::cover(true, "contract proof returns: harness_floor_char_boundary");
    }

    // A contract wrapper keeps the real, independently verified rounding
    // function separate from the valid-UTF-8 assumption used by the caller.
    #[kani::requires(nearby_boundary(s, index, false))]
    #[kani::ensures(|result| boundary_result(s, index, *result, false))]
    #[kani::modifies()]
    fn verified_floor_boundary(s: &str, index: usize) -> usize {
        s.floor_char_boundary(index)
    }

    #[kani::proof_for_contract(verified_floor_boundary)]
    #[kani::stub_verified(str::floor_char_boundary)]
    pub fn harness_verified_floor_boundary() {
        let s = any_str();
        let index = kani::any();
        kani::assume(nearby_boundary(s, index, false));
        kani::cover(true, "assume #12");
        let _ = verified_floor_boundary(s, index);
        kani::cover(
            true,
            "contract proof returns: harness_verified_floor_boundary",
        );
    }

    // Kani's ordinary stub pass retains the source function's contract
    // metadata. Matching the identifier and contract shape keeps its generated
    // closure names resolvable; the independent wrapper proof remains above.
    #[kani::requires(true)]
    #[kani::ensures(|result| boundary_result(s, index, *result, false))]
    #[kani::modifies()]
    fn floor_char_boundary(s: &str, index: usize) -> usize {
        // Holds at every index of every valid str, independently of the raw
        // search result. The wrapper's verified contract supplies the result.
        kani::assume(nearby_boundary(s, index, false));
        kani::cover(true, "assume #13");
        verified_floor_boundary(s, index)
    }

    #[kani::requires(nearby_boundary(s, index, true))]
    #[kani::ensures(|result| boundary_result(s, index, *result, true))]
    #[kani::modifies()]
    fn verified_ceil_boundary(s: &str, index: usize) -> usize {
        s.ceil_char_boundary(index)
    }

    #[kani::proof_for_contract(verified_ceil_boundary)]
    #[kani::stub_verified(str::ceil_char_boundary)]
    pub fn harness_verified_ceil_boundary() {
        let s = any_str();
        let index = kani::any();
        kani::assume(nearby_boundary(s, index, true));
        kani::cover(true, "assume #14");
        let _ = verified_ceil_boundary(s, index);
        kani::cover(
            true,
            "contract proof returns: harness_verified_ceil_boundary",
        );
    }

    // The same-name contract shape is required by Kani's ordinary stub pass;
    // see the corresponding floor model and the documented minimal regression.
    #[kani::requires(true)]
    #[kani::ensures(|result| boundary_result(s, index, *result, true))]
    #[kani::modifies()]
    fn ceil_char_boundary(s: &str, index: usize) -> usize {
        kani::assume(nearby_boundary(s, index, true));
        kani::cover(true, "assume #15");
        verified_ceil_boundary(s, index)
    }

    #[kani::proof_for_contract(floor_char_boundary)]
    #[kani::stub_verified(verified_floor_boundary)]
    pub fn harness_floor_boundary_adapter_contract() {
        let s = any_str();
        let index = kani::any();
        let result = floor_char_boundary(s, index);
        kani::cover(
            index > 4096 && result < index,
            "floor adapter at a distant index",
        );
        kani::cover(index >= s.len(), "floor adapter clamps at the end");
        kani::cover(
            true,
            "contract proof returns: harness_floor_boundary_adapter_contract",
        );
    }

    #[kani::proof_for_contract(ceil_char_boundary)]
    #[kani::stub_verified(verified_ceil_boundary)]
    pub fn harness_ceil_boundary_adapter_contract() {
        let s = any_str();
        let index = kani::any();
        let result = ceil_char_boundary(s, index);
        kani::cover(
            index > 4096 && result > index,
            "ceil adapter at a distant index",
        );
        kani::cover(index >= s.len(), "ceil adapter clamps at the end");
        kani::cover(
            true,
            "contract proof returns: harness_ceil_boundary_adapter_contract",
        );
    }

    // Every valid UTF-8 string satisfies this weaker, pointwise consequence:
    // a leading byte's width lands at the next character boundary. This
    // universal input fact is independent of the search and its output.
    fn utf8_scalar_steps(bytes: &[u8]) -> bool {
        let ptr = bytes.as_ptr();
        let len = bytes.len();
        unsafe {
            kani::internal::kani_forall(0, len, move |i: usize| {
                let b = *crate::intrinsics::arith_offset(ptr, i as isize);
                let width = match b {
                    0..=0x7f => 1,
                    0xc2..=0xdf => 2,
                    0xe0..=0xef => 3,
                    0xf0..=0xf4 => 4,
                    _ => 0,
                };
                width == 0
                    || (width <= len - i
                        && (i + width == len
                            || (*crate::intrinsics::arith_offset(ptr, (i + width) as isize) as i8)
                                >= -0x40))
            })
        }
    }

    #[kani::proof]
    #[kani::solver(z3)]
    pub fn harness_utf8_scalar_steps_lookup() {
        let h = any_str().as_bytes();
        kani::assume(utf8_scalar_steps(h));
        kani::cover(true, "assume #16");
        let i = kani::any();
        assert!(utf8_next_boundary_at(h, i));
        kani::cover(true, "assert #3");
    }

    fn any_empty() -> StrSearcher<'static, 'static> {
        let s = StrSearcher {
            haystack: any_str(),
            needle: "",
            searcher: StrSearcherImpl::Empty(EmptyNeedle {
                position: kani::any(),
                end: kani::any(),
                is_match_fw: kani::any(),
                is_match_bw: kani::any(),
                is_finished: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #17");
        s
    }

    pub(super) fn front_cursor(s: &StrSearcher<'_, '_>) -> *const usize {
        match &s.searcher {
            StrSearcherImpl::Empty(e) => &raw const e.position,
            StrSearcherImpl::Byte(b) => &raw const b.position,
            StrSearcherImpl::TwoWay(t) => &raw const t.position,
        }
    }
    pub(super) fn back_cursor(s: &StrSearcher<'_, '_>) -> *const usize {
        match &s.searcher {
            StrSearcherImpl::Empty(e) => &raw const e.end,
            StrSearcherImpl::Byte(b) => &raw const b.end,
            StrSearcherImpl::TwoWay(t) => &raw const t.end,
        }
    }
    pub(super) fn front_memory(s: &StrSearcher<'_, '_>) -> *const [usize] {
        match &s.searcher {
            StrSearcherImpl::TwoWay(t) => crate::ptr::slice_from_raw_parts(&raw const t.memory, 1),
            _ => crate::ptr::slice_from_raw_parts(s as *const _ as *const usize, 0),
        }
    }

    pub(super) fn back_memory(s: &StrSearcher<'_, '_>) -> *const [usize] {
        match &s.searcher {
            StrSearcherImpl::TwoWay(t) => {
                crate::ptr::slice_from_raw_parts(&raw const t.memory_back, 1)
            }
            _ => crate::ptr::slice_from_raw_parts(s as *const _ as *const usize, 0),
        }
    }

    pub(super) fn supported_contract_state(s: &StrSearcher<'_, '_>) -> bool {
        invariant(s)
    }

    pub(super) fn empty_forward_flag(s: &StrSearcher<'_, '_>) -> *const [bool] {
        match &s.searcher {
            StrSearcherImpl::Empty(e) => {
                crate::ptr::slice_from_raw_parts(&raw const e.is_match_fw, 1)
            }
            _ => crate::ptr::slice_from_raw_parts(s as *const _ as *const bool, 0),
        }
    }
    pub(super) fn empty_backward_flag(s: &StrSearcher<'_, '_>) -> *const [bool] {
        match &s.searcher {
            StrSearcherImpl::Empty(e) => {
                crate::ptr::slice_from_raw_parts(&raw const e.is_match_bw, 1)
            }
            _ => crate::ptr::slice_from_raw_parts(s as *const _ as *const bool, 0),
        }
    }
    pub(super) fn empty_finished(s: &StrSearcher<'_, '_>) -> *const [bool] {
        match &s.searcher {
            StrSearcherImpl::Empty(e) => {
                crate::ptr::slice_from_raw_parts(&raw const e.is_finished, 1)
            }
            _ => crate::ptr::slice_from_raw_parts(s as *const _ as *const bool, 0),
        }
    }

    /// Hooks for the real trait-default filters. The fallback covers the searcher
    /// storage; externally mutated predicate state needs its own specialization.
    /// The substring specialization preserves both input pointers.
    pub(super) trait FilterLoopContract {
        fn valid(&self) -> bool;
        fn cursor(&self, reverse: bool) -> *const [u8];
        fn word_cursor(&self, reverse: bool) -> *const [usize];
        fn flag(&self, reverse: bool) -> *const [bool];
        fn cache(&self, reverse: bool) -> *const [usize];
        fn finished(&self) -> *const [bool];
    }

    impl<T: ?Sized> FilterLoopContract for T {
        default fn valid(&self) -> bool {
            true
        }
        default fn cursor(&self, _: bool) -> *const [u8] {
            crate::ptr::slice_from_raw_parts(self as *const T as *const u8, size_of_val(self))
        }
        default fn word_cursor(&self, _: bool) -> *const [usize] {
            crate::ptr::slice_from_raw_parts(self as *const T as *const usize, 0)
        }
        default fn flag(&self, _: bool) -> *const [bool] {
            crate::ptr::slice_from_raw_parts(self as *const T as *const bool, 0)
        }
        default fn cache(&self, _: bool) -> *const [usize] {
            crate::ptr::slice_from_raw_parts(self as *const T as *const usize, 0)
        }
        default fn finished(&self) -> *const [bool] {
            crate::ptr::slice_from_raw_parts(self as *const T as *const bool, 0)
        }
    }

    impl FilterLoopContract for StrSearcher<'_, '_> {
        fn valid(&self) -> bool {
            match &self.searcher {
                StrSearcherImpl::Empty(_) => empty_loop_state(self),
                StrSearcherImpl::Byte(_) => byte_loop_state(self),
                StrSearcherImpl::TwoWay(_) => two_way_loop_state(self),
            }
        }
        fn cursor(&self, _: bool) -> *const [u8] {
            // The specialized word hook covers the same usize field below.
            crate::ptr::slice_from_raw_parts(self as *const Self as *const u8, 0)
        }
        fn word_cursor(&self, reverse: bool) -> *const [usize] {
            let ptr = match &self.searcher {
                StrSearcherImpl::Empty(e) => {
                    if reverse {
                        &raw const e.end
                    } else {
                        &raw const e.position
                    }
                }
                StrSearcherImpl::Byte(b) => {
                    if reverse {
                        &raw const b.end
                    } else {
                        &raw const b.position
                    }
                }
                StrSearcherImpl::TwoWay(t) => {
                    if reverse {
                        &raw const t.end
                    } else {
                        &raw const t.position
                    }
                }
            };
            crate::ptr::slice_from_raw_parts(ptr, 1)
        }
        fn flag(&self, reverse: bool) -> *const [bool] {
            match &self.searcher {
                StrSearcherImpl::Empty(e) => crate::ptr::slice_from_raw_parts(
                    if reverse {
                        &raw const e.is_match_bw
                    } else {
                        &raw const e.is_match_fw
                    },
                    1,
                ),
                _ => crate::ptr::slice_from_raw_parts(self as *const Self as *const bool, 0),
            }
        }
        fn cache(&self, reverse: bool) -> *const [usize] {
            match &self.searcher {
                StrSearcherImpl::TwoWay(t) => crate::ptr::slice_from_raw_parts(
                    if reverse {
                        &raw const t.memory_back
                    } else {
                        &raw const t.memory
                    },
                    1,
                ),
                _ => crate::ptr::slice_from_raw_parts(self as *const Self as *const usize, 0),
            }
        }
        fn finished(&self) -> *const [bool] {
            match &self.searcher {
                StrSearcherImpl::Empty(e) => {
                    crate::ptr::slice_from_raw_parts(&raw const e.is_finished, 1)
                }
                _ => crate::ptr::slice_from_raw_parts(self as *const Self as *const bool, 0),
            }
        }
    }

    pub(super) fn two_way_loop_state(s: &StrSearcher<'_, '_>) -> bool {
        let StrSearcherImpl::TwoWay(t) = &s.searcher else {
            return false;
        };
        if t.memory == usize::MAX {
            return long_loop_state(s);
        }
        // str and [u8] share the same immutable byte representation. Use raw
        // coercions here to avoid normal library-call ABIs in loop invariants.
        let h = unsafe { &*(s.haystack as *const str as *const [u8]) };
        let n = unsafe { &*(s.needle as *const str as *const [u8]) };
        if !short_loop_state(t, h, n) {
            return false;
        }
        let len = crate::intrinsics::ptr_metadata(s.haystack as *const str);
        let hp = s.haystack as *const str as *const u8;
        (t.position == 0
            || t.position == len
            || unsafe { *crate::intrinsics::arith_offset(hp, t.position as isize) } as i8 >= -0x40)
            && (t.end == 0
                || t.end == len
                || unsafe { *crate::intrinsics::arith_offset(hp, t.end as isize) } as i8 >= -0x40)
    }

    pub(super) fn long_loop_state(s: &StrSearcher<'_, '_>) -> bool {
        let n = crate::intrinsics::ptr_metadata(s.needle as *const str);
        let len = crate::intrinsics::ptr_metadata(s.haystack as *const str);
        let hp = s.haystack as *const str as *const u8;
        let StrSearcherImpl::TwoWay(t) = &s.searcher else {
            return false;
        };
        if n < 2
            || n > MAX_ALLOCATION_BYTES
            || len > MAX_ALLOCATION_BYTES
            || t.crit_pos == 0
            || t.crit_pos >= n
            || t.crit_pos_back != t.crit_pos
            || t.memory != usize::MAX
            || t.memory_back != usize::MAX
            || t.position > len
            || t.end > len
        {
            return false;
        }
        let other = n - t.crit_pos;
        let largest = if t.crit_pos > other {
            t.crit_pos
        } else {
            other
        };
        t.period == largest + 1
            && (t.position == 0
                || t.position == len
                || unsafe { *crate::intrinsics::arith_offset(hp, t.position as isize) } as i8
                    >= -0x40)
            && (t.end == 0
                || t.end == len
                || unsafe { *crate::intrinsics::arith_offset(hp, t.end as isize) } as i8 >= -0x40)
    }

    // Called only by the loop invariant: avoid ordinary library calls in this
    // expression because CBMC may otherwise share incompatible write-set ABIs
    // between calls inside and outside an invariant.
    pub(super) fn empty_loop_state(s: &StrSearcher<'_, '_>) -> bool {
        let len = crate::intrinsics::ptr_metadata(s.haystack as *const str);
        let needle_len = crate::intrinsics::ptr_metadata(s.needle as *const str);
        let ptr = s.haystack as *const str as *const u8;
        let StrSearcherImpl::Empty(e) = &s.searcher else {
            return false;
        };
        let (f, b) = (e.position, e.end);
        needle_len == 0
            && f <= len
            && b <= len
            && (f == 0
                || f == len
                || unsafe { *crate::intrinsics::arith_offset(ptr, f as isize) } as i8 >= -0x40)
            && (b == 0
                || b == len
                || unsafe { *crate::intrinsics::arith_offset(ptr, b as isize) } as i8 >= -0x40)
    }

    pub(super) fn byte_loop_state(s: &StrSearcher<'_, '_>) -> bool {
        let len = crate::intrinsics::ptr_metadata(s.haystack as *const str);
        let n = crate::intrinsics::ptr_metadata(s.needle as *const str);
        let ptr = s.haystack as *const str as *const u8;
        let np = s.needle as *const str as *const u8;
        let StrSearcherImpl::Byte(b) = &s.searcher else {
            return false;
        };
        let (f, e) = (b.position, b.end);
        n == 1
            && b.b < 128
            && unsafe { *np } == b.b
            && f <= len
            && e <= len
            && (f == 0
                || f == len
                || unsafe { *crate::intrinsics::arith_offset(ptr, f as isize) } as i8 >= -0x40)
            && (e == 0
                || e == len
                || unsafe { *crate::intrinsics::arith_offset(ptr, e as isize) } as i8 >= -0x40)
    }

    // On Byte inputs this is the original FilterLoopContract::valid branch.
    // Other variants return false, so using it in a Byte-only proof strengthens
    // the loop invariant and still detects an unexpected variant transition.
    fn byte_filter_loop_valid<'a: 'a, 'b: 'b>(s: &StrSearcher<'a, 'b>) -> bool {
        byte_loop_state(s)
    }

    // Numeric projection of C for the additional filter UB proof. It keeps
    // the cursor and cache ranges needed by the actual step implementations,
    // but does not repeat the separate UTF-8 endpoint proof. Every actual C
    // state satisfies this relation. The model below preserves it by choosing
    // bounded cursors and one of the real cache values, not by assuming C
    // after an arbitrary update.
    // Expand separate ordinary/loop predicates to avoid sharing a helper's
    // ABI between DFCC loop clauses and ordinary contract expressions.
    macro_rules! filter_ub_state_body {
        ($s:ident) => {{
            let hn = crate::intrinsics::ptr_metadata($s.haystack as *const str);
            let nn = crate::intrinsics::ptr_metadata($s.needle as *const str);
            hn <= MAX_ALLOCATION_BYTES
                && nn <= MAX_ALLOCATION_BYTES
                && match &$s.searcher {
                    StrSearcherImpl::Empty(e) => nn == 0 && e.position <= hn && e.end <= hn,
                    StrSearcherImpl::Byte(b) => {
                        nn == 1 && b.b < 128 && b.position <= hn && b.end <= hn
                    }
                    StrSearcherImpl::TwoWay(t) => {
                        nn >= 2
                            && t.crit_pos <= nn
                            && t.crit_pos_back <= nn
                            && t.period > 0
                            && t.period <= nn
                            && t.position <= hn
                            && t.end <= hn
                            && if t.memory == usize::MAX {
                                t.memory_back == usize::MAX
                            } else {
                                (t.memory == 0 || t.memory == nn - t.period)
                                    && (t.memory_back == nn || t.memory_back == t.period)
                            }
                    }
                }
        }};
    }

    fn filter_ub_state(s: &StrSearcher<'_, '_>) -> bool {
        filter_ub_state_body!(s)
    }

    fn filter_ub_loop_valid<'a: 'a, 'b: 'b>(s: &StrSearcher<'a, 'b>) -> bool {
        filter_ub_state_body!(s)
    }

    // Match empty_loop_state's late-bound lifetime signature.
    fn empty_ub_loop_valid(s: &StrSearcher<'_, '_>) -> bool {
        filter_ub_state_body!(s)
    }

    fn arbitrary_filter_storage() -> StrSearcher<'static, 'static> {
        let searcher = match kani::any::<u8>() {
            0 => StrSearcherImpl::Empty(EmptyNeedle {
                position: kani::any(),
                end: kani::any(),
                is_match_fw: kani::any(),
                is_match_bw: kani::any(),
                is_finished: kani::any(),
            }),
            1 => StrSearcherImpl::Byte(ByteNeedle {
                b: kani::any(),
                position: kani::any(),
                end: kani::any(),
            }),
            _ => StrSearcherImpl::TwoWay(TwoWaySearcher {
                crit_pos: kani::any(),
                crit_pos_back: kani::any(),
                period: kani::any(),
                byteset: kani::any(),
                position: kani::any(),
                end: kani::any(),
                memory: kani::any(),
                memory_back: kani::any(),
            }),
        };
        StrSearcher {
            haystack: any_str(),
            needle: any_str(),
            searcher,
        }
    }

    fn any_filter_storage() -> StrSearcher<'static, 'static> {
        let s = arbitrary_filter_storage();
        // This includes every C state: the independent implication proof
        // below starts from arbitrary storage without this assumption.
        kani::assume(filter_ub_state(&s));
        kani::cover(true, "assume #18");
        s
    }

    #[kani::proof]
    pub fn harness_filter_ub_projection_from_c() {
        let s = arbitrary_filter_storage();
        kani::assume(invariant(&s));
        kani::cover(true, "assume #19");
        assert!(filter_ub_state(&s));
        kani::cover(true, "assert #4");
        kani::cover(
            matches!(s.searcher, StrSearcherImpl::Empty(_)),
            "C projects Empty state",
        );
        kani::cover(
            matches!(s.searcher, StrSearcherImpl::Byte(_)),
            "C projects Byte state",
        );
        kani::cover(
            matches!(s.searcher, StrSearcherImpl::TwoWay(_)),
            "C projects TwoWay state",
        );
        kani::cover(
            s.haystack.len() > 4096,
            "C projects symbolic-length storage",
        );
    }

    fn arbitrary_filter_step(s: &mut StrSearcher<'_, '_>, reverse: bool) -> SearchStep {
        let cursor: usize = kani::any();
        kani::assume(cursor <= s.haystack.len());
        kani::cover(true, "assume #20");
        let needle_len = s.needle.len();
        match &mut s.searcher {
            StrSearcherImpl::Empty(e) => {
                if reverse {
                    e.end = cursor;
                    e.is_match_bw = kani::any();
                } else {
                    e.position = cursor;
                    e.is_match_fw = kani::any();
                }
                e.is_finished = kani::any();
            }
            StrSearcherImpl::Byte(b) => {
                if reverse {
                    b.end = cursor;
                } else {
                    b.position = cursor;
                }
            }
            StrSearcherImpl::TwoWay(t) => {
                let long = t.memory == usize::MAX;
                if reverse {
                    t.end = cursor;
                    t.memory_back = if long {
                        usize::MAX
                    } else if kani::any() {
                        needle_len
                    } else {
                        t.period
                    };
                } else {
                    t.position = cursor;
                    t.memory = if long {
                        usize::MAX
                    } else if kani::any() {
                        0
                    } else {
                        needle_len - t.period
                    };
                }
            }
        }
        kani::any()
    }

    struct FilterUbModel;
    impl FilterUbModel {
        // Every update consistent with the real step's numeric postcondition
        // is permitted, and the returned SearchStep is still arbitrary. The
        // separate full-C proofs justify using this weaker numeric summary.
        #[kani::requires(filter_ub_state(s))]
        #[kani::ensures(|_| filter_ub_state(s))]
        #[kani::modifies(
            front_cursor(s),
            front_memory(s),
            empty_forward_flag(s),
            empty_finished(s)
        )]
        fn next<'a: 'a, 'b: 'b>(s: &mut StrSearcher<'a, 'b>) -> SearchStep {
            arbitrary_filter_step(s, false)
        }

        #[kani::requires(filter_ub_state(s))]
        #[kani::ensures(|_| filter_ub_state(s))]
        #[kani::modifies(
            back_cursor(s),
            back_memory(s),
            empty_backward_flag(s),
            empty_finished(s)
        )]
        fn next_back<'a: 'a, 'b: 'b>(s: &mut StrSearcher<'a, 'b>) -> SearchStep {
            arbitrary_filter_step(s, true)
        }
    }

    #[kani::proof_for_contract(FilterUbModel::next)]
    pub fn harness_filter_ub_forward_frame() {
        let mut s = any_filter_storage();
        let _ = FilterUbModel::next(&mut s);
        assert!(filter_ub_state(&s));
        kani::cover(true, "assert #5");
        kani::cover(
            s.haystack.len() > 4096,
            "numeric filter frame at symbolic length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_filter_ub_forward_frame",
        );
    }

    #[kani::proof_for_contract(FilterUbModel::next_back)]
    pub fn harness_filter_ub_reverse_frame() {
        let mut s = any_filter_storage();
        let _ = FilterUbModel::next_back(&mut s);
        assert!(filter_ub_state(&s));
        kani::cover(true, "assert #6");
        kani::cover(
            s.haystack.len() > 4096,
            "reverse numeric filter frame at symbolic length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_filter_ub_reverse_frame",
        );
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as Searcher>::next, FilterUbModel::next)]
    #[kani::stub(<StrSearcher as FilterLoopContract>::valid, filter_ub_loop_valid)]
    pub fn harness_filter_next_reject_extra_ub() {
        let mut s = any_filter_storage();
        let was_empty = matches!(s.searcher, StrSearcherImpl::Empty(_));
        let was_byte = matches!(s.searcher, StrSearcherImpl::Byte(_));
        let result = s.next_reject();
        kani::cover(was_empty, "arbitrary Empty filter storage");
        kani::cover(was_byte, "arbitrary Byte filter storage");
        kani::cover(!was_empty && !was_byte, "arbitrary TwoWay filter storage");
        kani::cover(result.is_some(), "arbitrary rejection indices");
        kani::cover(result.is_none(), "filter exhaustion");
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as ReverseSearcher>::next_back, FilterUbModel::next_back)]
    #[kani::stub(<StrSearcher as FilterLoopContract>::valid, filter_ub_loop_valid)]
    pub fn harness_filter_next_reject_back_extra_ub() {
        let mut s = any_filter_storage();
        let was_empty = matches!(s.searcher, StrSearcherImpl::Empty(_));
        let was_byte = matches!(s.searcher, StrSearcherImpl::Byte(_));
        let result = s.next_reject_back();
        kani::cover(was_empty, "arbitrary Empty reverse filter storage");
        kani::cover(was_byte, "arbitrary Byte reverse filter storage");
        kani::cover(
            !was_empty && !was_byte,
            "arbitrary TwoWay reverse filter storage",
        );
        kani::cover(result.is_some(), "arbitrary reverse rejection indices");
        kani::cover(result.is_none(), "reverse filter exhaustion");
    }

    #[kani::proof]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    pub fn harness_str_searcher_empty_next_match() {
        let mut s = any_empty();
        let result = s.next_match();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Match(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #7");
        kani::cover(
            result.is_some_and(|(a, _)| a > 4096),
            "a distant empty match",
        );
        kani::cover(result.is_none(), "exhaustion");
    }

    #[kani::proof]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    pub fn harness_str_searcher_empty_next_match_back() {
        let mut s = any_empty();
        let result = s.next_match_back();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Match(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #8");
        kani::cover(
            result.is_some_and(|(a, _)| a > 4096),
            "a distant empty match",
        );
        kani::cover(result.is_none(), "exhaustion");
    }

    #[kani::proof]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    pub fn harness_str_searcher_empty_next_reject() {
        let mut s = any_empty();
        let result = s.next_reject();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #9");
        kani::cover(
            result.is_some_and(|(a, b)| a > 4096 && b > a),
            "a distant rejection",
        );
        kani::cover(result.is_none(), "exhaustion");
    }

    #[kani::proof]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    pub fn harness_str_searcher_empty_next_reject_back() {
        let mut s = any_empty();
        let result = s.next_reject_back();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #10");
        kani::cover(
            result.is_some_and(|(a, b)| a > 4096 && b > a),
            "a distant rejection",
        );
        kani::cover(result.is_none(), "exhaustion");
    }

    fn check_step(haystack: &str, step: SearchStep) {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert!(a <= b && b <= haystack.len());
                kani::cover(true, "assert #11");
                assert!(haystack.is_char_boundary(a));
                kani::cover(true, "assert #12");
                assert!(haystack.is_char_boundary(b));
                kani::cover(true, "assert #13");
            }
            SearchStep::Done => {}
        }
    }

    pub(super) fn step_ok(haystack: &str, step: SearchStep) -> bool {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                a <= b
                    && b <= haystack.len()
                    && haystack.is_char_boundary(a)
                    && haystack.is_char_boundary(b)
            }
            SearchStep::Done => true,
        }
    }

    #[unstable(feature = "kani", issue = "none")]
    impl kani::Arbitrary for SearchStep {
        fn any() -> Self {
            match kani::any::<u8>() {
                0 => SearchStep::Match(kani::any(), kani::any()),
                1 => SearchStep::Reject(kani::any(), kani::any()),
                _ => SearchStep::Done,
            }
        }
    }

    #[kani::proof_for_contract(<StrSearcher as Searcher>::next)]
    pub fn harness_str_searcher_empty_next() {
        let mut s = any_empty();
        let StrSearcherImpl::Empty(e) = &s.searcher else {
            unreachable!()
        };
        kani::assume(utf8_at(s.haystack.as_bytes(), e.position));
        kani::cover(true, "assume #21");
        let step = s.next();
        check_step(s.haystack, step);
        assert!(invariant(&s));
        kani::cover(true, "assert #14");
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if a > 4096 && b > a),
            "a distant reject",
        );
        kani::cover(matches!(step, SearchStep::Match(_, _)), "a match");
        kani::cover(matches!(step, SearchStep::Done), "exhaustion");
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_empty_next",
        );
    }

    #[kani::proof_for_contract(<StrSearcher as ReverseSearcher>::next_back)]
    pub fn harness_str_searcher_empty_next_back() {
        let mut s = any_empty();
        let StrSearcherImpl::Empty(e) = &s.searcher else {
            unreachable!()
        };
        if e.end > 0 {
            kani::assume(utf8_at(s.haystack.as_bytes(), e.end - 1));
            kani::cover(true, "assume #22");
        }
        let step = s.next_back();
        check_step(s.haystack, step);
        assert!(invariant(&s));
        kani::cover(true, "assert #15");
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if a > 4096 && b > a),
            "a distant reject",
        );
        kani::cover(matches!(step, SearchStep::Match(_, _)), "a match");
        kani::cover(matches!(step, SearchStep::Done), "exhaustion");
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_empty_next_back",
        );
    }

    // Pair these real-call UB audits with the full Empty step contract proofs.
    // Construct the same C domain in place to avoid a by-value state copy and
    // do not reevaluate the already-proved C/endpoint postcondition here.
    #[kani::proof]
    #[kani::stub_verified(str::ceil_char_boundary)]
    #[kani::stub(TwoWaySearcher::next, reject_two_way_in_byte_proof)]
    pub fn harness_str_searcher_empty_next_extra_ub() {
        let mut s = StrSearcher {
            haystack: any_str(),
            needle: "",
            searcher: StrSearcherImpl::Empty(EmptyNeedle {
                position: kani::any(),
                end: kani::any(),
                is_match_fw: kani::any(),
                is_match_bw: kani::any(),
                is_finished: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #23");
        let StrSearcherImpl::Empty(e) = &s.searcher else {
            unreachable!()
        };
        kani::assume(utf8_at(s.haystack.as_bytes(), e.position));
        kani::cover(true, "assume #24");
        let step = s.next();
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if a > 4096 && b > a),
            "distant Empty rejection",
        );
        kani::cover(matches!(step, SearchStep::Match(_, _)), "Empty match");
        kani::cover(matches!(step, SearchStep::Done), "Empty exhaustion");
    }

    #[kani::proof]
    #[kani::stub_verified(str::floor_char_boundary)]
    #[kani::stub(TwoWaySearcher::next_back, reject_two_way_in_byte_proof)]
    pub fn harness_str_searcher_empty_next_back_extra_ub() {
        let mut s = StrSearcher {
            haystack: any_str(),
            needle: "",
            searcher: StrSearcherImpl::Empty(EmptyNeedle {
                position: kani::any(),
                end: kani::any(),
                is_match_fw: kani::any(),
                is_match_bw: kani::any(),
                is_finished: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #25");
        let StrSearcherImpl::Empty(e) = &s.searcher else {
            unreachable!()
        };
        if e.end > 0 {
            kani::assume(utf8_at(s.haystack.as_bytes(), e.end - 1));
            kani::cover(true, "assume #26");
        }
        // The full reverse contract harness covers all three outcomes on
        // this same input domain. Keep this additional audit to UB checks.
        let _ = s.next_back();
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as Searcher>::next, FilterUbModel::next)]
    #[kani::stub(empty_loop_state, empty_ub_loop_valid)]
    #[kani::stub(TwoWaySearcher::next, reject_two_way_in_byte_proof)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    pub fn harness_empty_next_match_loop_extra_ub() {
        let mut s = StrSearcher {
            haystack: any_str(),
            needle: "",
            searcher: StrSearcherImpl::Empty(EmptyNeedle {
                position: kani::any(),
                end: kani::any(),
                is_match_fw: kani::any(),
                is_match_bw: kani::any(),
                is_finished: kani::any(),
            }),
        };
        kani::assume(filter_ub_state(&s));
        kani::cover(true, "assume #27");
        let result = s.next_match();
        kani::cover(result.is_some(), "arbitrary Empty match indices");
        kani::cover(result.is_none(), "Empty match loop exhaustion");
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as ReverseSearcher>::next_back, FilterUbModel::next_back)]
    #[kani::stub(empty_loop_state, empty_ub_loop_valid)]
    #[kani::stub(TwoWaySearcher::next_back, reject_two_way_in_byte_proof)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memchr)]
    pub fn harness_empty_next_match_back_loop_extra_ub() {
        let mut s = StrSearcher {
            haystack: any_str(),
            needle: "",
            searcher: StrSearcherImpl::Empty(EmptyNeedle {
                position: kani::any(),
                end: kani::any(),
                is_match_fw: kani::any(),
                is_match_bw: kani::any(),
                is_finished: kani::any(),
            }),
        };
        kani::assume(filter_ub_state(&s));
        kani::cover(true, "assume #28");
        let result = s.next_match_back();
        kani::cover(result.is_some(), "arbitrary Empty reverse match indices");
        kani::cover(result.is_none(), "Empty reverse match loop exhaustion");
    }

    #[kani::proof]
    pub fn harness_str_searcher_empty_into_searcher() {
        let haystack = any_str();
        let s = "".into_searcher(haystack);
        assert!(matches!(s.searcher, StrSearcherImpl::Empty(_)));
        kani::cover(true, "assert #16");
        assert!(invariant(&s));
        kani::cover(true, "assert #17");
        kani::cover(haystack.len() > 4096, "symbolic-length haystack");
    }

    #[kani::proof]
    pub fn harness_str_searcher_byte_into_searcher() {
        let haystack = any_str();
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #29");
        let bytes = [byte];
        // SAFETY: every ASCII byte is a complete UTF-8 string of length one.
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let s = needle.into_searcher(haystack);
        assert!(matches!(s.searcher, StrSearcherImpl::Byte(_)));
        kani::cover(true, "assert #18");
        assert!(invariant(&s));
        kani::cover(true, "assert #19");
        kani::cover(haystack.len() > 4096, "symbolic-length haystack");
    }

    fn any_byte<'a>(needle: &'a str) -> StrSearcher<'static, 'a> {
        let s = StrSearcher {
            haystack: any_str(),
            needle,
            searcher: StrSearcherImpl::Byte(ByteNeedle {
                b: needle.as_bytes()[0],
                position: kani::any(),
                end: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #30");
        s
    }

    #[kani::proof_for_contract(<StrSearcher as Searcher>::next)]
    #[kani::stub_verified(str::ceil_char_boundary)]
    #[kani::stub(TwoWaySearcher::next, reject_two_way_in_byte_proof)]
    pub fn harness_str_searcher_byte_next() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #31");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let StrSearcherImpl::Byte(b) = &s.searcher else {
            unreachable!()
        };
        kani::assume(utf8_at(s.haystack.as_bytes(), 0));
        kani::cover(true, "assume #32");
        kani::assume(utf8_at(s.haystack.as_bytes(), b.position));
        kani::cover(true, "assume #33");
        let step = s.next();
        check_step(s.haystack, step);
        assert!(invariant(&s));
        kani::cover(true, "assert #20");
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if a > 4096 && b > a),
            "distant byte rejection",
        );
        kani::cover(matches!(step, SearchStep::Match(_, _)), "byte match");
        kani::cover(matches!(step, SearchStep::Done), "exhaustion");
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_byte_next",
        );
    }

    // Additional UB audit of the real call, separate from the contract/frame
    // proof above. Keep the same Byte state domain; the full C/step postcondition
    // is proved by that contract harness, so it need not be evaluated again here.
    #[kani::proof]
    #[kani::stub_verified(str::ceil_char_boundary)]
    #[kani::stub(TwoWaySearcher::next, reject_two_way_in_byte_proof)]
    pub fn harness_str_searcher_byte_next_extra_ub() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #34");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = StrSearcher {
            haystack: any_str(),
            needle,
            searcher: StrSearcherImpl::Byte(ByteNeedle {
                b: byte,
                position: kani::any(),
                end: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #35");
        let StrSearcherImpl::Byte(b) = &s.searcher else {
            unreachable!()
        };
        kani::assume(utf8_at(s.haystack.as_bytes(), 0));
        kani::cover(true, "assume #36");
        kani::assume(utf8_at(s.haystack.as_bytes(), b.position));
        kani::cover(true, "assume #37");
        let step = s.next();
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if a > 4096 && b > a),
            "distant byte rejection",
        );
        kani::cover(matches!(step, SearchStep::Match(_, _)), "byte match");
        kani::cover(matches!(step, SearchStep::Done), "exhaustion");
    }

    #[kani::proof_for_contract(<StrSearcher as ReverseSearcher>::next_back)]
    #[kani::stub_verified(str::floor_char_boundary)]
    #[kani::stub(TwoWaySearcher::next_back, reject_two_way_in_byte_proof)]
    pub fn harness_str_searcher_byte_next_back() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #38");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let StrSearcherImpl::Byte(b) = &s.searcher else {
            unreachable!()
        };
        kani::assume(utf8_at(s.haystack.as_bytes(), 0));
        kani::cover(true, "assume #39");
        if b.end > 0 {
            kani::assume(utf8_at(s.haystack.as_bytes(), b.end - 1));
            kani::cover(true, "assume #40");
        }
        let step = s.next_back();
        check_step(s.haystack, step);
        assert!(invariant(&s));
        kani::cover(true, "assert #21");
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if a > 4096 && b > a),
            "distant byte rejection",
        );
        kani::cover(matches!(step, SearchStep::Match(_, _)), "byte match");
        kani::cover(matches!(step, SearchStep::Done), "exhaustion");
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_byte_next_back",
        );
    }

    // See the forward extra-UB harness: combine this real-call audit with the
    // full reverse contract/frame proof above.
    #[kani::proof]
    #[kani::stub_verified(str::floor_char_boundary)]
    #[kani::stub(TwoWaySearcher::next_back, reject_two_way_in_byte_proof)]
    pub fn harness_str_searcher_byte_next_back_extra_ub() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #41");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = StrSearcher {
            haystack: any_str(),
            needle,
            searcher: StrSearcherImpl::Byte(ByteNeedle {
                b: byte,
                position: kani::any(),
                end: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #42");
        let StrSearcherImpl::Byte(b) = &s.searcher else {
            unreachable!()
        };
        kani::assume(utf8_at(s.haystack.as_bytes(), 0));
        kani::cover(true, "assume #43");
        if b.end > 0 {
            kani::assume(utf8_at(s.haystack.as_bytes(), b.end - 1));
            kani::cover(true, "assume #44");
        }
        let step = s.next_back();
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if a > 4096 && b > a),
            "distant byte rejection",
        );
        kani::cover(matches!(step, SearchStep::Match(_, _)), "byte match");
        kani::cover(matches!(step, SearchStep::Done), "exhaustion");
    }

    fn byte_filter_state(s: &StrSearcher<'_, '_>) -> bool {
        let StrSearcherImpl::Byte(b) = &s.searcher else {
            return false;
        };
        s.needle.len() == 1
            && s.needle.as_bytes()[0] == b.b
            && b.b < 128
            && b.position <= s.haystack.len()
            && b.end <= s.haystack.len()
            && s.haystack.is_char_boundary(b.position)
            && s.haystack.is_char_boundary(b.end)
    }

    #[kani::requires(byte_filter_state(s))]
    #[kani::ensures(|step| byte_filter_state(s) && step_ok(s.haystack, *step))]
    #[kani::modifies(front_cursor(s))]
    fn verified_byte_filter_next(s: &mut StrSearcher<'_, '_>) -> SearchStep {
        s.next()
    }

    #[kani::requires(byte_filter_state(s))]
    #[kani::ensures(|step| byte_filter_state(s) && step_ok(s.haystack, *step))]
    #[kani::modifies(back_cursor(s))]
    fn verified_byte_filter_next_back(s: &mut StrSearcher<'_, '_>) -> SearchStep {
        s.next_back()
    }

    #[kani::proof_for_contract(verified_byte_filter_next)]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    pub fn harness_byte_filter_next_contract() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #45");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let step = verified_byte_filter_next(&mut s);
        kani::cover(
            matches!(step, SearchStep::Match(_, _)),
            "Byte filter match step",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(_, _)),
            "Byte filter reject step",
        );
        kani::cover(
            matches!(step, SearchStep::Done),
            "Byte filter exhausted step",
        );
        kani::cover(
            true,
            "contract proof returns: harness_byte_filter_next_contract",
        );
    }

    #[kani::proof_for_contract(verified_byte_filter_next_back)]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    pub fn harness_byte_filter_next_back_contract() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #46");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let step = verified_byte_filter_next_back(&mut s);
        kani::cover(
            matches!(step, SearchStep::Match(_, _)),
            "Byte filter reverse match step",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(_, _)),
            "Byte filter reverse reject step",
        );
        kani::cover(
            matches!(step, SearchStep::Done),
            "Byte filter reverse exhausted step",
        );
        kani::cover(
            true,
            "contract proof returns: harness_byte_filter_next_back_contract",
        );
    }

    struct ByteFilterModel;
    impl ByteFilterModel {
        #[kani::requires(byte_filter_state(s))]
        #[kani::ensures(|step| byte_filter_state(s) && step_ok(s.haystack, *step))]
        #[kani::modifies(front_cursor(s))]
        fn next<'a: 'a, 'b: 'b>(s: &mut StrSearcher<'a, 'b>) -> SearchStep {
            verified_byte_filter_next(s)
        }

        #[kani::requires(byte_filter_state(s))]
        #[kani::ensures(|step| byte_filter_state(s) && step_ok(s.haystack, *step))]
        #[kani::modifies(back_cursor(s))]
        fn next_back<'a: 'a, 'b: 'b>(s: &mut StrSearcher<'a, 'b>) -> SearchStep {
            verified_byte_filter_next_back(s)
        }
    }

    #[kani::proof_for_contract(ByteFilterModel::next)]
    #[kani::stub_verified(verified_byte_filter_next)]
    pub fn harness_byte_filter_model_next_contract() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #47");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let result = ByteFilterModel::next(&mut s);
        kani::cover(
            matches!(result, SearchStep::Match(_, _)),
            "Byte adapter match",
        );
        kani::cover(
            matches!(result, SearchStep::Reject(_, _)),
            "Byte adapter reject",
        );
        kani::cover(matches!(result, SearchStep::Done), "Byte adapter done");
        kani::cover(
            true,
            "contract proof returns: harness_byte_filter_model_next_contract",
        );
    }

    #[kani::proof_for_contract(ByteFilterModel::next_back)]
    #[kani::stub_verified(verified_byte_filter_next_back)]
    pub fn harness_byte_filter_model_next_back_contract() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #48");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let result = ByteFilterModel::next_back(&mut s);
        kani::cover(
            matches!(result, SearchStep::Match(_, _)),
            "Byte reverse adapter match",
        );
        kani::cover(
            matches!(result, SearchStep::Reject(_, _)),
            "Byte reverse adapter reject",
        );
        kani::cover(
            matches!(result, SearchStep::Done),
            "Byte reverse adapter done",
        );
        kani::cover(
            true,
            "contract proof returns: harness_byte_filter_model_next_back_contract",
        );
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as Searcher>::next, ByteFilterModel::next)]
    #[kani::stub_verified(verified_byte_filter_next)]
    #[kani::stub(<StrSearcher as FilterLoopContract>::valid, byte_filter_loop_valid)]
    pub fn harness_str_searcher_byte_next_reject() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #49");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let result = s.next_reject();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #22");
        kani::cover(
            result.is_some_and(|(a, b)| a > 4096 && b > a),
            "distant byte rejection",
        );
        kani::cover(result.is_none(), "exhaustion");
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as ReverseSearcher>::next_back, ByteFilterModel::next_back)]
    #[kani::stub_verified(verified_byte_filter_next_back)]
    #[kani::stub(<StrSearcher as FilterLoopContract>::valid, byte_filter_loop_valid)]
    pub fn harness_str_searcher_byte_next_reject_back() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #50");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let result = s.next_reject_back();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #23");
        kani::cover(
            result.is_some_and(|(a, b)| a > 4096 && b > a),
            "distant byte rejection",
        );
        kani::cover(result.is_none(), "exhaustion");
    }

    /// Assumption 1: slice searching returns a matching byte or no match. Allowing
    /// any match (and even None when one exists) overapproximates memchr/memrchr
    /// for the safety properties; the string searcher itself is still executed.
    fn model_memchr(byte: u8, bytes: &[u8]) -> Option<usize> {
        if kani::any() {
            None
        } else {
            let i: usize = kani::any();
            kani::assume(i < bytes.len() && bytes[i] == byte);
            kani::cover(true, "assume #51");
            Some(i)
        }
    }

    fn check_match(haystack: &str, result: Option<(usize, usize)>) {
        if let Some((a, b)) = result {
            // This assumption holds at every byte of every valid haystack. It
            // supplies the byte after an ASCII match, without assuming that the
            // algorithm's endpoints themselves are character boundaries.
            kani::assume(utf8_at(haystack.as_bytes(), a));
            kani::cover(true, "assume #52");
            check_step(haystack, SearchStep::Match(a, b));
            kani::cover(a > 4096, "a distant match");
        }
        kani::cover(result.is_none(), "exhaustion");
    }

    // These harnesses start with the Byte variant, whose fields never change
    // the enum discriminant. Keep the real public dispatch and Byte body, but
    // avoid instrumenting nested TwoWay loops on an unreachable branch.
    // An unexpected call fails the proof instead of assuming the path away.
    fn reject_two_way_in_byte_proof<S: TwoWayStrategy>(
        _searcher: &mut TwoWaySearcher,
        _haystack: &[u8],
        _needle: &[u8],
        _long_period: bool,
    ) -> S::Output {
        panic!("entered TwoWay from a Byte-only proof")
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as Searcher>::next, ByteFilterModel::next)]
    #[kani::stub_verified(verified_byte_filter_next)]
    #[kani::stub(TwoWaySearcher::next, reject_two_way_in_byte_proof)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    pub fn harness_str_searcher_byte_next_match() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #53");
        let bytes = [byte];
        // SAFETY: the byte is ASCII.
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let result = s.next_match();
        check_match(s.haystack, result);
        assert!(invariant(&s));
        kani::cover(true, "assert #24");
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as ReverseSearcher>::next_back, ByteFilterModel::next_back)]
    #[kani::stub_verified(verified_byte_filter_next_back)]
    #[kani::stub(TwoWaySearcher::next_back, reject_two_way_in_byte_proof)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memchr)]
    pub fn harness_str_searcher_byte_next_match_back() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #54");
        let bytes = [byte];
        // SAFETY: the byte is ASCII.
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = any_byte(needle);
        let result = s.next_match_back();
        check_match(s.haystack, result);
        assert!(invariant(&s));
        kani::cover(true, "assert #25");
    }

    // The preceding matching harnesses prove C and both returned endpoints.
    // These complementary proofs check UB in the same real calls, avoiding a
    // second evaluation of the already-proved postconditions under UB tracking.
    #[kani::proof]
    #[kani::stub(<StrSearcher as Searcher>::next, ByteFilterModel::next)]
    #[kani::stub_verified(verified_byte_filter_next)]
    #[kani::stub(TwoWaySearcher::next, reject_two_way_in_byte_proof)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    pub fn harness_str_searcher_byte_next_match_extra_ub() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #55");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = StrSearcher {
            haystack: any_str(),
            needle,
            searcher: StrSearcherImpl::Byte(ByteNeedle {
                b: byte,
                position: kani::any(),
                end: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #56");
        let result = s.next_match();
        kani::cover(
            matches!(result, Some((a, b)) if a > 4096 && b > a),
            "distant byte match",
        );
        kani::cover(result.is_none(), "byte match exhaustion");
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as ReverseSearcher>::next_back, ByteFilterModel::next_back)]
    #[kani::stub_verified(verified_byte_filter_next_back)]
    #[kani::stub(TwoWaySearcher::next_back, reject_two_way_in_byte_proof)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memchr)]
    pub fn harness_str_searcher_byte_next_match_back_extra_ub() {
        let byte: u8 = kani::any();
        kani::assume(byte < 128);
        kani::cover(true, "assume #57");
        let bytes = [byte];
        let needle = unsafe { crate::str::from_utf8_unchecked(&bytes) };
        let mut s = StrSearcher {
            haystack: any_str(),
            needle,
            searcher: StrSearcherImpl::Byte(ByteNeedle {
                b: byte,
                position: kani::any(),
                end: kani::any(),
            }),
        };
        kani::assume(invariant(&s));
        kani::cover(true, "assume #58");
        let result = s.next_match_back();
        kani::cover(
            matches!(result, Some((a, b)) if a > 4096 && b > a),
            "distant byte match",
        );
        kani::cover(result.is_none(), "byte match exhaustion");
    }

    // A read-only ghost observation. The production algorithm neither reads
    // nor writes it; only the verification predicate selects this byte.
    static mut SUFFIX_OBSERVATION: usize = 0;

    fn point_suffix_loop_state(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        let point = unsafe { SUFFIX_OBSERVATION };
        if n > MAX_ALLOCATION_BYTES
            || left >= right
            || right > n
            || period == 0
            || period > right - left
            || offset >= period
            || offset > n - right
            || point >= n
        {
            return false;
        }
        let ptr = arr as *const [u8] as *const u8;
        macro_rules! byte {
            ($i:expr) => {
                unsafe { *crate::intrinsics::arith_offset(ptr, $i as isize) }
            };
        }
        let periodic = point < left + period
            || point >= right + offset
            || byte!(point) == byte!(point - period);
        if point < period {
            return periodic;
        }
        let predecessor = point - period;
        // The block and comparison-prefix facts are observed at point-period.
        // When the right edge advances, the latter becomes the former.
        periodic
            && (predecessor < right - period
                || predecessor >= right
                || byte!(predecessor) == byte!(predecessor - (right - left - period)))
            && (predecessor < right
                || predecessor >= right + offset
                || byte!(predecessor) == byte!(predecessor - (right - left)))
    }

    fn suffix_result_at(arr: &[u8], result: (usize, usize), point: usize) -> bool {
        let (left, period) = result;
        left < arr.len()
            && period > 0
            && period <= arr.len() - left
            && (point < left + period || point >= arr.len() || arr[point] == arr[point - period])
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES
        && point < arr.len() && unsafe { SUFFIX_OBSERVATION == point })]
    #[kani::ensures(|result| suffix_result_at(arr, *result, point))]
    #[kani::modifies()]
    fn maximal_suffix_at(arr: &[u8], order: bool, point: usize) -> (usize, usize) {
        TwoWaySearcher::maximal_suffix(arr, order)
    }

    #[kani::proof_for_contract(maximal_suffix_at)]
    #[kani::stub(suffix_loop_state, point_suffix_loop_state)]
    pub fn harness_maximal_suffix_period_at() {
        let arr = any_nonempty_bytes();
        let point: usize = kani::any();
        kani::assume(point < arr.len());
        kani::cover(true, "assume #59");
        unsafe {
            SUFFIX_OBSERVATION = point;
        }
        let order: bool = kani::any();
        let (critical, period) = maximal_suffix_at(arr, order, point);
        kani::cover(
            point > 4096 && point >= critical + period,
            "period relation at an arbitrary distant byte in the repeated suffix",
        );
        kani::cover(
            true,
            "contract proof returns: harness_maximal_suffix_period_at",
        );
    }

    #[kani::requires(arr.len() <= MAX_ALLOCATION_BYTES
        && suffix_result(arr, (left, period))
        && word_prefix_equal(arr, 0, period, left))]
    #[kani::ensures(|_| range_agreement(arr, period, arr.len(), period))]
    #[kani::modifies()]
    fn global_period_from_suffix(arr: &[u8], left: usize, period: usize) {}

    fn suffix_result_at_global_observer(arr: &[u8], result: (usize, usize)) -> bool {
        let n = arr.len();
        let (left, period) = result;
        if n > MAX_ALLOCATION_BYTES || left >= n || period == 0 || period > n - left {
            return false;
        }
        let i = unsafe { WORD_EQUALITY_OBSERVATION };
        i < left + period || i >= n || arr[i] == arr[i - period]
    }

    fn prefix_at_second_absolute_observer(arr: &[u8], a: usize, b: usize, count: usize) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES || a > n || b > n || count > n - a || count > n - b {
            return false;
        }
        let i = unsafe { WORD_EQUALITY_OBSERVATION };
        i < b || i >= b + count || arr[a + (i - b)] == arr[i]
    }

    #[kani::proof_for_contract(global_period_from_suffix)]
    #[kani::stub(suffix_result, suffix_result_at_global_observer)]
    #[kani::stub(word_prefix_equal, prefix_at_second_absolute_observer)]
    #[kani::stub(range_agreement, word_range_equal_at_observer)]
    pub fn harness_global_period_from_suffix() {
        let arr = any_nonempty_bytes();
        unsafe {
            WORD_EQUALITY_OBSERVATION = kani::any();
        }
        global_period_from_suffix(arr, kani::any(), kani::any());
        kani::cover(
            unsafe { WORD_EQUALITY_OBSERVATION } > 4096
                && unsafe { WORD_EQUALITY_OBSERVATION } < arr.len(),
            "global period from suffix and prefix at an arbitrary distant index",
        );
        kani::cover(
            true,
            "contract proof returns: harness_global_period_from_suffix",
        );
    }

    // One selected preprocessing result. Models below keep its semantic
    // predicates opaque only after their exact arguments are checked.
    static mut SHORT_CERTIFICATE: (*const u8, usize, usize, usize) = (crate::ptr::null(), 0, 0, 1);

    fn short_certificate_suffix(arr: &[u8], result: (usize, usize)) -> bool {
        let saved = unsafe { SHORT_CERTIFICATE };
        assert!(
            arr.as_ptr() == saved.0
                && arr.len() == saved.1
                && result.0 == saved.2
                && result.1 == saved.3
        );
        kani::cover(true, "assert #26");
        result.0 < arr.len() && result.1 > 0 && result.1 <= arr.len() - result.0
    }

    fn short_certificate_prefix(arr: &[u8], a: usize, b: usize, count: usize) -> bool {
        let saved = unsafe { SHORT_CERTIFICATE };
        assert!(
            arr.as_ptr() == saved.0
                && arr.len() == saved.1
                && a == 0
                && b == saved.3
                && count == saved.2
        );
        kani::cover(true, "assert #27");
        b <= arr.len() && count <= arr.len() - b
    }

    fn short_certificate_period(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let saved = unsafe { SHORT_CERTIFICATE };
        assert!(
            arr.as_ptr() == saved.0
                && arr.len() == saved.1
                && begin == saved.3
                && end == arr.len()
                && delta == saved.3
        );
        kani::cover(true, "assert #28");
        0 < begin && begin <= end
    }

    #[kani::requires(arr.len() <= MAX_ALLOCATION_BYTES
        && suffix_result(arr, (left, period))
        && word_root_dominance(arr, left, period, order)
        && word_earlier_dominance(arr, left, order)
        && word_prefix_equal(arr, 0, period, left))]
    #[kani::ensures(|_| left < period && range_agreement(arr, period, arr.len(), period))]
    #[kani::modifies()]
    fn certify_short_period(arr: &[u8], left: usize, period: usize, order: bool) {
        global_period_from_suffix(arr, left, period);
        lexical_period_bounds(arr, left, period, period, order);
    }

    #[kani::proof_for_contract(certify_short_period)]
    #[kani::stub_verified(global_period_from_suffix)]
    #[kani::stub_verified(lexical_period_bounds)]
    #[kani::stub(suffix_result, short_certificate_suffix)]
    #[kani::stub(word_prefix_equal, short_certificate_prefix)]
    #[kani::stub(word_root_dominance, root_dominance_shape)]
    #[kani::stub(word_earlier_dominance, earlier_dominance_shape)]
    #[kani::stub(range_agreement, short_certificate_period)]
    pub fn harness_certify_short_period() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let period = kani::any();
        let order = kani::any();
        unsafe {
            SHORT_CERTIFICATE = (arr.as_ptr(), arr.len(), left, period);
            ROOT_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, period, order);
            EARLIER_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, order);
        }
        certify_short_period(arr, left, period, order);
        kani::cover(
            arr.len() > 4096 && left > 0,
            "positive critical point below a symbolic global short period",
        );
        kani::cover(true, "contract proof returns: harness_certify_short_period");
    }

    // A trusted slice equality may be observed at any chosen element. The
    // false result deliberately remains unconstrained. Used only in the
    // constructor's prefix-equality test, with T = U = u8.
    static mut PREFIX_OBSERVATION: usize = 0;

    fn observed_slice_equality<T: PartialEq<U>, U>(left: &[T], right: &[U]) -> bool {
        let equal: bool = kani::any();
        if equal {
            kani::assume(left.len() == right.len());
            kani::cover(true, "assume #60");
            let point = unsafe { PREFIX_OBSERVATION };
            if point < left.len() {
                kani::assume(left[point] == right[point]);
                kani::cover(true, "assume #61");
            }
        }
        equal
    }

    // Compose the independently proved suffix-period observation with the
    // real constructor selection and prefix test. For every arbitrary byte
    // in the Short case this proves the whole needle's period relation.
    // It proves neither lexical bounds nor the complete constructor C yet.
    #[kani::proof]
    #[kani::stub_verified(maximal_suffix_at)]
    #[kani::stub(<[u8] as crate::cmp::PartialEq<[u8]>>::eq, observed_slice_equality)]
    pub fn harness_short_constructor_global_period_at() {
        let n = any_nonempty_str().as_bytes();
        kani::assume(n.len() >= 2);
        kani::cover(true, "assume #62");
        let point: usize = kani::any();
        kani::assume(point < n.len());
        kani::cover(true, "assume #63");
        unsafe {
            SUFFIX_OBSERVATION = point;
        }
        let first = maximal_suffix_at(n, false, point);
        let second = maximal_suffix_at(n, true, point);
        let (critical, period) = if first.0 > second.0 { first } else { second };
        if point < period {
            return;
        }
        unsafe {
            PREFIX_OBSERVATION = point - period;
        }
        if n[..critical] == n[period..period + critical] {
            assert!(n[point] == n[point - period]);
            kani::cover(true, "assert #29");
            kani::cover(
                point > 4096,
                "global Short period at an arbitrary distant byte",
            );
            kani::cover(
                critical > 0 && point - period < critical,
                "period relation supplied by the constructor prefix test",
            );
        }
    }

    fn suffix_byte_preferred(a: u8, b: u8, reverse: bool) -> bool {
        if reverse { a < b } else { a > b }
    }

    // Observe the predecessor directly. Every P, B and S byte relation is
    // now covered by an arbitrary j < len, including the end of the array.
    // This avoids modular arithmetic and does not require the observation
    // point j + period to remain fixed when a new root is installed.
    fn predecessor_suffix_loop_state(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        let j = unsafe { SUFFIX_OBSERVATION };
        if n > MAX_ALLOCATION_BYTES
            || left >= right
            || right > n
            || period == 0
            || period > right - left
            || offset >= period
            || offset > n - right
            || j >= n
        {
            return false;
        }
        let point = j + period;
        let ptr = arr as *const [u8] as *const u8;
        macro_rules! byte {
            ($i:expr) => {
                unsafe { *crate::intrinsics::arith_offset(ptr, $i as isize) }
            };
        }
        (j < left || point >= right + offset || byte!(point) == byte!(j))
            && (j < right - period || j >= right || byte!(j) == byte!(j - (right - left - period)))
            && (j < right || j >= right + offset || byte!(j) == byte!(j - (right - left)))
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES
        && point < arr.len() && unsafe { SUFFIX_OBSERVATION == point })]
    #[kani::ensures(|result| result.0 < arr.len()
        && result.1 > 0 && result.1 <= arr.len() - result.0
        && (point < result.0 || point >= arr.len() - result.1
            || arr[point + result.1] == arr[point]))]
    #[kani::modifies()]
    fn maximal_suffix_predecessor_at(arr: &[u8], order: bool, point: usize) -> (usize, usize) {
        TwoWaySearcher::maximal_suffix(arr, order)
    }

    #[kani::proof_for_contract(maximal_suffix_predecessor_at)]
    #[kani::stub(suffix_loop_state, predecessor_suffix_loop_state)]
    pub fn harness_maximal_suffix_predecessor_facts() {
        let arr = any_nonempty_bytes();
        let point: usize = kani::any();
        kani::assume(point < arr.len());
        kani::cover(true, "assume #64");
        unsafe {
            SUFFIX_OBSERVATION = point;
        }
        let (critical, period) = maximal_suffix_predecessor_at(arr, kani::any(), point);
        kani::cover(
            point > 4096 && point >= critical && point < arr.len() - period,
            "all three suffix relations at an arbitrary distant predecessor",
        );
        kani::cover(
            true,
            "contract proof returns: harness_maximal_suffix_predecessor_facts",
        );
    }

    // P/B/S observed on the reversed byte word. The production reverse
    // algorithm still reads the original slice through its original indices.
    fn reverse_predecessor_suffix_loop_state(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        let j = unsafe { SUFFIX_OBSERVATION };
        if n > MAX_ALLOCATION_BYTES
            || known_period == 0
            || known_period > n
            || left >= right
            || right > n
            || period == 0
            || period > right - left
            || offset >= period
            || offset > n - right
            || j >= n
        {
            return false;
        }
        let point = j + period;
        let ptr = arr as *const [u8] as *const u8;
        macro_rules! byte {
            ($i:expr) => {
                unsafe { *crate::intrinsics::arith_offset(ptr, (n - 1 - $i) as isize) }
            };
        }
        (j < left || point >= right + offset || byte!(point) == byte!(j))
            && (j < right - period || j >= right || byte!(j) == byte!(j - (right - left - period)))
            && (j < right || j >= right + offset || byte!(j) == byte!(j - (right - left)))
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES
        && point < arr.len() && unsafe { SUFFIX_OBSERVATION == point })]
    #[kani::ensures(|result| *result < arr.len())]
    #[kani::modifies()]
    fn reverse_maximal_suffix_predecessor_at(arr: &[u8], order: bool, point: usize) -> usize {
        TwoWaySearcher::reverse_maximal_suffix(arr, arr.len(), order)
    }

    #[kani::proof_for_contract(reverse_maximal_suffix_predecessor_at)]
    #[kani::stub(reverse_suffix_loop_state, reverse_predecessor_suffix_loop_state)]
    pub fn harness_reverse_maximal_suffix_predecessor_facts() {
        let arr = any_nonempty_bytes();
        let point: usize = kani::any();
        kani::assume(point < arr.len());
        kani::cover(true, "assume #65");
        unsafe {
            SUFFIX_OBSERVATION = point;
        }
        let _ = reverse_maximal_suffix_predecessor_at(arr, kani::any(), point);
        kani::cover(
            point > 4096,
            "reversed P/B/S at an arbitrary distant predecessor",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reverse_maximal_suffix_predecessor_facts",
        );
    }

    #[kani::proof]
    #[kani::stub_verified(read_range_agreement)]
    #[kani::stub(range_agreement, word_range_equal_at_observer)]
    pub fn harness_reversal_preserves_global_period() {
        let arr = any_nonempty_bytes();
        let n = arr.len();
        let period: usize = kani::any();
        let point: usize = kani::any();
        kani::assume(0 < period && period <= point && point < n);
        kani::cover(true, "assume #66");
        let reflected = n - 1 - point;
        let index = reflected + period;
        assert!(period <= index && index < n);
        kani::cover(true, "assert #30");
        unsafe {
            WORD_EQUALITY_OBSERVATION = index;
        }
        kani::assume(range_agreement(arr, period, n, period));
        kani::cover(true, "assume #67");
        read_range_agreement(arr, period, n, period, index);
        assert!(index == n - 1 - (point - period));
        kani::cover(true, "assert #31");
        assert!(n - 1 - reflected == point);
        kani::cover(true, "assert #32");
        assert!(arr[n - 1 - point] == arr[n - 1 - (point - period)]);
        kani::cover(true, "assert #33");
        kani::cover(
            point > 4096,
            "global period reflected at a distant arbitrary point",
        );
    }

    // The logical word R[i] = arr[len-1-i] is a byte word of the same length.
    // The forward word lemmas use no UTF-8 assumption, so they apply to R.
    // These pure expressions make that interpretation explicit.
    macro_rules! reflected_byte {
        ($ptr:ident, $n:ident, $at:expr) => {
            unsafe {
                *crate::intrinsics::arith_offset(
                    $ptr,
                    crate::intrinsics::wrapping_sub(crate::intrinsics::wrapping_sub($n, 1), $at)
                        as isize,
                )
            }
        };
    }
    macro_rules! reflected_witness {
        ($ptr:ident, $n:ident, $a:expr, $b:expr, $w:expr, $order:expr) => {
            (((!$order)
                & (reflected_byte!($ptr, $n, crate::intrinsics::wrapping_add($a, $w))
                    > reflected_byte!($ptr, $n, crate::intrinsics::wrapping_add($b, $w))))
                | ($order
                    & (reflected_byte!($ptr, $n, crate::intrinsics::wrapping_add($a, $w))
                        < reflected_byte!($ptr, $n, crate::intrinsics::wrapping_add($b, $w)))))
                & kani::internal::kani_forall(0, $w, move |i: usize| {
                    reflected_byte!($ptr, $n, crate::intrinsics::wrapping_add($a, i))
                        == reflected_byte!($ptr, $n, crate::intrinsics::wrapping_add($b, i))
                })
        };
    }
    macro_rules! reverse_root_body {
        ($arr:ident, $left:ident, $period:ident, $order:ident) => {{
            let n = crate::intrinsics::ptr_metadata($arr as *const [u8]);
            if n > MAX_ALLOCATION_BYTES || $left >= n || $period == 0 || $period > n - $left {
                return false;
            }
            let ptr = $arr as *const [u8] as *const u8;
            kani::internal::kani_forall(1, $period, move |shift: usize| {
                kani::internal::kani_exists(
                    0,
                    crate::intrinsics::wrapping_sub($period, shift),
                    move |w: usize| {
                        reflected_witness!(
                            ptr,
                            n,
                            $left,
                            crate::intrinsics::wrapping_add($left, shift),
                            w,
                            $order
                        )
                    },
                )
            })
        }};
    }
    macro_rules! reverse_earlier_body {
        ($arr:ident, $left:ident, $order:ident) => {{
            let n = crate::intrinsics::ptr_metadata($arr as *const [u8]);
            if n > MAX_ALLOCATION_BYTES || $left >= n {
                return false;
            }
            let ptr = $arr as *const [u8] as *const u8;
            let bound = n - $left;
            kani::internal::kani_forall(0, $left, move |candidate: usize| {
                kani::internal::kani_exists(0, bound, move |w: usize| {
                    reflected_witness!(ptr, n, $left, candidate, w, $order)
                })
            })
        }};
    }
    fn reverse_loop_root(arr: &[u8], left: usize, period: usize, order: bool) -> bool {
        reverse_root_body!(arr, left, period, order)
    }
    fn reverse_word_earlier(arr: &[u8], left: usize, order: bool) -> bool {
        reverse_earlier_body!(arr, left, order)
    }
    fn reverse_loop_earlier(arr: &[u8], left: usize, order: bool) -> bool {
        reverse_earlier_body!(arr, left, order)
    }

    fn reverse_loop_facts(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES
            || left >= right
            || right > n
            || period == 0
            || period > right - left
            || offset >= period
            || offset > n - right
        {
            return false;
        }
        let ptr = arr as *const [u8] as *const u8;
        kani::internal::kani_forall(left + period, right + offset, move |j: usize| {
            reflected_byte!(ptr, n, j)
                == reflected_byte!(ptr, n, crate::intrinsics::wrapping_sub(j, period))
        }) & kani::internal::kani_forall(right - period, right, move |j: usize| {
            reflected_byte!(ptr, n, j)
                == reflected_byte!(
                    ptr,
                    n,
                    crate::intrinsics::wrapping_sub(
                        j,
                        crate::intrinsics::wrapping_sub(
                            crate::intrinsics::wrapping_sub(right, left),
                            period
                        )
                    )
                )
        }) & kani::internal::kani_forall(right, right + offset, move |j: usize| {
            reflected_byte!(ptr, n, j)
                == reflected_byte!(
                    ptr,
                    n,
                    crate::intrinsics::wrapping_sub(
                        j,
                        crate::intrinsics::wrapping_sub(right, left)
                    )
                )
        })
    }

    #[kani::proof]
    pub fn harness_reverse_byte_view_correspondence() {
        let arr = any_nonempty_bytes();
        let (a, b, w): (usize, usize, usize) = (kani::any(), kani::any(), kani::any());
        let n = arr.len();
        kani::assume(a < n && b < n && w < n - a && w < n - b);
        kani::cover(true, "after harness_reverse_byte_view_correspondence input bounds");
        let ptr = arr.as_ptr();
        let x = reflected_byte!(ptr, n, a + w);
        let y = reflected_byte!(ptr, n, b + w);
        assert!(x == arr[n - 1 - (a + w)] && y == arr[n - 1 - (b + w)]);
        kani::cover(true, "reverse byte view agrees at both witness operands");
        assert!(n - 1 - (n - 1 - (a + w)) == a + w);
        kani::cover(true, "reverse byte view is an involution at an arbitrary index");
        assert!((x < y) == (arr[n - 1 - (a + w)] < arr[n - 1 - (b + w)]));
        kani::cover(true, "spatial reversal does not reverse the byte order relation");
        kani::cover(n > 4096 && w > 4096, "reverse byte view at symbolic length and prefix offset");
    }

    #[kani::proof]
    #[kani::solver(z3)]
    pub fn harness_reverse_transfer_full_premise_reachable() {
        let arr = any_nonempty_bytes();
        kani::assume(arr.len() >= 2);
        kani::cover(true, "after harness_reverse_transfer_full_premise_reachable length premise");
        kani::assume(arr[arr.len() - 1] > arr[arr.len() - 2]);
        kani::cover(true, "after harness_reverse_transfer_full_premise_reachable byte premise");
        assert!(reverse_root_transfer_pre(arr, 0, 1, 0, 1, false));
        kani::cover(true, "full reverse root transfer premise is feasible");
        assert!(reverse_left_transfer_pre(arr, 0, 1, 0, 1, true));
        kani::cover(true, "full reverse left transfer premise is feasible");
        kani::cover(arr.len() > 4096, "full reverse transfer premises at symbolic length");
    }

    // Reversal is a bijection on arbitrary byte words of the same length.
    // The reverse P/L/D definitions below are the forward definitions on
    // R(a)[i] = a[n-1-i]. These are pure mathematical implications with empty
    // bodies, so changing the proof representation to R(a) commutes with the
    // body. The production reverse search still executes its original code.
    // Each own proof calls the checked forward theorem on that representation
    // and observes its same uniform witness at an arbitrary prefix position.
    static mut REVERSE_THEOREM_INPUT: (*const u8, usize, usize, usize, usize, usize, bool, bool) =
        (crate::ptr::null(), 0, 0, 0, 0, 0, false, false);
    static mut REVERSE_THEOREM_OUTPUT: (usize, usize) = (0, 0);
    static mut REVERSE_THEOREM_OBSERVATION: (usize, usize) = (0, 0);
    static mut REVERSE_THEOREM_WITNESS: usize = 0;

    fn prepare_reverse_theorem(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize,
        order: bool, reset: bool,
    ) {
        unsafe {
            REVERSE_THEOREM_INPUT =
                (arr.as_ptr(), arr.len(), left, right, offset, period, order, reset);
            REVERSE_THEOREM_OBSERVATION = (kani::any(), kani::any());
            ROOT_TRANSFER_SHIFT = REVERSE_THEOREM_OBSERVATION.0;
            LEFT_TRANSFER_CANDIDATE = REVERSE_THEOREM_OBSERVATION.0;
            WORD_WITNESS_PREFIX_OBSERVATION = REVERSE_THEOREM_OBSERVATION.1;
        }
    }

    fn reverse_theorem_observation(reset: bool) {
        let saved = unsafe { REVERSE_THEOREM_OBSERVATION };
        let selected = unsafe {
            if reset { LEFT_TRANSFER_CANDIDATE } else { ROOT_TRANSFER_SHIFT }
        };
        assert!(selected == saved.0 && unsafe { WORD_WITNESS_PREFIX_OBSERVATION } == saved.1);
        kani::cover(true, "reverse theorem preserves its uniform-witness observation");
    }

    fn reverse_theorem_input(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize,
        order: bool, reset: bool,
    ) -> bool {
        let saved = unsafe { REVERSE_THEOREM_INPUT };
        assert!(arr.as_ptr() == saved.0 && arr.len() == saved.1
            && left == saved.2 && right == saved.3 && offset == saved.4
            && period == saved.5 && order == saved.6 && reset == saved.7);
        kani::cover(true, "reverse theorem checks every input operand");
        reverse_theorem_observation(reset);
        root_transfer_premise_bounds(arr, left, right, offset, period, order)
    }

    fn reverse_root_input_model(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        reverse_theorem_input(arr, left, right, offset, period, order, false)
    }

    fn reverse_left_input_model(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        reverse_theorem_input(arr, left, right, offset, period, order, true)
    }

    fn reverse_theorem_output(
        arr: &[u8], left: usize, period: usize, order: bool, reset: bool,
    ) {
        let input = unsafe { REVERSE_THEOREM_INPUT };
        let output = unsafe { REVERSE_THEOREM_OUTPUT };
        assert!(arr.as_ptr() == input.0 && arr.len() == input.1
            && left == output.0 && period == output.1
            && order == input.6 && reset == input.7);
        kani::cover(true, "reverse theorem checks every output operand");
        reverse_theorem_observation(reset);
    }

    fn forward_root_post_in_reverse_proof(
        arr: &[u8], left: usize, period: usize, order: bool, shift: usize, witness: usize,
    ) -> bool {
        reverse_theorem_output(arr, left, period, order, false);
        assert!(shift == unsafe { REVERSE_THEOREM_OBSERVATION }.0);
        kani::cover(true, "reverse root theorem checks the selected shift");
        root_transfer_post_at_shift(arr, left, period, order, shift, witness)
    }

    fn reverse_root_post_at_forward_witness(
        arr: &[u8], left: usize, period: usize, order: bool,
    ) -> bool {
        forward_root_post_in_reverse_proof(arr, left, period, order,
            unsafe { ROOT_TRANSFER_SHIFT }, unsafe { REVERSE_THEOREM_WITNESS })
    }

    fn forward_left_post_in_reverse_proof(
        arr: &[u8], left: usize, order: bool, candidate: usize, witness: usize,
    ) -> bool {
        reverse_theorem_output(arr, left, 0, order, true);
        assert!(candidate == unsafe { REVERSE_THEOREM_OBSERVATION }.0);
        kani::cover(true, "reverse left theorem checks the selected candidate");
        left_transfer_post_at_candidate(arr, left, order, candidate, witness)
    }

    fn reverse_left_post_at_forward_witness(arr: &[u8], left: usize, order: bool) -> bool {
        forward_left_post_in_reverse_proof(arr, left, order,
            unsafe { LEFT_TRANSFER_CANDIDATE }, unsafe { REVERSE_THEOREM_WITNESS })
    }

    fn reverse_root_transfer_pre(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        reverse_loop_facts(arr, left, right, offset, period)
            && reverse_loop_root(arr, left, period, order)
            && right + offset < arr.len()
            && suffix_byte_preferred(arr[arr.len() - (1 + left + offset)],
                arr[arr.len() - (1 + right + offset)], order)
    }

    fn reverse_root_transfer_post(arr: &[u8], left: usize, period: usize, order: bool) -> bool {
        reverse_loop_root(arr, left, period, order)
    }

    #[kani::requires(reverse_root_transfer_pre(arr, left, right, offset, period, order))]
    #[kani::ensures(|_| reverse_root_transfer_post(arr, left, right + offset + 1 - left, order))]
    #[kani::modifies()]
    fn verified_reverse_root_transfer(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) {}

    #[kani::proof_for_contract(verified_reverse_root_transfer)]
    #[kani::stub_verified(verified_root_transfer)]
    #[kani::stub(root_transfer_pre, reverse_root_input_model)]
    #[kani::stub(reverse_root_transfer_pre, reverse_root_input_model)]
    #[kani::stub(root_transfer_post, forward_root_post_in_reverse_proof)]
    #[kani::stub(reverse_root_transfer_post, reverse_root_post_at_forward_witness)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    #[kani::stub(full_word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_reverse_root_transfer_from_forward() {
        // This symbolic byte word represents R(original), not a str.
        let arr = any_nonempty_bytes();
        let (left, right, offset, period, order) =
            (kani::any(), kani::any(), kani::any(), kani::any(), kani::any());
        prepare_reverse_theorem(arr, left, right, offset, period, order, false);
        kani::assume(root_transfer_premise_bounds(arr, left, right, offset, period, order));
        kani::cover(true, "after harness_reverse_root_transfer_from_forward input premise");
        unsafe { REVERSE_THEOREM_OUTPUT = (left, right + offset + 1 - left); }
        let witness = verified_root_transfer(arr, left, right, offset, period, order);
        unsafe { REVERSE_THEOREM_WITNESS = witness; }
        verified_reverse_root_transfer(arr, left, right, offset, period, order);
        kani::cover(arr.len() > 4096, "reverse root transfer retains symbolic byte lengths");
        kani::cover(true, "contract proof returns: harness_reverse_root_transfer_from_forward");
    }

    fn reverse_left_transfer_pre(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        reverse_loop_facts(arr, left, right, offset, period)
            && reverse_loop_root(arr, left, period, order)
            && reverse_loop_earlier(arr, left, order)
            && right + offset < arr.len()
            && suffix_byte_preferred(arr[arr.len() - (1 + right + offset)],
                arr[arr.len() - (1 + left + offset)], order)
    }

    fn reverse_left_transfer_post(arr: &[u8], left: usize, order: bool) -> bool {
        reverse_loop_earlier(arr, left, order)
    }

    #[kani::requires(reverse_left_transfer_pre(arr, left, right, offset, period, order))]
    #[kani::ensures(|_| reverse_left_transfer_post(arr, right, order))]
    #[kani::modifies()]
    fn verified_reverse_left_transfer(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) {}

    #[kani::proof_for_contract(verified_reverse_left_transfer)]
    #[kani::stub_verified(verified_left_transfer)]
    #[kani::stub(left_transfer_pre, reverse_left_input_model)]
    #[kani::stub(reverse_left_transfer_pre, reverse_left_input_model)]
    #[kani::stub(left_transfer_post, forward_left_post_in_reverse_proof)]
    #[kani::stub(reverse_left_transfer_post, reverse_left_post_at_forward_witness)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    #[kani::stub(full_word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_reverse_left_transfer_from_forward() {
        let arr = any_nonempty_bytes();
        let (left, right, offset, period, order) =
            (kani::any(), kani::any(), kani::any(), kani::any(), kani::any());
        prepare_reverse_theorem(arr, left, right, offset, period, order, true);
        kani::assume(root_transfer_premise_bounds(arr, left, right, offset, period, order));
        kani::cover(true, "after harness_reverse_left_transfer_from_forward input premise");
        unsafe { REVERSE_THEOREM_OUTPUT = (right, 0); }
        let witness = verified_left_transfer(arr, left, right, offset, period, order);
        unsafe { REVERSE_THEOREM_WITNESS = witness; }
        verified_reverse_left_transfer(arr, left, right, offset, period, order);
        kani::cover(arr.len() > 4096, "reverse left transfer retains symbolic byte lengths");
        kani::cover(true, "contract proof returns: harness_reverse_left_transfer_from_forward");
    }

    fn apply_reverse_root_extension(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        order: bool,
    ) {
        assert!(reverse_loop_facts(arr, left, right, offset, period));
        kani::cover(true, "assert #34");
        assert!(reverse_loop_root(arr, left, period, order));
        kani::cover(true, "assert #35");
        assert!(right + offset < arr.len());
        kani::cover(true, "assert #36");
        let a = arr[arr.len() - (1 + right + offset)];
        let b = arr[arr.len() - (1 + left + offset)];
        assert!((a < b && !order) || (a > b && order));
        kani::cover(true, "assert #37");
        verified_reverse_root_transfer(arr, left, right, offset, period, order);
    }

    fn apply_reverse_left_reset(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        order: bool,
    ) {
        assert!(reverse_loop_facts(arr, left, right, offset, period));
        kani::cover(true, "assert #38");
        assert!(reverse_loop_root(arr, left, period, order));
        kani::cover(true, "assert #39");
        assert!(reverse_loop_earlier(arr, left, order));
        kani::cover(true, "assert #40");
        assert!(right + offset < arr.len());
        kani::cover(true, "assert #41");
        let a = arr[arr.len() - (1 + right + offset)];
        let b = arr[arr.len() - (1 + left + offset)];
        assert!((a > b && !order) || (a < b && order));
        kani::cover(true, "assert #42");
        verified_reverse_left_transfer(arr, left, right, offset, period, order);
    }

    fn reverse_lexical_loop(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        order: bool,
        prove_d: bool,
    ) -> bool {
        let n = arr.len();
        if known_period == 0
            || known_period > n
            || !probe_suffix_shape(arr, left, right, offset, period)
        {
            return false;
        }
        if !reverse_loop_facts(arr, left, right, offset, period) {
            return false;
        }
        let root = reverse_loop_root(arr, left, period, order);
        let valid = if prove_d {
            root && reverse_loop_earlier(arr, left, order)
        } else {
            root
        };
        if valid && right + offset < n {
            let a = arr[n - (1 + right + offset)];
            let b = arr[n - (1 + left + offset)];
            if !prove_d && ((a < b && !order) || (a > b && order)) {
                apply_reverse_root_extension(arr, left, right, offset, period, order);
            }
            if prove_d && ((a > b && !order) || (a < b && order)) {
                apply_reverse_left_reset(arr, left, right, offset, period, order);
            }
        }
        valid
    }

    fn reverse_root_loop_false(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        reverse_lexical_loop(arr, known_period, left, right, offset, period, false, false)
    }

    fn reverse_root_loop_true(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        reverse_lexical_loop(arr, known_period, left, right, offset, period, true, false)
    }

    fn reverse_dominance_loop_false(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        reverse_lexical_loop(arr, known_period, left, right, offset, period, false, true)
    }

    fn reverse_dominance_loop_true(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        reverse_lexical_loop(arr, known_period, left, right, offset, period, true, true)
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES)]
    #[kani::ensures(|result| *result < arr.len())]
    #[kani::modifies()]
    fn reverse_suffix_root_baseline(arr: &[u8], order: bool) -> usize {
        TwoWaySearcher::reverse_maximal_suffix(arr, arr.len(), order)
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES)]
    #[kani::ensures(|result| *result < arr.len() && reverse_word_earlier(arr, *result, order))]
    #[kani::modifies()]
    fn reverse_suffix_dominance_baseline(arr: &[u8], order: bool) -> usize {
        TwoWaySearcher::reverse_maximal_suffix(arr, arr.len(), order)
    }

    #[kani::proof_for_contract(reverse_suffix_root_baseline)]
    #[kani::stub_verified(verified_reverse_root_transfer)]
    #[kani::stub(reverse_suffix_loop_state, reverse_root_loop_false)]
    #[kani::stub(reverse_loop_facts, probe_suffix_shape)]
    #[kani::stub(reverse_loop_root, root_exclusion_for_loop)]
    pub fn harness_reverse_maximal_suffix_root_probe_false() {
        let arr = any_nonempty_bytes();
        unsafe {
            ROOT_STATE_PROBE = (kani::any(), kani::any());
            EARLIER_STATE_PROBE = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), false);
        }
        let result = reverse_suffix_root_baseline(arr, false);
        kani::cover(
            arr.len() > 4096 && result > 0,
            "reverse root false traverses a symbolic-length byte word",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reverse_maximal_suffix_root_probe_false",
        );
    }

    #[kani::proof_for_contract(reverse_suffix_root_baseline)]
    #[kani::stub_verified(verified_reverse_root_transfer)]
    #[kani::stub(reverse_suffix_loop_state, reverse_root_loop_true)]
    #[kani::stub(reverse_loop_facts, probe_suffix_shape)]
    #[kani::stub(reverse_loop_root, root_exclusion_for_loop)]
    pub fn harness_reverse_maximal_suffix_root_probe_true() {
        let arr = any_nonempty_bytes();
        unsafe {
            ROOT_STATE_PROBE = (kani::any(), kani::any());
            EARLIER_STATE_PROBE = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), true);
        }
        let result = reverse_suffix_root_baseline(arr, true);
        kani::cover(
            arr.len() > 4096 && result > 0,
            "reverse root true traverses a symbolic-length byte word",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reverse_maximal_suffix_root_probe_true",
        );
    }

    #[kani::proof_for_contract(reverse_suffix_dominance_baseline)]
    #[kani::stub_verified(verified_reverse_left_transfer)]
    #[kani::stub(reverse_suffix_loop_state, reverse_dominance_loop_false)]
    #[kani::stub(reverse_loop_facts, probe_suffix_shape)]
    #[kani::stub(reverse_loop_root, root_shape_for_loop)]
    #[kani::stub(reverse_loop_earlier, earlier_exclusion_for_loop)]
    #[kani::stub(reverse_word_earlier, earlier_exclusion_predicate)]
    pub fn harness_reverse_maximal_suffix_dominance_probe_false() {
        let arr = any_nonempty_bytes();
        unsafe {
            ROOT_STATE_PROBE = (kani::any(), kani::any());
            EARLIER_STATE_PROBE = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), false);
        }
        let result = reverse_suffix_dominance_baseline(arr, false);
        kani::cover(
            arr.len() > 4096 && result > 0,
            "reverse dominance false traverses a symbolic-length byte word",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reverse_maximal_suffix_dominance_probe_false",
        );
    }

    #[kani::proof_for_contract(reverse_suffix_dominance_baseline)]
    #[kani::stub_verified(verified_reverse_left_transfer)]
    #[kani::stub(reverse_suffix_loop_state, reverse_dominance_loop_true)]
    #[kani::stub(reverse_loop_facts, probe_suffix_shape)]
    #[kani::stub(reverse_loop_root, root_shape_for_loop)]
    #[kani::stub(reverse_loop_earlier, earlier_exclusion_for_loop)]
    #[kani::stub(reverse_word_earlier, earlier_exclusion_predicate)]
    pub fn harness_reverse_maximal_suffix_dominance_probe_true() {
        let arr = any_nonempty_bytes();
        unsafe {
            ROOT_STATE_PROBE = (kani::any(), kani::any());
            EARLIER_STATE_PROBE = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), true);
        }
        let result = reverse_suffix_dominance_baseline(arr, true);
        kani::cover(
            arr.len() > 4096 && result > 0,
            "reverse dominance true traverses a symbolic-length byte word",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reverse_maximal_suffix_dominance_probe_true",
        );
    }

    // With known_period=len, an early break can only occur at the terminal
    // small-branch update. Therefore another positive known period never
    // causes additional body steps after that baseline execution ends.
    #[kani::proof]
    pub fn harness_reverse_full_period_break_is_terminal() {
        let n: usize = kani::any();
        let left: usize = kani::any();
        let right: usize = kani::any();
        let offset: usize = kani::any();
        let period: usize = kani::any();
        kani::assume(0 < n && n <= MAX_ALLOCATION_BYTES && left < right && right <= n);
        kani::cover(true, "assume #68");
        kani::assume(
            0 < period && period <= right - left && offset < period && offset <= n - right,
        );
        kani::cover(true, "assume #69");
        if right + offset < n {
            assert!(n > 1 && period < n);
            kani::cover(true, "assert #43");
            let next_right = right + offset + 1;
            let next_period = next_right - left;
            if next_period == n {
                assert!(left == 0 && next_right == n);
                kani::cover(true, "assert #44");
                assert!(next_right >= n);
                kani::cover(true, "assert #45");
            }
            kani::cover(
                n > 4096 && next_period == n,
                "full-period break is terminal at symbolic length",
            );
        }
    }

    // A period is preserved by reversing a finite word. The point proof uses
    // the original array: j maps to the original period comparison at n-1-j+k.
    fn reflected_global_period(arr: &[u8], k: usize) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES || k == 0 || k > n { return false; }
        let ptr = arr.as_ptr();
        kani::internal::kani_forall(k, n, move |j: usize| {
            reflected_byte!(ptr, n, j)
                == reflected_byte!(ptr, n, crate::intrinsics::wrapping_sub(j, k))
        })
    }

    #[kani::requires(0 < k && k <= arr.len() && arr.len() <= MAX_ALLOCATION_BYTES
        && range_agreement(arr, k, arr.len(), k))]
    #[kani::ensures(|_| reflected_global_period(arr, k))]
    #[kani::modifies()]
    fn verified_reflected_global_period(arr: &[u8], k: usize) {}

    static mut REFLECTED_PERIOD_OBSERVATION: usize = 0;

    fn reflection_range_at_observer(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES || delta > begin || begin > end || end > n {
            return false;
        }
        let j = unsafe { REFLECTED_PERIOD_OBSERVATION };
        if delta <= j && j < n {
            let i = n - 1 - j + delta;
            i < begin || i >= end || arr[i] == arr[i - delta]
        } else { true }
    }

    fn reflected_period_at_observer(arr: &[u8], k: usize) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES || k == 0 || k > n { return false; }
        let j = unsafe { REFLECTED_PERIOD_OBSERVATION };
        j < k || j >= n || arr[n - 1 - j] == arr[n - 1 - (j - k)]
    }

    #[kani::proof_for_contract(verified_reflected_global_period)]
    #[kani::stub(range_agreement, reflection_range_at_observer)]
    #[kani::stub(reflected_global_period, reflected_period_at_observer)]
    pub fn harness_reflected_global_period() {
        let arr = any_nonempty_bytes();
        unsafe { REFLECTED_PERIOD_OBSERVATION = kani::any(); }
        let k = kani::any();
        verified_reflected_global_period(arr, k);
        kani::cover(arr.len() > 4096 && unsafe { REFLECTED_PERIOD_OBSERVATION } >= k
            && unsafe { REFLECTED_PERIOD_OBSERVATION } < arr.len(),
            "reflected period checks an interior byte at symbolic length");
        kani::cover(true, "contract proof returns: harness_reflected_global_period");
    }

    fn reverse_lexical_bounds_pre(arr: &[u8], left: usize, period: usize, k: usize, order: bool) -> bool {
        reverse_loop_root(arr, left, period, order)
            && reverse_loop_earlier(arr, left, order) && reflected_global_period(arr, k)
    }

    #[kani::requires(reverse_lexical_bounds_pre(arr, left, period, k, order))]
    #[kani::ensures(|_| left < k && period <= k)]
    #[kani::modifies()]
    fn verified_reverse_lexical_bounds(arr: &[u8], left: usize, period: usize, k: usize, order: bool) {}

    static mut REVERSE_BOUND_INPUT: (*const u8, usize, usize, usize, usize, bool) =
        (crate::ptr::null(), 0, 0, 0, 0, false);

    fn period_bound_range_shape(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let saved = unsafe { REVERSE_BOUND_INPUT };
        assert!(arr.as_ptr() == saved.0 && arr.len() == saved.1
            && begin == saved.4 && end == saved.1 && delta == saved.4);
        kani::cover(true, "period bound checks the unchanged global-period operands");
        0 < begin && begin <= end && end <= MAX_ALLOCATION_BYTES
    }

    fn reverse_bound_input_model(arr: &[u8], left: usize, period: usize, k: usize, order: bool) -> bool {
        let saved = unsafe { REVERSE_BOUND_INPUT };
        assert!(arr.as_ptr() == saved.0 && arr.len() == saved.1 && left == saved.2
            && period == saved.3 && k == saved.4 && order == saved.5);
        kani::cover(true, "reverse period bound checks every input operand");
        root_dominance_shape(arr, left, period, order)
            && earlier_dominance_shape(arr, left, order)
            && period_bound_range_shape(arr, k, arr.len(), k)
    }

    // R(a) is an arbitrary byte word. Its root and earlier predicates are
    // exactly reverse_loop_root/earlier on a, with identical numeric operands;
    // reflected_global_period(a,k) is its ordinary global-period predicate.
    // Both theorem bodies have an empty frame. The scalar conclusion needs
    // no representation change. Guard every shared premise operand.
    #[kani::proof_for_contract(verified_reverse_lexical_bounds)]
    #[kani::stub_verified(lexical_period_bounds)]
    #[kani::stub(reverse_lexical_bounds_pre, reverse_bound_input_model)]
    #[kani::stub(word_root_dominance, root_dominance_shape)]
    #[kani::stub(word_earlier_dominance, earlier_dominance_shape)]
    #[kani::stub(range_agreement, period_bound_range_shape)]
    pub fn harness_reverse_lexical_bounds_from_forward() {
        let arr = any_nonempty_bytes();
        let (left, period, k, order) = (kani::any(), kani::any(), kani::any(), kani::any());
        unsafe {
            REVERSE_BOUND_INPUT = (arr.as_ptr(), arr.len(), left, period, k, order);
            ROOT_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, period, order);
            EARLIER_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, order);
        }
        kani::assume(reverse_bound_input_model(arr, left, period, k, order));
        kani::cover(true, "after harness_reverse_lexical_bounds_from_forward input premise");
        lexical_period_bounds(arr, left, period, k, order);
        verified_reverse_lexical_bounds(arr, left, period, k, order);
        kani::cover(arr.len() > 4096, "reverse lexical period bounds retain symbolic lengths");
        kani::cover(true, "contract proof returns: harness_reverse_lexical_bounds_from_forward");
    }

    static mut REVERSE_KNOWN_PERIOD: usize = 0;

    fn known_period_range_shape(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let saved = unsafe { PREPROCESSING_INPUT };
        let k = unsafe { REVERSE_KNOWN_PERIOD };
        assert!(arr.as_ptr() == saved.0 && arr.len() == saved.1
            && begin == k && end == saved.1 && delta == k);
        kani::cover(true, "reverse loop retains its original global-period operand");
        0 < k && k <= arr.len() && arr.len() <= MAX_ALLOCATION_BYTES
    }

    fn known_reflected_period_shape(arr: &[u8], k: usize) -> bool {
        known_period_range_shape(arr, k, arr.len(), k)
    }



    fn earlier_shape_for_reverse_bound(arr: &[u8], left: usize, order: bool) -> bool {
        let saved = unsafe { PREPROCESSING_INPUT };
        assert!(arr.as_ptr() == saved.0 && arr.len() == saved.1 && order == saved.2);
        kani::cover(true, "reverse numeric proof retains the earlier-predicate operands");
        arr.len() <= MAX_ALLOCATION_BYTES && left < arr.len()
    }





    // The known-period execution is a prefix of the len-period execution:
    // the parameter is inspected only by the early-break test, after updates.
    // Thus its states have the independently proved P/L/D properties. Combined
    // with the reflected global period and lexical_period_bounds, these give
    // both the current and predicted successor inequalities below.
    fn bounded_reverse_loop(
        arr: &[u8], known_period: usize, left: usize, right: usize,
        offset: usize, period: usize, order: bool,
    ) -> bool {
        let n = arr.len();
        if known_period == 0 || known_period > n
            || !probe_suffix_shape(arr, left, right, offset, period)
            || left >= known_period || period > known_period
            || !range_agreement(arr, known_period, n, known_period)
            || !reverse_loop_facts(arr, left, right, offset, period)
            || !reverse_loop_root(arr, left, period, order)
            || !reverse_loop_earlier(arr, left, order)
        {
            return false;
        }
        verified_reflected_global_period(arr, known_period);
        if right + offset < n {
            let a = arr[n - (1 + right + offset)];
            let b = arr[n - (1 + left + offset)];
            if (a < b && !order) || (a > b && order) {
                verified_reverse_root_transfer(arr, left, right, offset, period, order);
                verified_reverse_lexical_bounds(
                    arr, left, right + offset + 1 - left, known_period, order);
            } else if a != b {
                verified_reverse_left_transfer(arr, left, right, offset, period, order);
                verified_reverse_lexical_bounds(arr, right, 1, known_period, order);
            }
        }
        true
    }

    fn bounded_reverse_loop_false(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        bounded_reverse_loop(arr, known_period, left, right, offset, period, false)
    }

    fn bounded_reverse_loop_true(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        bounded_reverse_loop(arr, known_period, left, right, offset, period, true)
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES
        && 0 < known_period && known_period <= arr.len()
        && range_agreement(arr, known_period, arr.len(), known_period))]
    #[kani::ensures(|result| *result < known_period)]
    #[kani::modifies()]
    fn reverse_suffix_period(arr: &[u8], known_period: usize, order: bool) -> usize {
        TwoWaySearcher::reverse_maximal_suffix(arr, known_period, order)
    }

    #[kani::proof_for_contract(reverse_suffix_period)]
    #[kani::stub_verified(verified_reverse_root_transfer)]
    #[kani::stub_verified(verified_reverse_left_transfer)]
    #[kani::stub_verified(verified_reflected_global_period)]
    #[kani::stub_verified(verified_reverse_lexical_bounds)]
    #[kani::stub(reverse_loop_facts, probe_suffix_shape)]
    #[kani::stub(reverse_loop_root, root_shape_for_loop)]
    #[kani::stub(reverse_loop_earlier, earlier_shape_for_reverse_bound)]
    #[kani::stub(reflected_global_period, known_reflected_period_shape)]
    #[kani::stub(range_agreement, known_period_range_shape)]
    #[kani::stub(reverse_suffix_loop_state, bounded_reverse_loop_false)]
    pub fn harness_reverse_suffix_period_false() {
        let arr = any_nonempty_bytes();
        let known_period = kani::any();
        unsafe {
            WORD_EQUALITY_OBSERVATION = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), false);
            REVERSE_KNOWN_PERIOD = known_period;
        }
        let left = reverse_suffix_period(arr, known_period, false);
        kani::cover(
            arr.len() > 4096 && known_period < arr.len(),
            "shorter global period bounds real reverse preprocessing",
        );
        kani::cover(
            left > 0,
            "nonzero reverse critical point remains below its period",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reverse_suffix_period_false",
        );
    }

    #[kani::proof_for_contract(reverse_suffix_period)]
    #[kani::stub_verified(verified_reverse_root_transfer)]
    #[kani::stub_verified(verified_reverse_left_transfer)]
    #[kani::stub_verified(verified_reflected_global_period)]
    #[kani::stub_verified(verified_reverse_lexical_bounds)]
    #[kani::stub(reverse_loop_facts, probe_suffix_shape)]
    #[kani::stub(reverse_loop_root, root_shape_for_loop)]
    #[kani::stub(reverse_loop_earlier, earlier_shape_for_reverse_bound)]
    #[kani::stub(reflected_global_period, known_reflected_period_shape)]
    #[kani::stub(range_agreement, known_period_range_shape)]
    #[kani::stub(reverse_suffix_loop_state, bounded_reverse_loop_true)]
    pub fn harness_reverse_suffix_period_true() {
        let arr = any_nonempty_bytes();
        let known_period = kani::any();
        unsafe {
            WORD_EQUALITY_OBSERVATION = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), true);
            REVERSE_KNOWN_PERIOD = known_period;
        }
        let left = reverse_suffix_period(arr, known_period, true);
        kani::cover(
            arr.len() > 4096 && known_period < arr.len(),
            "shorter global period bounds the opposite reverse order",
        );
        kani::cover(left > 0, "opposite reverse critical point can be nonzero");
        kani::cover(
            true,
            "contract proof returns: harness_reverse_suffix_period_true",
        );
    }

    // Quantifier bodies must be pure expressions. These macros contain
    // only primitive comparisons, pointer reads and quantifiers. Callers
    // check all index bounds before expanding them. The wrapping additions
    // cannot wrap under those bounds (every accessed index is below len).
    macro_rules! word_prefix_expr {
        ($ptr:ident, $a:expr, $b:expr, $count:expr) => {
            kani::internal::kani_forall(0, $count, move |word_index: usize| unsafe {
                *crate::intrinsics::arith_offset(
                    $ptr,
                    crate::intrinsics::wrapping_add($a, word_index) as isize,
                ) == *crate::intrinsics::arith_offset(
                    $ptr,
                    crate::intrinsics::wrapping_add($b, word_index) as isize,
                )
            })
        };
    }

    macro_rules! word_witness_expr {
        ($ptr:ident, $a:expr, $b:expr, $witness:expr, $reverse:expr) => {
            (((!$reverse)
                & unsafe {
                    *crate::intrinsics::arith_offset(
                        $ptr,
                        crate::intrinsics::wrapping_add($a, $witness) as isize,
                    ) > *crate::intrinsics::arith_offset(
                        $ptr,
                        crate::intrinsics::wrapping_add($b, $witness) as isize,
                    )
                })
                | ($reverse
                    & unsafe {
                        *crate::intrinsics::arith_offset(
                            $ptr,
                            crate::intrinsics::wrapping_add($a, $witness) as isize,
                        ) < *crate::intrinsics::arith_offset(
                            $ptr,
                            crate::intrinsics::wrapping_add($b, $witness) as isize,
                        )
                    }))
                & word_prefix_expr!($ptr, $a, $b, $witness)
        };
    }

    // Equal-length prefixes, expressed directly at every relative index.
    // No lexicographic algorithm is assumed here.
    fn word_prefix_equal(arr: &[u8], a: usize, b: usize, count: usize) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || a > n || b > n || count > n - a || count > n - b {
            return false;
        }
        let ptr = arr as *const [u8] as *const u8;
        word_prefix_expr!(ptr, a, b, count)
    }

    fn word_strict_witness(arr: &[u8], a: usize, b: usize, witness: usize, reverse: bool) -> bool {
        full_word_strict_witness(arr, a, b, witness, reverse)
    }

    fn full_word_strict_witness(
        arr: &[u8],
        a: usize,
        b: usize,
        witness: usize,
        reverse: bool,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || a >= n || b >= n || witness >= n - a || witness >= n - b {
            return false;
        }
        let ptr = arr as *const [u8] as *const u8;
        word_witness_expr!(ptr, a, b, witness, reverse)
    }

    fn root_word_witness_exists(
        arr: &[u8],
        left: usize,
        period: usize,
        shift: usize,
        reverse: bool,
    ) -> bool {
        uncached_root_word_witness_exists(arr, left, period, shift, reverse)
    }

    fn uncached_root_word_witness_exists(
        arr: &[u8],
        left: usize,
        period: usize,
        shift: usize,
        reverse: bool,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES
            || left >= n
            || period == 0
            || period > n - left
            || shift == 0
            || shift >= period
        {
            return false;
        }
        let ptr = arr as *const [u8] as *const u8;
        kani::internal::kani_exists(0, period - shift, move |witness: usize| {
            word_witness_expr!(
                ptr,
                left,
                crate::intrinsics::wrapping_add(left, shift),
                witness,
                reverse
            )
        })
    }

    fn earlier_word_witness_exists(
        arr: &[u8],
        left: usize,
        candidate: usize,
        reverse: bool,
    ) -> bool {
        uncached_earlier_word_witness_exists(arr, left, candidate, reverse)
    }

    fn uncached_earlier_word_witness_exists(
        arr: &[u8],
        left: usize,
        candidate: usize,
        reverse: bool,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || left >= n || candidate >= left {
            return false;
        }
        let ptr = arr as *const [u8] as *const u8;
        kani::internal::kani_exists(0, n - left, move |witness: usize| {
            word_witness_expr!(ptr, left, candidate, witness, reverse)
        })
    }

    // In each original pre-state, L/D provides a witness for this requested
    // instance. The proof harness makes it an explicit ghost input and checks
    // a weaker point condition. All original pre-states remain represented.
    // The existence query is true on those original states; every use checks
    // identical arguments and the empty frame keeps the array unchanged.
    static mut WORD_EXISTS_SNAPSHOT: (*const u8, usize, usize, usize, usize, bool, bool) =
        (crate::ptr::null(), 0, 0, 0, 0, false, false);

    fn cached_root_word_witness_exists(
        arr: &[u8],
        left: usize,
        period: usize,
        shift: usize,
        reverse: bool,
    ) -> bool {
        let saved = unsafe { WORD_EXISTS_SNAPSHOT };
        assert!(
            arr.as_ptr() == saved.0
                && arr.len() == saved.1
                && left == saved.2
                && period == saved.3
                && shift == saved.4
                && reverse == saved.5
        );
        kani::cover(true, "assert #46");
        saved.6
    }

    fn cached_earlier_word_witness_exists(
        arr: &[u8],
        left: usize,
        candidate: usize,
        reverse: bool,
    ) -> bool {
        let saved = unsafe { WORD_EXISTS_SNAPSHOT };
        assert!(
            arr.as_ptr() == saved.0
                && arr.len() == saved.1
                && left == saved.2
                && saved.3 == 0
                && candidate == saved.4
                && reverse == saved.5
        );
        kani::cover(true, "assert #47");
        saved.6
    }

    // Universal postcondition projection. The real chooser's assumption is
    // stronger than this point condition, so every concrete returned witness
    // remains possible at every observation. An actual bad postcondition has
    // a bad prefix point. The original L/D precondition still supplies a full witness.
    static mut WORD_WITNESS_PREFIX_OBSERVATION: usize = 0;

    fn word_strict_witness_at_observer(
        arr: &[u8],
        a: usize,
        b: usize,
        witness: usize,
        reverse: bool,
    ) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES || a >= n || b >= n || witness >= n - a || witness >= n - b {
            return false;
        }
        let point = unsafe { WORD_WITNESS_PREFIX_OBSERVATION };
        (point >= witness || arr[a + point] == arr[b + point])
            && suffix_byte_preferred(arr[a + witness], arr[b + witness], reverse)
    }

    // Only the selected quantified instance is needed to choose a witness.
    // These are weaker preconditions than the full L/D predicates; the
    // witness postconditions below retain their full, unprojected meaning.
    fn root_dominance_at_requested_shift(
        arr: &[u8],
        left: usize,
        period: usize,
        reverse: bool,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || left >= n || period == 0 || period > n - left {
            return false;
        }
        let shift = unsafe { WORD_EQUALITY_OBSERVATION };
        shift == 0 || shift >= period || root_word_witness_exists(arr, left, period, shift, reverse)
    }

    fn earlier_dominance_at_requested_candidate(arr: &[u8], left: usize, reverse: bool) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || left >= n {
            return false;
        }
        let candidate = unsafe { WORD_EQUALITY_OBSERVATION };
        candidate >= left || earlier_word_witness_exists(arr, left, candidate, reverse)
    }

    macro_rules! word_root_body {
        ($arr:ident, $left:ident, $period:ident, $reverse:ident) => {{
            let n = crate::intrinsics::ptr_metadata($arr as *const [u8]);
            if n > MAX_ALLOCATION_BYTES || $left >= n || $period == 0 || $period > n - $left {
                return false;
            }
            let ptr = $arr as *const [u8] as *const u8;
            kani::internal::kani_forall(1, $period, move |shift: usize| {
                kani::internal::kani_exists(
                    0,
                    crate::intrinsics::wrapping_sub($period, shift),
                    move |witness: usize| {
                        word_witness_expr!(
                            ptr,
                            $left,
                            crate::intrinsics::wrapping_add($left, shift),
                            witness,
                            $reverse
                        )
                    },
                )
            })
        }};
    }

    fn word_root_dominance(arr: &[u8], left: usize, period: usize, reverse: bool) -> bool {
        word_root_body!(arr, left, period, reverse)
    }

    macro_rules! word_earlier_body {
        ($arr:ident, $left:ident, $reverse:ident) => {{
            let n = crate::intrinsics::ptr_metadata($arr as *const [u8]);
            if n > MAX_ALLOCATION_BYTES || $left >= n {
                return false;
            }
            let ptr = $arr as *const [u8] as *const u8;
            let bound = n - $left;
            kani::internal::kani_forall(0, $left, move |candidate: usize| {
                kani::internal::kani_exists(0, bound, move |witness: usize| {
                    word_witness_expr!(ptr, $left, candidate, witness, $reverse)
                })
            })
        }};
    }

    fn word_earlier_dominance(arr: &[u8], left: usize, reverse: bool) -> bool {
        word_earlier_body!(arr, left, reverse)
    }

    #[kani::requires(word_root_dominance(arr, left, period, reverse)
        && 0 < shift && shift < period)]
    #[kani::ensures(|witness| *witness < period - shift
        && word_strict_witness(arr, left, left + shift, *witness, reverse))]
    #[kani::modifies()]
    fn choose_root_word_witness(
        arr: &[u8],
        left: usize,
        period: usize,
        shift: usize,
        reverse: bool,
    ) -> usize {
        // Check existence before making a nondeterministic witness choice.
        assert!(root_word_witness_exists(arr, left, period, shift, reverse));
        kani::cover(true, "assert #48");
        let witness: usize = kani::any();
        kani::assume(
            witness < period - shift
                && word_strict_witness(arr, left, left + shift, witness, reverse),
        );
        kani::cover(true, "assume #70");
        witness
    }

    #[kani::proof_for_contract(choose_root_word_witness)]
    #[kani::stub(word_root_dominance, root_dominance_at_requested_shift)]
    #[kani::stub(root_word_witness_exists, cached_root_word_witness_exists)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    #[kani::stub(full_word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_choose_root_word_witness_projected() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let period = kani::any();
        let shift = kani::any();
        let reverse: bool = kani::any();
        unsafe {
            WORD_WITNESS_PREFIX_OBSERVATION = kani::any();
        }
        kani::assume(left < arr.len() && 0 < period && period <= arr.len() - left);
        kani::cover(true, "assume #71");
        kani::assume(0 < shift && shift < period);
        kani::cover(true, "assume #72");
        let supplied_witness: usize = kani::any();
        kani::assume(supplied_witness < period - shift);
        kani::cover(true, "assume #73");
        kani::assume(full_word_strict_witness(
            arr,
            left,
            left + shift,
            supplied_witness,
            reverse,
        ));
        kani::cover(true, "assume #74");
        // Existential elimination: every permitted input admits such a ghost
        // witness. It is independent of the function's chosen return value.
        let exists = true;
        unsafe {
            WORD_EQUALITY_OBSERVATION = shift;
            WORD_EXISTS_SNAPSHOT = (
                arr.as_ptr(),
                arr.len(),
                left,
                period,
                shift,
                reverse,
                exists,
            );
        }
        let witness = choose_root_word_witness(arr, left, period, shift, reverse);
        kani::cover(
            arr.len() > 4096 && period == 2,
            "root-witness domain is nonempty at symbolic length",
        );
        kani::cover(
            witness > 0 && unsafe { WORD_WITNESS_PREFIX_OBSERVATION } < witness,
            "nonempty prefix observed inside the returned strict witness",
        );
        kani::cover(
            true,
            "contract proof returns: harness_choose_root_word_witness_projected",
        );
    }

    #[kani::requires(word_earlier_dominance(arr, left, reverse) && candidate < left)]
    #[kani::ensures(|witness| *witness < arr.len() - left
        && word_strict_witness(arr, left, candidate, *witness, reverse))]
    #[kani::modifies()]
    fn choose_earlier_word_witness(
        arr: &[u8],
        left: usize,
        candidate: usize,
        reverse: bool,
    ) -> usize {
        assert!(earlier_word_witness_exists(arr, left, candidate, reverse));
        kani::cover(true, "assert #49");
        let witness: usize = kani::any();
        kani::assume(
            witness < arr.len() - left
                && word_strict_witness(arr, left, candidate, witness, reverse),
        );
        kani::cover(true, "assume #75");
        witness
    }

    #[kani::proof_for_contract(choose_earlier_word_witness)]
    #[kani::stub(word_earlier_dominance, earlier_dominance_at_requested_candidate)]
    #[kani::stub(earlier_word_witness_exists, cached_earlier_word_witness_exists)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    #[kani::stub(full_word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_choose_earlier_word_witness_projected() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let candidate = kani::any();
        let reverse: bool = kani::any();
        unsafe {
            WORD_WITNESS_PREFIX_OBSERVATION = kani::any();
        }
        kani::assume(left < arr.len() && candidate < left);
        kani::cover(true, "assume #76");
        let supplied_witness: usize = kani::any();
        kani::assume(supplied_witness < arr.len() - left);
        kani::cover(true, "assume #77");
        kani::assume(full_word_strict_witness(
            arr,
            left,
            candidate,
            supplied_witness,
            reverse,
        ));
        kani::cover(true, "assume #78");
        let exists = true;
        unsafe {
            WORD_EQUALITY_OBSERVATION = candidate;
            WORD_EXISTS_SNAPSHOT = (arr.as_ptr(), arr.len(), left, 0, candidate, reverse, exists);
        }
        let witness = choose_earlier_word_witness(arr, left, candidate, reverse);
        kani::cover(left > 4096, "earlier-candidate witness at a distant suffix");
        kani::cover(
            witness > 0 && unsafe { WORD_WITNESS_PREFIX_OBSERVATION } < witness,
            "nonempty prefix observed inside the returned strict witness",
        );
        kani::cover(
            true,
            "contract proof returns: harness_choose_earlier_word_witness_projected",
        );
    }

    // Counterexample-preserving projection of the universal equality
    // predicates. A failed full predicate has a failing byte: choosing that
    // byte as the arbitrary, read-only observation keeps the failure.
    static mut WORD_EQUALITY_OBSERVATION: usize = 0;

    fn word_prefix_equal_at_observer(arr: &[u8], a: usize, b: usize, count: usize) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || a > n || b > n || count > n - a || count > n - b {
            return false;
        }
        let i = unsafe { WORD_EQUALITY_OBSERVATION };
        let ptr = arr as *const [u8] as *const u8;
        i >= count
            || unsafe {
                *crate::intrinsics::arith_offset(ptr, (a + i) as isize)
                    == *crate::intrinsics::arith_offset(ptr, (b + i) as isize)
            }
    }

    fn word_range_equal_at_observer(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || delta > begin || begin > end || end > n {
            return false;
        }
        let i = unsafe { WORD_EQUALITY_OBSERVATION };
        let ptr = arr as *const [u8] as *const u8;
        i < begin
            || i >= end
            || unsafe {
                *crate::intrinsics::arith_offset(ptr, i as isize)
                    == *crate::intrinsics::arith_offset(ptr, (i - delta) as isize)
            }
    }

    // Indexed forms of the prefix laws. The observation index is arbitrary
    // and all inputs are read-only, so their universally quantified forms
    // follow by universal introduction; no algorithmic result is assumed.
    #[kani::requires(word_prefix_equal(arr, a, b, count) && index < count)]
    #[kani::ensures(|_| arr[a + index] == arr[b + index])]
    #[kani::modifies()]
    fn read_word_prefix(arr: &[u8], a: usize, b: usize, count: usize, index: usize) {}

    #[kani::proof_for_contract(read_word_prefix)]
    #[kani::stub(word_prefix_equal, word_prefix_equal_at_observer)]
    pub fn harness_read_word_prefix_projected() {
        let arr = any_nonempty_bytes();
        let a = kani::any();
        let b = kani::any();
        let count = kani::any();
        let index = kani::any();
        unsafe {
            WORD_EQUALITY_OBSERVATION = index;
        }
        read_word_prefix(arr, a, b, count, index);
        kani::cover(index > 4096, "read equal prefixes at any distant element");
        kani::cover(
            true,
            "contract proof returns: harness_read_word_prefix_projected",
        );
    }

    fn small_root_extension_pre(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
    ) -> bool {
        suffix_facts(arr, left, right, offset, period)
            && word_root_dominance(arr, left, period, reverse)
            && right + offset < arr.len()
            && suffix_byte_preferred(arr[left + offset], arr[right + offset], reverse)
    }

    // Construct a strict witness for every shift of the newly extended root.
    // Recursion decreases shift by period; no remainder operation is used.
    #[kani::requires(small_root_extension_pre(arr, left, right, offset, period, reverse)
        && 0 < shift && shift < right + offset + 1 - left)]
    #[kani::ensures(|witness| *witness < right + offset + 1 - left - shift
        && word_strict_witness(arr, left, left + shift, *witness, reverse))]
    #[kani::modifies()]
    #[kani::recursion]
    fn root_extension_witness(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
        shift: usize,
    ) -> usize {
        root_extension_witness_body(arr, left, right, offset, period, reverse, shift)
    }

    // Share one assertion-bearing body between the ordinary call and the
    // contract checker. Recursive calls still cross the verified wrapper.
    #[inline(never)]
    fn root_extension_witness_body(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
        shift: usize,
    ) -> usize {
        let end = right + offset;
        let gap = end - left - shift;
        if shift < period {
            let witness = choose_root_word_witness(arr, left, period, shift, reverse);
            assert!(witness < gap);
            kani::cover(true, "assert #50");
            return witness;
        }
        if shift == period {
            assert!(left + period + gap == end);
            kani::cover(true, "assert #51");
            prefix_from_range(arr, left + period, left + period + gap, period);
            assert!(word_prefix_equal(arr, left, left + period, gap));
            kani::cover(true, "assert #52");
            read_range_agreement(
                arr,
                right - period,
                right,
                right - left - period,
                end - period,
            );
            assert!(left + gap == end - period);
            kani::cover(true, "assert #53");
            assert!(suffix_byte_preferred(
                arr[left + gap],
                arr[left + shift + gap],
                reverse
            ));
            kani::cover(true, "assert #54");
            return gap;
        }
        assert!(shift - period < shift);
        kani::cover(true, "assert #55");
        let previous =
            root_extension_witness(arr, left, right, offset, period, reverse, shift - period);
        let previous_start = left + shift - period;
        let witness = cmp::min(previous, gap);
        prefix_from_range(arr, left + shift, left + shift + witness, period);
        assert!(word_prefix_equal(
            arr,
            previous_start,
            left + shift,
            witness
        ));
        kani::cover(true, "assert #56");
        if witness < gap {
            assert!(witness == previous);
            kani::cover(true, "assert #57");
            read_range_agreement(arr, left + period, end, period, left + shift + witness);
        } else {
            assert!(witness == gap && gap <= previous);
            kani::cover(true, "assert #58");
            read_range_agreement(
                arr,
                right - period,
                right,
                right - left - period,
                end - period,
            );
            assert!(previous_start + gap == end - period);
            kani::cover(true, "assert #59");
            if gap < previous {
                read_word_prefix(arr, left, previous_start, previous, gap);
            }
        }
        assert!(word_prefix_equal(arr, left, left + shift, witness));
        kani::cover(true, "assert #60");
        assert!(suffix_byte_preferred(
            arr[left + witness],
            arr[left + shift + witness],
            reverse
        ));
        kani::cover(true, "assert #61");
        witness
    }

    #[kani::requires(word_root_dominance(arr, left, period, reverse)
        && word_earlier_dominance(arr, left, reverse)
        && 0 < global_period && global_period <= arr.len()
        && range_agreement(arr, global_period, arr.len(), global_period))]
    #[kani::ensures(|_| left < global_period && period <= global_period)]
    #[kani::modifies()]
    fn lexical_period_bounds(
        arr: &[u8],
        left: usize,
        period: usize,
        global_period: usize,
        reverse: bool,
    ) {
        // State these obligations after the case split. The forbidden cases
        // close by contradiction between strict dominance and period equality;
        // an assertion *inside* either case has no reachable passing state.
        let earlier_equalities = if left >= global_period {
            let candidate = left - global_period;
            let witness = choose_earlier_word_witness(arr, left, candidate, reverse);
            let index = left + witness;
            read_range_agreement(arr, global_period, arr.len(), global_period, index);
            (
                index - global_period == candidate + witness,
                arr[left + witness] == arr[candidate + witness],
            )
        } else {
            (true, true)
        };
        assert!(earlier_equalities.0);
        kani::cover(true, "after lexical_period_bounds earlier index equality");
        assert!(earlier_equalities.1);
        kani::cover(true, "after lexical_period_bounds earlier byte equality");
        assert!(
            left < global_period,
            "a global period cannot have an earlier strictly dominated copy"
        );
        kani::cover(true, "after lexical_period_bounds left bound");

        let root_equalities = if period > global_period {
            let witness = choose_root_word_witness(arr, left, period, global_period, reverse);
            let index = left + global_period + witness;
            read_range_agreement(arr, global_period, arr.len(), global_period, index);
            (
                index - global_period == left + witness,
                arr[left + witness] == arr[left + global_period + witness],
            )
        } else {
            (true, true)
        };
        assert!(root_equalities.0);
        kani::cover(true, "after lexical_period_bounds root index equality");
        assert!(root_equalities.1);
        kani::cover(true, "after lexical_period_bounds root byte equality");
        assert!(
            period <= global_period,
            "a global period cannot be shorter than the primitive root"
        );
        kani::cover(true, "after lexical_period_bounds period bound");
    }

    // Only the strict witness byte is needed here. The same checked-input
    // abstraction used for the chooser and transition lemmas applies.
    #[kani::proof_for_contract(lexical_period_bounds)]
    #[kani::stub_verified(choose_root_word_witness)]
    #[kani::stub_verified(choose_earlier_word_witness)]
    #[kani::stub_verified(read_range_agreement)]
    #[kani::stub(word_root_dominance, root_dominance_shape)]
    #[kani::stub(word_earlier_dominance, earlier_dominance_shape)]
    #[kani::stub(range_agreement, word_range_equal_at_observer)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_lexical_period_bounds() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let period = kani::any();
        let global_period = kani::any();
        let reverse = kani::any();
        let point = kani::any();
        unsafe {
            WORD_EQUALITY_OBSERVATION = point;
            WORD_WITNESS_PREFIX_OBSERVATION = point;
            ROOT_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, period, reverse);
            EARLIER_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, reverse);
        }
        lexical_period_bounds(arr, left, period, global_period, reverse);
        kani::cover(
            arr.len() > 4096 && global_period == arr.len(),
            "lexical bounds apply at symbolic word length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_lexical_period_bounds",
        );
    }

    // The semantic L premise is used only at the original, unchanged array,
    // left, period and order. Check that fact at every abstract predicate call.
    static mut ROOT_DOMINANCE_CALL: (*const u8, usize, usize, usize, bool) =
        (crate::ptr::null(), 0, 0, 0, false);

    fn root_dominance_shape(arr: &[u8], left: usize, period: usize, reverse: bool) -> bool {
        let saved = unsafe { ROOT_DOMINANCE_CALL };
        assert!(
            arr.as_ptr() == saved.0
                && arr.len() == saved.1
                && left == saved.2
                && period == saved.3
                && reverse == saved.4
        );
        kani::cover(true, "assert #62");
        let n = arr.len();
        n <= MAX_ALLOCATION_BYTES && left < n && 0 < period && period <= n - left
    }

    // Proof-only point abstraction: every full input and every actual output
    // of the original function is retained at every observation. Verified
    // callees retain their scalar conclusions and point projections. The
    // first failing original precondition, or the final postcondition, has a
    // bad observation and would therefore still fail in this proof.
    #[kani::proof_for_contract(root_extension_witness)]
    #[kani::stub_verified(choose_root_word_witness)]
    #[kani::stub_verified(prefix_from_range)]
    #[kani::stub_verified(read_word_prefix)]
    #[kani::stub_verified(read_range_agreement)]
    #[kani::stub(word_root_dominance, root_dominance_shape)]
    #[kani::stub(range_agreement, word_range_equal_at_observer)]
    #[kani::stub(word_prefix_equal, word_prefix_equal_at_observer)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_root_extension_pointwise() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let right = kani::any();
        let offset = kani::any();
        let period = kani::any();
        let reverse = kani::any();
        let shift = kani::any();
        let point: usize = kani::any();
        unsafe {
            WORD_EQUALITY_OBSERVATION = point;
            WORD_WITNESS_PREFIX_OBSERVATION = point;
            ROOT_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, period, reverse);
        }
        let witness = root_extension_witness(arr, left, right, offset, period, reverse, shift);
        kani::cover(
            arr.len() > 4096 && point < witness,
            "root extension checks an interior prefix point at symbolic length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_root_extension_pointwise",
        );
    }

    static mut EARLIER_DOMINANCE_CALL: (*const u8, usize, usize, bool) =
        (crate::ptr::null(), 0, 0, false);

    fn earlier_dominance_shape(arr: &[u8], left: usize, reverse: bool) -> bool {
        let saved = unsafe { EARLIER_DOMINANCE_CALL };
        assert!(
            arr.as_ptr() == saved.0
                && arr.len() == saved.1
                && left == saved.2
                && reverse == saved.3
        );
        kani::cover(true, "assert #63");
        arr.len() <= MAX_ALLOCATION_BYTES && left < arr.len()
    }

    #[kani::proof_for_contract(reset_dominance_witness)]
    #[kani::stub_verified(choose_root_word_witness)]
    #[kani::stub_verified(choose_earlier_word_witness)]
    #[kani::stub_verified(prefix_from_range)]
    #[kani::stub_verified(read_word_prefix)]
    #[kani::stub_verified(read_range_agreement)]
    #[kani::stub(word_root_dominance, root_dominance_shape)]
    #[kani::stub(word_earlier_dominance, earlier_dominance_shape)]
    #[kani::stub(range_agreement, word_range_equal_at_observer)]
    #[kani::stub(word_prefix_equal, word_prefix_equal_at_observer)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_reset_dominance_pointwise() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let right = kani::any();
        let offset = kani::any();
        let period = kani::any();
        let reverse = kani::any();
        let candidate = kani::any();
        let point: usize = kani::any();
        unsafe {
            WORD_EQUALITY_OBSERVATION = point;
            WORD_WITNESS_PREFIX_OBSERVATION = point;
            ROOT_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, period, reverse);
            EARLIER_DOMINANCE_CALL = (arr.as_ptr(), arr.len(), left, reverse);
        }
        let witness = reset_dominance_witness(arr, left, right, offset, period, reverse, candidate);
        kani::cover(
            arr.len() > 4096 && point < witness,
            "left reset checks an interior prefix point at symbolic length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reset_dominance_pointwise",
        );
    }

    #[kani::requires(range_agreement(arr, begin, end, delta))]
    #[kani::ensures(|_| word_prefix_equal(arr, begin - delta, begin, end - begin))]
    #[kani::modifies()]
    fn prefix_from_range(arr: &[u8], begin: usize, end: usize, delta: usize) {}

    // Select the absolute range byte using the same relative offset as the
    // prefix postcondition. Full range equality implies every such instance.
    fn range_at_relative_observer(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES || delta > begin || begin > end || end > n {
            return false;
        }
        let i = unsafe { WORD_EQUALITY_OBSERVATION };
        i >= end - begin || arr[begin + i] == arr[begin + i - delta]
    }

    #[kani::proof_for_contract(prefix_from_range)]
    #[kani::stub(range_agreement, range_at_relative_observer)]
    #[kani::stub(word_prefix_equal, word_prefix_equal_at_observer)]
    pub fn harness_prefix_from_range_projected() {
        let arr = any_nonempty_bytes();
        let begin = kani::any();
        let end = kani::any();
        let delta = kani::any();
        unsafe {
            WORD_EQUALITY_OBSERVATION = kani::any();
        }
        prefix_from_range(arr, begin, end, delta);
        kani::cover(
            unsafe { WORD_EQUALITY_OBSERVATION } > 4096
                && unsafe { WORD_EQUALITY_OBSERVATION } < end - begin,
            "range to prefix conversion at an interior distant offset",
        );
        kani::cover(
            true,
            "contract proof returns: harness_prefix_from_range_projected",
        );
    }

    fn large_root_reset_pre(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
    ) -> bool {
        suffix_facts(arr, left, right, offset, period)
            && word_root_dominance(arr, left, period, reverse)
            && word_earlier_dominance(arr, left, reverse)
            && right + offset < arr.len()
            && suffix_byte_preferred(arr[right + offset], arr[left + offset], reverse)
    }

    // Every candidate before the new left is strictly dominated. The
    // recursive periodic case decreases candidate by period, with no modulo.
    #[kani::requires(large_root_reset_pre(arr, left, right, offset, period, reverse)
        && candidate < right)]
    #[kani::ensures(|witness| *witness <= offset && *witness < arr.len() - right
        && word_strict_witness(arr, right, candidate, *witness, reverse))]
    #[kani::modifies()]
    #[kani::recursion]
    fn reset_dominance_witness(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
        candidate: usize,
    ) -> usize {
        let end = right + offset;
        if candidate >= left + period {
            assert!(candidate - period < candidate);
            kani::cover(true, "assert #64");
            let witness = reset_dominance_witness(
                arr,
                left,
                right,
                offset,
                period,
                reverse,
                candidate - period,
            );
            assert!(candidate + witness + 1 <= end);
            kani::cover(true, "assert #65");
            prefix_from_range(arr, candidate, candidate + witness + 1, period);
            assert!(word_prefix_equal(
                arr,
                candidate - period,
                candidate,
                witness + 1
            ));
            kani::cover(true, "assert #66");
            read_range_agreement(arr, left + period, end, period, candidate + witness);
            assert!(suffix_byte_preferred(
                arr[right + witness],
                arr[candidate + witness],
                reverse
            ));
            kani::cover(true, "assert #67");
            return witness;
        }
        let previous = if candidate < left {
            choose_earlier_word_witness(arr, left, candidate, reverse)
        } else if candidate == left {
            offset
        } else {
            choose_root_word_witness(arr, left, period, candidate - left, reverse)
        };
        let witness = cmp::min(previous, offset);
        if candidate != left {
        } else {
            assert!(word_prefix_equal(arr, left, candidate, witness));
            kani::cover(true, "assert #68");
        }
        prefix_from_range(arr, right, right + witness, right - left);
        assert!(word_prefix_equal(arr, right, left, witness));
        kani::cover(true, "assert #69");
        if witness < offset {
            assert!(candidate != left && witness == previous);
            kani::cover(true, "assert #70");
            read_range_agreement(arr, right, end, right - left, right + witness);
        } else {
            assert!(witness == offset);
            kani::cover(true, "assert #71");
            if candidate != left && offset < previous {
                read_word_prefix(arr, left, candidate, previous, offset);
            }
        }
        assert!(word_prefix_equal(arr, right, candidate, witness));
        kani::cover(true, "assert #72");
        assert!(suffix_byte_preferred(
            arr[right + witness],
            arr[candidate + witness],
            reverse
        ));
        kani::cover(true, "assert #73");
        witness
    }

    // Three byte relations make the period update inductive: the processed
    // suffix repeats at distance `period`; its last whole block matches the
    // first block; and the current comparison has matched `offset` bytes.
    // Expand the same predicate for ordinary contracts and loop contracts to
    // keep their instrumented helper-call ABIs separate.
    macro_rules! suffix_facts_body {
        ($arr:ident, $left:ident, $right:ident, $offset:ident, $period:ident) => {{
            let n = crate::intrinsics::ptr_metadata($arr as *const [u8]);
            if n > MAX_ALLOCATION_BYTES
                || $left >= $right
                || $right > n
                || $period == 0
                || $offset >= $period
                || $period > $right - $left
                || $offset > n - $right
            {
                return false;
            }
            let ptr = $arr as *const [u8] as *const u8;
            // Evaluate all three pure predicates without short-circuit CFG paths.
            // SAFETY: the numeric invariant puts every quantified index in $arr.
            unsafe {
                kani::internal::kani_forall($left + $period, $right + $offset, move |j: usize| {
                    *crate::intrinsics::arith_offset(ptr, j as isize)
                        == *crate::intrinsics::arith_offset(ptr, (j - $period) as isize)
                }) & kani::internal::kani_forall($right - $period, $right, move |j: usize| {
                    *crate::intrinsics::arith_offset(ptr, j as isize)
                        == *crate::intrinsics::arith_offset(
                            ptr,
                            (j - ($right - $left - $period)) as isize,
                        )
                }) & kani::internal::kani_forall($right, $right + $offset, move |j: usize| {
                    *crate::intrinsics::arith_offset(ptr, j as isize)
                        == *crate::intrinsics::arith_offset(ptr, (j - ($right - $left)) as isize)
                })
            }
        }};
    }

    fn suffix_facts(arr: &[u8], left: usize, right: usize, offset: usize, period: usize) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES
            || left >= right
            || right > n
            || period == 0
            || offset >= period
            || period > right - left
            || offset > n - right
        {
            return false;
        }
        range_agreement(arr, left + period, right + offset, period)
            & range_agreement(arr, right - period, right, right - left - period)
            & range_agreement(arr, right, right + offset, right - left)
    }

    // This alias is only called from loop clauses, so its instrumented ABI
    // is not shared with ordinary contract predicates.
    fn loop_word_root(arr: &[u8], left: usize, period: usize, reverse: bool) -> bool {
        word_root_body!(arr, left, period, reverse)
    }

    fn loop_suffix_facts(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        suffix_facts_body!(arr, left, right, offset, period)
    }

    // Universal introduction is checked through an arbitrary shift and the
    // uniform witness returned by the already proved witness constructor.
    // Unlike a bad-state exclusion, this observation checks the actual byte
    // property and leaves the complete transition premise unchanged.
    static mut ROOT_TRANSFER_SHIFT: usize = 0;

    fn root_transfer_pre(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        small_root_extension_pre(arr, left, right, offset, period, order)
    }

    fn root_transfer_post(
        arr: &[u8], left: usize, period: usize, order: bool, shift: usize, witness: usize,
    ) -> bool {
        // Callers that use the returned witness need this relation in the
        // real contract, in addition to the complete existential L predicate.
        word_root_body!(arr, left, period, order)
            && root_transfer_post_at_shift(arr, left, period, order, shift, witness)
    }

    fn root_transfer_post_at_shift(
        arr: &[u8], left: usize, period: usize, order: bool, shift: usize, witness: usize,
    ) -> bool {
        let n = arr.len();
        n <= MAX_ALLOCATION_BYTES && left < n && 0 < period && period <= n - left
            && (shift == 0 || shift >= period || (witness < period - shift
                && word_strict_witness(arr, left, left + shift, witness, order)))
    }

    // The wrapper and its sole verified callee use the identical premise,
    // with identical arguments and no intervening writes. Abstract only that
    // shared premise to its numeric consequences in the wrapper's proof.
    // This admits every real pre-state; the witness constructor's independent
    // proof still checks its full premise.
    fn root_transfer_premise_bounds(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, _order: bool,
    ) -> bool {
        probe_suffix_shape(arr, left, right, offset, period) && right + offset < arr.len()
    }

    #[kani::requires(root_transfer_pre(arr, left, right, offset, period, order))]
    #[kani::ensures(|witness| root_transfer_post(
        arr, left, right + offset + 1 - left, order, unsafe { ROOT_TRANSFER_SHIFT }, *witness))]
    #[kani::modifies()]
    fn verified_root_transfer(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> usize {
        let shift = unsafe { ROOT_TRANSFER_SHIFT };
        let next_period = right + offset + 1 - left;
        if shift > 0 && shift < next_period {
            root_extension_witness(arr, left, right, offset, period, order, shift)
        } else {
            0
        }
    }

    #[kani::proof_for_contract(verified_root_transfer)]
    #[kani::stub_verified(root_extension_witness)]
    #[kani::stub(small_root_extension_pre, root_transfer_premise_bounds)]
    #[kani::stub(root_transfer_post, root_transfer_post_at_shift)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    #[kani::stub(full_word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_verified_root_transfer() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let right = kani::any();
        let offset = kani::any();
        let period = kani::any();
        let order = kani::any();
        unsafe {
            ROOT_TRANSFER_SHIFT = kani::any();
            WORD_WITNESS_PREFIX_OBSERVATION = kani::any();
        }
        let _ = verified_root_transfer(arr, left, right, offset, period, order);
        kani::cover(arr.len() > 4096, "root transfer accepts a symbolic-length word");
        kani::cover(true, "contract proof returns: harness_verified_root_transfer");
    }

    // A real full-premise witness, separate from the premise abstraction.
    // A one-byte old root has no nontrivial shifts; its repeated block is
    // automatic at (left,right,offset,period) = (0,1,0,1).
    #[kani::proof]
    #[kani::solver(z3)]
    pub fn harness_root_transfer_full_premise_reachable() {
        let arr = any_nonempty_bytes();
        kani::assume(arr.len() >= 2);
        kani::cover(true, "assume #79");
        kani::assume(arr[0] > arr[1]);
        kani::cover(true, "assume #80");
        assert!(root_transfer_pre(arr, 0, 1, 0, 1, false));
        kani::cover(true, "assert #74");
        assert!(left_transfer_pre(arr, 0, 1, 0, 1, true));
        kani::cover(true, "assert #75");
        kani::cover(arr.len() > 4096, "full forward transfer premises at symbolic length");
    }

    // These two abstractions are used only by the existing first-counterexample
    // induction. Their exact transition arguments are checked by the contract;
    // the original transfer itself is proved above with its full premise.
    fn root_transfer_probe_pre(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        loop_suffix_facts(arr, left, right, offset, period)
            && loop_word_root(arr, left, period, order)
            && right + offset < arr.len()
            && suffix_byte_preferred(arr[left + offset], arr[right + offset], order)
    }

    fn root_transfer_probe_post(
        arr: &[u8], left: usize, period: usize, order: bool, _shift: usize, _witness: usize,
    ) -> bool {
        root_exclusion_predicate(arr, left, period, order)
    }

    fn apply_root_extension_for_loop(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
    ) {
        assert!(loop_suffix_facts(arr, left, right, offset, period));
        kani::cover(true, "assert #76");
        assert!(loop_word_root(arr, left, period, reverse));
        kani::cover(true, "assert #77");
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        assert!(right + offset < n);
        kani::cover(true, "assert #78");
        let ptr = arr as *const [u8] as *const u8;
        let a = unsafe { *crate::intrinsics::arith_offset(ptr, (right + offset) as isize) };
        let b = unsafe { *crate::intrinsics::arith_offset(ptr, (left + offset) as isize) };
        assert!((a < b && !reverse) || (a > b && reverse));
        kani::cover(true, "assert #79");
        let _ = verified_root_transfer(arr, left, right, offset, period, reverse);
    }

    fn lyndon_suffix_loop_state(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES
            || left >= right
            || right > n
            || period == 0
            || period > right - left
            || offset >= period
            || offset > n - right
        {
            return false;
        }
        if !loop_suffix_facts(arr, left, right, offset, period) {
            return false;
        }
        let root = loop_word_root(arr, left, period, reverse);
        if root && right + offset < n {
            let ptr = arr as *const [u8] as *const u8;
            let a = unsafe { *crate::intrinsics::arith_offset(ptr, (right + offset) as isize) };
            let b = unsafe { *crate::intrinsics::arith_offset(ptr, (left + offset) as isize) };
            if (a < b && !reverse) || (a > b && reverse) {
                apply_root_extension_for_loop(arr, left, right, offset, period, reverse);
            }
        }
        root
    }

    fn lyndon_suffix_loop_false(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        lyndon_suffix_loop_state(arr, left, right, offset, period, false)
    }

    fn lyndon_suffix_loop_true(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        lyndon_suffix_loop_state(arr, left, right, offset, period, true)
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES)]
    #[kani::ensures(|result| result.0 < arr.len() && 0 < result.1
        && result.1 <= arr.len() - result.0
        && word_root_dominance(arr, result.0, result.1, reverse))]
    #[kani::modifies()]
    fn maximal_suffix_root(arr: &[u8], reverse: bool) -> (usize, usize) {
        TwoWaySearcher::maximal_suffix(arr, reverse)
    }

    // Counterexample probe for L induction. If real L first fails at (l,p),
    // select that pair here. Earlier true L states and all successors certified
    // by root_extension_witness differ from it. p=1 is always a valid root.
    static mut ROOT_STATE_PROBE: (usize, usize) = (0, 0);
    static mut PREPROCESSING_INPUT: (*const u8, usize, bool) = (crate::ptr::null(), 0, false);

    macro_rules! root_exclusion_body {
        ($arr:ident, $left:ident, $period:ident, $reverse:ident) => {{
            let n = crate::intrinsics::ptr_metadata($arr as *const [u8]);
            let saved = unsafe { PREPROCESSING_INPUT };
            assert!(
                $arr as *const [u8] as *const u8 == saved.0 && n == saved.1 && $reverse == saved.2
            );
            kani::cover(true, "assert #80");
            let bad = unsafe { ROOT_STATE_PROBE };
            n <= MAX_ALLOCATION_BYTES
                && $left < n
                && 0 < $period
                && $period <= n - $left
                && ($period == 1 || $left != bad.0 || $period != bad.1)
        }};
    }

    fn root_exclusion_predicate(arr: &[u8], left: usize, period: usize, reverse: bool) -> bool {
        root_exclusion_body!(arr, left, period, reverse)
    }

    fn root_exclusion_for_loop(arr: &[u8], left: usize, period: usize, reverse: bool) -> bool {
        root_exclusion_body!(arr, left, period, reverse)
    }

    fn probe_suffix_shape(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        n <= MAX_ALLOCATION_BYTES
            && left < right
            && right <= n
            && 0 < period
            && period <= right - left
            && offset < period
            && offset <= n - right
    }

    #[kani::proof_for_contract(maximal_suffix_root)]
    #[kani::stub_verified(verified_root_transfer)]
    #[kani::stub(root_transfer_pre, root_transfer_probe_pre)]
    #[kani::stub(root_transfer_post, root_transfer_probe_post)]
    #[kani::stub(suffix_loop_state, lyndon_suffix_loop_false)]
    #[kani::stub(loop_word_root, root_exclusion_for_loop)]
    #[kani::stub(word_root_dominance, root_exclusion_predicate)]
    #[kani::stub(loop_suffix_facts, probe_suffix_shape)]
    pub fn harness_maximal_suffix_root_probe_false() {
        let arr = any_nonempty_bytes();
        unsafe {
            ROOT_STATE_PROBE = (kani::any(), kani::any());
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), false);
        }
        let result = maximal_suffix_root(arr, false);
        kani::cover(
            arr.len() > 4096 && result.1 > 1,
            "nontrivial root period in a symbolic-length actual search",
        );
        kani::cover(
            true,
            "contract proof returns: harness_maximal_suffix_root_probe_false",
        );
    }

    #[kani::proof_for_contract(maximal_suffix_root)]
    #[kani::stub_verified(verified_root_transfer)]
    #[kani::stub(root_transfer_pre, root_transfer_probe_pre)]
    #[kani::stub(root_transfer_post, root_transfer_probe_post)]
    #[kani::stub(suffix_loop_state, lyndon_suffix_loop_true)]
    #[kani::stub(loop_word_root, root_exclusion_for_loop)]
    #[kani::stub(word_root_dominance, root_exclusion_predicate)]
    #[kani::stub(loop_suffix_facts, probe_suffix_shape)]
    pub fn harness_maximal_suffix_root_probe_true() {
        let arr = any_nonempty_bytes();
        unsafe {
            ROOT_STATE_PROBE = (kani::any(), kani::any());
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), true);
        }
        let result = maximal_suffix_root(arr, true);
        kani::cover(
            arr.len() > 4096 && result.1 > 1,
            "opposite byte order retains symbolic lengths and non-unit periods",
        );
        kani::cover(
            true,
            "contract proof returns: harness_maximal_suffix_root_probe_true",
        );
    }

    fn loop_word_earlier(arr: &[u8], left: usize, reverse: bool) -> bool {
        word_earlier_body!(arr, left, reverse)
    }

    static mut LEFT_TRANSFER_CANDIDATE: usize = 0;

    fn left_transfer_pre(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        large_root_reset_pre(arr, left, right, offset, period, order)
    }

    fn left_transfer_post(
        arr: &[u8], left: usize, order: bool, candidate: usize, witness: usize,
    ) -> bool {
        word_earlier_body!(arr, left, order)
            && left_transfer_post_at_candidate(arr, left, order, candidate, witness)
    }

    fn left_transfer_post_at_candidate(
        arr: &[u8], left: usize, order: bool, candidate: usize, witness: usize,
    ) -> bool {
        let n = arr.len();
        n <= MAX_ALLOCATION_BYTES && left < n
            && (candidate >= left || (witness < n - left
                && word_strict_witness(arr, left, candidate, witness, order)))
    }

    #[kani::requires(left_transfer_pre(arr, left, right, offset, period, order))]
    #[kani::ensures(|witness| left_transfer_post(
        arr, right, order, unsafe { LEFT_TRANSFER_CANDIDATE }, *witness))]
    #[kani::modifies()]
    fn verified_left_transfer(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> usize {
        let candidate = unsafe { LEFT_TRANSFER_CANDIDATE };
        if candidate < right {
            reset_dominance_witness(arr, left, right, offset, period, order, candidate)
        } else {
            0
        }
    }

    // Each proof universally checks every nondeterministic callee return at
    // an arbitrary prefix position. Its weakened callee postcondition admits
    // every return of the full, independently checked contract at every
    // position. Thus for any such real return w, forall i is checked for that
    // same w; no separate existential witness is chosen for each i. The real
    // witness constructors never read this proof observation.
    #[kani::proof_for_contract(verified_left_transfer)]
    #[kani::stub_verified(reset_dominance_witness)]
    #[kani::stub(large_root_reset_pre, root_transfer_premise_bounds)]
    #[kani::stub(left_transfer_post, left_transfer_post_at_candidate)]
    #[kani::stub(word_strict_witness, word_strict_witness_at_observer)]
    #[kani::stub(full_word_strict_witness, word_strict_witness_at_observer)]
    pub fn harness_verified_left_transfer() {
        let arr = any_nonempty_bytes();
        let left = kani::any();
        let right = kani::any();
        let offset = kani::any();
        let period = kani::any();
        let order = kani::any();
        unsafe {
            LEFT_TRANSFER_CANDIDATE = kani::any();
            WORD_WITNESS_PREFIX_OBSERVATION = kani::any();
        }
        let _ = verified_left_transfer(arr, left, right, offset, period, order);
        kani::cover(arr.len() > 4096, "left transfer accepts a symbolic-length word");
        kani::cover(true, "contract proof returns: harness_verified_left_transfer");
    }

    fn left_transfer_probe_pre(
        arr: &[u8], left: usize, right: usize, offset: usize, period: usize, order: bool,
    ) -> bool {
        loop_suffix_facts(arr, left, right, offset, period)
            && loop_word_root(arr, left, period, order)
            && loop_word_earlier(arr, left, order)
            && right + offset < arr.len()
            && suffix_byte_preferred(arr[right + offset], arr[left + offset], order)
    }

    fn left_transfer_probe_post(
        arr: &[u8], left: usize, order: bool, _candidate: usize, _witness: usize,
    ) -> bool {
        earlier_exclusion_predicate(arr, left, order)
    }

    fn apply_left_reset_for_loop(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
    ) {
        assert!(loop_suffix_facts(arr, left, right, offset, period));
        kani::cover(true, "assert #81");
        assert!(loop_word_root(arr, left, period, reverse));
        kani::cover(true, "assert #82");
        assert!(loop_word_earlier(arr, left, reverse));
        kani::cover(true, "assert #83");
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        assert!(right + offset < n);
        kani::cover(true, "assert #84");
        let ptr = arr as *const [u8] as *const u8;
        let a = unsafe { *crate::intrinsics::arith_offset(ptr, (right + offset) as isize) };
        let b = unsafe { *crate::intrinsics::arith_offset(ptr, (left + offset) as isize) };
        assert!((a > b && !reverse) || (a < b && reverse));
        kani::cover(true, "assert #85");
        let _ = verified_left_transfer(arr, left, right, offset, period, reverse);
    }

    fn dominance_suffix_loop_state(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
        reverse: bool,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES
            || left >= right
            || right > n
            || period == 0
            || period > right - left
            || offset >= period
            || offset > n - right
        {
            return false;
        }
        if !loop_suffix_facts(arr, left, right, offset, period)
            || !loop_word_root(arr, left, period, reverse)
        {
            return false;
        }
        let earlier = loop_word_earlier(arr, left, reverse);
        if earlier && right + offset < n {
            let ptr = arr as *const [u8] as *const u8;
            let a = unsafe { *crate::intrinsics::arith_offset(ptr, (right + offset) as isize) };
            let b = unsafe { *crate::intrinsics::arith_offset(ptr, (left + offset) as isize) };
            if (a > b && !reverse) || (a < b && reverse) {
                apply_left_reset_for_loop(arr, left, right, offset, period, reverse);
            }
        }
        earlier
    }

    fn dominance_suffix_loop_false(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        dominance_suffix_loop_state(arr, left, right, offset, period, false)
    }

    fn dominance_suffix_loop_true(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        dominance_suffix_loop_state(arr, left, right, offset, period, true)
    }

    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES)]
    #[kani::ensures(|result| result.0 < arr.len() && 0 < result.1
        && result.1 <= arr.len() - result.0
        && word_earlier_dominance(arr, result.0, reverse))]
    #[kani::modifies()]
    fn maximal_suffix_dominance(arr: &[u8], reverse: bool) -> (usize, usize) {
        TwoWaySearcher::maximal_suffix(arr, reverse)
    }

    // D is vacuous at left=0. If it first fails at some other left, this
    // one-state exclusion probe preserves that first counterexample.
    static mut EARLIER_STATE_PROBE: usize = 0;

    macro_rules! earlier_exclusion_body {
        ($arr:ident, $left:ident, $reverse:ident) => {{
            let n = crate::intrinsics::ptr_metadata($arr as *const [u8]);
            let saved = unsafe { PREPROCESSING_INPUT };
            assert!(
                $arr as *const [u8] as *const u8 == saved.0 && n == saved.1 && $reverse == saved.2
            );
            kani::cover(true, "assert #86");
            let bad = unsafe { EARLIER_STATE_PROBE };
            n <= MAX_ALLOCATION_BYTES && $left < n && ($left == 0 || $left != bad)
        }};
    }

    fn earlier_exclusion_predicate(arr: &[u8], left: usize, reverse: bool) -> bool {
        earlier_exclusion_body!(arr, left, reverse)
    }

    fn earlier_exclusion_for_loop(arr: &[u8], left: usize, reverse: bool) -> bool {
        earlier_exclusion_body!(arr, left, reverse)
    }

    fn root_shape_for_loop(arr: &[u8], left: usize, period: usize, reverse: bool) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        let saved = unsafe { PREPROCESSING_INPUT };
        assert!(arr as *const [u8] as *const u8 == saved.0 && n == saved.1 && reverse == saved.2);
        kani::cover(true, "assert #87");
        n <= MAX_ALLOCATION_BYTES && left < n && 0 < period && period <= n - left
    }

    #[kani::proof_for_contract(maximal_suffix_dominance)]
    #[kani::stub_verified(verified_left_transfer)]
    #[kani::stub(left_transfer_pre, left_transfer_probe_pre)]
    #[kani::stub(left_transfer_post, left_transfer_probe_post)]
    #[kani::stub(suffix_loop_state, dominance_suffix_loop_false)]
    #[kani::stub(loop_word_earlier, earlier_exclusion_for_loop)]
    #[kani::stub(word_earlier_dominance, earlier_exclusion_predicate)]
    #[kani::stub(loop_word_root, root_shape_for_loop)]
    #[kani::stub(loop_suffix_facts, probe_suffix_shape)]
    pub fn harness_maximal_suffix_dominance_probe_false() {
        let arr = any_nonempty_bytes();
        unsafe {
            EARLIER_STATE_PROBE = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), false);
        }
        let result = maximal_suffix_dominance(arr, false);
        kani::cover(
            arr.len() > 4096 && result.0 > 0,
            "actual maximal suffix moves its left endpoint at symbolic length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_maximal_suffix_dominance_probe_false",
        );
    }

    #[kani::proof_for_contract(maximal_suffix_dominance)]
    #[kani::stub_verified(verified_left_transfer)]
    #[kani::stub(left_transfer_pre, left_transfer_probe_pre)]
    #[kani::stub(left_transfer_post, left_transfer_probe_post)]
    #[kani::stub(suffix_loop_state, dominance_suffix_loop_true)]
    #[kani::stub(loop_word_earlier, earlier_exclusion_for_loop)]
    #[kani::stub(word_earlier_dominance, earlier_exclusion_predicate)]
    #[kani::stub(loop_word_root, root_shape_for_loop)]
    #[kani::stub(loop_suffix_facts, probe_suffix_shape)]
    pub fn harness_maximal_suffix_dominance_probe_true() {
        let arr = any_nonempty_bytes();
        unsafe {
            EARLIER_STATE_PROBE = kani::any();
            PREPROCESSING_INPUT = (arr.as_ptr(), arr.len(), true);
        }
        let result = maximal_suffix_dominance(arr, true);
        kani::cover(
            arr.len() > 4096 && result.0 > 0,
            "left endpoint moves in the opposite byte order",
        );
        kani::cover(
            true,
            "contract proof returns: harness_maximal_suffix_dominance_probe_true",
        );
    }

    pub(super) fn suffix_loop_state(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let valid = suffix_facts_body!(arr, left, right, offset, period);
        if valid && right + offset < crate::intrinsics::ptr_metadata(arr as *const [u8]) {
            let ptr = arr as *const [u8] as *const u8;
            if unsafe {
                *crate::intrinsics::arith_offset(ptr, (right + offset) as isize)
                    == *crate::intrinsics::arith_offset(ptr, (left + offset) as isize)
            } {
                // Same verified contracts, expressed without nested guard calls.
                apply_read_range_contract(
                    arr,
                    right - period,
                    right,
                    right - left - period,
                    right - period + offset,
                );
                apply_extend_range_contract(arr, left + period, right + offset, period);
                apply_extend_range_contract(arr, right, right + offset, right - left);
            }
        }
        valid
    }

    pub(super) fn suffix_result(arr: &[u8], result: (usize, usize)) -> bool {
        let (left, period) = result;
        let n = arr.len();
        if left >= n || period == 0 || period > n - left {
            return false;
        }
        let ptr = arr.as_ptr();
        // SAFETY: both indices belong to the suffix arr[left..].
        unsafe {
            kani::internal::kani_forall(left + period, n, move |j: usize| {
                *crate::intrinsics::arith_offset(ptr, j as isize)
                    == *crate::intrinsics::arith_offset(ptr, (j - period) as isize)
            })
        }
    }

    fn range_agreement(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let n = arr.len();
        if n > MAX_ALLOCATION_BYTES || delta > begin || begin > end || end > n {
            return false;
        }
        let ptr = arr.as_ptr();
        unsafe {
            kani::internal::kani_forall(begin, end, move |i: usize| {
                *crate::intrinsics::arith_offset(ptr, i as isize)
                    == *crate::intrinsics::arith_offset(ptr, (i - delta) as isize)
            })
        }
    }

    // Keep loop-clause calls separate from ordinary slice helper ABIs.
    fn range_agreement_for_loop(arr: &[u8], begin: usize, end: usize, delta: usize) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        if n > MAX_ALLOCATION_BYTES || delta > begin || begin > end || end > n {
            return false;
        }
        let ptr = arr as *const [u8] as *const u8;
        unsafe {
            kani::internal::kani_forall(begin, end, move |i: usize| {
                *crate::intrinsics::arith_offset(ptr, i as isize)
                    == *crate::intrinsics::arith_offset(ptr, (i - delta) as isize)
            })
        }
    }

    #[kani::proof]
    #[kani::solver(z3)]
    pub fn harness_loop_range_predicate_equivalent() {
        let arr = any_nonempty_bytes();
        let begin = kani::any();
        let end = kani::any();
        let delta = kani::any();
        assert!(
            range_agreement_for_loop(arr, begin, end, delta)
                == range_agreement(arr, begin, end, delta)
        );
        kani::cover(true, "assert #88");
        kani::cover(arr.len() > 4096, "equivalent predicates at symbolic length");
    }

    // Direct read/extend obligations, without nested contract-guard calls.
    // Both premises and conclusions are checked in the actual loop context.
    fn apply_read_range_contract(arr: &[u8], begin: usize, end: usize, delta: usize, index: usize) {
        assert!(range_agreement_for_loop(arr, begin, end, delta) && begin <= index && index < end);
        kani::cover(true, "assert #89");
        let ptr = arr as *const [u8] as *const u8;
        assert!(unsafe {
            *crate::intrinsics::arith_offset(ptr, index as isize)
                == *crate::intrinsics::arith_offset(ptr, (index - delta) as isize)
        });
        kani::cover(true, "assert #90");
    }

    fn apply_extend_range_contract(arr: &[u8], begin: usize, end: usize, delta: usize) {
        assert!(
            range_agreement_for_loop(arr, begin, end, delta)
                && end < crate::intrinsics::ptr_metadata(arr as *const [u8])
        );
        kani::cover(true, "assert #91");
        let ptr = arr as *const [u8] as *const u8;
        assert!(unsafe {
            *crate::intrinsics::arith_offset(ptr, end as isize)
                == *crate::intrinsics::arith_offset(ptr, (end - delta) as isize)
        });
        kani::cover(true, "assert #92");
        assert!(range_agreement_for_loop(arr, begin, end + 1, delta));
        kani::cover(true, "assert #93");
    }

    #[kani::requires(range_agreement(arr, begin, end, delta)
        && end < arr.len() && arr[end] == arr[end - delta])]
    #[kani::ensures(|_| range_agreement(arr, begin, end + 1, delta))]
    #[kani::modifies()]
    fn extend_range_agreement(arr: &[u8], begin: usize, end: usize, delta: usize) {}

    #[kani::proof_for_contract(extend_range_agreement)]
    #[kani::solver(z3)]
    pub fn harness_extend_range_agreement() {
        let arr = any_nonempty_bytes();
        let begin = kani::any();
        let end = kani::any();
        let delta = kani::any();
        extend_range_agreement(arr, begin, end, delta);
        apply_extend_range_contract(arr, begin, end, delta);
        kani::cover(end > 4096, "extend agreement at an unbounded offset");
        kani::cover(
            true,
            "contract proof returns: harness_extend_range_agreement",
        );
    }

    #[kani::requires(range_agreement(arr, begin, end, delta)
        && begin <= index && index < end)]
    #[kani::ensures(|_| arr[index] == arr[index - delta])]
    #[kani::modifies()]
    fn read_range_agreement(arr: &[u8], begin: usize, end: usize, delta: usize, index: usize) {}

    #[kani::proof_for_contract(read_range_agreement)]
    #[kani::solver(z3)]
    pub fn harness_read_range_agreement() {
        let arr = any_nonempty_bytes();
        let begin = kani::any();
        let end = kani::any();
        let delta = kani::any();
        let index = kani::any();
        read_range_agreement(arr, begin, end, delta, index);
        apply_read_range_contract(arr, begin, end, delta, index);
        kani::cover(index > 4096, "instantiate agreement at an unbounded offset");
        kani::cover(true, "contract proof returns: harness_read_range_agreement");
    }

    // The general preprocessing contract states the numeric guarantee used
    // by constructor summaries. Stronger period/root/dominance properties
    // retain their separate, already-proved contracts and input domains.
    pub(super) fn numeric_suffix_result(arr: &[u8], result: (usize, usize)) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        n <= MAX_ALLOCATION_BYTES && result.0 < n && result.1 > 0 && result.1 <= n - result.0
    }

    // A weaker loop invariant proves the numeric constructor facts without
    // repeating the separate quantified period/preprocessing proofs.
    fn numeric_suffix_loop_state(
        arr: &[u8],
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        n <= MAX_ALLOCATION_BYTES
            && left < right
            && right <= n
            && period > 0
            && period <= right - left
            && offset < period
            && offset <= n - right
    }

    #[kani::proof_for_contract(TwoWaySearcher::maximal_suffix)]
    #[kani::stub(suffix_loop_state, numeric_suffix_loop_state)]
    pub fn harness_maximal_suffix_numeric_bounds() {
        let input = any_nonempty_bytes();
        let order: bool = kani::any();
        let (critical, period) = TwoWaySearcher::maximal_suffix(input, order);
        assert!(critical < input.len());
        kani::cover(true, "assert #94");
        assert!(period > 0 && period <= input.len() - critical);
        kani::cover(true, "assert #95");
        kani::cover(
            input.len() > 4096,
            "numeric suffix bounds at symbolic length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_maximal_suffix_numeric_bounds",
        );
    }

    // Every positive-critical Short state can use its cache-prefix length
    // as a parameter instead of an independent period. This checks coverage
    // before changing the input generator used by the expensive scan proof.
    #[kani::proof]
    pub fn harness_short_period_parameterization() {
        let len: usize = kani::any();
        let critical: usize = kani::any();
        let period: usize = kani::any();
        kani::assume(2 <= len && len <= MAX_ALLOCATION_BYTES);
        kani::cover(true, "assume #81");
        kani::assume(0 < critical && critical < len);
        kani::cover(true, "assume #82");
        kani::assume(critical < period && period <= len - critical);
        kani::cover(true, "assume #83");
        let prefix = len - period;
        let gap = prefix - critical;
        assert!(critical <= (len - 1) / 2);
        kani::cover(true, "assert #96");
        assert!(gap < len - 2 * critical);
        kani::cover(true, "assert #97");
        assert!(len - (critical + gap) == period);
        kani::cover(true, "assert #98");
        kani::cover(len > 4096, "parameterization preserves symbolic lengths");
    }

    pub(super) fn reverse_suffix_loop_state(
        arr: &[u8],
        known_period: usize,
        left: usize,
        right: usize,
        offset: usize,
        period: usize,
    ) -> bool {
        let n = crate::intrinsics::ptr_metadata(arr as *const [u8]);
        n <= MAX_ALLOCATION_BYTES
            && 0 < known_period
            && known_period <= n
            && left < right
            && right <= n
            && 0 < period
            && period <= right - left
            && offset < period
            && offset <= n - right
    }

    // A numeric baseline for the real reverse preprocessing loop. The full
    // input length is always a valid period; shorter known periods still need
    // the lexical L/D lemmas before this proof can be generalized.
    #[kani::requires(!arr.is_empty() && arr.len() <= MAX_ALLOCATION_BYTES)]
    #[kani::ensures(|result| *result < arr.len())]
    #[kani::modifies()]
    fn reverse_suffix_full_period(arr: &[u8], order: bool) -> usize {
        TwoWaySearcher::reverse_maximal_suffix(arr, arr.len(), order)
    }

    #[kani::proof_for_contract(reverse_suffix_full_period)]
    pub fn harness_reverse_suffix_full_period_bounds() {
        let arr = any_nonempty_bytes();
        let _ = reverse_suffix_full_period(arr, kani::any());
        kani::cover(
            arr.len() > 4096,
            "reverse preprocessing with symbolic input length",
        );
        kani::cover(
            true,
            "contract proof returns: harness_reverse_suffix_full_period_bounds",
        );
    }

    // Numeric safety of the real Two-Way scan is checked separately from the
    // stronger byte equalities required for UTF-8 result boundaries.
    pub(super) fn raw_loop_state(s: &TwoWaySearcher, h: &[u8], n: &[u8], long: bool) -> bool {
        let hn = crate::intrinsics::ptr_metadata(h as *const [u8]);
        let nn = crate::intrinsics::ptr_metadata(n as *const [u8]);
        hn <= MAX_ALLOCATION_BYTES
            && 2 <= nn
            && nn <= MAX_ALLOCATION_BYTES
            && s.crit_pos <= nn
            && s.crit_pos_back <= nn
            && s.period > 0
            && s.period <= nn
            && s.position <= hn
            && s.end <= hn
            && if long {
                s.memory == usize::MAX && s.memory_back == usize::MAX
            } else {
                short_cache_state(s, h, n)
            }
    }

    // Static preprocessing and needle-byte facts are preserved by the
    // checked write set (only the active cursor/cache may change). The raw
    // loop needs to restate only the cache facts that a body can invalidate.
    fn short_cache_state(s: &TwoWaySearcher, h: &[u8], n: &[u8]) -> bool {
        let len = crate::intrinsics::ptr_metadata(n as *const [u8]);
        let hn = crate::intrinsics::ptr_metadata(h as *const [u8]);
        if s.period > len
            || s.position > hn
            || s.end > hn
            || (s.memory != 0 && s.memory != len - s.period)
            || (s.memory_back != len && s.memory_back != s.period)
        {
            return false;
        }
        let hp = h as *const [u8] as *const u8;
        (s.memory == 0
            || s.position == 0
            || s.position == hn
            || unsafe { *crate::intrinsics::arith_offset(hp, s.position as isize) } as i8 >= -0x40)
            && (s.memory_back == len
                || s.end == 0
                || s.end == hn
                || unsafe { *crate::intrinsics::arith_offset(hp, s.end as isize) } as i8 >= -0x40)
    }

    // A view of the two concrete raw strategies, used only by function
    // contracts. The generic fallback is explicitly outside the contract's
    // domain; it never assumes a representation for an arbitrary Output.
    pub(super) enum RawOutcome {
        Match(usize, usize),
        Reject(usize, usize),
        Exhausted,
        Unsupported,
    }

    pub(super) trait RawStrategy: TwoWayStrategy {
        fn supported() -> bool;
        fn needs_last_scalar() -> bool;
        fn outcome(result: &Self::Output) -> RawOutcome;
    }

    impl<T: TwoWayStrategy> RawStrategy for T {
        default fn supported() -> bool {
            false
        }
        default fn needs_last_scalar() -> bool {
            true
        }
        default fn outcome(_: &Self::Output) -> RawOutcome {
            RawOutcome::Unsupported
        }
    }

    impl RawStrategy for RejectAndMatch {
        fn supported() -> bool {
            true
        }
        fn needs_last_scalar() -> bool {
            false
        }
        fn outcome(result: &SearchStep) -> RawOutcome {
            match *result {
                SearchStep::Match(a, b) => RawOutcome::Match(a, b),
                SearchStep::Reject(a, b) => RawOutcome::Reject(a, b),
                SearchStep::Done => RawOutcome::Unsupported,
            }
        }
    }

    impl RawStrategy for MatchOnly {
        fn supported() -> bool {
            true
        }
        fn needs_last_scalar() -> bool {
            true
        }
        fn outcome(result: &Option<(usize, usize)>) -> RawOutcome {
            match *result {
                Some((a, b)) => RawOutcome::Match(a, b),
                None => RawOutcome::Exhausted,
            }
        }
    }

    pub(super) fn raw_reverse_pre<S: TwoWayStrategy>(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
    ) -> bool {
        if !S::supported()
            || h.len() > MAX_ALLOCATION_BYTES
            || n.len() < 2
            || n.len() > MAX_ALLOCATION_BYTES
            || s.position > h.len()
            || s.end > h.len()
            || lead_width(n[0]) == 0
        {
            return false;
        }
        if long {
            if s.memory != usize::MAX
                || s.memory_back != usize::MAX
                || !long_preprocessing_state(s, n)
            {
                return false;
            }
        } else if !short_state(s, h, n) {
            return false;
        }
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        text.is_char_boundary(s.position)
            && text.is_char_boundary(s.end)
            && (!S::needs_last_scalar()
                || lead_width(n[last_scalar_start(n)]) == n.len() - last_scalar_start(n))
    }

    pub(super) fn raw_reverse_post<S: TwoWayStrategy>(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
        initial_end: usize,
        result: &S::Output,
    ) -> bool {
        if s.position > h.len() || s.end > initial_end || initial_end > h.len() {
            return false;
        }
        if long {
            if s.memory != usize::MAX
                || s.memory_back != usize::MAX
                || !long_preprocessing_state(s, n)
            {
                return false;
            }
        } else if !short_state(s, h, n) {
            return false;
        }
        match S::outcome(result) {
            RawOutcome::Match(a, b) => {
                if a >= b || b > h.len() || b - a != n.len() || s.end != a {
                    return false;
                }
                if S::needs_last_scalar() {
                    let text = unsafe { crate::str::from_utf8_unchecked(h) };
                    let needle = unsafe { crate::str::from_utf8_unchecked(n) };
                    assume_utf8_at_match(text, needle, SearchStep::Match(a, b));
                }
                match_boundaries(h, a, b)
            }
            RawOutcome::Reject(a, b) => a <= b && b == initial_end && s.end == a,
            RawOutcome::Exhausted => s.end == 0,
            RawOutcome::Unsupported => false,
        }
    }

    // Keep the function-contract boundary outside the generic algorithm's
    // nested loops. The wrapper still executes the original method unchanged.
    #[kani::requires(raw_reverse_pre::<S>(searcher, h, n, long))]
    #[kani::ensures(|result| raw_reverse_post::<S>(
        searcher, h, n, long, old(searcher.end), result))]
    #[kani::modifies(&searcher.end, &searcher.memory_back)]
    fn verified_raw_reverse<S: TwoWayStrategy>(
        searcher: &mut TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
    ) -> S::Output {
        searcher.next_back::<S>(h, n, long)
    }

    // Used only after the wrapper's contract has independently verified.
    fn model_raw_reverse<S: TwoWayStrategy>(
        searcher: &mut TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
    ) -> S::Output {
        verified_raw_reverse::<S>(searcher, h, n, long)
    }

    // The real raw algorithm is checked independently before this contract
    // may be used as a summary by the public boundary-rounding wrapper.
    #[kani::proof_for_contract(verified_raw_reverse)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    pub fn harness_two_way_short_next_back_contract() {
        let h = any_str().as_bytes();
        let n = any_str().as_bytes();
        let mut s = any_short_reverse_searcher(h, n);
        let _ = verified_raw_reverse::<RejectAndMatch>(&mut s, h, n, false);
        kani::cover(
            true,
            "contract proof returns: harness_two_way_short_next_back_contract",
        );
    }

    fn raw_forward_pre<S: TwoWayStrategy>(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
    ) -> bool {
        raw_reverse_pre::<S>(s, h, n, long)
            && lead_width(n[last_scalar_start(n)]) == n.len() - last_scalar_start(n)
    }

    fn raw_forward_post<S: TwoWayStrategy>(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
        initial_pos: usize,
        result: &S::Output,
    ) -> bool {
        if s.position < initial_pos || s.position > h.len() || s.end > h.len() {
            return false;
        }
        if long {
            if s.memory != usize::MAX
                || s.memory_back != usize::MAX
                || !long_preprocessing_state(s, n)
            {
                return false;
            }
        } else if !short_state(s, h, n) {
            return false;
        }
        match S::outcome(result) {
            RawOutcome::Match(a, b) => {
                if a >= b || b > h.len() || b - a != n.len() || s.position != b {
                    return false;
                }
                let text = unsafe { crate::str::from_utf8_unchecked(h) };
                let needle = unsafe { crate::str::from_utf8_unchecked(n) };
                assume_utf8_at_match(text, needle, SearchStep::Match(a, b));
                match_boundaries(h, a, b)
            }
            RawOutcome::Reject(a, b) => a == initial_pos && a <= b && b == s.position,
            RawOutcome::Exhausted => s.position == h.len(),
            RawOutcome::Unsupported => false,
        }
    }

    #[kani::requires(raw_forward_pre::<S>(searcher, h, n, long))]
    #[kani::ensures(|result| raw_forward_post::<S>(
        searcher, h, n, long, old(searcher.position), result))]
    #[kani::modifies(&searcher.position, &searcher.memory)]
    fn verified_raw_forward<S: TwoWayStrategy>(
        searcher: &mut TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
    ) -> S::Output {
        let result = searcher.next::<S>(h, n, long);
        if let RawOutcome::Match(a, b) = S::outcome(&result) {
            check_short_match(h, n, a, b);
        }
        result
    }

    // Enabled only by harnesses whose strategy/domain has a proved wrapper.
    fn model_raw_forward<S: TwoWayStrategy>(
        searcher: &mut TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
    ) -> S::Output {
        verified_raw_forward::<S>(searcher, h, n, long)
    }

    fn check_short_forward_contract(cached: bool) {
        let h = any_str().as_bytes();
        let n = any_str().as_bytes();
        let mut s = any_short_searcher(h, n);
        kani::assume((s.memory != 0) == cached);
        kani::cover(true, "assume #84");
        let _ = verified_raw_forward::<RejectAndMatch>(&mut s, h, n, false);
    }

    // Zero and nonzero cache values exhaust the entire candidate state.
    fn any_uncached_short_searcher(h: &[u8], n: &[u8], has_left_part: bool) -> TwoWaySearcher {
        assume_needle_edges(n);
        let critical = if has_left_part {
            let c: usize = kani::any();
            kani::assume(c != 0);
            kani::cover(true, "assume #85");
            c
        } else {
            0
        };
        let s = TwoWaySearcher {
            crit_pos: critical,
            crit_pos_back: kani::any(),
            period: kani::any(),
            byteset: kani::any(),
            position: kani::any(),
            end: kani::any(),
            memory: 0,
            memory_back: kani::any(),
        };
        kani::assume(short_state(&s, h, n));
        kani::cover(true, "assume #86");
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        kani::assume(text.is_char_boundary(s.position) && text.is_char_boundary(s.end));
        kani::cover(true, "assume #87");
        if has_left_part {
            let needle = unsafe { crate::str::from_utf8_unchecked(n) };
            establish_last_scalar_bound(needle, n.len() - s.period);
            if s.period < n.len() {
                establish_last_scalar_bound(needle, s.period);
            }
            let last = last_scalar_start(n);
            assert!(s.crit_pos <= last);
            kani::cover(true, "assert #99");
            assert!(s.period == n.len() || s.period <= last);
            kani::cover(true, "assert #100");
        }
        s
    }

    fn check_uncached_forward_contract(has_left_part: bool) {
        let h = any_str().as_bytes();
        let n = any_str().as_bytes();
        let mut s = any_uncached_short_searcher(h, n, has_left_part);
        let _ = verified_raw_forward::<RejectAndMatch>(&mut s, h, n, false);
    }

    #[kani::proof_for_contract(verified_raw_forward)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(establish_last_scalar_bound)]
    #[kani::stub_verified(establish_long_match_boundaries)]
    pub fn harness_two_way_short_next_contract_uncached_no_left() {
        check_uncached_forward_contract(false);
        kani::cover(
            true,
            "contract proof returns: harness_two_way_short_next_contract_uncached_no_left",
        );
    }

    #[kani::proof_for_contract(verified_raw_forward)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(establish_last_scalar_bound)]
    #[kani::stub_verified(establish_long_match_boundaries)]
    pub fn harness_two_way_short_next_contract_uncached_left() {
        check_uncached_forward_contract(true);
        kani::cover(
            true,
            "contract proof returns: harness_two_way_short_next_contract_uncached_left",
        );
    }

    #[kani::proof_for_contract(verified_raw_forward)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(establish_long_match_boundaries)]
    pub fn harness_two_way_short_next_contract_cached() {
        check_short_forward_contract(true);
        kani::cover(
            true,
            "contract proof returns: harness_two_way_short_next_contract_cached",
        );
    }

    // Check the exact strategy instantiated by the public MatchOnly adapter.
    // This is independent of the RejectAndMatch contract partitions above.
    #[kani::proof_for_contract(verified_raw_forward)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(establish_last_scalar_bound)]
    #[kani::stub_verified(establish_long_match_boundaries)]
    pub fn harness_two_way_short_forward_match_contract() {
        let h = any_str().as_bytes();
        let n = any_str().as_bytes();
        let mut s = any_short_searcher(h, n);
        let _ = verified_raw_forward::<MatchOnly>(&mut s, h, n, false);
        kani::cover(n.len() > 4096, "forward MatchOnly contract at arbitrary needle length");
        kani::cover(
            true,
            "contract proof returns: harness_two_way_short_forward_match_contract",
        );
    }

    #[kani::proof_for_contract(verified_raw_reverse)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    pub fn harness_two_way_short_reverse_match_contract() {
        let h = any_str().as_bytes();
        let n = any_str().as_bytes();
        assume_needle_edges(n);
        let mut s = any_short_reverse_searcher(h, n);
        let _ = verified_raw_reverse::<MatchOnly>(&mut s, h, n, false);
        kani::cover(n.len() > 4096, "reverse MatchOnly contract at arbitrary needle length");
        kani::cover(
            true,
            "contract proof returns: harness_two_way_short_reverse_match_contract",
        );
    }

    // Short-period state. Its static factorization inequalities are
    // established by harness_short_constructor_from_preprocessing.
    // Loop-contract instrumentation changes helper-call ABIs. Expand the same
    // predicate separately for ordinary checks and loop-contract evaluation.
    macro_rules! short_state_body {
        ($s:ident, $h:ident, $n:ident) => {{
            let len = crate::intrinsics::ptr_metadata($n as *const [u8]);
            let hn = crate::intrinsics::ptr_metadata($h as *const [u8]);
            if len < 2
                || len > MAX_ALLOCATION_BYTES
                || hn > MAX_ALLOCATION_BYTES
                || $s.period == 0
                || $s.period > len
                || $s.crit_pos >= $s.period
                || $s.crit_pos > len - $s.period
                || $s.crit_pos_back > len
                || $s.crit_pos_back <= len - $s.period
                || $s.position > hn
                || $s.end > hn
                || ($s.memory != 0 && $s.memory != len - $s.period)
                || ($s.memory_back != len && $s.memory_back != $s.period)
            {
                return false;
            }
            let np = $n as *const [u8] as *const u8;
            let hp = $h as *const [u8] as *const u8;
            macro_rules! n_boundary {
                ($i:expr) => {
                    $i == 0
                        || $i == len
                        || unsafe { *crate::intrinsics::arith_offset(np, $i as isize) } as i8
                            >= -0x40
                };
            }
            macro_rules! h_boundary {
                ($i:expr) => {
                    $i == 0
                        || $i == hn
                        || unsafe { *crate::intrinsics::arith_offset(hp, $i as isize) } as i8
                            >= -0x40
                };
            }
            n_boundary!($s.period)
                && n_boundary!(len - $s.period)
                && ($s.memory == 0 || h_boundary!($s.position))
                && ($s.memory_back == len || h_boundary!($s.end))
        }};
    }

    pub(super) fn short_loop_state(s: &TwoWaySearcher, h: &[u8], n: &[u8]) -> bool {
        short_state_body!(s, h, n)
    }

    fn short_state(s: &TwoWaySearcher, h: &[u8], n: &[u8]) -> bool {
        short_state_body!(s, h, n)
    }

    pub(super) fn raw_scan_state(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
        forward: bool,
    ) -> bool {
        raw_loop_state(s, h, n, long)
            && if forward {
                crate::intrinsics::ptr_metadata(n as *const [u8])
                    <= crate::intrinsics::ptr_metadata(h as *const [u8]) - s.position
            } else {
                crate::intrinsics::ptr_metadata(n as *const [u8]) <= s.end
            }
    }

    fn any_raw_searcher(h: &[u8], n: &[u8], long: bool) -> TwoWaySearcher {
        let s = TwoWaySearcher {
            crit_pos: kani::any(),
            crit_pos_back: kani::any(),
            period: kani::any(),
            byteset: kani::any(),
            position: kani::any(),
            end: kani::any(),
            memory: kani::any(),
            memory_back: kani::any(),
        };
        kani::assume(n.len() >= 2);
        kani::cover(true, "assume #88");
        kani::assume(s.crit_pos <= n.len() && s.crit_pos_back <= n.len());
        kani::cover(true, "assume #89");
        kani::assume(s.period > 0 && s.period <= n.len());
        kani::cover(true, "assume #90");
        kani::assume(s.position <= h.len() && s.end <= h.len());
        kani::cover(true, "assume #91");
        kani::assume(if long {
            s.memory == usize::MAX && s.memory_back == usize::MAX
        } else {
            short_state(&s, h, n)
        });
        kani::cover(true, "assume #92");
        s
    }

    pub(super) fn last_scalar_start(bytes: &[u8]) -> usize {
        // Also evaluated by on_entry: avoid ordinary library-call ABIs here.
        let n = crate::intrinsics::ptr_metadata(bytes as *const [u8]);
        let ptr = bytes as *const [u8] as *const u8;
        if n == 0 {
            return 0;
        }
        macro_rules! leading {
            ($i:expr) => {
                (unsafe { *crate::intrinsics::arith_offset(ptr, $i as isize) } as i8) >= -0x40
            };
        }
        if leading!(n - 1) {
            n - 1
        } else if n >= 2 && leading!(n - 2) {
            n - 2
        } else if n >= 3 && leading!(n - 3) {
            n - 3
        } else if n >= 4 {
            n - 4
        } else {
            0
        }
    }

    // A boundary before the end cannot lie after the last scalar's start.
    // This local byte fact can be checked independently of the search loops.
    #[kani::requires(n.len() >= 2 && n.len() <= MAX_ALLOCATION_BYTES
        && boundary < n.len() && n.is_char_boundary(boundary))]
    #[kani::ensures(|_| boundary <= last_scalar_start(n.as_bytes()))]
    #[kani::modifies()]
    fn establish_last_scalar_bound(n: &str, boundary: usize) {}

    #[kani::proof_for_contract(establish_last_scalar_bound)]
    pub fn harness_last_scalar_boundary_bound() {
        let n = any_nonempty_str();
        let boundary = kani::any();
        establish_last_scalar_bound(n, boundary);
        kani::cover(boundary > 4096, "a boundary in a symbolic-length needle");
        kani::cover(
            true,
            "contract proof returns: harness_last_scalar_boundary_bound",
        );
    }

    fn assume_needle_edges(bytes: &[u8]) {
        kani::assume(bytes.len() >= 2);
        kani::cover(true, "assume #93");
        let last = last_scalar_start(bytes);
        kani::assume(lead_width(bytes[0]) != 0);
        kani::cover(true, "assume #94");
        kani::assume(lead_width(bytes[last]) == bytes.len() - last);
        kani::cover(true, "assume #95");
    }

    // The two private strategies have fixed early-rejection behavior.
    // Keep this verification-only dispatch out of the algorithm body.
    pub(super) trait ProbeMode {
        fn early_reject() -> bool;
        fn early_reject_on_entry() -> bool;
    }
    impl<T> ProbeMode for T {
        default fn early_reject() -> bool {
            false
        }
        default fn early_reject_on_entry() -> bool {
            false
        }
    }
    impl ProbeMode for RejectAndMatch {
        fn early_reject() -> bool {
            true
        }
        fn early_reject_on_entry() -> bool {
            true
        }
    }

    // A reverse single step retains its old end boundary. Only MatchOnly,
    // which can traverse several candidates, needs the last-scalar probe.
    // The loop predicate does not observe this probe in early-reject mode.
    pub(super) fn reverse_scan_probe<S: ProbeMode>(needle: &[u8]) -> usize {
        if S::early_reject_on_entry() {
            0
        } else {
            last_scalar_start(needle)
        }
    }

    pub(super) fn long_scan_probes<S: ProbeMode>(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
        progress: usize,
        phase: u8,
        initial: usize,
        last_probe: usize,
    ) -> bool {
        if !long {
            return short_scan_probes::<S>(s, h, n, progress, phase, initial, last_probe);
        }
        let forward = phase < 2;
        let early = S::early_reject();
        if early && (if forward { s.position } else { s.end }) != initial {
            return false;
        }
        if !raw_scan_state(s, h, n, long, forward) {
            return false;
        }
        let len = crate::intrinsics::ptr_metadata(n as *const [u8]);
        if last_probe >= len {
            return false;
        }
        let critical = if forward { s.crit_pos } else { s.crit_pos_back };
        let (lo, hi) = match phase {
            0 => {
                if progress > len - critical {
                    return false;
                }
                (critical, critical + progress)
            }
            1 => {
                if progress > critical {
                    return false;
                }
                (critical - progress, len)
            }
            2 => {
                if progress > critical {
                    return false;
                }
                (critical - progress, critical)
            }
            _ => {
                if progress > len - critical {
                    return false;
                }
                (0, critical + progress)
            }
        };
        let base = if forward { s.position } else { s.end - len };
        let np = n as *const [u8] as *const u8;
        let hp = h as *const [u8] as *const u8;
        macro_rules! same {
            ($i:expr) => {
                unsafe {
                    *crate::intrinsics::arith_offset(hp, (base + $i) as isize)
                        == *crate::intrinsics::arith_offset(np, $i as isize)
                }
            };
        }
        macro_rules! matched {
            ($probe:expr) => {{
                let probe = $probe;
                probe < lo || probe >= hi || same!(probe)
            }};
        }
        // The last-scalar index is captured once before entering the loop;
        // immutable needle bytes determine it, not the search result. Keep
        // only the observations needed for each strategy's boundary proof.
        ((early && forward) || matched!(0)) && ((early && !forward) || matched!(last_probe))
    }

    // Long-only harnesses cannot take this branch of long_scan_probes:
    // the raw search's long flag is fixed true. Returning false makes the
    // actual loop invariant fail if a Short scan is nevertheless entered.
    // This avoids expanding irrelevant Short-cache proof code; the real
    // Long algorithm and every Long probe remain unchanged.
    fn reject_short_probe_in_long_proof<S: ProbeMode>(
        _s: &TwoWaySearcher,
        _h: &[u8],
        _n: &[u8],
        _progress: usize,
        _phase: u8,
        _initial: usize,
        _last_probe: usize,
    ) -> bool {
        false
    }

    // Each scan invariant checks raw_scan_state before this predicate.
    // Keep only its progress and byte observations here, avoiding a second
    // evaluation of the same state and pointer-boundary checks.
    fn short_scan_probes<S: ProbeMode>(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        progress: usize,
        phase: u8,
        initial: usize,
        last_probe: usize,
    ) -> bool {
        let forward = phase < 2;
        let early = S::early_reject();
        if early && (if forward { s.position } else { s.end }) != initial {
            return false;
        }
        let len = crate::intrinsics::ptr_metadata(n as *const [u8]);
        if last_probe >= len {
            return false;
        }
        let right_start = if s.crit_pos > s.memory {
            s.crit_pos
        } else {
            s.memory
        };
        let left_end = if s.crit_pos_back < s.memory_back {
            s.crit_pos_back
        } else {
            s.memory_back
        };
        let (lo, hi, extra_lo, extra_hi) = match phase {
            0 => {
                if progress > len - right_start {
                    return false;
                }
                (right_start, right_start + progress, 0, 0)
            }
            1 => {
                let count = if s.crit_pos > s.memory {
                    s.crit_pos - s.memory
                } else {
                    0
                };
                if progress > count {
                    return false;
                }
                (s.crit_pos - progress, s.crit_pos, right_start, len)
            }
            2 => {
                if progress > left_end {
                    return false;
                }
                (left_end - progress, left_end, 0, 0)
            }
            _ => {
                let count = if s.memory_back > s.crit_pos_back {
                    s.memory_back - s.crit_pos_back
                } else {
                    0
                };
                if progress > count {
                    return false;
                }
                (s.crit_pos_back, s.crit_pos_back + progress, 0, left_end)
            }
        };
        let base = if forward { s.position } else { s.end - len };
        let np = n as *const [u8] as *const u8;
        let hp = h as *const [u8] as *const u8;
        macro_rules! matched {
            ($probe:expr) => {{
                let i = $probe;
                !((i >= lo && i < hi) || (i >= extra_lo && i < extra_hi))
                    || unsafe {
                        *crate::intrinsics::arith_offset(hp, (base + i) as isize)
                            == *crate::intrinsics::arith_offset(np, i as isize)
                    }
            }};
        }
        // The period probe is used only to establish a cached cursor's
        // boundary. Its exact byte value is not needed for the safety proof.
        macro_rules! boundary_matched {
            ($probe:expr) => {{
                let i = $probe;
                !((i >= lo && i < hi) || (i >= extra_lo && i < extra_hi))
                    || unsafe {
                        *crate::intrinsics::arith_offset(hp, (base + i) as isize) as i8 >= -0x40
                    }
            }};
        }
        ((early && forward) || matched!(0))
            && ((early && !forward) || matched!(last_probe))
            && (!forward
                || s.memory >= s.crit_pos
                || s.period == len
                || boundary_matched!(s.period))
            && (forward
                || s.memory_back <= s.crit_pos_back
                || s.period == len
                || boundary_matched!(len - s.period))
    }



    // Used only when last_probe is unobserved by every loop predicate and
    // assertion in the harness. This is a ghost projection, not a model of
    // the last character or an assumption about its width.
    fn unused_last_probe(_: &[u8]) -> usize {
        0
    }

    fn numeric_raw_loop_state(s: &TwoWaySearcher, h: &[u8], n: &[u8], long: bool) -> bool {
        let hn = crate::intrinsics::ptr_metadata(h as *const [u8]);
        let nn = crate::intrinsics::ptr_metadata(n as *const [u8]);
        hn <= MAX_ALLOCATION_BYTES
            && 2 <= nn
            && nn <= MAX_ALLOCATION_BYTES
            && s.crit_pos <= nn
            && s.crit_pos_back <= nn
            && s.period > 0
            && s.period <= nn
            && s.position <= hn
            && s.end <= hn
            && if long {
                s.memory == usize::MAX && s.memory_back == usize::MAX
            } else {
                (s.memory == 0 || s.memory == nn - s.period)
                    && (s.memory_back == nn || s.memory_back == s.period)
            }
    }

    // Numeric-only scan facts for the additional UB audit. These constrain
    // the real for-loop index and search window, without assuming any matched
    // bytes or UTF-8 property. Full endpoint proofs keep their stronger probes.
    fn ub_scan_probes<S: ProbeMode>(
        s: &TwoWaySearcher,
        h: &[u8],
        n: &[u8],
        long: bool,
        progress: usize,
        phase: u8,
        _initial: usize,
        _last_probe: usize,
    ) -> bool {
        if !raw_scan_state(s, h, n, long, phase < 2) {
            return false;
        }
        let len = crate::intrinsics::ptr_metadata(n as *const [u8]);
        let count = match phase {
            0 => {
                let start = if long || s.crit_pos > s.memory {
                    s.crit_pos
                } else {
                    s.memory
                };
                len - start
            }
            1 => {
                let start = if long { 0 } else { s.memory };
                if s.crit_pos > start {
                    s.crit_pos - start
                } else {
                    0
                }
            }
            2 => {
                if long || s.crit_pos_back < s.memory_back {
                    s.crit_pos_back
                } else {
                    s.memory_back
                }
            }
            3 => {
                let end = if long { len } else { s.memory_back };
                if end > s.crit_pos_back {
                    end - s.crit_pos_back
                } else {
                    0
                }
            }
            _ => return false,
        };
        progress <= count
    }

    fn any_raw_ub_haystack() -> &'static [u8] {
        if kani::any() {
            &[]
        } else {
            any_nonempty_bytes()
        }
    }

    fn any_raw_ub_state(h: &[u8], n: &[u8], long: bool) -> TwoWaySearcher {
        kani::assume(n.len() >= 2);
        kani::cover(true, "assume #96");
        let period: usize = kani::any();
        kani::assume(period > 0 && period <= n.len());
        kani::cover(true, "assume #97");
        let s = TwoWaySearcher {
            crit_pos: kani::any(),
            crit_pos_back: kani::any(),
            period,
            byteset: kani::any(),
            position: kani::any(),
            end: kani::any(),
            memory: if long {
                usize::MAX
            } else if kani::any() {
                0
            } else {
                n.len() - period
            },
            memory_back: if long {
                usize::MAX
            } else if kani::any() {
                n.len()
            } else {
                period
            },
        };
        kani::assume(numeric_raw_loop_state(&s, h, n, long));
        kani::cover(true, "assume #98");
        s
    }

    #[kani::proof]
    #[kani::stub(raw_loop_state, numeric_raw_loop_state)]
    #[kani::stub(long_scan_probes, ub_scan_probes)]
    #[kani::stub(last_scalar_start, unused_last_probe)]
    pub fn harness_raw_next_step_extra_ub() {
        let h = any_raw_ub_haystack();
        let n = any_nonempty_bytes();
        let long = kani::any();
        let mut s = any_raw_ub_state(h, n, long);
        let _ = s.next::<RejectAndMatch>(h, n, long);
        kani::cover(long && n.len() > 4096, "long raw forward step");
        kani::cover(!long && n.len() > 4096, "short raw forward step");
    }

    #[kani::proof]
    #[kani::stub(raw_loop_state, numeric_raw_loop_state)]
    #[kani::stub(long_scan_probes, ub_scan_probes)]
    #[kani::stub(last_scalar_start, unused_last_probe)]
    pub fn harness_raw_next_back_step_extra_ub() {
        let h = any_raw_ub_haystack();
        let n = any_nonempty_bytes();
        let long = kani::any();
        let mut s = any_raw_ub_state(h, n, long);
        let _ = s.next_back::<RejectAndMatch>(h, n, long);
        kani::cover(long && n.len() > 4096, "long raw reverse step");
        kani::cover(!long && n.len() > 4096, "short raw reverse step");
    }

    #[kani::proof]
    #[kani::stub(raw_loop_state, numeric_raw_loop_state)]
    #[kani::stub(long_scan_probes, ub_scan_probes)]
    #[kani::stub(last_scalar_start, unused_last_probe)]
    pub fn harness_raw_next_match_extra_ub() {
        let h = any_raw_ub_haystack();
        let n = any_nonempty_bytes();
        let long = kani::any();
        let mut s = any_raw_ub_state(h, n, long);
        let _ = s.next::<MatchOnly>(h, n, long);
        kani::cover(long && n.len() > 4096, "long raw forward match");
        kani::cover(!long && n.len() > 4096, "short raw forward match");
    }

    #[kani::proof]
    #[kani::stub(raw_loop_state, numeric_raw_loop_state)]
    #[kani::stub(long_scan_probes, ub_scan_probes)]
    #[kani::stub(last_scalar_start, unused_last_probe)]
    pub fn harness_raw_next_back_match_extra_ub() {
        let h = any_raw_ub_haystack();
        let n = any_nonempty_bytes();
        let long = kani::any();
        let mut s = any_raw_ub_state(h, n, long);
        let _ = s.next_back::<MatchOnly>(h, n, long);
        kani::cover(long && n.len() > 4096, "long raw reverse match");
        kani::cover(!long && n.len() > 4096, "short raw reverse match");
    }

    // Every actual raw call satisfies the already-proved directional frame.
    // This model permits all typed results and all values in that frame, so
    // the public-wrapper UB checks do not depend on matching semantics or C.
    struct RawUbModel;

    impl RawUbModel {
        fn next<S: TwoWayStrategy>(
            state: &mut TwoWaySearcher,
            _haystack: &[u8],
            _needle: &[u8],
            _long: bool,
        ) -> S::Output {
            state.position = kani::any();
            state.memory = kani::any();
            if kani::any() {
                S::matching(kani::any(), kani::any())
            } else {
                S::rejecting(kani::any(), kani::any())
            }
        }

        fn next_back<S: TwoWayStrategy>(
            state: &mut TwoWaySearcher,
            _haystack: &[u8],
            _needle: &[u8],
            _long: bool,
        ) -> S::Output {
            state.end = kani::any();
            state.memory_back = kani::any();
            if kani::any() {
                S::matching(kani::any(), kani::any())
            } else {
                S::rejecting(kani::any(), kani::any())
            }
        }
    }

    fn any_two_way_ub_storage() -> StrSearcher<'static, 'static> {
        StrSearcher {
            haystack: any_str(),
            needle: any_str(),
            searcher: StrSearcherImpl::TwoWay(TwoWaySearcher {
                crit_pos: kani::any(),
                crit_pos_back: kani::any(),
                period: kani::any(),
                byteset: kani::any(),
                position: kani::any(),
                end: kani::any(),
                memory: kani::any(),
                memory_back: kani::any(),
            }),
        }
    }

    #[kani::proof]
    #[kani::stub(TwoWaySearcher::next, RawUbModel::next)]
    #[kani::stub(str::ceil_char_boundary, ceil_char_boundary)]
    #[kani::stub_verified(verified_ceil_boundary)]
    pub fn harness_two_way_public_next_extra_ub() {
        let mut s = any_two_way_ub_storage();
        let step = s.next();
        kani::cover(
            matches!(step, SearchStep::Match(_, _)),
            "public TwoWay match",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(_, _)),
            "public TwoWay reject",
        );
        kani::cover(matches!(step, SearchStep::Done), "public TwoWay exhaustion");
    }

    #[kani::proof]
    #[kani::stub(TwoWaySearcher::next_back, RawUbModel::next_back)]
    #[kani::stub(str::floor_char_boundary, floor_char_boundary)]
    #[kani::stub_verified(verified_floor_boundary)]
    pub fn harness_two_way_public_next_back_extra_ub() {
        let mut s = any_two_way_ub_storage();
        let step = s.next_back();
        kani::cover(
            matches!(step, SearchStep::Match(_, _)),
            "public TwoWay reverse match",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(_, _)),
            "public TwoWay reverse reject",
        );
        kani::cover(
            matches!(step, SearchStep::Done),
            "public TwoWay reverse exhaustion",
        );
    }

    #[kani::proof]
    #[kani::stub(TwoWaySearcher::next, RawUbModel::next)]
    #[kani::stub(<StrSearcher as Searcher>::next, FilterUbModel::next)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    pub fn harness_two_way_public_next_match_extra_ub() {
        let mut s = any_two_way_ub_storage();
        let result = s.next_match();
        kani::cover(result.is_some(), "public TwoWay MatchOnly result");
        kani::cover(result.is_none(), "public TwoWay MatchOnly exhaustion");
    }

    #[kani::proof]
    #[kani::stub(TwoWaySearcher::next_back, RawUbModel::next_back)]
    #[kani::stub(<StrSearcher as ReverseSearcher>::next_back, FilterUbModel::next_back)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memchr)]
    pub fn harness_two_way_public_next_match_back_extra_ub() {
        let mut s = any_two_way_ub_storage();
        let result = s.next_match_back();
        kani::cover(result.is_some(), "public TwoWay reverse MatchOnly result");
        kani::cover(
            result.is_none(),
            "public TwoWay reverse MatchOnly exhaustion",
        );
    }

    /// A consequence of valid UTF-8 at every index, with no search index or
    /// needle in its definition. Continuation bytes add no constraint. A lead
    /// byte determines the width of its scalar and hence the next boundary.
    fn utf8_next_boundary_at(bytes: &[u8], i: usize) -> bool {
        if i >= bytes.len() {
            return true;
        }
        let width = lead_width(bytes[i]);
        width == 0
            || (width <= bytes.len() - i
                && (i + width == bytes.len() || !continuation(bytes[i + width])))
    }

    /// Instantiate an input validity fact at a computed index. Every valid
    /// haystack satisfies it at every index, even for an incorrect result.
    /// Bounds, equality of bytes, output boundaries and cursor state remain
    /// proof obligations; none of them is assumed here. The guards make this
    /// safe even when evaluating a contract on arbitrary stubbed outputs.
    pub(super) fn assume_utf8_at_match(h: &str, n: &str, step: SearchStep) {
        if let SearchStep::Match(a, b) = step {
            if n.len() >= 2 && a <= b && b <= h.len() && b - a == n.len() {
                let q = last_scalar_start(n.as_bytes());
                kani::assume(utf8_next_boundary_at(h.as_bytes(), a + q));
                kani::cover(true, "assume #99");
            }
        }
    }

    fn long_boundary_pre(h: &[u8], n: &[u8], start: usize, end: usize) -> bool {
        if start > end || end > h.len() || n.len() < 2 || end - start != n.len() {
            return false;
        }
        let last = last_scalar_start(n);
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        text.is_char_boundary(start)
            && lead_width(n[last]) == n.len() - last
            && h[start + last] == n[last]
            && utf8_next_boundary_at(h, start + last)
    }

    fn match_boundaries(h: &[u8], start: usize, end: usize) -> bool {
        let s = unsafe { crate::str::from_utf8_unchecked(h) };
        s.is_char_boundary(start) && s.is_char_boundary(end)
    }

    #[kani::requires(long_boundary_pre(h, n, start, end))]
    #[kani::ensures(|_| match_boundaries(h, start, end))]
    #[kani::modifies()]
    fn establish_long_match_boundaries(h: &[u8], n: &[u8], start: usize, end: usize) {
        assert!(match_boundaries(h, start, end));
        kani::cover(true, "assert #101");
    }

    #[kani::proof_for_contract(establish_long_match_boundaries)]
    #[kani::solver(cadical)]
    pub fn harness_long_match_boundary_lemma() {
        let h = any_str().as_bytes();
        let n = any_str().as_bytes();
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(long_boundary_pre(h, n, start, end));
        kani::cover(true, "assume #100");
        establish_long_match_boundaries(h, n, start, end);
        kani::cover(
            true,
            "contract proof returns: harness_long_match_boundary_lemma",
        );
    }

    fn check_match_start(h: &[u8], n: &[u8], start: usize, end: usize) {
        assert!(start < end && end <= h.len() && end - start == n.len());
        kani::cover(true, "assert #102");
        assert!(h[start] == n[0]);
        kani::cover(true, "assert #103");
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        assert!(text.is_char_boundary(start));
        kani::cover(true, "assert #104");
    }

    fn check_long_match(h: &[u8], n: &[u8], start: usize, end: usize) {
        assert!(start <= end && end <= h.len() && end - start == n.len());
        kani::cover(true, "assert #105");
        let last = last_scalar_start(n);
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        assert!(text.is_char_boundary(start));
        kani::cover(true, "assert #106");
        assert!(h[start + last] == n[last]);
        kani::cover(true, "assert #107");
        // A valid haystack satisfies this at every index, including any index
        // computed by the search. It does not assume that an endpoint is valid.
        kani::assume(utf8_next_boundary_at(h, start + last));
        kani::cover(true, "assume #101");
        establish_long_match_boundaries(h, n, start, end);
    }

    fn period_edge_facts(n: &str, period: usize) -> bool {
        let bytes = n.as_bytes();
        let len = bytes.len();
        if len < 2 || period == 0 || period > len {
            return false;
        }
        let q = last_scalar_start(bytes);
        lead_width(bytes[0]) != 0
            && lead_width(bytes[q]) == len - q
            && (period == len
                || (bytes[period] == bytes[0]
                    && (q < period
                        || (bytes[q - period] == bytes[q]
                            && utf8_next_boundary_at(bytes, q - period)))))
    }

    // Any true period of a valid UTF-8 word supplies these two byte
    // equalities. This lemma proves the boundary consequence, leaving the
    // constructor responsible for establishing the equalities themselves.
    #[kani::requires(period_edge_facts(n, period))]
    #[kani::ensures(|_| n.is_char_boundary(period) && n.is_char_boundary(n.len() - period))]
    #[kani::modifies()]
    fn establish_period_boundaries(n: &str, period: usize) {
        assert!(n.is_char_boundary(period));
        kani::cover(true, "assert #108");
        if period < n.len() {
            let q = last_scalar_start(n.as_bytes());
            assert!(q >= period);
            kani::cover(true, "assert #109");
        }
        assert!(n.is_char_boundary(n.len() - period));
        kani::cover(true, "assert #110");
    }

    #[kani::proof_for_contract(establish_period_boundaries)]
    pub fn harness_needle_period_boundaries() {
        let n = any_str();
        let period: usize = kani::any();
        kani::assume(period_edge_facts(n, period));
        kani::cover(true, "assume #102");
        establish_period_boundaries(n, period);
        kani::cover(period < n.len(), "a proper period");
        kani::cover(period == n.len(), "the full word is a period");
        kani::cover(
            true,
            "contract proof returns: harness_needle_period_boundaries",
        );
    }

    // Arbitrary numeric suffix results include the results of the actual
    // algorithm (harness_maximal_suffix_numeric_bounds). Holding each result
    // fixed for its order parameter also preserves repeated-call consistency.
    static mut LONG_SUFFIX_FALSE: (usize, usize) = (0, 1);
    static mut LONG_SUFFIX_TRUE: (usize, usize) = (0, 1);

    fn long_suffix_model_input(arr: &[u8], order: bool) -> bool {
        let result = unsafe {
            if order {
                LONG_SUFFIX_TRUE
            } else {
                LONG_SUFFIX_FALSE
            }
        };
        numeric_suffix_result(arr, result)
    }

    struct LongConstructorSuffixModel;
    impl LongConstructorSuffixModel {
        #[kani::requires(long_suffix_model_input(arr, order_greater))]
        #[kani::ensures(|result| result.0 < arr.len() && result.1 > 0
            && result.1 <= arr.len() - result.0)]
        #[kani::modifies()]
        fn maximal_suffix(arr: &[u8], order_greater: bool) -> (usize, usize) {
            let result = unsafe {
                if order_greater {
                    LONG_SUFFIX_TRUE
                } else {
                    LONG_SUFFIX_FALSE
                }
            };
            assert!(result.0 < arr.len() && result.1 > 0 && result.1 <= arr.len() - result.0);
            kani::cover(true, "assert #111");
            result
        }
    }

    #[kani::proof_for_contract(LongConstructorSuffixModel::maximal_suffix)]
    pub fn harness_long_suffix_model_contract() {
        let arr = any_nonempty_bytes();
        unsafe {
            LONG_SUFFIX_FALSE = kani::any();
            LONG_SUFFIX_TRUE = kani::any();
        }
        let order = kani::any();
        let _ = LongConstructorSuffixModel::maximal_suffix(arr, order);
        kani::cover(
            arr.len() > 4096 && order,
            "Long suffix adapter greater order",
        );
        kani::cover(
            arr.len() > 4096 && !order,
            "Long suffix adapter lesser order",
        );
        kani::cover(
            true,
            "contract proof returns: harness_long_suffix_model_contract",
        );
    }

    // This model describes the constructor's unequal-prefix case. A correct
    // equality test returns true for empty equal-length slices, so every
    // actual Long constructor has positive critical position. Check this
    // domain explicitly before selecting the unequal branch.
    fn long_constructor_prefix_unequal<T, U>(left: &[T], right: &[U]) -> bool {
        assert!(!left.is_empty() && left.len() == right.len());
        kani::cover(true, "assert #112");
        false
    }

    #[kani::proof]
    #[kani::stub(
        TwoWaySearcher::maximal_suffix,
        LongConstructorSuffixModel::maximal_suffix
    )]
    #[kani::stub(<[u8] as crate::cmp::PartialEq<[u8]>>::eq, long_constructor_prefix_unequal)]
    #[kani::stub_verified(TwoWaySearcher::byteset_create)]
    pub fn harness_long_constructor_from_numeric_suffixes() {
        let h = any_str();
        let n = any_nonempty_str();
        kani::assume(n.len() >= 2);
        kani::cover(true, "assume #103");
        let first: (usize, usize) = kani::any();
        let second: (usize, usize) = kani::any();
        kani::assume(first.0 < n.len() && first.1 > 0 && first.1 <= n.len() - first.0);
        kani::cover(true, "assume #104");
        kani::assume(second.0 < n.len() && second.1 > 0 && second.1 <= n.len() - second.0);
        kani::cover(true, "assume #105");
        let selected = if first.0 > second.0 { first } else { second };
        kani::assume(selected.0 > 0);
        kani::cover(true, "assume #106");
        unsafe {
            LONG_SUFFIX_FALSE = first;
            LONG_SUFFIX_TRUE = second;
        }
        let searcher = n.into_searcher(h);
        assert!(invariant(&searcher));
        kani::cover(true, "assert #113");
        let StrSearcherImpl::TwoWay(state) = &searcher.searcher else {
            unreachable!()
        };
        assert!(state.memory == usize::MAX && state.memory_back == usize::MAX);
        kani::cover(true, "assert #114");
        assert!(state.position == 0 && state.end == h.len());
        kani::cover(true, "assert #115");
        assert!(long_preprocessing_state(state, n.as_bytes()));
        kani::cover(true, "assert #116");
        kani::cover(
            n.len() > 4096,
            "Long constructor with arbitrary-length needle",
        );
        kani::cover(h.is_empty(), "Long constructor with empty haystack");
    }

    struct ConstructorUbModel;

    impl ConstructorUbModel {
        fn reverse_maximal_suffix(arr: &[u8], known_period: usize, _: bool) -> usize {
            assert!(!arr.is_empty() && 0 < known_period && known_period <= arr.len());
            kani::cover(true, "assert #117");
            let result: usize = kani::any();
            kani::assume(result < arr.len());
            kani::cover(true, "assume #107");
            result
        }
    }

    fn constructor_ub_prefix<T, U>(left: &[T], right: &[U]) -> bool {
        assert!(left.len() == right.len());
        kani::cover(true, "assert #118");
        kani::any()
    }

    // The numerical suffix summaries contain every actual preprocessing result.
    // Reverse bounds and its debug assertion require a genuine global period:
    // see harness_reverse_suffix_period_{false,true}, rather than an arbitrary
    // positive numeric argument. Both orders are part of this proof's dependency.
    // Full Short/Long C establishment is proved separately, with the stronger
    // period and UTF-8 facts. Here both constructor arms retain all UB checks.
    #[kani::proof]
    #[kani::stub(
        TwoWaySearcher::maximal_suffix,
        LongConstructorSuffixModel::maximal_suffix
    )]
    #[kani::stub(
        TwoWaySearcher::reverse_maximal_suffix,
        ConstructorUbModel::reverse_maximal_suffix
    )]
    #[kani::stub(<[u8] as crate::cmp::PartialEq<[u8]>>::eq, constructor_ub_prefix)]
    #[kani::stub_verified(TwoWaySearcher::byteset_create)]
    pub fn harness_two_way_constructor_extra_ub() {
        let h = any_str();
        let n = any_nonempty_str();
        kani::assume(n.len() >= 2);
        kani::cover(true, "assume #108");
        let first: (usize, usize) = kani::any();
        let second: (usize, usize) = kani::any();
        kani::assume(first.0 < n.len() && 0 < first.1 && first.1 <= n.len() - first.0);
        kani::cover(true, "assume #109");
        kani::assume(second.0 < n.len() && 0 < second.1 && second.1 <= n.len() - second.0);
        kani::cover(true, "assume #110");
        unsafe {
            LONG_SUFFIX_FALSE = first;
            LONG_SUFFIX_TRUE = second;
        }
        let s = n.into_searcher(h);
        let StrSearcherImpl::TwoWay(state) = &s.searcher else {
            unreachable!()
        };
        kani::cover(
            state.memory == usize::MAX && n.len() > 4096,
            "Long constructor UB",
        );
        kani::cover(state.memory == 0 && n.len() > 4096, "Short constructor UB");
        kani::cover(h.is_empty(), "constructor with an empty haystack");
    }

    static mut SHORT_SUFFIX_FALSE: (usize, usize) = (0, 1);
    static mut SHORT_SUFFIX_TRUE: (usize, usize) = (0, 1);
    static mut SHORT_REVERSE_FALSE: usize = 0;
    static mut SHORT_REVERSE_TRUE: usize = 0;

    fn short_suffix_model_input(arr: &[u8], order: bool) -> bool {
        let saved = unsafe { SHORT_CERTIFICATE };
        let result = unsafe {
            if order {
                SHORT_SUFFIX_TRUE
            } else {
                SHORT_SUFFIX_FALSE
            }
        };
        arr.as_ptr() == saved.0 && arr.len() == saved.1 && numeric_suffix_result(arr, result)
    }

    struct ShortConstructorSuffixModel;
    impl ShortConstructorSuffixModel {
        #[kani::requires(short_suffix_model_input(arr, order))]
        #[kani::ensures(|result| result.0 < arr.len() && result.1 > 0
            && result.1 <= arr.len() - result.0)]
        #[kani::modifies()]
        fn maximal_suffix(arr: &[u8], order: bool) -> (usize, usize) {
            let saved = unsafe { SHORT_CERTIFICATE };
            assert!(arr.as_ptr() == saved.0 && arr.len() == saved.1);
            kani::cover(true, "assert #119");
            let result = unsafe {
                if order {
                    SHORT_SUFFIX_TRUE
                } else {
                    SHORT_SUFFIX_FALSE
                }
            };
            assert!(result.0 < arr.len() && 0 < result.1 && result.1 <= arr.len() - result.0);
            kani::cover(true, "assert #120");
            result
        }
        fn reverse_maximal_suffix(arr: &[u8], known_period: usize, order: bool) -> usize {
            let saved = unsafe { SHORT_CERTIFICATE };
            assert!(arr.as_ptr() == saved.0 && arr.len() == saved.1 && known_period == saved.3);
            kani::cover(true, "assert #121");
            let result = unsafe {
                if order {
                    SHORT_REVERSE_TRUE
                } else {
                    SHORT_REVERSE_FALSE
                }
            };
            assert!(result < known_period);
            kani::cover(true, "assert #122");
            result
        }
    }

    #[kani::proof_for_contract(ShortConstructorSuffixModel::maximal_suffix)]
    pub fn harness_short_suffix_model_contract() {
        let arr = any_nonempty_bytes();
        unsafe {
            SHORT_CERTIFICATE = (arr.as_ptr(), arr.len(), kani::any(), kani::any());
            SHORT_SUFFIX_FALSE = kani::any();
            SHORT_SUFFIX_TRUE = kani::any();
        }
        let order = kani::any();
        let _ = ShortConstructorSuffixModel::maximal_suffix(arr, order);
        kani::cover(
            arr.len() > 4096 && order,
            "Short suffix adapter greater order",
        );
        kani::cover(
            arr.len() > 4096 && !order,
            "Short suffix adapter lesser order",
        );
        kani::cover(
            true,
            "contract proof returns: harness_short_suffix_model_contract",
        );
    }

    // Select the Short arm. Correct slice equality returns true on every
    // actual Short execution; the full prefix equality is a certificate input.
    fn short_constructor_prefix_equal<T, U>(left: &[T], right: &[U]) -> bool {
        assert!(left.len() == right.len());
        kani::cover(true, "assert #123");
        true
    }

    #[kani::proof]
    #[kani::stub(
        TwoWaySearcher::maximal_suffix,
        ShortConstructorSuffixModel::maximal_suffix
    )]
    #[kani::stub(
        TwoWaySearcher::reverse_maximal_suffix,
        ShortConstructorSuffixModel::reverse_maximal_suffix
    )]
    #[kani::stub(<[u8] as crate::cmp::PartialEq<[u8]>>::eq, short_constructor_prefix_equal)]
    #[kani::stub_verified(certify_short_period)]
    #[kani::stub_verified(reverse_suffix_period)]
    #[kani::stub_verified(read_range_agreement)]
    #[kani::stub_verified(establish_period_boundaries)]
    #[kani::stub_verified(TwoWaySearcher::byteset_create)]
    #[kani::stub(suffix_result, short_certificate_suffix)]
    #[kani::stub(word_prefix_equal, short_certificate_prefix)]
    #[kani::stub(word_root_dominance, root_dominance_shape)]
    #[kani::stub(word_earlier_dominance, earlier_dominance_shape)]
    #[kani::stub(range_agreement, short_certificate_period)]
    pub fn harness_short_constructor_from_preprocessing() {
        let h = any_str();
        let n = any_nonempty_str();
        kani::assume(n.len() >= 2);
        kani::cover(true, "assume #111");
        let bytes = n.as_bytes();
        let first: (usize, usize) = kani::any();
        let second: (usize, usize) = kani::any();
        kani::assume(first.0 < n.len() && 0 < first.1 && first.1 <= n.len() - first.0);
        kani::cover(true, "assume #112");
        kani::assume(second.0 < n.len() && 0 < second.1 && second.1 <= n.len() - second.0);
        kani::cover(true, "assume #113");
        let (selected, order) = if first.0 > second.0 {
            (first, false)
        } else {
            (second, true)
        };
        let (critical, period) = selected;
        unsafe {
            SHORT_CERTIFICATE = (bytes.as_ptr(), bytes.len(), critical, period);
            ROOT_DOMINANCE_CALL = (bytes.as_ptr(), bytes.len(), critical, period, order);
            EARLIER_DOMINANCE_CALL = (bytes.as_ptr(), bytes.len(), critical, order);
            SHORT_SUFFIX_FALSE = first;
            SHORT_SUFFIX_TRUE = second;
        }
        // These are precisely the proved maximal_suffix postconditions and
        // the true prefix test selecting Short. They do not assume C.
        kani::assume(suffix_result(bytes, selected));
        kani::cover(true, "assume #114");
        kani::assume(word_root_dominance(bytes, critical, period, order));
        kani::cover(true, "assume #115");
        kani::assume(word_earlier_dominance(bytes, critical, order));
        kani::cover(true, "assume #116");
        kani::assume(word_prefix_equal(bytes, 0, period, critical));
        kani::cover(true, "assume #117");
        certify_short_period(bytes, critical, period, order);
        let backward_false = reverse_suffix_period(bytes, period, false);
        let backward_true = reverse_suffix_period(bytes, period, true);
        unsafe {
            SHORT_REVERSE_FALSE = backward_false;
            SHORT_REVERSE_TRUE = backward_true;
        }

        // Local consequences of a valid UTF-8 input, as allowed by the
        // challenge. Byte equalities come from the proved global period.
        let last = last_scalar_start(bytes);
        kani::assume(lead_width(bytes[0]) != 0);
        kani::cover(true, "assume #118");
        kani::assume(lead_width(bytes[last]) == bytes.len() - last);
        kani::cover(true, "assume #119");
        if period < bytes.len() {
            read_range_agreement(bytes, period, bytes.len(), period, period);
            if last >= period {
                read_range_agreement(bytes, period, bytes.len(), period, last);
                kani::assume(utf8_next_boundary_at(bytes, last - period));
                kani::cover(true, "assume #120");
            }
        }
        assert!(period_edge_facts(n, period));
        kani::cover(true, "assert #124");
        establish_period_boundaries(n, period);

        let searcher = n.into_searcher(h);
        assert!(invariant(&searcher));
        kani::cover(true, "assert #125");
        let StrSearcherImpl::TwoWay(state) = &searcher.searcher else {
            unreachable!()
        };
        assert!(state.memory == 0 && state.memory_back == n.len());
        kani::cover(true, "assert #126");
        assert!(state.position == 0 && state.end == h.len());
        kani::cover(true, "assert #127");
        assert!(short_state(state, h.as_bytes(), bytes));
        kani::cover(true, "assert #128");
        kani::cover(
            n.len() > 4096,
            "complete Short constructor at symbolic needle length",
        );
        kani::cover(h.is_empty(), "Short constructor with empty haystack");
        kani::cover(
            critical > 0 && lead_width(bytes[last]) > 1,
            "non-ASCII Short needle with a positive critical point",
        );
    }

    // Static relations assigned by the actual long-period constructor,
    // established by harness_long_constructor_from_numeric_suffixes.
    pub(super) fn long_preprocessing_state(s: &TwoWaySearcher, n: &[u8]) -> bool {
        let len = n.len();
        s.crit_pos > 0
            && s.crit_pos < len
            && s.crit_pos_back == s.crit_pos
            && s.period == cmp::max(s.crit_pos, len - s.crit_pos) + 1
    }

    fn any_long_searcher(h: &[u8], n: &[u8]) -> TwoWaySearcher {
        kani::assume(n.len() >= 2);
        kani::cover(true, "assume #121");
        let critical: usize = kani::any();
        kani::assume(critical > 0 && critical < n.len());
        kani::cover(true, "assume #122");
        let s = TwoWaySearcher {
            crit_pos: critical,
            crit_pos_back: critical,
            period: cmp::max(critical, n.len() - critical) + 1,
            byteset: kani::any(),
            position: kani::any(),
            end: kani::any(),
            memory: usize::MAX,
            memory_back: usize::MAX,
        };
        kani::assume(s.position <= h.len() && s.end <= h.len());
        kani::cover(true, "assume #123");
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        kani::assume(text.is_char_boundary(s.position) && text.is_char_boundary(s.end));
        kani::cover(true, "assume #124");
        assert!(long_preprocessing_state(&s, n));
        kani::cover(true, "assert #129");
        s
    }

    fn any_long_str_searcher() -> StrSearcher<'static, 'static> {
        let haystack = any_str();
        let needle = any_str();
        kani::assume(needle.len() >= 2);
        kani::cover(true, "assume #125");
        kani::assume(lead_width(needle.as_bytes()[0]) != 0);
        kani::cover(true, "assume #126");
        let searcher =
            StrSearcherImpl::TwoWay(any_long_searcher(haystack.as_bytes(), needle.as_bytes()));
        let s = StrSearcher {
            haystack,
            needle,
            searcher,
        };
        assert!(supported_contract_state(&s));
        kani::cover(true, "assert #130");
        s
    }

    #[kani::proof_for_contract(<StrSearcher as ReverseSearcher>::next_back)]
    #[kani::stub(str::floor_char_boundary, floor_char_boundary)]
    #[kani::stub_verified(verified_floor_boundary)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub(short_scan_probes, reject_short_probe_in_long_proof)]
    pub fn harness_str_searcher_long_next_back() {
        let mut s = any_long_str_searcher();
        let step = s.next_back();
        // proof_for_contract checks C and both returned boundaries.
        kani::cover(
            matches!(step, SearchStep::Match(a, _) if a > 4096),
            "distant long-period reverse match",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(_, _)),
            "long-period reverse rejection",
        );
        kani::cover(
            matches!(step, SearchStep::Done),
            "long-period reverse exhaustion",
        );
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_long_next_back",
        );
    }

    fn check_public_long_next(split: u8) {
        let mut s = any_long_str_searcher();
        assume_needle_edges(s.needle.as_bytes());
        let StrSearcherImpl::TwoWay(t) = &s.searcher else {
            unreachable!()
        };
        assume_long_split(t, s.needle.as_bytes(), false, split);
        // Both callers are proof_for_contract harnesses. The public
        // postcondition already checks the full C and step_ok.
        let _ = s.next();
        kani::cover(
            s.haystack.len() == MAX_ALLOCATION_BYTES,
            "public Long next reaches the largest haystack in the CI pointer model",
        );
        kani::cover(
            s.needle.len() == MAX_ALLOCATION_BYTES,
            "public Long next reaches the largest needle in the CI pointer model",
        );
    }

    #[kani::proof_for_contract(<StrSearcher as Searcher>::next)]
    #[kani::stub(str::ceil_char_boundary, ceil_char_boundary)]
    #[kani::stub_verified(verified_ceil_boundary)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub(short_scan_probes, reject_short_probe_in_long_proof)]
    pub fn harness_str_searcher_long_next_split_probes() {
        check_public_long_next(1);
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_long_next_split_probes",
        );
    }

    #[kani::proof_for_contract(<StrSearcher as Searcher>::next)]
    #[kani::stub(str::ceil_char_boundary, ceil_char_boundary)]
    #[kani::stub_verified(verified_ceil_boundary)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub(short_scan_probes, reject_short_probe_in_long_proof)]
    pub fn harness_str_searcher_long_next_left_probes() {
        check_public_long_next(2);
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_long_next_left_probes",
        );
    }

    #[kani::proof]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    pub fn harness_str_searcher_long_next_reject() {
        let mut s = any_long_str_searcher();
        let result = s.next_reject();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(supported_contract_state(&s));
        kani::cover(true, "assert #131");
        kani::cover(
            result.is_some_and(|(a, _)| a > 4096),
            "distant long-period rejection",
        );
        kani::cover(result.is_none(), "long-period rejection exhaustion");
    }

    #[kani::proof]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    pub fn harness_str_searcher_long_next_reject_back() {
        let mut s = any_long_str_searcher();
        let result = s.next_reject_back();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(supported_contract_state(&s));
        kani::cover(true, "assert #132");
        kani::cover(
            result.is_some_and(|(a, _)| a > 4096),
            "distant long-period reverse rejection",
        );
        kani::cover(result.is_none(), "long-period reverse rejection exhaustion");
    }

    fn any_short_str_searcher() -> StrSearcher<'static, 'static> {
        let haystack = any_str();
        let needle = any_str();
        let searcher =
            StrSearcherImpl::TwoWay(any_short_searcher(haystack.as_bytes(), needle.as_bytes()));
        let s = StrSearcher {
            haystack,
            needle,
            searcher,
        };
        assert!(invariant(&s));
        kani::cover(true, "assert #133");
        s
    }

    fn any_short_reverse_str_searcher() -> StrSearcher<'static, 'static> {
        let haystack = any_str();
        let needle = any_str();
        let searcher = StrSearcherImpl::TwoWay(any_short_reverse_searcher(
            haystack.as_bytes(),
            needle.as_bytes(),
        ));
        let s = StrSearcher {
            haystack,
            needle,
            searcher,
        };
        assert!(invariant(&s));
        kani::cover(true, "assert #134");
        s
    }

    #[kani::proof_for_contract(<StrSearcher as Searcher>::next)]
    #[kani::stub(str::ceil_char_boundary, ceil_char_boundary)]
    #[kani::stub_verified(verified_ceil_boundary)]
    #[kani::stub(TwoWaySearcher::next, model_raw_forward)]
    #[kani::stub_verified(verified_raw_forward)]
    #[kani::stub_verified(establish_last_scalar_bound)]
    pub fn harness_str_searcher_short_next() {
        let mut s = any_short_str_searcher();
        // proof_for_contract checks the full postcondition, including the
        // output boundaries and C; avoid repeating the same expression here.
        let step = s.next();
        kani::cover(
            matches!(step, SearchStep::Match(a, b) if a > 4096 && b > a),
            "distant short-period match",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if b > a),
            "short-period rejection",
        );
        kani::cover(matches!(step, SearchStep::Done), "short-period exhaustion");
        kani::cover(
            matches!(step, SearchStep::Match(_, _)) && s.needle.as_bytes()[0] >= 128,
            "non-ASCII short-period match",
        );
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_short_next",
        );
    }

    // The independently proved raw contract handles every Short state;
    // this proof checks public dispatch and boundary rounding.
    #[kani::proof_for_contract(<StrSearcher as ReverseSearcher>::next_back)]
    #[kani::stub(TwoWaySearcher::next_back, model_raw_reverse)]
    #[kani::stub_verified(verified_raw_reverse)]
    #[kani::stub(str::floor_char_boundary, floor_char_boundary)]
    #[kani::stub_verified(verified_floor_boundary)]
    pub fn harness_str_searcher_short_next_back() {
        let mut s = any_short_reverse_str_searcher();
        let step = s.next_back();
        kani::cover(
            matches!(step, SearchStep::Match(a, b) if a > 4096 && b > a),
            "distant short-period match",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(a, b) if b > a),
            "short-period rejection",
        );
        kani::cover(matches!(step, SearchStep::Done), "short-period exhaustion");
        kani::cover(
            matches!(step, SearchStep::Match(_, _)) && s.needle.as_bytes()[0] >= 128,
            "non-ASCII short-period match",
        );
        kani::cover(
            true,
            "contract proof returns: harness_str_searcher_short_next_back",
        );
    }

    #[kani::proof]
    #[kani::stub_verified(establish_long_match_boundaries)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    #[kani::stub_verified(establish_last_scalar_bound)]
    #[kani::stub(TwoWaySearcher::next, model_raw_forward)]
    #[kani::stub_verified(verified_raw_forward)]
    pub fn harness_str_searcher_short_next_match() {
        let mut s = any_short_str_searcher();
        if let Some((a, b)) = s.next_match() {
            let StrSearcherImpl::TwoWay(t) = &s.searcher else {
                unreachable!()
            };
            assert!(t.position == b);
            kani::cover(true, "assert #135");
            check_short_match(s.haystack.as_bytes(), s.needle.as_bytes(), a, b);
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #136");
    }

    #[kani::proof]
    #[kani::stub_verified(establish_long_match_boundaries)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memchr)]
    #[kani::stub(TwoWaySearcher::next_back, model_raw_reverse)]
    #[kani::stub_verified(verified_raw_reverse)]
    pub fn harness_str_searcher_short_next_match_back() {
        // Reverse matching needs the last-scalar fact, but none of the
        // forward-specific period/last-boundary derivations.
        let mut s = any_short_reverse_str_searcher();
        assume_needle_edges(s.needle.as_bytes());
        let result = s.next_match_back();
        if let Some((a, b)) = result {
            let StrSearcherImpl::TwoWay(t) = &s.searcher else {
                unreachable!()
            };
            assert!(t.end == a);
            kani::cover(true, "assert #137");
            check_short_match(s.haystack.as_bytes(), s.needle.as_bytes(), a, b);
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #138");
        kani::cover(
            result.is_some_and(|(a, _)| a > 4096),
            "distant short-period reverse match",
        );
        kani::cover(result.is_none(), "short-period reverse match exhaustion");
        kani::cover(
            result.is_some() && s.needle.as_bytes()[0] >= 128,
            "non-ASCII short-period reverse match",
        );
    }

    // A filter needs the step's state, endpoints and frame, but not the
    // internal UTF-8 instantiation in the general public-step contract.
    // Prove this smaller interface once before using it in the real loop.
    fn short_filter_state(s: &StrSearcher<'_, '_>) -> bool {
        matches!(&s.searcher, StrSearcherImpl::TwoWay(t) if t.memory != usize::MAX) && invariant(s)
    }

    #[kani::requires(short_filter_state(s))]
    #[kani::ensures(|step| short_filter_state(s) && step_ok(s.haystack, *step))]
    #[kani::modifies(front_cursor(s), front_memory(s))]
    fn verified_short_filter_next(s: &mut StrSearcher<'_, '_>) -> SearchStep {
        s.next()
    }

    #[kani::requires(short_filter_state(s))]
    #[kani::ensures(|step| short_filter_state(s) && step_ok(s.haystack, *step))]
    #[kani::modifies(back_cursor(s), back_memory(s))]
    fn verified_short_filter_next_back(s: &mut StrSearcher<'_, '_>) -> SearchStep {
        s.next_back()
    }

    #[kani::proof_for_contract(verified_short_filter_next)]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    #[kani::stub_verified(establish_last_scalar_bound)]
    pub fn harness_short_filter_next_contract() {
        let mut s = any_short_str_searcher();
        let result = verified_short_filter_next(&mut s);
        kani::cover(
            matches!(result, SearchStep::Match(_, _)),
            "Short filter match step",
        );
        kani::cover(
            matches!(result, SearchStep::Reject(_, _)),
            "Short filter reject step",
        );
        kani::cover(
            matches!(result, SearchStep::Done),
            "Short filter exhausted step",
        );
        kani::cover(
            true,
            "contract proof returns: harness_short_filter_next_contract",
        );
    }

    #[kani::proof_for_contract(verified_short_filter_next_back)]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    pub fn harness_short_filter_next_back_contract() {
        let mut s = any_short_reverse_str_searcher();
        let result = verified_short_filter_next_back(&mut s);
        kani::cover(
            matches!(result, SearchStep::Match(_, _)),
            "Short reverse filter match step",
        );
        kani::cover(
            matches!(result, SearchStep::Reject(_, _)),
            "Short reverse filter reject step",
        );
        kani::cover(
            matches!(result, SearchStep::Done),
            "Short reverse filter exhausted step",
        );
        kani::cover(
            true,
            "contract proof returns: harness_short_filter_next_back_contract",
        );
    }

    struct ShortFilterModel;
    impl ShortFilterModel {
        // Match the contracted target's name and early-bound lifetimes so
        // Kani can resolve its generated contract closures after stubbing.
        // Reflexive lifetime bounds do not constrain either input string.
        #[kani::requires(short_filter_state(s))]
        #[kani::ensures(|step| short_filter_state(s) && step_ok(s.haystack, *step))]
        #[kani::modifies(front_cursor(s), front_memory(s))]
        fn next<'a: 'a, 'b: 'b>(s: &mut StrSearcher<'a, 'b>) -> SearchStep {
            verified_short_filter_next(s)
        }

        #[kani::requires(short_filter_state(s))]
        #[kani::ensures(|step| short_filter_state(s) && step_ok(s.haystack, *step))]
        #[kani::modifies(back_cursor(s), back_memory(s))]
        fn next_back<'a: 'a, 'b: 'b>(s: &mut StrSearcher<'a, 'b>) -> SearchStep {
            verified_short_filter_next_back(s)
        }
    }

    #[kani::proof_for_contract(ShortFilterModel::next)]
    #[kani::stub_verified(verified_short_filter_next)]
    pub fn harness_short_filter_model_next_contract() {
        let mut s = any_short_str_searcher();
        let result = ShortFilterModel::next(&mut s);
        kani::cover(
            matches!(result, SearchStep::Match(_, _)),
            "Short adapter match",
        );
        kani::cover(
            matches!(result, SearchStep::Reject(_, _)),
            "Short adapter reject",
        );
        kani::cover(matches!(result, SearchStep::Done), "Short adapter done");
        kani::cover(
            true,
            "contract proof returns: harness_short_filter_model_next_contract",
        );
    }

    #[kani::proof_for_contract(ShortFilterModel::next_back)]
    #[kani::stub_verified(verified_short_filter_next_back)]
    pub fn harness_short_filter_model_next_back_contract() {
        let mut s = any_short_reverse_str_searcher();
        let result = ShortFilterModel::next_back(&mut s);
        kani::cover(
            matches!(result, SearchStep::Match(_, _)),
            "Short reverse adapter match",
        );
        kani::cover(
            matches!(result, SearchStep::Reject(_, _)),
            "Short reverse adapter reject",
        );
        kani::cover(
            matches!(result, SearchStep::Done),
            "Short reverse adapter done",
        );
        kani::cover(
            true,
            "contract proof returns: harness_short_filter_model_next_back_contract",
        );
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as Searcher>::next, ShortFilterModel::next)]
    #[kani::stub_verified(verified_short_filter_next)]
    #[kani::stub_verified(establish_last_scalar_bound)]
    pub fn harness_str_searcher_short_next_reject() {
        let mut s = any_short_str_searcher();
        let result = s.next_reject();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #139");
        kani::cover(
            result.is_some_and(|(a, _)| a > 4096),
            "distant short-period rejection",
        );
        kani::cover(result.is_none(), "short-period rejection exhaustion");
    }

    #[kani::proof]
    #[kani::stub(<StrSearcher as ReverseSearcher>::next_back, ShortFilterModel::next_back)]
    #[kani::stub_verified(verified_short_filter_next_back)]
    pub fn harness_str_searcher_short_next_reject_back() {
        let mut s = any_short_reverse_str_searcher();
        let result = s.next_reject_back();
        if let Some((a, b)) = result {
            check_step(s.haystack, SearchStep::Reject(a, b));
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #140");
        kani::cover(
            result.is_some_and(|(a, _)| a > 4096),
            "distant short-period reverse rejection",
        );
        kani::cover(
            result.is_none(),
            "short-period reverse rejection exhaustion",
        );
    }

    // The two disjoint cases cover every positive critical position in the
    // candidate long-period type invariant. No string-length bound is added.
    fn assume_long_split(s: &TwoWaySearcher, n: &[u8], reverse: bool, split: u8) {
        let critical = if reverse { s.crit_pos_back } else { s.crit_pos };
        let last = last_scalar_start(n);
        kani::assume(match split {
            0 => critical == 0,
            1 => critical > 0 && critical <= last,
            2 => critical > last,
            _ => false,
        });
        kani::cover(true, "assume #127");
    }

    fn check_long_public_match(split: u8) {
        let mut s = any_long_str_searcher();
        assume_needle_edges(s.needle.as_bytes());
        let StrSearcherImpl::TwoWay(t) = &s.searcher else {
            unreachable!()
        };
        assume_long_split(t, s.needle.as_bytes(), false, split);
        let result = s.next_match();
        if let Some((a, b)) = result {
            check_match_start(s.haystack.as_bytes(), s.needle.as_bytes(), a, b);
            check_long_match(s.haystack.as_bytes(), s.needle.as_bytes(), a, b);
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #141");
    }

    fn check_long_public_match_back(split: u8) {
        let mut s = any_long_str_searcher();
        assume_needle_edges(s.needle.as_bytes());
        let StrSearcherImpl::TwoWay(t) = &s.searcher else {
            unreachable!()
        };
        assume_long_split(t, s.needle.as_bytes(), true, split);
        let result = s.next_match_back();
        if let Some((a, b)) = result {
            check_match_start(s.haystack.as_bytes(), s.needle.as_bytes(), a, b);
            check_long_match(s.haystack.as_bytes(), s.needle.as_bytes(), a, b);
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #142");
    }

    #[kani::proof]
    #[kani::stub_verified(establish_long_match_boundaries)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    #[kani::stub(short_scan_probes, reject_short_probe_in_long_proof)]
    pub fn harness_str_searcher_long_next_match_split_probes() {
        check_long_public_match(1);
    }

    #[kani::proof]
    #[kani::stub_verified(establish_long_match_boundaries)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(<StrSearcher as Searcher>::next)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    #[kani::stub(short_scan_probes, reject_short_probe_in_long_proof)]
    pub fn harness_str_searcher_long_next_match_left_probes() {
        let mut s = any_long_str_searcher();
        let haystack = s.haystack;
        let needle = s.needle;
        assume_needle_edges(needle.as_bytes());
        let StrSearcherImpl::TwoWay(t) = &s.searcher else {
            unreachable!()
        };
        kani::assume(t.crit_pos > last_scalar_start(needle.as_bytes()));
        kani::cover(true, "assume #128");
        let result = s.next_match();
        let StrSearcherImpl::TwoWay(t) = &s.searcher else {
            unreachable!()
        };
        if let Some((a, b)) = result {
            assert!(t.position == b);
            kani::cover(true, "assert #143");
            check_match_start(haystack.as_bytes(), needle.as_bytes(), a, b);
            check_long_match(haystack.as_bytes(), needle.as_bytes(), a, b);
        } else {
            assert!(t.position == haystack.len());
            kani::cover(true, "assert #144");
        }
        assert!(invariant(&s));
        kani::cover(true, "assert #145");
    }

    #[kani::proof]
    #[kani::stub_verified(establish_long_match_boundaries)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memchr)]
    #[kani::stub(short_scan_probes, reject_short_probe_in_long_proof)]
    pub fn harness_str_searcher_long_next_match_back_split_probes() {
        check_long_public_match_back(1);
    }

    #[kani::proof]
    #[kani::stub_verified(establish_long_match_boundaries)]
    #[kani::stub_verified(TwoWaySearcher::byteset_contains)]
    #[kani::stub_verified(<StrSearcher as ReverseSearcher>::next_back)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memchr)]
    #[kani::stub(short_scan_probes, reject_short_probe_in_long_proof)]
    pub fn harness_str_searcher_long_next_match_back_left_probes() {
        check_long_public_match_back(2);
    }

    // Existential witnesses use concrete ASCII / non-ASCII needles and the
    // real byteset filter. They supplement the symbolic-needle proofs.
    #[kani::proof]
    #[kani::stub(str::ceil_char_boundary, ceil_char_boundary)]
    #[kani::stub_verified(verified_ceil_boundary)]
    pub fn harness_str_searcher_long_coverage() {
        let non_ascii: bool = kani::any();
        let needle = if non_ascii { "é" } else { "ab" };
        let haystack = any_str();
        let mut t = any_long_searcher(haystack.as_bytes(), needle.as_bytes());
        // Exact two-byte mask. The producer's arbitrary-length fold has its
        // own callback/frame proof; the filter below is the real implementation.
        t.byteset =
            (1u64 << (needle.as_bytes()[0] & 0x3f)) | (1u64 << (needle.as_bytes()[1] & 0x3f));
        let mut s = StrSearcher {
            haystack,
            needle,
            searcher: StrSearcherImpl::TwoWay(t),
        };
        let step = s.next();
        assume_utf8_at_match(s.haystack, s.needle, step);
        check_step(s.haystack, step);
        assert!(invariant(&s));
        kani::cover(true, "assert #146");
        kani::cover(
            non_ascii && matches!(step, SearchStep::Match(a, _) if a > 4096),
            "distant non-ASCII match",
        );
        kani::cover(
            !non_ascii && matches!(step, SearchStep::Match(a, _) if a > 4096),
            "distant ASCII match",
        );
        kani::cover(
            matches!(step, SearchStep::Reject(_, _)),
            "actual filter rejects",
        );
        kani::cover(matches!(step, SearchStep::Done), "public exhaustion");
    }

    fn any_short_searcher(h: &[u8], n: &[u8]) -> TwoWaySearcher {
        assume_needle_edges(n);
        let s = any_raw_searcher(h, n, false);
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        kani::assume(text.is_char_boundary(s.position) && text.is_char_boundary(s.end));
        kani::cover(true, "assume #129");
        // The last boundary cannot precede another in-bounds boundary.
        // Derive this from the candidate boundary at n.len()-period.
        let needle = unsafe { crate::str::from_utf8_unchecked(n) };
        establish_last_scalar_bound(needle, n.len() - s.period);
        if s.period < n.len() {
            establish_last_scalar_bound(needle, s.period);
        }
        let last = last_scalar_start(n);
        assert!(last >= n.len() - s.period);
        kani::cover(true, "assert #147");
        assert!(s.crit_pos <= last);
        kani::cover(true, "assert #148");
        assert!(s.period == n.len() || s.period <= last);
        kani::cover(true, "assert #149");
        s
    }

    fn any_short_reverse_searcher(h: &[u8], n: &[u8]) -> TwoWaySearcher {
        let s = any_raw_searcher(h, n, false);
        kani::assume(lead_width(n[0]) != 0);
        kani::cover(true, "assume #130");
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        kani::assume(text.is_char_boundary(s.position) && text.is_char_boundary(s.end));
        kani::cover(true, "assume #131");
        s
    }

    fn check_short_match(h: &[u8], n: &[u8], a: usize, b: usize) {
        assert!(a < b && b <= h.len() && b - a == n.len());
        kani::cover(true, "assert #150");
        let text = unsafe { crate::str::from_utf8_unchecked(h) };
        assert!(text.is_char_boundary(a));
        kani::cover(true, "assert #151");
        // Cached reverse comparisons may already establish the old end as a
        // boundary. Otherwise the compared last-scalar lead must justify it.
        if !text.is_char_boundary(b) {
            check_long_match(h, n, a, b);
        }
        assert!(text.is_char_boundary(b));
        kani::cover(true, "assert #152");
    }

    // Challenge assumption 1 covers the slice iterator implementation. For
    // this pure zero-capture callback, arbitrary arguments cover every fold
    // invocation; executing the real callback checks its arithmetic and frame.
    // The accumulator result is intentionally unrestricted for safety-only C.
    struct SliceFoldModel<'a, T: 'a>(crate::marker::PhantomData<&'a T>);

    impl<'a, T: 'a> SliceFoldModel<'a, T> {
        fn fold<B, F>(iter: crate::slice::Iter<'a, T>, _initial: B, mut f: F) -> B
        where
            B: kani::Arbitrary,
            F: FnMut(B, &'a T) -> B,
        {
            assert!(crate::mem::size_of::<F>() == 0);
            kani::cover(true, "assert #153");
            assert!(crate::mem::size_of::<T>() == 1 && crate::mem::align_of::<T>() == 1);
            kani::cover(true, "assert #154");
            let bytes = iter.as_slice();
            if !bytes.is_empty() {
                let index: usize = kani::any();
                kani::assume(index < bytes.len());
                kani::cover(true, "assume #132");
                let _ = f(kani::any(), &bytes[index]);
            }
            kani::any()
        }
    }

    #[kani::proof_for_contract(TwoWaySearcher::byteset_create)]
    #[kani::stub(<crate::slice::Iter<'_, u8> as crate::iter::Iterator>::fold, SliceFoldModel::fold)]
    pub fn harness_two_way_byteset_create() {
        let bytes = any_str().as_bytes();
        let _ = TwoWaySearcher::byteset_create(bytes);
        kani::cover(bytes.len() > 4096, "long input to the bit-set callback");
        kani::cover(bytes.is_empty(), "empty bit-set input");
        kani::cover(
            true,
            "contract proof returns: harness_two_way_byteset_create",
        );
    }

    // For search safety either filter answer is conservative: rejecting a
    // candidate may miss a match, but cannot invent an unsafe matching range.
    // First verify that the real bit-set test itself is safe and read-only.
    #[kani::proof_for_contract(TwoWaySearcher::byteset_contains)]
    pub fn harness_two_way_byteset_contains() {
        let searcher = TwoWaySearcher {
            crit_pos: kani::any(),
            crit_pos_back: kani::any(),
            period: kani::any(),
            byteset: kani::any(),
            position: kani::any(),
            end: kani::any(),
            memory: kani::any(),
            memory_back: kani::any(),
        };
        let _ = searcher.byteset_contains(kani::any());
        kani::cover(
            true,
            "contract proof returns: harness_two_way_byteset_contains",
        );
    }
}
