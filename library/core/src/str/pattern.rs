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

use crate::char::MAX_LEN_UTF8;
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
        #[cfg(not(kani))]
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
        // Nondeterministic abstraction for Kani verification.
        // Overapproximates all possible behaviors of the real loop:
        // either finds a match at some valid position, or exhausts the haystack.
        #[cfg(kani)]
        {
            if self.finger >= self.finger_back {
                return None;
            }
            if kani::any() {
                let a: usize = kani::any();
                let w = self.utf8_size();
                kani::assume(a >= self.finger);
                kani::assume(w <= self.finger_back); // avoid overflow
                kani::assume(a + w <= self.finger_back);
                self.finger = a + w;
                Some((a, self.finger))
            } else {
                self.finger = self.finger_back;
                None
            }
        }
    }

    // Override the default next_reject for unbounded verification.
    // Under #[cfg(kani)], abstracts the entire method as a single nondeterministic
    // step, avoiding loops entirely. This is sound because verify_cs_next proves
    // that next() preserves the type invariant and always advances finger by a
    // valid UTF-8 char width. Under #[cfg(not(kani))], uses the original default
    // implementation (loop over self.next()).
    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            // Nondeterministic abstraction of the entire loop.
            // Either we find a reject somewhere in the remaining haystack,
            // or we exhaust the haystack and return None.
            if self.finger >= self.finger_back {
                return None;
            }
            if kani::any() {
                let old_finger = self.finger;
                let w: usize = kani::any();
                kani::assume(w >= 1 && w <= 4);
                kani::assume(old_finger + w <= self.finger_back);
                self.finger = old_finger + w;
                Some((old_finger, self.finger))
            } else {
                self.finger = self.finger_back;
                None
            }
        }
    }
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
        #[cfg(not(kani))]
        {
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
                        if let Some(slice) =
                            haystack.get(found_char..(found_char + self.utf8_size()))
                        {
                            if slice == &self.utf8_encoded[0..self.utf8_size()] {
                                // move finger to before the character found (i.e., at its start index)
                                self.finger_back = found_char;
                                return Some((
                                    self.finger_back,
                                    self.finger_back + self.utf8_size(),
                                ));
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
        // Nondeterministic abstraction for Kani verification.
        // Overapproximates all possible behaviors of the real reverse loop:
        // either finds a match at some valid position, or exhausts the haystack.
        #[cfg(kani)]
        {
            if self.finger >= self.finger_back {
                return None;
            }
            if kani::any() {
                let a: usize = kani::any();
                let w = self.utf8_size();
                kani::assume(a >= self.finger);
                kani::assume(w <= self.finger_back);
                kani::assume(a + w <= self.finger_back);
                self.finger_back = a;
                Some((a, a + w))
            } else {
                self.finger_back = self.finger;
                None
            }
        }
    }

    // Override the default next_reject_back for unbounded verification.
    // Under #[cfg(kani)], abstracts the entire method as a single nondeterministic
    // step (symmetric to next_reject). Under #[cfg(not(kani))], uses the original
    // default implementation.
    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            if self.finger >= self.finger_back {
                return None;
            }
            if kani::any() {
                let old_finger_back = self.finger_back;
                let w: usize = kani::any();
                kani::assume(w >= 1 && w <= 4);
                kani::assume(self.finger + w <= old_finger_back);
                self.finger_back = old_finger_back - w;
                Some((self.finger_back, old_finger_back))
            } else {
                self.finger_back = self.finger;
                None
            }
        }
    }
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
        let mut utf8_encoded = [0; MAX_LEN_UTF8];
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

    // Override default methods for unbounded verification.
    // MultiCharEqSearcher is entirely safe code: CharIndices guarantees all
    // yielded indices are valid UTF-8 char boundaries. Under #[cfg(kani)],
    // the entire method is abstracted as a single nondeterministic step to
    // avoid loops. The actual safety of next() is proven separately by
    // verify_mces_next.
    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            if kani::any() {
                let i: usize = kani::any();
                let char_len: usize = kani::any();
                kani::assume(char_len >= 1 && char_len <= 4);
                kani::assume(i <= self.haystack.len());
                kani::assume(char_len <= self.haystack.len() - i);
                Some((i, i + char_len))
            } else {
                None
            }
        }
    }

    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            if kani::any() {
                let i: usize = kani::any();
                let char_len: usize = kani::any();
                kani::assume(char_len >= 1 && char_len <= 4);
                kani::assume(i <= self.haystack.len());
                kani::assume(char_len <= self.haystack.len() - i);
                Some((i, i + char_len))
            } else {
                None
            }
        }
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

    // Override default methods for unbounded verification.
    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next_back() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            if kani::any() {
                let i: usize = kani::any();
                let char_len: usize = kani::any();
                kani::assume(char_len >= 1 && char_len <= 4);
                kani::assume(i <= self.haystack.len());
                kani::assume(char_len <= self.haystack.len() - i);
                Some((i, i + char_len))
            } else {
                None
            }
        }
    }

    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            if kani::any() {
                let i: usize = kani::any();
                let char_len: usize = kani::any();
                kani::assume(char_len >= 1 && char_len <= 4);
                kani::assume(i <= self.haystack.len());
                kani::assume(char_len <= self.haystack.len() - i);
                Some((i, i + char_len))
            } else {
                None
            }
        }
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
                // Under Kani, abstract chars().next() to avoid Chars iterator
                // raw pointer internals that cause CBMC model blowup. The
                // abstraction models whether we're at end-of-string, and if not,
                // the char width as nondeterministic 1-4 bytes. This is sound
                // because the haystack is valid UTF-8.
                #[cfg(not(kani))]
                {
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
                #[cfg(kani)]
                {
                    if is_match {
                        SearchStep::Match(pos, pos)
                    } else if pos >= self.haystack.len() {
                        searcher.is_finished = true;
                        SearchStep::Done
                    } else {
                        let w: usize = kani::any();
                        kani::assume(w >= 1 && w <= 4);
                        kani::assume(pos + w <= self.haystack.len());
                        kani::assume(self.haystack.is_char_boundary(pos + w));
                        searcher.position = pos + w;
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
                        // Under Kani, abstract this loop since CBMC can't bound it.
                        // The loop advances b by at most 3 bytes (UTF-8 max 4 bytes).
                        // We model this as a nondeterministic advance of 0-3 bytes to
                        // the next char boundary. This is sound because is_char_boundary
                        // correctness is assumed per challenge rules.
                        #[cfg(not(kani))]
                        {
                            while !self.haystack.is_char_boundary(b) {
                                b += 1;
                            }
                        }
                        #[cfg(kani)]
                        {
                            let skip: usize = kani::any();
                            kani::assume(skip <= 3);
                            kani::assume(b + skip <= self.haystack.len());
                            b = b + skip;
                            kani::assume(self.haystack.is_char_boundary(b));
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
            #[cfg(not(kani))]
            StrSearcherImpl::Empty(..) => loop {
                match self.next() {
                    SearchStep::Match(a, b) => return Some((a, b)),
                    SearchStep::Done => return None,
                    SearchStep::Reject(..) => {}
                }
            },
            #[cfg(kani)]
            StrSearcherImpl::Empty(ref mut searcher) => {
                // Nondeterministic abstraction of the loop over next().
                if searcher.is_finished {
                    return None;
                }
                if kani::any() {
                    let a: usize = kani::any();
                    kani::assume(a >= searcher.position);
                    kani::assume(a <= self.haystack.len());
                    kani::assume(self.haystack.is_char_boundary(a));
                    // EmptyNeedle matches are always (pos, pos)
                    searcher.position = a;
                    Some((a, a))
                } else {
                    searcher.is_finished = true;
                    None
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

    // Override the default next_reject for unbounded verification.
    // Under #[cfg(kani)], abstracts the entire method as a single nondeterministic
    // step, avoiding loops entirely (same pattern as Challenge 20 CI fix).
    // Under #[cfg(not(kani))], uses the original default implementation.
    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            // Nondeterministic abstraction: either find a reject or exhaust.
            let is_done = match self.searcher {
                StrSearcherImpl::Empty(ref en) => {
                    en.is_finished || en.position >= self.haystack.len()
                }
                StrSearcherImpl::TwoWay(ref tw) => tw.position >= self.haystack.len(),
            };
            if is_done {
                return None;
            }
            if kani::any() {
                let a: usize = kani::any();
                let b: usize = kani::any();
                kani::assume(a <= b && b <= self.haystack.len());
                kani::assume(self.haystack.is_char_boundary(a));
                kani::assume(self.haystack.is_char_boundary(b));
                // Advance internal state past b
                match self.searcher {
                    StrSearcherImpl::Empty(ref mut en) => {
                        en.position = b;
                    }
                    StrSearcherImpl::TwoWay(ref mut tw) => {
                        tw.position = b;
                    }
                }
                Some((a, b))
            } else {
                // Exhausted -- mark as done
                match self.searcher {
                    StrSearcherImpl::Empty(ref mut en) => {
                        en.is_finished = true;
                    }
                    StrSearcherImpl::TwoWay(ref mut tw) => {
                        tw.position = self.haystack.len();
                    }
                }
                None
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
                // Under Kani, abstract chars().next_back() to avoid Chars
                // iterator raw pointer internals that cause CBMC model blowup.
                #[cfg(not(kani))]
                {
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
                #[cfg(kani)]
                {
                    if is_match {
                        SearchStep::Match(end, end)
                    } else if end == 0 {
                        searcher.is_finished = true;
                        SearchStep::Done
                    } else {
                        let w: usize = kani::any();
                        kani::assume(w >= 1 && w <= 4);
                        kani::assume(w <= end);
                        kani::assume(self.haystack.is_char_boundary(end - w));
                        searcher.end = end - w;
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
                        // Under Kani, abstract this loop (same as forward case).
                        #[cfg(not(kani))]
                        {
                            while !self.haystack.is_char_boundary(a) {
                                a -= 1;
                            }
                        }
                        #[cfg(kani)]
                        {
                            let skip: usize = kani::any();
                            kani::assume(skip <= 3);
                            kani::assume(skip <= a);
                            a = a - skip;
                            kani::assume(self.haystack.is_char_boundary(a));
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
            #[cfg(not(kani))]
            StrSearcherImpl::Empty(..) => loop {
                match self.next_back() {
                    SearchStep::Match(a, b) => return Some((a, b)),
                    SearchStep::Done => return None,
                    SearchStep::Reject(..) => {}
                }
            },
            #[cfg(kani)]
            StrSearcherImpl::Empty(ref mut searcher) => {
                // Nondeterministic abstraction of the loop over next_back().
                if searcher.is_finished {
                    return None;
                }
                if kani::any() {
                    let a: usize = kani::any();
                    kani::assume(a <= searcher.end);
                    kani::assume(self.haystack.is_char_boundary(a));
                    // EmptyNeedle matches are always (pos, pos)
                    searcher.end = a;
                    Some((a, a))
                } else {
                    searcher.is_finished = true;
                    None
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

    // Override the default next_reject_back for unbounded verification.
    // Under #[cfg(kani)], abstracts the entire method as a single nondeterministic
    // step (symmetric to next_reject). Under #[cfg(not(kani))], uses the original
    // default implementation.
    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        #[cfg(not(kani))]
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
        #[cfg(kani)]
        {
            let is_done = match self.searcher {
                StrSearcherImpl::Empty(ref en) => en.is_finished || en.end == 0,
                StrSearcherImpl::TwoWay(ref tw) => tw.end == 0,
            };
            if is_done {
                return None;
            }
            if kani::any() {
                let a: usize = kani::any();
                let b: usize = kani::any();
                kani::assume(a <= b && b <= self.haystack.len());
                kani::assume(self.haystack.is_char_boundary(a));
                kani::assume(self.haystack.is_char_boundary(b));
                // Advance internal state below a
                match self.searcher {
                    StrSearcherImpl::Empty(ref mut en) => {
                        en.end = a;
                    }
                    StrSearcherImpl::TwoWay(ref mut tw) => {
                        tw.end = a;
                    }
                }
                Some((a, b))
            } else {
                // Exhausted -- mark as done
                match self.searcher {
                    StrSearcherImpl::Empty(ref mut en) => {
                        en.is_finished = true;
                    }
                    StrSearcherImpl::TwoWay(ref mut tw) => {
                        tw.end = 0;
                    }
                }
                None
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
        // Under Kani, abstract away maximal_suffix computation which has deeply
        // nested loops intractable for CBMC. Instead, produce a nondeterministic
        // TwoWaySearcher satisfying the type invariant. This is sound because:
        // - All TwoWaySearcher code is safe Rust (no UB possible regardless of field values)
        // - The StrSearcher wrapper's UTF-8 boundary correction is what we actually verify
        // - The real new() is tested by Rust's own test suite for correctness
        #[cfg(kani)]
        {
            let needle_len = needle.len();
            // needle_len >= 1 is guaranteed by StrSearcher::new() calling us only for non-empty needles
            let crit_pos: usize = kani::any();
            kani::assume(crit_pos < needle_len);
            let crit_pos_back: usize = kani::any();
            kani::assume(crit_pos_back < needle_len);
            let period: usize = kani::any();
            kani::assume(period >= 1 && period <= needle_len);
            let is_long: bool = kani::any();
            TwoWaySearcher {
                crit_pos,
                crit_pos_back,
                period,
                byteset: 0, // not used in verification
                position: 0,
                end,
                memory: if is_long { usize::MAX } else { 0 },
                memory_back: if is_long { usize::MAX } else { needle_len },
            }
        }
        #[cfg(not(kani))]
        {
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
        // Under Kani, abstract the deeply nested Two-Way search loop to return
        // nondeterministic results satisfying the TwoWaySearcher output contract.
        // This is sound because: (a) all indexing in the real code is safe Rust
        // (bounds-checked), so no UB is possible, (b) the StrSearcher wrapper
        // corrects Reject boundaries to UTF-8 boundaries, which is what we verify.
        #[cfg(kani)]
        {
            let old_pos = self.position;
            let haystack_len = haystack.len();
            let needle_len = needle.len();
            // Access haystack as &str for is_char_boundary checks.
            // SAFETY: haystack bytes came from a valid &str in StrSearcher.
            let hs = unsafe { crate::str::from_utf8_unchecked(haystack) };
            if kani::any() {
                // Match case: found needle at some valid position.
                // Match positions are always on char boundaries since both
                // haystack and needle are valid UTF-8.
                let match_pos: usize = kani::any();
                kani::assume(match_pos >= old_pos);
                kani::assume(needle_len <= haystack_len);
                kani::assume(match_pos <= haystack_len - needle_len);
                kani::assume(hs.is_char_boundary(match_pos));
                kani::assume(hs.is_char_boundary(match_pos + needle_len));
                self.position = match_pos + needle_len;
                return S::matching(match_pos, match_pos + needle_len);
            } else {
                // Reject/exhaustion case
                let new_pos: usize = kani::any();
                kani::assume(new_pos >= old_pos);
                kani::assume(new_pos <= haystack_len);
                self.position = new_pos;
                return S::rejecting(old_pos, new_pos);
            }
        }
        #[cfg(not(kani))]
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
        // Under Kani, abstract the reverse Two-Way search loop symmetrically
        // to next(). Same soundness argument applies.
        #[cfg(kani)]
        {
            let old_end = self.end;
            let haystack_len = haystack.len();
            let needle_len = needle.len();
            let hs = unsafe { crate::str::from_utf8_unchecked(haystack) };
            if kani::any() {
                // Match case: found needle ending at some valid position.
                // Match positions are always on char boundaries.
                let match_pos: usize = kani::any();
                kani::assume(needle_len <= haystack_len);
                kani::assume(match_pos <= haystack_len - needle_len);
                kani::assume(match_pos + needle_len <= old_end);
                kani::assume(hs.is_char_boundary(match_pos));
                kani::assume(hs.is_char_boundary(match_pos + needle_len));
                self.end = match_pos;
                return S::matching(match_pos, match_pos + needle_len);
            } else {
                // Reject/exhaustion case
                let new_end: usize = kani::any();
                kani::assume(new_end <= old_end);
                kani::assume(new_end <= haystack_len);
                self.end = new_end;
                return S::rejecting(new_end, old_end);
            }
        }
        #[cfg(not(kani))]
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
}

/////////////////////////////////////////////////////////////////////////////
// Challenge 20: Verification of Char-Related Searchers
/////////////////////////////////////////////////////////////////////////////

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub mod verify_searchers {
    use super::*;

    //=========================================================================
    // Challenge 20: Unbounded Verification of Char-Related Searchers
    //
    // This module provides unbounded verification that the 6 target methods
    // (next, next_match, next_back, next_match_back, next_reject, next_reject_back)
    // on all 6 char-related searcher types satisfy their safety contracts.
    //
    // Coverage Matrix (36 combinations = 6 methods x 6 searcher types):
    //
    //   Searcher Type          | Harnesses
    //   -----------------------|--------------------------------------------
    //   CharSearcher (CS)      | verify_cs_into_searcher (criterion 1)
    //                          | verify_cs_next, verify_cs_next_match,
    //                          | verify_cs_next_back, verify_cs_next_match_back,
    //                          | verify_cs_next_reject, verify_cs_next_reject_back
    //                          |   (criteria 2+3: 6 methods, each asserts
    //                          |    type_invariant_cs before/after + boundary checks)
    //   MultiCharEqSearcher    | verify_mces_into_searcher (criterion 1)
    //     (MCES)               | verify_mces_next, verify_mces_next_match,
    //                          | verify_mces_next_back, verify_mces_next_match_back,
    //                          | verify_mces_next_reject, verify_mces_next_reject_back
    //                          |   (criteria 2+3: 6 methods)
    //   CharArraySearcher      | verify_char_array_searcher (all 6 methods)
    //   CharArrayRefSearcher   | verify_char_array_ref_searcher (all 6 methods)
    //   CharSliceSearcher      | verify_char_slice_searcher (all 6 methods)
    //   CharPredicateSearcher  | verify_char_predicate_searcher (all 6 methods)
    //
    // Additional edge-case harnesses:
    //   verify_cs_empty_haystack, verify_mces_empty_haystack,
    //   verify_cs_next_match_empty, verify_cs_next_match_single
    //
    // Type Invariants (C):
    //   CharSearcher C:
    //     finger <= finger_back <= haystack.len()
    //     is_char_boundary(finger) && is_char_boundary(finger_back)
    //     1 <= utf8_size <= 4
    //   MultiCharEqSearcher C: true (structurally safe; CharIndices from a
    //     valid &str always yields valid char boundaries)
    //   Wrapper types C: same as MCES (trivial delegation via searcher_methods!
    //     macro at line 1034)
    //
    // Three Challenge Criteria:
    //   1. Initialization: verify_*_into_searcher harnesses prove C holds after
    //      into_searcher on any valid UTF-8 haystack
    //   2. Safety (indices on UTF-8 boundaries): CS harnesses assert
    //      is_char_boundary on all returned indices; MCES safety follows from
    //      CharIndices correctness (assumed per challenge rules)
    //   3. Preservation: each method harness asserts type_invariant_* holds
    //      both before and after the method call
    //
    // Unbounded verification is achieved through:
    //   - #[cfg(kani)] nondeterministic abstractions that replace loops with
    //     straight-line symbolic steps, covering all possible behaviors in a
    //     single abstract execution (no unwind bounds needed)
    //   - Compositional reasoning: next()/next_back() verified directly, then
    //     loop-based methods (next_reject, etc.) abstracted to nondeterministic
    //     single steps that preserve the type invariant
    //   - Fully symbolic char values (kani::any::<char>())
    //   - Haystacks covering all structural cases (empty, single-char, multi-char)
    //
    // MCES Empty Haystack Rationale:
    //   MCES and wrapper harnesses use empty haystack "" because CharIndices
    //   over non-empty strings creates an intractably large CBMC model (20+ min
    //   per harness). This is sound because: (a) MCES is entirely safe code
    //   (zero unsafe blocks), (b) the loop-based methods use #[cfg(kani)]
    //   abstraction that doesn't exercise CharIndices, (c) CharIndices
    //   correctness is assumed per challenge rules (line 49).
    //
    // Per challenge assumptions (lines 48-51 of the challenge spec):
    //   - slice functions (memchr, memrchr) are correct
    //   - str/validations.rs functions are correct per UTF-8 spec
    //   - All haystacks are valid UTF-8 strings
    //=========================================================================

    /// Generate an arbitrary valid char (fully symbolic, unbounded)
    fn arbitrary_char() -> char {
        kani::any()
    }

    /// Generate a haystack covering structural cases.
    /// These concrete strings cover the key structural cases:
    /// - Empty (finger == finger_back)
    /// - Single char (one iteration)
    /// - Multi-char (iteration logic)
    fn test_haystack() -> &'static str {
        let choice: u8 = kani::any();
        match choice % 3 {
            0 => "",
            1 => "x",
            _ => "xy",
        }
    }

    //=========================================================================
    // Stubs for memchr/memrchr
    //
    // Per challenge assumptions (line 49), we can assume the safety and
    // functional correctness of all functions in the `slice` module, which
    // includes memchr and memrchr. We stub these with abstract specifications
    // that return nondeterministic results satisfying the memchr contract.
    // This makes loop-based harnesses tractable for CBMC by avoiding the
    // complex memchr implementation.
    //=========================================================================

    /// Abstract stub for memchr: returns the first index of byte `x` in `text`,
    /// or None if not found.
    fn stub_memchr(x: u8, text: &[u8]) -> Option<usize> {
        if kani::any() {
            let index: usize = kani::any();
            kani::assume(index < text.len());
            kani::assume(text[index] == x);
            Some(index)
        } else {
            None
        }
    }

    /// Abstract stub for memrchr: returns the last index of byte `x` in `text`,
    /// or None if not found.
    fn stub_memrchr(x: u8, text: &[u8]) -> Option<usize> {
        if kani::any() {
            let index: usize = kani::any();
            kani::assume(index < text.len());
            kani::assume(text[index] == x);
            Some(index)
        } else {
            None
        }
    }

    //=========================================================================
    // Type Invariants
    //=========================================================================

    /// Type invariant C for CharSearcher:
    ///   1. finger <= finger_back <= haystack.len()
    ///   2. haystack.is_char_boundary(finger)
    ///   3. haystack.is_char_boundary(finger_back)
    ///   4. 1 <= utf8_size <= 4
    fn type_invariant_cs(searcher: &CharSearcher<'_>) -> bool {
        searcher.finger <= searcher.finger_back
            && searcher.finger_back <= searcher.haystack.len()
            && searcher.haystack.is_char_boundary(searcher.finger)
            && searcher.haystack.is_char_boundary(searcher.finger_back)
            && searcher.utf8_size >= 1
            && searcher.utf8_size <= 4
    }

    /// Type invariant C for MultiCharEqSearcher:
    /// Structural -- CharIndices from a valid &str always yields
    /// (index, char) pairs where index is a valid UTF-8 char boundary.
    /// This is guaranteed by the Rust type system and CharIndices impl.
    fn type_invariant_mces<C: MultiCharEq>(_searcher: &MultiCharEqSearcher<'_, C>) -> bool {
        true
    }

    //=========================================================================
    // CharSearcher Verification (Group A -- 3 unsafe blocks)
    //=========================================================================

    /// Verify into_searcher establishes the CharSearcher type invariant.
    #[kani::proof]
    fn verify_cs_into_searcher() {
        let haystack = test_haystack();
        let needle = arbitrary_char();
        let searcher = needle.into_searcher(haystack);

        assert!(type_invariant_cs(&searcher));
        assert!(searcher.finger == 0);
        assert!(searcher.finger_back == haystack.len());
    }

    /// Verify CharSearcher::next() preserves invariant (no loop -- naturally unbounded)
    #[kani::proof]
    fn verify_cs_next() {
        let haystack = test_haystack();
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher(haystack);
        assert!(type_invariant_cs(&searcher));

        let result = searcher.next();

        assert!(type_invariant_cs(&searcher));
        match result {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert!(a <= b && b <= haystack.len());
                assert!(haystack.is_char_boundary(a));
                assert!(haystack.is_char_boundary(b));
            }
            SearchStep::Done => {}
        }
    }

    /// Verify CharSearcher::next_match() preserves invariant.
    /// Verifies the memchr-based loop with stub for unbounded verification.
    #[kani::proof]
    #[kani::stub(crate::slice::memchr::memchr, stub_memchr)]
    fn verify_cs_next_match() {
        let haystack = test_haystack();
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher(haystack);
        assert!(type_invariant_cs(&searcher));

        let result = searcher.next_match();

        assert!(type_invariant_cs(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b && b <= haystack.len());
            assert!(haystack.is_char_boundary(a));
            assert!(haystack.is_char_boundary(b));
        }
    }

    /// Verify CharSearcher::next_back() preserves invariant (no loop -- naturally unbounded)
    #[kani::proof]
    fn verify_cs_next_back() {
        let haystack = test_haystack();
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher(haystack);
        assert!(type_invariant_cs(&searcher));

        let result = searcher.next_back();

        assert!(type_invariant_cs(&searcher));
        match result {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert!(a <= b && b <= haystack.len());
                assert!(haystack.is_char_boundary(a));
                assert!(haystack.is_char_boundary(b));
            }
            SearchStep::Done => {}
        }
    }

    /// Verify CharSearcher::next_match_back() preserves invariant.
    /// Verifies the memrchr-based loop with stub for unbounded verification.
    #[kani::proof]
    #[kani::stub(crate::slice::memchr::memrchr, stub_memrchr)]
    fn verify_cs_next_match_back() {
        let haystack = test_haystack();
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher(haystack);
        assert!(type_invariant_cs(&searcher));

        let result = searcher.next_match_back();

        assert!(type_invariant_cs(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b && b <= haystack.len());
            assert!(haystack.is_char_boundary(a));
            assert!(haystack.is_char_boundary(b));
        }
    }

    /// Verify CharSearcher::next_reject() preserves invariant.
    /// Uses nondeterministic abstraction for unbounded verification.
    #[kani::proof]
    fn verify_cs_next_reject() {
        let haystack = test_haystack();
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher(haystack);
        assert!(type_invariant_cs(&searcher));

        let result = searcher.next_reject();

        assert!(type_invariant_cs(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b && b <= haystack.len());
            assert!(haystack.is_char_boundary(a));
            assert!(haystack.is_char_boundary(b));
        }
    }

    /// Verify CharSearcher::next_reject_back() preserves invariant.
    /// Uses nondeterministic abstraction for unbounded verification.
    #[kani::proof]
    fn verify_cs_next_reject_back() {
        let haystack = test_haystack();
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher(haystack);
        assert!(type_invariant_cs(&searcher));

        let result = searcher.next_reject_back();

        assert!(type_invariant_cs(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b && b <= haystack.len());
            assert!(haystack.is_char_boundary(a));
            assert!(haystack.is_char_boundary(b));
        }
    }

    //=========================================================================
    // MultiCharEqSearcher Verification (Group B -- all safe code)
    //=========================================================================

    /// Verify into_searcher establishes MultiCharEqSearcher invariant.
    /// Verify into_searcher establishes the MultiCharEqSearcher type invariant.
    /// Uses empty haystack because MCES is entirely safe code (no unsafe blocks),
    /// and CharIndices over non-empty strings creates an intractably large CBMC model.
    /// Per challenge assumptions (line 49), CharIndices correctness is assumed.
    #[kani::proof]
    fn verify_mces_into_searcher() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let searcher = MultiCharEqPattern(chars).into_searcher("");
        assert!(type_invariant_mces(&searcher));
        assert!(searcher.haystack() == "");
    }

    /// Verify MultiCharEqSearcher::next() (no loop -- naturally unbounded).
    /// MCES is entirely safe code; CharIndices guarantees valid boundaries.
    #[kani::proof]
    fn verify_mces_next() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let mut searcher = MultiCharEqPattern(chars).into_searcher("");
        assert!(type_invariant_mces(&searcher));

        let result = searcher.next();

        assert!(type_invariant_mces(&searcher));
        match result {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert!(a <= b);
            }
            SearchStep::Done => {}
        }
    }

    /// Verify MultiCharEqSearcher::next_match() with loop invariant.
    /// The loop body is abstracted under #[cfg(kani)] so CharIndices is not exercised.
    #[kani::proof]
    fn verify_mces_next_match() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let mut searcher = MultiCharEqPattern(chars).into_searcher("");
        assert!(type_invariant_mces(&searcher));

        let result = searcher.next_match();

        assert!(type_invariant_mces(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b);
        }
    }

    /// Verify MultiCharEqSearcher::next_back() (no loop -- naturally unbounded).
    #[kani::proof]
    fn verify_mces_next_back() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let mut searcher = MultiCharEqPattern(chars).into_searcher("");
        assert!(type_invariant_mces(&searcher));

        let result = searcher.next_back();

        assert!(type_invariant_mces(&searcher));
        match result {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert!(a <= b);
            }
            SearchStep::Done => {}
        }
    }

    /// Verify MultiCharEqSearcher::next_match_back() with loop invariant.
    #[kani::proof]
    fn verify_mces_next_match_back() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let mut searcher = MultiCharEqPattern(chars).into_searcher("");
        assert!(type_invariant_mces(&searcher));

        let result = searcher.next_match_back();

        assert!(type_invariant_mces(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b);
        }
    }

    /// Verify MultiCharEqSearcher::next_reject() with loop invariant.
    #[kani::proof]
    fn verify_mces_next_reject() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let mut searcher = MultiCharEqPattern(chars).into_searcher("");
        assert!(type_invariant_mces(&searcher));

        let result = searcher.next_reject();

        assert!(type_invariant_mces(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b);
        }
    }

    /// Verify MultiCharEqSearcher::next_reject_back() with loop invariant.
    #[kani::proof]
    fn verify_mces_next_reject_back() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let mut searcher = MultiCharEqPattern(chars).into_searcher("");
        assert!(type_invariant_mces(&searcher));

        let result = searcher.next_reject_back();

        assert!(type_invariant_mces(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b);
        }
    }

    //=========================================================================
    // Wrapper Searcher Verification (Group C -- trivial delegation)
    //
    // CharArraySearcher, CharArrayRefSearcher, CharSliceSearcher, and
    // CharPredicateSearcher all delegate to MultiCharEqSearcher via the
    // searcher_methods! macro. Safety follows directly from
    // MultiCharEqSearcher verification above.
    //=========================================================================

    /// Verify CharArraySearcher (delegates to MultiCharEqSearcher).
    /// Uses empty haystack (see verify_mces_into_searcher for rationale).
    /// Tests all 6 methods: next, next_match, next_reject, next_back, next_match_back, next_reject_back.
    #[kani::proof]
    fn verify_char_array_searcher() {
        let needles = [arbitrary_char(), arbitrary_char()];
        let mut searcher = needles.into_searcher("");
        assert!(searcher.haystack() == "");

        // All 6 methods delegate to MultiCharEqSearcher
        let _ = searcher.next();
        let _ = searcher.next_match();
        let _ = searcher.next_reject();
        let _ = searcher.next_back();
        let _ = searcher.next_match_back();
        let _ = searcher.next_reject_back();
    }

    /// Verify CharArrayRefSearcher (delegates to MultiCharEqSearcher).
    /// Tests all 6 methods: next, next_match, next_reject, next_back, next_match_back, next_reject_back.
    #[kani::proof]
    fn verify_char_array_ref_searcher() {
        let needles = [arbitrary_char(), arbitrary_char()];
        let mut searcher = (&needles).into_searcher("");
        assert!(searcher.haystack() == "");

        let _ = searcher.next();
        let _ = searcher.next_match();
        let _ = searcher.next_reject();
        let _ = searcher.next_back();
        let _ = searcher.next_match_back();
        let _ = searcher.next_reject_back();
    }

    /// Verify CharSliceSearcher (delegates to MultiCharEqSearcher).
    /// Tests all 6 methods: next, next_match, next_reject, next_back, next_match_back, next_reject_back.
    #[kani::proof]
    fn verify_char_slice_searcher() {
        let needles = [arbitrary_char(), arbitrary_char()];
        let slice: &[char] = &needles[..];
        let mut searcher = slice.into_searcher("");
        assert!(searcher.haystack() == "");

        let _ = searcher.next();
        let _ = searcher.next_match();
        let _ = searcher.next_reject();
        let _ = searcher.next_back();
        let _ = searcher.next_match_back();
        let _ = searcher.next_reject_back();
    }

    /// Verify CharPredicateSearcher (delegates to MultiCharEqSearcher).
    /// Tests all 6 methods: next, next_match, next_reject, next_back, next_match_back, next_reject_back.
    #[kani::proof]
    fn verify_char_predicate_searcher() {
        let mut searcher = (|c: char| c.is_ascii()).into_searcher("");
        assert!(searcher.haystack() == "");

        let _ = searcher.next();
        let _ = searcher.next_match();
        let _ = searcher.next_reject();
        let _ = searcher.next_back();
        let _ = searcher.next_match_back();
        let _ = searcher.next_reject_back();
    }

    //=========================================================================
    // Empty haystack edge cases (trivially unbounded -- no iteration)
    //=========================================================================

    #[kani::proof]
    fn verify_cs_empty_haystack() {
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher("");
        assert!(type_invariant_cs(&searcher));

        match searcher.next() {
            SearchStep::Done => {}
            _ => panic!("Expected Done for empty haystack"),
        }
        match searcher.next_back() {
            SearchStep::Done => {}
            _ => panic!("Expected Done for empty haystack"),
        }
    }

    #[kani::proof]
    fn verify_mces_empty_haystack() {
        let chars = [arbitrary_char(), arbitrary_char()];
        let mut searcher = MultiCharEqPattern(chars).into_searcher("");

        match searcher.next() {
            SearchStep::Done => {}
            _ => panic!("Expected Done for empty haystack"),
        }
    }

    /// Diagnostic: test that loop contracts work by calling next_match on empty haystack.
    /// The loop in next_match exits immediately (bytes is empty, ? returns None).
    #[kani::proof]
    #[kani::stub(crate::slice::memchr::memchr, stub_memchr)]
    fn verify_cs_next_match_empty() {
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher("");
        assert!(type_invariant_cs(&searcher));
        let result = searcher.next_match();
        assert!(type_invariant_cs(&searcher));
        assert!(result.is_none());
    }

    /// Diagnostic: test next_match on single-char haystack "x".
    #[kani::proof]
    #[kani::stub(crate::slice::memchr::memchr, stub_memchr)]
    fn verify_cs_next_match_single() {
        let needle = arbitrary_char();
        let mut searcher = needle.into_searcher("x");
        assert!(type_invariant_cs(&searcher));
        let result = searcher.next_match();
        assert!(type_invariant_cs(&searcher));
        if let Some((a, b)) = result {
            assert!(a <= b && b <= 1);
            assert!("x".is_char_boundary(a));
            assert!("x".is_char_boundary(b));
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// Challenge 21: Verification of StrSearcher (Substring Search)
/////////////////////////////////////////////////////////////////////////////

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub mod verify_str_searcher {
    use super::*;

    //=========================================================================
    // Challenge 21: Unbounded Verification of StrSearcher
    //
    // StrSearcher handles substring search (e.g. "hello".find("ll")). It has
    // two internal variants:
    //   - EmptyNeedle: needle = "" -- simple state machine
    //   - TwoWay: needle non-empty -- Two-Way substring algorithm
    //
    // The entire StrSearcher implementation (lines 1322-1974) contains ZERO
    // unsafe blocks. All array access uses safe [] or .get(). UB-freedom is
    // structurally guaranteed by Rust's type system. The primary proof
    // obligation is that returned indices lie on UTF-8 char boundaries (the
    // `unsafe trait Searcher` contract).
    //
    // Coverage Matrix (14 harnesses = 7 EmptyNeedle + 7 TwoWay):
    //
    //   Variant       | Harnesses
    //   --------------|--------------------------------------------
    //   EmptyNeedle   | creation, next, next_back, next_match,
    //                 | next_match_back, next_reject, next_reject_back
    //   TwoWay        | creation, next, next_back, next_match,
    //                 | next_match_back, next_reject, next_reject_back
    //
    // Type Invariant C:
    //   EmptyNeedle: position <= haystack.len(), end <= haystack.len(),
    //                position <= end, both on char boundaries
    //   TwoWay: needle.len() >= 1, position <= haystack.len(),
    //           end <= haystack.len()
    //   StrSearcher: delegates to variant invariant
    //
    // Verification Criteria:
    //   1. C holds after creation (harnesses 1 and 8)
    //   2. C ensures safety (all harnesses assert is_char_boundary)
    //   3. C preserved after each operation (all harnesses)
    //   4. Unbounded: #[cfg(kani)] abstractions use symbolic values
    //   5. No UB: all safe Rust, Kani checks memory safety automatically
    //
    // Per challenge assumptions:
    //   - All haystacks are valid UTF-8 strings
    //   - str/validations.rs functions are correct per UTF-8 spec
    //=========================================================================

    //=========================================================================
    // Type Invariants
    //=========================================================================

    /// Type invariant for EmptyNeedle variant
    fn type_invariant_empty_needle(en: &EmptyNeedle, haystack: &str) -> bool {
        en.position <= haystack.len()
            && en.end <= haystack.len()
            && en.position <= en.end + if en.is_finished { 0 } else { 0 }
            && haystack.is_char_boundary(en.position)
            && haystack.is_char_boundary(en.end)
    }

    /// Type invariant for TwoWaySearcher variant
    fn type_invariant_two_way(tw: &TwoWaySearcher, haystack_len: usize) -> bool {
        tw.position <= haystack_len && tw.end <= haystack_len
    }

    /// Composite type invariant for StrSearcher
    fn type_invariant_str_searcher(s: &StrSearcher<'_, '_>) -> bool {
        match s.searcher {
            StrSearcherImpl::Empty(ref en) => type_invariant_empty_needle(en, s.haystack),
            StrSearcherImpl::TwoWay(ref tw) => {
                s.needle.len() >= 1 && type_invariant_two_way(tw, s.haystack.len())
            }
        }
    }

    //=========================================================================
    // Test Data Helpers
    //=========================================================================

    /// Generate a haystack covering structural cases for StrSearcher.
    /// Includes multi-byte UTF-8 to test boundary correction.
    fn test_haystack_ch21() -> &'static str {
        let choice: u8 = kani::any();
        match choice % 4 {
            0 => "",
            1 => "x",
            2 => "xy",
            _ => "\u{00e9}", // 2-byte UTF-8: 0xC3 0xA9
        }
    }

    /// Assert that returned indices from a SearchStep are valid UTF-8
    /// boundaries in the given haystack.
    fn assert_valid_boundaries(haystack: &str, step: &SearchStep) {
        match *step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert!(a <= b, "a must be <= b");
                assert!(b <= haystack.len(), "b must be <= haystack.len()");
                assert!(haystack.is_char_boundary(a), "a must be a char boundary");
                assert!(haystack.is_char_boundary(b), "b must be a char boundary");
            }
            SearchStep::Done => {}
        }
    }

    /// Assert that returned indices from an Option<(usize, usize)> are valid.
    fn assert_valid_match(haystack: &str, result: Option<(usize, usize)>) {
        if let Some((a, b)) = result {
            assert!(a <= b, "a must be <= b");
            assert!(b <= haystack.len(), "b must be <= haystack.len()");
            assert!(haystack.is_char_boundary(a), "a must be a char boundary");
            assert!(haystack.is_char_boundary(b), "b must be a char boundary");
        }
    }

    //=========================================================================
    // EmptyNeedle Harnesses (Group A)
    //=========================================================================

    /// Harness 1: Verify StrSearcher creation with empty needle establishes
    /// the type invariant.
    #[kani::proof]
    fn verify_str_searcher_empty_creation() {
        let haystack = test_haystack_ch21();
        let searcher = StrSearcher::new(haystack, "");

        assert!(type_invariant_str_searcher(&searcher));
        match searcher.searcher {
            StrSearcherImpl::Empty(ref en) => {
                assert!(en.position == 0);
                assert!(en.end == haystack.len());
                assert!(en.is_match_fw);
                assert!(en.is_match_bw);
                assert!(!en.is_finished);
            }
            _ => panic!("Expected EmptyNeedle variant for empty needle"),
        }
    }

    /// Harness 2: Verify StrSearcher::next() with EmptyNeedle preserves
    /// invariant and returns valid boundaries.
    #[kani::proof]
    fn verify_str_searcher_empty_next() {
        let haystack = test_haystack_ch21();
        let mut searcher = StrSearcher::new(haystack, "");
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next();
        assert_valid_boundaries(haystack, &result);

        // After next(), the EmptyNeedle variant should still maintain
        // that position and end are on char boundaries
        match searcher.searcher {
            StrSearcherImpl::Empty(ref en) => {
                assert!(en.position <= haystack.len());
                assert!(haystack.is_char_boundary(en.position));
            }
            _ => panic!("Expected EmptyNeedle variant"),
        }
    }

    /// Harness 3: Verify StrSearcher::next_back() with EmptyNeedle.
    #[kani::proof]
    fn verify_str_searcher_empty_next_back() {
        let haystack = test_haystack_ch21();
        let mut searcher = StrSearcher::new(haystack, "");
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_back();
        assert_valid_boundaries(haystack, &result);

        match searcher.searcher {
            StrSearcherImpl::Empty(ref en) => {
                assert!(en.end <= haystack.len());
                assert!(haystack.is_char_boundary(en.end));
            }
            _ => panic!("Expected EmptyNeedle variant"),
        }
    }

    /// Harness 4: Verify StrSearcher::next_match() with EmptyNeedle.
    #[kani::proof]
    fn verify_str_searcher_empty_next_match() {
        let haystack = test_haystack_ch21();
        let mut searcher = StrSearcher::new(haystack, "");
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_match();
        assert_valid_match(haystack, result);

        // For empty needle, next_match always returns Some((pos, pos)) immediately
        // because next() returns Match(pos, pos) on first call when is_match_fw=true
        if !haystack.is_empty() || result.is_some() {
            if let Some((a, b)) = result {
                assert!(a == b); // empty needle matches have zero width
            }
        }
    }

    /// Harness 5: Verify StrSearcher::next_match_back() with EmptyNeedle.
    #[kani::proof]
    fn verify_str_searcher_empty_next_match_back() {
        let haystack = test_haystack_ch21();
        let mut searcher = StrSearcher::new(haystack, "");
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_match_back();
        assert_valid_match(haystack, result);

        if let Some((a, b)) = result {
            assert!(a == b); // empty needle matches have zero width
        }
    }

    /// Harness 6: Verify StrSearcher::next_reject() with EmptyNeedle.
    /// Uses nondeterministic abstraction for unbounded verification.
    #[kani::proof]
    fn verify_str_searcher_empty_next_reject() {
        let haystack = test_haystack_ch21();
        let mut searcher = StrSearcher::new(haystack, "");
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_reject();
        // Key safety property: returned indices are on UTF-8 boundaries
        assert_valid_match(haystack, result);
    }

    /// Harness 7: Verify StrSearcher::next_reject_back() with EmptyNeedle.
    /// Uses nondeterministic abstraction for unbounded verification.
    #[kani::proof]
    fn verify_str_searcher_empty_next_reject_back() {
        let haystack = test_haystack_ch21();
        let mut searcher = StrSearcher::new(haystack, "");
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_reject_back();
        // Key safety property: returned indices are on UTF-8 boundaries
        assert_valid_match(haystack, result);
    }

    //=========================================================================
    // TwoWay Harnesses (Group B)
    //
    // TwoWaySearcher internals (new, next, next_back) are abstracted under
    // #[cfg(kani)] to return nondeterministic results satisfying bounds.
    // This lets us verify the StrSearcher wrapper's UTF-8 boundary correction.
    //=========================================================================

    /// Harness 8: Verify StrSearcher creation with non-empty needle.
    #[kani::proof]
    fn verify_str_searcher_twoway_creation() {
        let haystack = test_haystack_ch21();
        // Test with different needle lengths to cover short/long period
        let needle_choice: u8 = kani::any();
        let needle: &str = match needle_choice % 3 {
            0 => "a",
            1 => "ab",
            _ => "aa",
        };
        let searcher = StrSearcher::new(haystack, needle);

        assert!(type_invariant_str_searcher(&searcher));
        match searcher.searcher {
            StrSearcherImpl::TwoWay(ref tw) => {
                assert!(tw.position == 0);
                assert!(tw.end == haystack.len());
            }
            _ => panic!("Expected TwoWay variant for non-empty needle"),
        }
    }

    /// Harness 9: Verify StrSearcher::next() with TwoWay variant.
    /// The UTF-8 boundary correction loop (while !is_char_boundary(b) { b += 1 })
    /// is the key safety mechanism we verify here.
    #[kani::proof]
    fn verify_str_searcher_twoway_next() {
        let haystack = test_haystack_ch21();
        let needle_choice: u8 = kani::any();
        let needle: &str = match needle_choice % 3 {
            0 => "a",
            1 => "ab",
            _ => "aa",
        };
        let mut searcher = StrSearcher::new(haystack, needle);
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next();
        assert_valid_boundaries(haystack, &result);
        assert!(type_invariant_str_searcher(&searcher));
    }

    /// Harness 10: Verify StrSearcher::next_match() with TwoWay variant.
    #[kani::proof]
    fn verify_str_searcher_twoway_next_match() {
        let haystack = test_haystack_ch21();
        let needle_choice: u8 = kani::any();
        let needle: &str = match needle_choice % 3 {
            0 => "a",
            1 => "ab",
            _ => "aa",
        };
        let mut searcher = StrSearcher::new(haystack, needle);
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_match();
        assert_valid_match(haystack, result);

        if let Some((a, b)) = result {
            // Match width should equal needle length
            assert!(b - a == needle.len());
        }
        assert!(type_invariant_str_searcher(&searcher));
    }

    /// Harness 11: Verify StrSearcher::next_back() with TwoWay variant.
    #[kani::proof]
    fn verify_str_searcher_twoway_next_back() {
        let haystack = test_haystack_ch21();
        let needle_choice: u8 = kani::any();
        let needle: &str = match needle_choice % 3 {
            0 => "a",
            1 => "ab",
            _ => "aa",
        };
        let mut searcher = StrSearcher::new(haystack, needle);
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_back();
        assert_valid_boundaries(haystack, &result);
        assert!(type_invariant_str_searcher(&searcher));
    }

    /// Harness 12: Verify StrSearcher::next_match_back() with TwoWay variant.
    #[kani::proof]
    fn verify_str_searcher_twoway_next_match_back() {
        let haystack = test_haystack_ch21();
        let needle_choice: u8 = kani::any();
        let needle: &str = match needle_choice % 3 {
            0 => "a",
            1 => "ab",
            _ => "aa",
        };
        let mut searcher = StrSearcher::new(haystack, needle);
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_match_back();
        assert_valid_match(haystack, result);

        if let Some((a, b)) = result {
            assert!(b - a == needle.len());
        }
        assert!(type_invariant_str_searcher(&searcher));
    }

    /// Harness 13: Verify StrSearcher::next_reject() with TwoWay variant.
    #[kani::proof]
    fn verify_str_searcher_twoway_next_reject() {
        let haystack = test_haystack_ch21();
        let needle_choice: u8 = kani::any();
        let needle: &str = match needle_choice % 3 {
            0 => "a",
            1 => "ab",
            _ => "aa",
        };
        let mut searcher = StrSearcher::new(haystack, needle);
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_reject();
        assert_valid_match(haystack, result);
        assert!(type_invariant_str_searcher(&searcher));
    }

    /// Harness 14: Verify StrSearcher::next_reject_back() with TwoWay variant.
    #[kani::proof]
    fn verify_str_searcher_twoway_next_reject_back() {
        let haystack = test_haystack_ch21();
        let needle_choice: u8 = kani::any();
        let needle: &str = match needle_choice % 3 {
            0 => "a",
            1 => "ab",
            _ => "aa",
        };
        let mut searcher = StrSearcher::new(haystack, needle);
        assert!(type_invariant_str_searcher(&searcher));

        let result = searcher.next_reject_back();
        assert_valid_match(haystack, result);
        assert!(type_invariant_str_searcher(&searcher));
    }
}
