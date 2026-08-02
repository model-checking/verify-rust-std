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
#[cfg_attr(kani, derive(kani::Arbitrary))]
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

    #[cfg(kani)]
    fn utf8_encoded_matches(&self, slice: &[u8]) -> bool {
        // Kani-only replacement for
        // `slice == &self.utf8_encoded[..self.utf8_size()]`.
        //
        // All call sites provide a 1..=4-byte candidate. Matching on the cached
        // width also makes a width mismatch return false. The finite cases avoid
        // lowering symbolic-length slice equality to CBMC's `memcmp` model.
        match (self.utf8_size, slice) {
            (1, [b0]) => *b0 == self.utf8_encoded[0],
            (2, [b0, b1]) => *b0 == self.utf8_encoded[0] && *b1 == self.utf8_encoded[1],
            (3, [b0, b1, b2]) => {
                *b0 == self.utf8_encoded[0]
                    && *b1 == self.utf8_encoded[1]
                    && *b2 == self.utf8_encoded[2]
            }
            (4, [b0, b1, b2, b3]) => {
                *b0 == self.utf8_encoded[0]
                    && *b1 == self.utf8_encoded[1]
                    && *b2 == self.utf8_encoded[2]
                    && *b3 == self.utf8_encoded[3]
            }
            _ => false,
        }
    }

    #[cfg(kani)]
    fn utf8_encoding_matches_needle(&self) -> bool {
        // Explicit refinement of the cached representation produced by
        // `char::encode_utf8`. The constructor harness proves these four cases
        // from the production constructor; method harnesses carry them in C.
        let code = self.needle as u32;
        let bytes = &self.utf8_encoded;

        match self.utf8_size() {
            1 => code <= 0x7f && bytes[0] as u32 == code,
            2 => {
                code >= 0x80
                    && code <= 0x7ff
                    && bytes[0] == (0xc0 | (code >> 6) as u8)
                    && bytes[1] == (0x80 | (code & 0x3f) as u8)
            }
            3 => {
                code >= 0x800
                    && code <= 0xffff
                    && (code < 0xd800 || code > 0xdfff)
                    && bytes[0] == (0xe0 | (code >> 12) as u8)
                    && bytes[1] == (0x80 | ((code >> 6) & 0x3f) as u8)
                    && bytes[2] == (0x80 | (code & 0x3f) as u8)
            }
            4 => {
                code >= 0x10000
                    && code <= 0x10ffff
                    && bytes[0] == (0xf0 | (code >> 18) as u8)
                    && bytes[1] == (0x80 | ((code >> 12) & 0x3f) as u8)
                    && bytes[2] == (0x80 | ((code >> 6) & 0x3f) as u8)
                    && bytes[3] == (0x80 | (code & 0x3f) as u8)
            }
            _ => false,
        }
    }
}

unsafe impl<'a> Searcher<'a> for CharSearcher<'a> {
    #[inline]
    fn haystack(&self) -> &'a str {
        self.haystack
    }
    #[cfg_attr(
        kani,
        kani::requires(kani_pattern_harness_helpers::type_invariant_char_searcher(self))
    )]
    #[cfg_attr(kani, kani::modifies(&mut self.finger))]
    #[cfg_attr(kani, kani::ensures(|step: &SearchStep| {
        kani_pattern_harness_helpers::type_invariant_char_searcher(self)
            && kani_pattern_harness_helpers::valid_char_next_step(
                self.haystack,
                old(self.finger),
                old(self.finger_back),
                self.finger,
                self.finger_back,
                *step,
            )
    }))]
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
        #[cfg(not(kani))]
        {
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

        #[cfg(kani)]
        {
            let step = if let Some(ch) = iter.next() {
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
            };

            kani_pattern_harness_helpers::assume_valid_utf8_forward_boundary(
                self.haystack,
                old_finger,
                self.finger_back,
                self.finger,
            );
            step
        }
    }
    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        #[cfg(kani)]
        let search_start = self.finger;
        #[cfg(kani)]
        let search_end = self.finger_back;

        // Loop stubbing: verify the real loop body at an arbitrary
        // loop-head state, then over-approximate the remaining iterations.
        // A loop-head `finger` need not be a UTF-8 boundary.
        #[cfg(kani)]
        {
            assert!(kani_pattern_harness_helpers::valid_char_next_match_loop_head(
                self,
                search_start,
                search_end,
            ));
            self.finger =
                kani::any_where(|finger: &usize| search_start <= *finger && *finger <= search_end);
            assert!(kani_pattern_harness_helpers::valid_char_next_match_loop_head(
                self,
                search_start,
                search_end,
            ));
        }

        loop {
            #[cfg(kani)]
            let iteration_start = self.finger;

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
                        #[cfg(kani)]
                        if self.utf8_encoded_matches(slice) {
                            return Some((found_char, self.finger));
                        }
                        #[cfg(not(kani))]
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

            #[cfg(kani)]
            {
                // Every continuing concrete iteration strictly reduces
                // `search_end - self.finger` and re-establishes the abstract
                // loop-head relation. This justifies using one arbitrary
                // representative iteration for the unbounded scan.
                assert!(iteration_start < self.finger);
                assert!(self.finger <= search_end);
                assert!(search_end - self.finger < search_end - iteration_start);
                assert!(kani_pattern_harness_helpers::valid_char_next_match_loop_head(
                    self,
                    search_start,
                    search_end,
                ));

                return kani_pattern_harness_helpers::stub_char_next_match_remaining(
                    self,
                    search_start,
                    search_end,
                );
            }
        }
    }

    // let next_reject use the default implementation from the Searcher trait

    // Kani needs a concrete override so its loop contract can refer to
    // `CharSearcher` state. Non-Kani builds use the `Searcher` default.
    #[cfg(kani)]
    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        let search_start = self.finger;
        let search_end = self.finger_back;
        let haystack_len = self.haystack.len();
        let search_end_is_boundary = self.haystack.is_char_boundary(search_end);
        let utf8_size = self.utf8_size;
        let mut old_finger = self.finger;
        let mut old_finger_back = self.finger_back;
        let mut step = SearchStep::Done;

        // == Kani Loop Contract Start: CharSearcher::next_reject ==
        #[cfg_attr(kani, kani::loop_invariant(
            search_start <= self.finger
                && self.finger <= search_end
                && self.finger_back == search_end
                && search_end <= haystack_len
                && search_end_is_boundary
                && self.haystack.is_char_boundary(self.finger)
                && self.utf8_size == utf8_size
                && 1 <= self.utf8_size
                && self.utf8_size <= MAX_LEN_UTF8 as u8
        ))]
        #[cfg_attr(kani, kani::loop_modifies(
            &self.finger,
            &old_finger,
            &old_finger_back,
            &step
        ))]
        // == Kani Loop Contract End: CharSearcher::next_reject ==
        loop {
            assert!(self.haystack.is_char_boundary(self.finger));
            assert!(self.haystack.is_char_boundary(self.finger_back));
            // `next` decodes a `char` from this active window. Under the
            // challenge assumptions, a subslice of a valid `str` whose
            // endpoints are UTF-8 boundaries is itself valid UTF-8; this
            // is the pre-call cut needed for `next_code_point`'s
            // `unwrap_unchecked` continuation-byte reads.
            kani::assume(
                crate::str::from_utf8(
                    self.haystack.as_bytes().get(self.finger..self.finger_back).unwrap(),
                )
                .is_ok(),
            );

            old_finger = self.finger;
            old_finger_back = self.finger_back;
            step = self.next();

            kani_pattern_harness_helpers::assume_valid_utf8_forward_boundary(
                self.haystack,
                old_finger,
                old_finger_back,
                self.finger,
            );
            assert!(kani_pattern_harness_helpers::valid_char_next_step(
                self.haystack,
                old_finger,
                old_finger_back,
                self.finger,
                self.finger_back,
                step,
            ));

            match step {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }
}

unsafe impl<'a> ReverseSearcher<'a> for CharSearcher<'a> {
    #[cfg_attr(
        kani,
        kani::requires(kani_pattern_harness_helpers::type_invariant_char_searcher(self))
    )]
    #[cfg_attr(kani, kani::modifies(&mut self.finger_back))]
    #[cfg_attr(kani, kani::ensures(|step: &SearchStep| {
        kani_pattern_harness_helpers::type_invariant_char_searcher(self)
            && kani_pattern_harness_helpers::valid_char_next_back_step(
                self.haystack,
                old(self.finger),
                old(self.finger_back),
                self.finger,
                self.finger_back,
                *step,
            )
    }))]
    #[inline]
    fn next_back(&mut self) -> SearchStep {
        let old_finger = self.finger_back;
        // SAFETY: see the comment for next() above
        let slice = unsafe { self.haystack.get_unchecked(self.finger..old_finger) };
        let mut iter = slice.chars();
        let old_len = iter.iter.len();
        #[cfg(not(kani))]
        {
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

        #[cfg(kani)]
        {
            let step = if let Some(ch) = iter.next_back() {
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
            };

            kani_pattern_harness_helpers::assume_valid_utf8_reverse_boundary(
                self.haystack,
                self.finger,
                old_finger,
                self.finger_back,
                step,
            );
            step
        }
    }
    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        let haystack = self.haystack.as_bytes();
        #[cfg(kani)]
        let search_start = self.finger;
        #[cfg(kani)]
        let search_end = self.finger_back;
        #[cfg(kani)]
        let haystack_len = self.haystack.len();
        #[cfg(kani)]
        let haystack_ptr = self.haystack.as_ptr();
        #[cfg(kani)]
        let search_start_is_boundary = self.haystack.is_char_boundary(search_start);
        #[cfg(kani)]
        let search_end_is_boundary = self.haystack.is_char_boundary(search_end);
        #[cfg(kani)]
        let utf8_size = self.utf8_size;
        #[cfg(kani)]
        let needle = self.needle;
        #[cfg(kani)]
        let utf8_encoded_0 = self.utf8_encoded[0];
        #[cfg(kani)]
        let utf8_encoded_1 = self.utf8_encoded[1];
        #[cfg(kani)]
        let utf8_encoded_2 = self.utf8_encoded[2];
        #[cfg(kani)]
        let utf8_encoded_3 = self.utf8_encoded[3];

        // == Kani Loop Contract Start: CharSearcher::next_match_back ==
        #[cfg_attr(kani, kani::loop_invariant(
            self.haystack.as_ptr() == haystack_ptr
                && self.haystack.len() == haystack_len
                && self.needle == needle
                && self.utf8_encoded[0] == utf8_encoded_0
                && self.utf8_encoded[1] == utf8_encoded_1
                && self.utf8_encoded[2] == utf8_encoded_2
                && self.utf8_encoded[3] == utf8_encoded_3
                && self.finger == search_start
                && search_start <= self.finger_back
                && self.finger_back <= search_end
                && search_end <= haystack_len
                && search_start_is_boundary
                && search_end_is_boundary
                && self.utf8_size == utf8_size
                && 1 <= self.utf8_size
                && self.utf8_size <= MAX_LEN_UTF8 as u8
        ))]
        // == Kani Loop Contract End: CharSearcher::next_match_back ==
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
                        #[cfg(kani)]
                        if self.utf8_encoded_matches(slice) {
                            // move finger to before the character found (i.e., at its start index)
                            self.finger_back = found_char;
                            return Some((self.finger_back, self.finger_back + self.utf8_size()));
                        }
                        #[cfg(not(kani))]
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

    // Kani needs a concrete override so its loop contract can refer to
    // `CharSearcher` state. Non-Kani builds use the `ReverseSearcher` default.
    #[cfg(kani)]
    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        let search_start = self.finger;
        let search_end = self.finger_back;
        let haystack_len = self.haystack.len();
        let search_start_is_boundary = self.haystack.is_char_boundary(search_start);
        let search_end_is_boundary = self.haystack.is_char_boundary(search_end);
        let utf8_size = self.utf8_size;
        let mut old_finger = self.finger;
        let mut old_finger_back = self.finger_back;
        let mut step = SearchStep::Done;

        // == Kani Loop Contract Start: CharSearcher::next_reject_back ==
        #[cfg_attr(kani, kani::loop_invariant(
            self.finger == search_start
                && search_start <= self.finger_back
                && self.finger_back <= search_end
                && search_end <= haystack_len
                && search_start_is_boundary
                && search_end_is_boundary
                && self.haystack.is_char_boundary(self.finger_back)
                && self.utf8_size == utf8_size
                && 1 <= self.utf8_size
                && self.utf8_size <= MAX_LEN_UTF8 as u8
        ))]
        #[cfg_attr(kani, kani::loop_modifies(
            &self.finger_back,
            &old_finger,
            &old_finger_back,
            &step
        ))]
        // == Kani Loop Contract End: CharSearcher::next_reject_back ==
        loop {
            assert!(self.haystack.is_char_boundary(self.finger));
            assert!(self.haystack.is_char_boundary(self.finger_back));
            kani::assume(
                crate::str::from_utf8(
                    self.haystack.as_bytes().get(self.finger..self.finger_back).unwrap(),
                )
                .is_ok(),
            );

            old_finger = self.finger;
            old_finger_back = self.finger_back;
            step = self.next_back();

            kani_pattern_harness_helpers::assume_valid_utf8_reverse_boundary(
                self.haystack,
                old_finger,
                old_finger_back,
                self.finger_back,
                step,
            );
            assert!(kani_pattern_harness_helpers::valid_char_next_back_step(
                self.haystack,
                old_finger,
                old_finger_back,
                self.finger,
                self.finger_back,
                step,
            ));

            match step {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
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
        #[cfg(kani)]
        {
            let _ = (self, c);

            // Challenge 20 allows the safety and functional correctness of
            // slice operations to be assumed. For Searcher safety, `contains`
            // only chooses Match versus Reject after the consumed UTF-8 range
            // has already been computed; it cannot affect the range or the
            // CharIndices state. An arbitrary boolean is therefore a sound
            // over-approximation of every real result and avoids unwinding the
            // dynamic slice implementation of `contains`. This abstraction is
            // not suitable for proving functional matching semantics.
            kani::any()
        }

        #[cfg(not(kani))]
        {
            self.contains(&c)
        }
    }
}

struct MultiCharEqPattern<C: MultiCharEq>(C);

#[derive(Clone, Debug)]
struct MultiCharEqSearcher<'a, C: MultiCharEq> {
    char_eq: C,
    haystack: &'a str,
    char_indices: super::CharIndices<'a>,
}

#[cfg(kani)]
fn kani_utf8_char_len_from_first_byte(first: u8) -> usize {
    if first < 0x80 {
        1
    } else if first < 0xe0 {
        2
    } else if first < 0xf0 {
        3
    } else {
        4
    }
}

#[cfg(kani)]
fn kani_utf8_char_start_before(haystack: &str, cursor: usize) -> Option<usize> {
    let bytes = haystack.as_bytes();
    let last_index = cursor.checked_sub(1)?;
    let last = *bytes.get(last_index)?;
    if last < 0x80 {
        return Some(last_index);
    }

    let second_index = cursor.checked_sub(2)?;
    let second_last = *bytes.get(second_index)?;
    if (second_last as i8) >= -64 {
        return Some(second_index);
    }

    let third_index = cursor.checked_sub(3)?;
    let third_last = *bytes.get(third_index)?;
    if (third_last as i8) >= -64 {
        return Some(third_index);
    }

    let fourth_index = cursor.checked_sub(4)?;
    let fourth_last = *bytes.get(fourth_index)?;
    if (fourth_last as i8) >= -64 { Some(fourth_index) } else { None }
}

#[cfg(kani)]
impl<'a, C: MultiCharEq> MultiCharEqSearcher<'a, C> {
    #[inline]
    fn kani_rebuild_char_indices_window(&mut self, front: usize, back: usize) {
        let haystack = self.haystack;
        self.char_indices.front_offset = front;
        self.char_indices.iter = haystack.get(front..back).unwrap().chars();
    }
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

    // Kani-only safety loop stub. The abstraction intentionally excludes
    // matcher-internal state and summarizes only the remaining search window.
    #[cfg(kani)]
    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        let initial = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
        let search_start = initial.front;
        let search_end = initial.back;

        assert!(kani_pattern_harness_helpers::valid_multi_char_eq_next_match_loop_head(
            self,
            search_start,
            search_end,
        ));

        loop {
            let before = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
            let step = self.next();
            let after = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);

            kani_pattern_harness_helpers::assume_valid_utf8_forward_boundary(
                self.haystack,
                before.front,
                before.back,
                after.front,
            );
            assert!(kani_pattern_harness_helpers::type_invariant_multi_char_eq_searcher(self));
            // The projection plus the preserved type invariant already implies
            // the complete one-step range and state relation. The continuing
            // arm below keeps the strict progress facts needed by the loop stub.
            assert!(kani_pattern_harness_helpers::valid_multi_char_eq_forward_projection(
                before,
                after,
                step,
                self.haystack,
            ));

            match step {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Reject(_, _) => {
                    assert!(before.front < after.front);
                    assert!(after.remaining < before.remaining);
                    assert!(
                        kani_pattern_harness_helpers::valid_multi_char_eq_next_match_loop_head(
                            self,
                            search_start,
                            search_end,
                        )
                    );

                    return kani_pattern_harness_helpers::stub_multi_char_eq_next_match_remaining(
                        self,
                        search_start,
                        search_end,
                    );
                }
            }
        }
    }

    // Reject-filtering counterpart of the Kani-only safety loop stub.
    #[cfg(kani)]
    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        let initial = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
        let search_start = initial.front;
        let search_end = initial.back;

        assert!(kani_pattern_harness_helpers::valid_multi_char_eq_next_reject_loop_head(
            self,
            search_start,
            search_end,
        ));

        loop {
            let before = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
            let step = self.next();
            let after = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);

            kani_pattern_harness_helpers::assume_valid_utf8_forward_boundary(
                self.haystack,
                before.front,
                before.back,
                after.front,
            );
            assert!(kani_pattern_harness_helpers::type_invariant_multi_char_eq_searcher(self));
            // The projection plus the preserved type invariant already implies
            // the complete one-step range and state relation. The continuing
            // arm below keeps the strict progress facts needed by the loop stub.
            assert!(kani_pattern_harness_helpers::valid_multi_char_eq_forward_projection(
                before,
                after,
                step,
                self.haystack,
            ));

            match step {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Match(_, _) => {
                    assert!(before.front < after.front);
                    assert!(after.remaining < before.remaining);
                    assert!(
                        kani_pattern_harness_helpers::valid_multi_char_eq_next_reject_loop_head(
                            self,
                            search_start,
                            search_end,
                        )
                    );

                    return kani_pattern_harness_helpers::stub_multi_char_eq_next_reject_remaining(
                        self,
                        search_start,
                        search_end,
                    );
                }
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

    // Reverse counterpart of the Kani-only match-filtering safety loop stub.
    #[cfg(kani)]
    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        let initial = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
        let search_start = initial.front;
        let search_end = initial.back;

        assert!(kani_pattern_harness_helpers::valid_multi_char_eq_next_match_back_loop_head(
            self,
            search_start,
            search_end,
        ));

        loop {
            let before = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
            let step = self.next_back();
            let after = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);

            kani_pattern_harness_helpers::assume_valid_utf8_reverse_boundary(
                self.haystack,
                before.front,
                before.back,
                after.back,
                step,
            );
            assert!(kani_pattern_harness_helpers::type_invariant_multi_char_eq_searcher(self));
            // The projection plus the preserved type invariant already implies
            // the complete reverse one-step range and state relation. The
            // continuing arm below retains the strict progress facts for the stub.
            assert!(kani_pattern_harness_helpers::valid_multi_char_eq_reverse_projection(
                before,
                after,
                step,
                self.haystack,
            ));

            match step {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Reject(_, _) => {
                    assert!(after.back < before.back);
                    assert!(after.remaining < before.remaining);
                    assert!(
                        kani_pattern_harness_helpers::valid_multi_char_eq_next_match_back_loop_head(
                            self,
                            search_start,
                            search_end,
                        )
                    );

                    return kani_pattern_harness_helpers::stub_multi_char_eq_next_match_back_remaining(
                        self,
                        search_start,
                        search_end,
                    );
                }
            }
        }
    }

    // Reverse counterpart of the Kani-only reject-filtering safety loop stub.
    #[cfg(kani)]
    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        let initial = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
        let search_start = initial.front;
        let search_end = initial.back;

        assert!(kani_pattern_harness_helpers::valid_multi_char_eq_next_reject_back_loop_head(
            self,
            search_start,
            search_end,
        ));

        loop {
            let before = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);
            let step = self.next_back();
            let after = kani_pattern_harness_helpers::char_indices_state(&self.char_indices);

            kani_pattern_harness_helpers::assume_valid_utf8_reverse_boundary(
                self.haystack,
                before.front,
                before.back,
                after.back,
                step,
            );
            assert!(kani_pattern_harness_helpers::type_invariant_multi_char_eq_searcher(self));
            // The projection plus the preserved type invariant already implies
            // the complete reverse one-step range and state relation. The
            // continuing arm below retains the strict progress facts for the stub.
            assert!(kani_pattern_harness_helpers::valid_multi_char_eq_reverse_projection(
                before,
                after,
                step,
                self.haystack,
            ));

            match step {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                SearchStep::Match(_, _) => {
                    assert!(after.back < before.back);
                    assert!(after.remaining < before.remaining);
                    assert!(
                        kani_pattern_harness_helpers::valid_multi_char_eq_next_reject_back_loop_head(
                            self,
                            search_start,
                            search_end,
                        )
                    );

                    return kani_pattern_harness_helpers::stub_multi_char_eq_next_reject_back_remaining(
                        self,
                        search_start,
                        search_end,
                    );
                }
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
mod kani_pattern_harness_helpers {
    use super::super::CharIndices;
    use super::*;

    pub(super) const MAX_UTF8_BYTES: usize = 4;

    pub(super) fn any_valid_utf8_str<'a, const MAX: usize>(bytes: &'a [u8; MAX]) -> &'a str {
        let xs: &[u8] = kani::slice::any_slice_of_array(bytes);
        match crate::str::from_utf8(xs) {
            Ok(s) => s,
            Err(_) => {
                kani::assume(false);
                ""
            }
        }
    }

    // Type invariant C for CharSearcher.
    //
    // This predicate gives sufficient safety and representation-consistency
    // conditions for calls to the Searcher and ReverseSearcher methods:
    // - `finger..finger_back` is a well-formed byte range inside `haystack`.
    // - Both ends of the active range are valid UTF-8 boundaries, as required
    //   by the unsafe Searcher/ReverseSearcher contracts and by the unchecked
    //   slicing in `next` and `next_back`.
    // - `utf8_size` is the length of one encoded `char`, so it is never zero
    //   and never greater than the fixed four-byte UTF-8 buffer.
    // - `utf8_encoded[..utf8_size]` is exactly the UTF-8 encoding of `needle`;
    //   this ties the cached bytes used by `next_match` and `next_match_back`
    //   back to the semantic character being searched for.
    pub(super) fn type_invariant_char_searcher(s: &CharSearcher<'_>) -> bool {
        s.finger <= s.finger_back
            && s.finger_back <= s.haystack.len()
            && s.haystack.is_char_boundary(s.finger)
            && s.haystack.is_char_boundary(s.finger_back)
            && 1 <= s.utf8_size()
            && s.utf8_size() <= 4
            && s.utf8_encoding_matches_needle()
    }

    // Abstract loop-head relation for `CharSearcher::next_match`.
    //
    // Unlike the public type invariant, this deliberately does not require
    // `s.finger` to be a UTF-8 boundary. The byte scan can stop on a
    // continuation byte before a later iteration finds the complete needle.
    pub(super) fn valid_char_next_match_loop_head(
        s: &CharSearcher<'_>,
        search_start: usize,
        search_end: usize,
    ) -> bool {
        search_start <= s.finger
            && s.finger <= search_end
            && s.finger_back == search_end
            && search_end <= s.haystack.len()
            && s.haystack.is_char_boundary(search_start)
            && s.haystack.is_char_boundary(search_end)
            && 1 <= s.utf8_size()
            && s.utf8_size() <= MAX_LEN_UTF8
            && s.utf8_encoding_matches_needle()
    }

    // Exit relation used by the loop stub for the unexecuted suffix of
    // `CharSearcher::next_match`. It omits UTF-8 boundary facts: the harness
    // imports those only after proving that a successful range contains the
    // complete cached encoding of `needle` in a valid UTF-8 haystack.
    pub(super) fn valid_char_next_match_stub_result(
        s: &CharSearcher<'_>,
        search_start: usize,
        search_end: usize,
        result: Option<(usize, usize)>,
    ) -> bool {
        if !valid_char_next_match_loop_head(s, search_start, search_end) {
            return false;
        }

        match result {
            Some((a, b)) => {
                if search_start > a || a >= b || b > search_end || b != s.finger {
                    return false;
                }
                let Some(candidate) = s.haystack.as_bytes().get(a..b) else {
                    return false;
                };
                b - a == s.utf8_size() && s.utf8_encoded_matches(candidate)
            }
            None => s.finger == search_end,
        }
    }

    // Over-approximate every possible exit after a continuing representative
    // iteration. `None` is always possible in the abstraction. A symbolic
    // `Some` is restricted only by safety-relevant facts true of every concrete
    // successful exit; it intentionally does not promise the first match.
    pub(super) fn stub_char_next_match_remaining(
        s: &mut CharSearcher<'_>,
        search_start: usize,
        search_end: usize,
    ) -> Option<(usize, usize)> {
        assert!(valid_char_next_match_loop_head(s, search_start, search_end));

        let result = if kani::any::<bool>() {
            let a: usize = kani::any();
            let b: usize = kani::any();
            kani::assume(search_start <= a);
            kani::assume(a < b);
            kani::assume(b <= search_end);
            kani::assume(b - a == s.utf8_size());

            let candidate = s.haystack.as_bytes().get(a..b).unwrap();
            kani::assume(s.utf8_encoded_matches(candidate));

            s.finger = b;
            Some((a, b))
        } else {
            s.finger = search_end;
            None
        };

        assert!(valid_char_next_match_stub_result(s, search_start, search_end, result,));
        result
    }

    // Type invariant C for MultiCharEqSearcher.
    //
    // `front_offset` and the remaining byte iterator describe the active
    // search window in the original haystack. The iterator must be safe to
    // read, must point at exactly that haystack window, and both ends of the
    // window must be UTF-8 character boundaries. `char_eq` is intentionally
    // excluded because it only selects Match or Reject and does not affect the
    // returned range.
    pub(super) fn type_invariant_multi_char_eq_searcher<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
    ) -> bool {
        let byte_iter = &s.char_indices.iter.iter;
        if !crate::ub_checks::Invariant::is_safe(byte_iter) {
            return false;
        }

        let remaining = byte_iter.as_slice();
        let front = s.char_indices.front_offset;
        let Some(back) = front.checked_add(remaining.len()) else {
            return false;
        };
        let Some(expected) = s.haystack.as_bytes().get(front..back) else {
            return false;
        };

        crate::ptr::eq(remaining, expected)
            && s.haystack.is_char_boundary(front)
            && s.haystack.is_char_boundary(back)
    }

    // Type invariant C for CharArraySearcher.
    //
    // CharArraySearcher only wraps the MultiCharEqSearcher created for its
    // owned char array, so it introduces no additional safety-relevant state.
    pub(super) fn type_invariant_char_array<const N: usize>(s: &CharArraySearcher<'_, N>) -> bool {
        type_invariant_multi_char_eq_searcher(&s.0)
    }

    // Type invariant C for CharArrayRefSearcher.
    //
    // The borrowed char array only determines Match versus Reject. The wrapper
    // adds no safety-relevant state beyond its inner MultiCharEqSearcher.
    pub(super) fn type_invariant_char_array_ref<const N: usize>(
        s: &CharArrayRefSearcher<'_, '_, N>,
    ) -> bool {
        type_invariant_multi_char_eq_searcher(&s.0)
    }

    // Type invariant C for CharSliceSearcher.
    //
    // The borrowed char slice only determines Match versus Reject. The wrapper
    // adds no safety-relevant state beyond its inner MultiCharEqSearcher.
    pub(super) fn type_invariant_char_slice(s: &CharSliceSearcher<'_, '_>) -> bool {
        type_invariant_multi_char_eq_searcher(&s.0)
    }

    // Type invariant C for CharPredicateSearcher.
    //
    // The predicate may mutate its captured state, but it only determines Match
    // versus Reject. It cannot affect the active haystack window or UTF-8 indices.
    pub(super) fn type_invariant_char_predicate<F>(s: &CharPredicateSearcher<'_, F>) -> bool
    where
        F: FnMut(char) -> bool,
    {
        type_invariant_multi_char_eq_searcher(&s.0)
    }

    // Safety condition for any range returned by `Searcher::next`.
    //
    // The unsafe `Searcher` contract requires returned indices to be valid
    // UTF-8 boundaries in the same haystack. The range must also be ordered
    // and in bounds so consumers can safely slice `haystack[a..b]`.
    pub(super) fn valid_range_on_haystack(haystack: &str, a: usize, b: usize) -> bool {
        a <= b
            && b <= haystack.len()
            && haystack.is_char_boundary(a)
            && haystack.is_char_boundary(b)
    }

    // Snapshot of the numeric `CharIndices` window and progress state. Iterator
    // validity and pointer identity are checked separately by the type invariant.
    #[derive(Clone, Copy)]
    pub(super) struct CharIndicesState {
        pub(super) front: usize,
        pub(super) remaining: usize,
        pub(super) back: usize,
    }

    pub(super) fn char_indices_state(char_indices: &CharIndices<'_>) -> CharIndicesState {
        let front = char_indices.front_offset;
        let remaining = char_indices.iter.iter.len();
        let back = front.checked_add(remaining).unwrap();
        CharIndicesState { front, remaining, back }
    }

    // Abstract loop-head relation for the safety-only
    // `MultiCharEqSearcher::next_match` loop stub. Matcher state is omitted.
    pub(super) fn valid_multi_char_eq_next_match_loop_head<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> bool {
        if !type_invariant_multi_char_eq_searcher(s) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        search_start <= state.front && state.back == search_end
    }

    // Exit relation for the unexecuted suffix of the safety-only `next_match`
    // loop. It captures only safety-relevant facts, not matcher state or
    // first-match semantics.
    pub(super) fn valid_multi_char_eq_next_match_stub_result<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
        suffix_start: usize,
        result: Option<(usize, usize)>,
    ) -> bool {
        if !valid_multi_char_eq_next_match_loop_head(s, search_start, search_end) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        match result {
            Some((a, b)) => {
                suffix_start <= a
                    && a < b
                    && b <= search_end
                    && b == state.front
                    && state.back == search_end
                    && b - a <= MAX_LEN_UTF8
                    && valid_range_on_haystack(s.haystack, a, b)
            }
            None => state.front == search_end && state.remaining == 0,
        }
    }

    // Over-approximate every safety-relevant exit after one real rejecting
    // iteration. Matcher-internal state is outside this abstraction.
    pub(super) fn stub_multi_char_eq_next_match_remaining<C: MultiCharEq>(
        s: &mut MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> Option<(usize, usize)> {
        assert!(valid_multi_char_eq_next_match_loop_head(s, search_start, search_end));

        let suffix_start = char_indices_state(&s.char_indices).front;
        let result = if suffix_start < search_end && kani::any::<bool>() {
            let a: usize = kani::any();
            let b: usize = kani::any();
            kani::assume(suffix_start <= a);
            kani::assume(a < b);
            kani::assume(b <= search_end);
            kani::assume(b - a <= MAX_LEN_UTF8);
            kani::assume(s.haystack.is_char_boundary(a));
            kani::assume(s.haystack.is_char_boundary(b));

            s.kani_rebuild_char_indices_window(b, search_end);
            Some((a, b))
        } else {
            s.kani_rebuild_char_indices_window(search_end, search_end);
            None
        };

        assert!(valid_multi_char_eq_next_match_stub_result(
            s,
            search_start,
            search_end,
            suffix_start,
            result,
        ));
        result
    }

    // Abstract loop-head relation for the safety-only
    // `MultiCharEqSearcher::next_reject` loop stub. Matcher state is omitted.
    pub(super) fn valid_multi_char_eq_next_reject_loop_head<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> bool {
        if !type_invariant_multi_char_eq_searcher(s) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        search_start <= state.front && state.back == search_end
    }

    // Exit relation for the unexecuted suffix of the safety-only `next_reject`
    // loop. It captures only safety-relevant facts, not matcher state or
    // first-reject semantics.
    pub(super) fn valid_multi_char_eq_next_reject_stub_result<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
        suffix_start: usize,
        result: Option<(usize, usize)>,
    ) -> bool {
        if !valid_multi_char_eq_next_reject_loop_head(s, search_start, search_end) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        match result {
            Some((a, b)) => {
                suffix_start <= a
                    && a < b
                    && b <= search_end
                    && b == state.front
                    && state.back == search_end
                    && b - a <= MAX_LEN_UTF8
                    && valid_range_on_haystack(s.haystack, a, b)
            }
            None => state.front == search_end && state.remaining == 0,
        }
    }

    // Over-approximate every safety-relevant exit after one real matching
    // iteration. Matcher-internal state is outside this abstraction.
    pub(super) fn stub_multi_char_eq_next_reject_remaining<C: MultiCharEq>(
        s: &mut MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> Option<(usize, usize)> {
        assert!(valid_multi_char_eq_next_reject_loop_head(s, search_start, search_end));

        let suffix_start = char_indices_state(&s.char_indices).front;
        let result = if suffix_start < search_end && kani::any::<bool>() {
            let a: usize = kani::any();
            let b: usize = kani::any();
            kani::assume(suffix_start <= a);
            kani::assume(a < b);
            kani::assume(b <= search_end);
            kani::assume(b - a <= MAX_LEN_UTF8);
            kani::assume(s.haystack.is_char_boundary(a));
            kani::assume(s.haystack.is_char_boundary(b));

            s.kani_rebuild_char_indices_window(b, search_end);
            Some((a, b))
        } else {
            s.kani_rebuild_char_indices_window(search_end, search_end);
            None
        };

        assert!(valid_multi_char_eq_next_reject_stub_result(
            s,
            search_start,
            search_end,
            suffix_start,
            result,
        ));
        result
    }

    // Abstract loop-head relation for the safety-only
    // `MultiCharEqSearcher::next_match_back` loop stub. Matcher state is omitted.
    pub(super) fn valid_multi_char_eq_next_match_back_loop_head<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> bool {
        if !type_invariant_multi_char_eq_searcher(s) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        state.front == search_start
            && state.back <= search_end
            && search_end <= s.haystack.len()
            && s.haystack.is_char_boundary(search_end)
    }

    // Exit relation for the unexecuted prefix of the safety-only
    // `next_match_back` loop. It captures only safety-relevant facts, not
    // matcher state or last-match semantics.
    pub(super) fn valid_multi_char_eq_next_match_back_stub_result<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
        prefix_end: usize,
        result: Option<(usize, usize)>,
    ) -> bool {
        if !valid_multi_char_eq_next_match_back_loop_head(s, search_start, search_end) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        match result {
            Some((a, b)) => {
                search_start <= a
                    && a < b
                    && b <= prefix_end
                    && a == state.back
                    && state.front == search_start
                    && b - a <= MAX_LEN_UTF8
                    && valid_range_on_haystack(s.haystack, a, b)
            }
            None => state.back == search_start && state.remaining == 0,
        }
    }

    // Over-approximate every safety-relevant exit after one real reverse
    // rejecting iteration. Matcher-internal state is outside this abstraction.
    pub(super) fn stub_multi_char_eq_next_match_back_remaining<C: MultiCharEq>(
        s: &mut MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> Option<(usize, usize)> {
        assert!(valid_multi_char_eq_next_match_back_loop_head(s, search_start, search_end,));

        let prefix_end = char_indices_state(&s.char_indices).back;
        let result = if search_start < prefix_end && kani::any::<bool>() {
            let a: usize = kani::any();
            let b: usize = kani::any();
            kani::assume(search_start <= a);
            kani::assume(a < b);
            kani::assume(b <= prefix_end);
            kani::assume(b - a <= MAX_LEN_UTF8);
            kani::assume(s.haystack.is_char_boundary(a));
            kani::assume(s.haystack.is_char_boundary(b));

            s.kani_rebuild_char_indices_window(search_start, a);
            Some((a, b))
        } else {
            s.kani_rebuild_char_indices_window(search_start, search_start);
            None
        };

        assert!(valid_multi_char_eq_next_match_back_stub_result(
            s,
            search_start,
            search_end,
            prefix_end,
            result,
        ));
        result
    }

    // Abstract loop-head relation for the safety-only
    // `MultiCharEqSearcher::next_reject_back` loop stub. Matcher state is omitted.
    pub(super) fn valid_multi_char_eq_next_reject_back_loop_head<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> bool {
        if !type_invariant_multi_char_eq_searcher(s) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        state.front == search_start
            && state.back <= search_end
            && search_end <= s.haystack.len()
            && s.haystack.is_char_boundary(search_end)
    }

    // Exit relation for the unexecuted prefix of the safety-only
    // `next_reject_back` loop. It captures only safety-relevant facts, not
    // matcher state or rightmost-reject semantics.
    pub(super) fn valid_multi_char_eq_next_reject_back_stub_result<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
        prefix_end: usize,
        result: Option<(usize, usize)>,
    ) -> bool {
        if !valid_multi_char_eq_next_reject_back_loop_head(s, search_start, search_end) {
            return false;
        }

        let state = char_indices_state(&s.char_indices);
        match result {
            Some((a, b)) => {
                search_start <= a
                    && a < b
                    && b <= prefix_end
                    && a == state.back
                    && state.front == search_start
                    && b - a <= MAX_LEN_UTF8
                    && valid_range_on_haystack(s.haystack, a, b)
            }
            None => state.back == search_start && state.remaining == 0,
        }
    }

    // Over-approximate every safety-relevant exit after one real reverse
    // matching iteration. Matcher-internal state is outside this abstraction.
    pub(super) fn stub_multi_char_eq_next_reject_back_remaining<C: MultiCharEq>(
        s: &mut MultiCharEqSearcher<'_, C>,
        search_start: usize,
        search_end: usize,
    ) -> Option<(usize, usize)> {
        assert!(valid_multi_char_eq_next_reject_back_loop_head(s, search_start, search_end,));

        let prefix_end = char_indices_state(&s.char_indices).back;
        let result = if search_start < prefix_end && kani::any::<bool>() {
            let a: usize = kani::any();
            let b: usize = kani::any();
            kani::assume(search_start <= a);
            kani::assume(a < b);
            kani::assume(b <= prefix_end);
            kani::assume(b - a <= MAX_LEN_UTF8);
            kani::assume(s.haystack.is_char_boundary(a));
            kani::assume(s.haystack.is_char_boundary(b));

            s.kani_rebuild_char_indices_window(search_start, a);
            Some((a, b))
        } else {
            s.kani_rebuild_char_indices_window(search_start, search_start);
            None
        };

        assert!(valid_multi_char_eq_next_reject_back_stub_result(
            s,
            search_start,
            search_end,
            prefix_end,
            result,
        ));
        result
    }

    // Safety projection for one production `MultiCharEqSearcher::next` step.
    // The projection intentionally contains no `char_eq` state: `C::matches`
    // may mutate that state, but it cannot change the already-consumed UTF-8
    // range represented here.
    pub(super) fn valid_multi_char_eq_forward_projection(
        old: CharIndicesState,
        new: CharIndicesState,
        step: SearchStep,
        haystack: &str,
    ) -> bool {
        if old.front > old.back
            || old.back > haystack.len()
            || old.remaining != old.back - old.front
            || new.front > new.back
            || new.back > haystack.len()
            || new.remaining != new.back - new.front
            || !haystack.is_char_boundary(old.front)
            || !haystack.is_char_boundary(old.back)
        {
            return false;
        }

        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                let Some(&first) = haystack.as_bytes().get(old.front) else {
                    return false;
                };
                let width = kani_utf8_char_len_from_first_byte(first);
                let Some(expected_end) = old.front.checked_add(width) else {
                    return false;
                };

                a == old.front
                    && b == expected_end
                    && new.front == expected_end
                    && new.back == old.back
                    && haystack.is_char_boundary(expected_end)
            }
            SearchStep::Done => {
                old.front == old.back
                    && new.front == old.front
                    && new.back == old.back
                    && new.remaining == old.remaining
            }
        }
    }

    // Reverse counterpart of `valid_multi_char_eq_forward_projection`.
    pub(super) fn valid_multi_char_eq_reverse_projection(
        old: CharIndicesState,
        new: CharIndicesState,
        step: SearchStep,
        haystack: &str,
    ) -> bool {
        if old.front > old.back
            || old.back > haystack.len()
            || old.remaining != old.back - old.front
            || new.front > new.back
            || new.back > haystack.len()
            || new.remaining != new.back - new.front
            || !haystack.is_char_boundary(old.front)
            || !haystack.is_char_boundary(old.back)
        {
            return false;
        }

        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                let Some(expected_start) = kani_utf8_char_start_before(haystack, old.back) else {
                    return false;
                };

                a == expected_start
                    && b == old.back
                    && new.front == old.front
                    && new.back == expected_start
                    && haystack.is_char_boundary(expected_start)
            }
            SearchStep::Done => {
                old.front == old.back
                    && new.front == old.front
                    && new.back == old.back
                    && new.remaining == old.remaining
            }
        }
    }

    pub(super) fn assert_forward_step(
        old: CharIndicesState,
        new: CharIndicesState,
        step: SearchStep,
        haystack: &str,
    ) {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_eq!(a, old.front);
                assert_eq!(b, new.front);
                assert!(old.front < new.front);
                assert!(new.remaining < old.remaining);
                assert_eq!(old.remaining - new.remaining, b - a);
                assert!(b - a <= MAX_LEN_UTF8);
                assert_eq!(new.back, old.back);
                assert!(valid_range_on_haystack(haystack, a, b));
            }
            SearchStep::Done => {
                assert_eq!(old.remaining, 0);
                assert_eq!(new.front, old.front);
                assert_eq!(new.remaining, old.remaining);
                assert_eq!(new.back, old.back);
            }
        }
    }

    pub(super) fn assert_forward_filtered(
        old: CharIndicesState,
        new: CharIndicesState,
        result: Option<(usize, usize)>,
        haystack: &str,
    ) {
        match result {
            Some((a, b)) => {
                assert!(old.front <= a);
                assert!(a < b);
                assert_eq!(b, new.front);
                assert!(b <= old.back);
                assert!(new.remaining < old.remaining);
                assert_eq!(old.remaining - new.remaining, b - old.front);
                assert_eq!(new.back, old.back);
                assert!(b - a <= MAX_LEN_UTF8);
                assert!(b - a <= old.remaining - new.remaining);
                assert!(valid_range_on_haystack(haystack, a, b));
            }
            None => {
                assert_eq!(new.front, old.back);
                assert_eq!(new.remaining, 0);
                assert_eq!(new.back, old.back);
            }
        }
    }

    pub(super) fn assert_reverse_step(
        old: CharIndicesState,
        new: CharIndicesState,
        step: SearchStep,
        haystack: &str,
    ) {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_eq!(new.front, old.front);
                assert_eq!(a, new.back);
                assert_eq!(b, old.back);
                assert!(old.front <= new.back);
                assert!(new.back < old.back);
                assert!(new.remaining < old.remaining);
                assert_eq!(old.remaining - new.remaining, b - a);
                assert!(b - a <= MAX_LEN_UTF8);
                assert!(valid_range_on_haystack(haystack, a, b));
            }
            SearchStep::Done => {
                assert_eq!(old.remaining, 0);
                assert_eq!(new.front, old.front);
                assert_eq!(new.remaining, old.remaining);
                assert_eq!(new.back, old.back);
            }
        }
    }

    pub(super) fn assert_reverse_filtered(
        old: CharIndicesState,
        new: CharIndicesState,
        result: Option<(usize, usize)>,
        haystack: &str,
    ) {
        match result {
            Some((a, b)) => {
                assert_eq!(new.front, old.front);
                assert_eq!(a, new.back);
                assert!(old.front <= a);
                assert!(a < b);
                assert!(b <= old.back);
                assert!(new.back < old.back);
                assert!(new.remaining < old.remaining);
                assert!(b - a <= MAX_LEN_UTF8);
                assert!(b - a <= old.remaining - new.remaining);
                assert!(valid_range_on_haystack(haystack, a, b));
            }
            None => {
                assert_eq!(new.front, old.front);
                assert_eq!(new.remaining, 0);
                assert_eq!(new.back, old.front);
            }
        }
    }

    // Proof cut for one forward UTF-8 decoding step.
    //
    // The challenge allows us to assume the functional correctness of
    // `str::validations`. Starting from a valid UTF-8 active window, every
    // successful `Chars::next` consumes exactly one complete code point.
    // Therefore, after one successful `next` step, an advanced cursor is a
    // UTF-8 character boundary in the original haystack. The ordering checks
    // remain assertions because they follow from the iterator implementation
    // rather than from the UTF-8 assumption.
    pub(super) fn assume_valid_utf8_forward_boundary(
        haystack: &str,
        old_front: usize,
        old_back: usize,
        new_front: usize,
    ) {
        assert!(old_front <= old_back);
        assert!(old_back <= haystack.len());
        assert!(haystack.is_char_boundary(old_front));
        assert!(haystack.is_char_boundary(old_back));
        assert!(old_front <= new_front);
        assert!(new_front <= old_back);

        if old_front < new_front {
            kani::assume(haystack.is_char_boundary(new_front));
        }
    }

    // Proof cut for one reverse UTF-8 decoding step.
    //
    // Starting from a valid UTF-8 active window, a successful `Chars::next_back`
    // consumes exactly one complete code point from the end. Therefore the new
    // back cursor is a character boundary in the original haystack. Ordering
    // remains an assertion because it follows from the iterator implementation
    // rather than from the UTF-8 assumption.
    pub(super) fn assume_valid_utf8_reverse_boundary(
        haystack: &str,
        old_front: usize,
        old_back: usize,
        new_back: usize,
        step: SearchStep,
    ) {
        assert!(old_front <= old_back);
        assert!(old_back <= haystack.len());
        assert!(haystack.is_char_boundary(old_front));
        assert!(haystack.is_char_boundary(old_back));
        assert!(old_front <= new_back);
        assert!(new_back <= old_back);

        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert_eq!(a, new_back);
                assert_eq!(b, old_back);
                assert!(new_back < old_back);

                kani::assume(haystack.is_char_boundary(new_back));
            }
            SearchStep::Done => {
                // Challenge 20 permits assuming functional correctness of slice
                // iterators and `next_code_point_reverse`: Done means that the
                // active byte window was empty before the call.
                kani::assume(old_front == old_back);
            }
        }
    }

    // Minimal UTF-8 proof cut for a successful `CharSearcher::next_match`.
    //
    // The scan may temporarily leave `finger` between UTF-8 boundaries, so that
    // property cannot be a loop invariant. Before importing any UTF-8 fact, this
    // helper proves that the returned range belongs to the searcher's original
    // haystack, ends at the new `finger`, and contains exactly the cached UTF-8
    // encoding of `needle`. These checks also make the cut sound when Kani uses
    // the over-approximating `memchr_like_stub`: an arbitrary occurrence of the last
    // byte is insufficient unless the complete candidate encoding matches.
    //
    // Challenge 20 permits assuming that `str::validations` is functionally
    // correct and that the haystack has valid UTF-8. The only facts assumed
    // below are the resulting UTF-8 theorem: a complete encoded `char` occurring
    // in a valid string starts and ends at character boundaries. All range,
    // state-transition, and encoding-consistency obligations remain assertions.
    pub(super) fn assume_valid_utf8_next_match_boundaries(
        haystack: &str,
        searcher: &CharSearcher<'_>,
        step: Option<(usize, usize)>,
    ) {
        assert!(searcher.haystack.as_ptr() == haystack.as_ptr());
        assert!(searcher.haystack.len() == haystack.len());

        if let Some((a, b)) = step {
            assert!(a < b);
            assert!(b == searcher.finger);
            assert!(b <= searcher.finger_back);
            assert!(searcher.finger_back <= searcher.haystack.len());

            let utf8_size = searcher.utf8_size();
            assert!(1 <= utf8_size);
            assert!(utf8_size <= MAX_LEN_UTF8);
            assert!(b - a == utf8_size);

            let candidate = searcher.haystack.as_bytes().get(a..b).unwrap();
            assert!(searcher.utf8_encoded_matches(candidate));
            assert!(searcher.utf8_encoding_matches_needle());

            kani::assume(searcher.haystack.is_char_boundary(a));
            kani::assume(searcher.haystack.is_char_boundary(b));
        }
    }

    // Minimal UTF-8 proof cut for a successful
    // `CharSearcher::next_match_back`.
    //
    // Reverse scanning may temporarily leave `finger_back` between UTF-8
    // boundaries, so that property cannot be a loop invariant. Before importing
    // any UTF-8 fact, this helper proves that the returned range lies in the old
    // active window, starts at the new `finger_back`, and contains exactly the
    // cached UTF-8 encoding of `needle`. These checks also make the cut sound for
    // the over-approximating `memchr_like_stub`: an arbitrary occurrence of the last
    // byte is insufficient unless the complete candidate encoding matches.
    //
    // Challenge 20 permits assuming that `str::validations` is functionally
    // correct and that the haystack has valid UTF-8. The only facts assumed
    // below are the resulting UTF-8 theorem: a complete encoded `char` occurring
    // in a valid string starts and ends at character boundaries. All range,
    // state-transition, and encoding-consistency obligations remain assertions.
    pub(super) fn assume_valid_utf8_next_match_back_boundaries(
        haystack: &str,
        old_finger: usize,
        old_finger_back: usize,
        searcher: &CharSearcher<'_>,
        step: Option<(usize, usize)>,
    ) {
        assert!(searcher.haystack.as_ptr() == haystack.as_ptr());
        assert!(searcher.haystack.len() == haystack.len());
        assert!(old_finger <= old_finger_back);
        assert!(old_finger_back <= searcher.haystack.len());

        if let Some((a, b)) = step {
            assert!(searcher.finger == old_finger);
            assert!(a == searcher.finger_back);
            assert!(old_finger <= a);
            assert!(a < b);
            assert!(b <= old_finger_back);

            let utf8_size = searcher.utf8_size();
            assert!(1 <= utf8_size);
            assert!(utf8_size <= MAX_LEN_UTF8);
            assert!(b - a == utf8_size);

            let candidate = searcher.haystack.as_bytes().get(a..b).unwrap();
            assert!(searcher.utf8_encoded_matches(candidate));
            assert!(searcher.utf8_encoding_matches_needle());

            kani::assume(searcher.haystack.is_char_boundary(a));
            kani::assume(searcher.haystack.is_char_boundary(b));
        }
    }

    // Safety-relevant state transition for one call to `CharSearcher::next`.
    //
    // `next` searches from the front of the active window
    // `old_finger..old_finger_back`. For `Match` and `Reject`, the
    // predicate checks that the implementation returns
    // `(old_finger, self.finger)`, advances to a later UTF-8 boundary, and does
    // not change `finger_back`. It deliberately does not encode the full
    // functional semantics of UTF-8 decoding. For `Done`, the active window is
    // empty and both fingers stay unchanged.
    pub(super) fn valid_char_next_step(
        haystack: &str,
        old_finger: usize,
        old_finger_back: usize,
        new_finger: usize,
        new_finger_back: usize,
        step: SearchStep,
    ) -> bool {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                a == old_finger
                    && b == new_finger
                    && new_finger_back == old_finger_back
                    && old_finger < b
                    && b <= old_finger_back
                    && valid_range_on_haystack(haystack, a, b)
            }
            SearchStep::Done => {
                new_finger == old_finger
                    && new_finger_back == old_finger_back
                    && old_finger == old_finger_back
            }
        }
    }

    // Safety-relevant state transition for one call to
    // `CharSearcher::next_back`.
    //
    // `next_back` is the reverse-direction counterpart of `next`: it searches
    // from the back of the active window `old_finger..old_finger_back`. For
    // `Match` and `Reject`, the predicate checks that it returns
    // `(self.finger_back, old_finger_back)`, moves to an earlier UTF-8 boundary,
    // and does not change `finger`. It deliberately does not encode the full
    // functional semantics of reverse UTF-8 decoding. For `Done`, the active
    // window is empty and both fingers stay unchanged.
    pub(super) fn valid_char_next_back_step(
        haystack: &str,
        old_finger: usize,
        old_finger_back: usize,
        new_finger: usize,
        new_finger_back: usize,
        step: SearchStep,
    ) -> bool {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                a == new_finger_back
                    && b == old_finger_back
                    && new_finger == old_finger
                    && old_finger <= a
                    && a < old_finger_back
                    && valid_range_on_haystack(haystack, a, b)
            }
            SearchStep::Done => {
                new_finger == old_finger
                    && new_finger_back == old_finger_back
                    && old_finger == old_finger_back
            }
        }
    }

    // Shared postcondition for `CharSearcher::next_match` and `next_reject`.
    //
    // Both methods scan from the front until they find the requested kind of
    // step. Whether that step is Match or Reject does not affect the safety
    // obligations: a successful range lies inside the old active window, ends
    // at the new forward finger, and leaves the reverse finger unchanged.
    // `None` means the active window was consumed, so both fingers meet at the
    // old back finger.
    pub(super) fn valid_char_next_filtered_result(
        haystack: &str,
        old_finger: usize,
        old_finger_back: usize,
        new_finger: usize,
        new_finger_back: usize,
        step: Option<(usize, usize)>,
    ) -> bool {
        match step {
            Some((a, b)) => {
                old_finger <= a
                    && a < b
                    && b == new_finger
                    && b <= old_finger_back
                    && new_finger_back == old_finger_back
                    && valid_range_on_haystack(haystack, a, b)
            }
            None => new_finger == old_finger_back && new_finger_back == old_finger_back,
        }
    }

    // Shared postcondition for `CharSearcher::next_match_back` and
    // `next_reject_back`.
    //
    // Both methods scan from the back until they find the requested kind of
    // step. Whether that step is Match or Reject does not affect the safety
    // obligations: a successful range starts at the new reverse finger, lies
    // inside the old active window, and leaves the forward finger unchanged.
    // `None` means the active window was consumed, so the reverse finger meets
    // the old forward finger.
    pub(super) fn valid_char_next_filtered_back_result(
        haystack: &str,
        old_finger: usize,
        old_finger_back: usize,
        new_finger: usize,
        new_finger_back: usize,
        step: Option<(usize, usize)>,
    ) -> bool {
        match step {
            Some((a, b)) => {
                a < b
                    && a == new_finger_back
                    && new_finger == old_finger
                    && old_finger <= a
                    && b <= old_finger_back
                    && valid_range_on_haystack(haystack, a, b)
            }
            None => new_finger == old_finger && new_finger_back == old_finger,
        }
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

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify_char_searcher {
    use super::kani_pattern_harness_helpers::*;
    use super::*;

    //==========================================================================
    // Challenge 20: Verify the safety of char-related functions in str::pattern
    //==========================================================================

    // Construct every `CharSearcher` state admitted by C. Constructor harnesses
    // separately prove that production initialization establishes C; method
    // harnesses use this helper to prove preservation from an arbitrary C state.
    fn any_char_searcher_state(haystack: &str) -> CharSearcher<'_> {
        let searcher = CharSearcher {
            haystack,
            finger: kani::any(),
            finger_back: kani::any(),
            needle: kani::any(),
            utf8_size: kani::any(),
            utf8_encoded: kani::any(),
        };
        kani::assume(type_invariant_char_searcher(&searcher));

        // Challenge 20 permits importing valid-UTF-8 properties. Since C says
        // both fingers are boundaries in a valid haystack, their intervening
        // byte range is itself valid UTF-8. Kani does not derive this theorem
        // automatically through `Chars`.
        let active =
            searcher.haystack.as_bytes().get(searcher.finger..searcher.finger_back).unwrap();
        kani::assume(crate::str::from_utf8(active).is_ok());
        searcher
    }

    // Choose an arbitrary representative of every safety-relevant state allowed
    // by `type_invariant_multi_char_eq_searcher`. For a fixed haystack window,
    // the `CharIndices` fields in C are uniquely reconstructed from the safe
    // substring. `char_eq` is intentionally left untouched because the
    // abstraction relation forgets predicate-internal state.
    fn set_any_multi_char_eq_active_window<C: MultiCharEq>(
        searcher: &mut MultiCharEqSearcher<'_, C>,
    ) {
        let front: usize = kani::any();
        let back: usize = kani::any();
        kani::assume(front <= back);
        kani::assume(back <= searcher.haystack.len());
        kani::assume(searcher.haystack.is_char_boundary(front));
        kani::assume(searcher.haystack.is_char_boundary(back));
        kani::assume(
            crate::str::from_utf8(searcher.haystack.as_bytes().get(front..back).unwrap()).is_ok(),
        );

        searcher.kani_rebuild_char_indices_window(front, back);
        assert!(type_invariant_multi_char_eq_searcher(searcher));
    }

    // Kani stub shared by `crate::slice::memchr::{memchr, memrchr}`.
    //
    // The forward and reverse CharSearcher safety proofs need the same facts: a
    // successful result is an index inside `text`, and the indexed byte equals
    // the searched byte. Whether the real implementation returns the first or
    // last matching byte is irrelevant to range safety and invariant
    // preservation.
    //
    // This stub is therefore a conservative over-approximation for safety: it
    // may return `None`, or it may return any in-bounds matching index. Every
    // real `memchr` and `memrchr` result is included in that set. Do not use
    // this stub for exact functional-correctness proofs: it intentionally omits
    // directional ordering and the guarantee that `None` means no match exists.
    fn memchr_like_stub(x: u8, text: &[u8]) -> Option<usize> {
        if kani::any::<bool>() {
            let index: usize = kani::any();
            kani::assume(index < text.len());
            kani::assume(text[index] == x);
            Some(index)
        } else {
            None
        }
    }

    // CharSearcher Harnesses

    // Harness for `CharSearcher::into_searcher`
    #[kani::proof]
    fn harness_char_searcher_into_searcher() {
        let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
        let haystack = any_valid_utf8_str(&bytes);
        let pattern: char = kani::any();
        let searcher = pattern.into_searcher(haystack);

        assert!(type_invariant_char_searcher(&searcher));
    }

    // Harness for `CharSearcher::next`
    #[kani::proof_for_contract(CharSearcher::next)]
    fn harness_char_searcher_next() {
        let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
        let haystack = any_valid_utf8_str(&bytes);
        let mut searcher = any_char_searcher_state(haystack);

        assert!(type_invariant_char_searcher(&searcher));

        let old_finger = searcher.finger;
        let old_finger_back = searcher.finger_back;

        let step = searcher.next();

        assume_valid_utf8_forward_boundary(haystack, old_finger, old_finger_back, searcher.finger);

        assert!(type_invariant_char_searcher(&searcher));
        assert!(valid_char_next_step(
            haystack,
            old_finger,
            old_finger_back,
            searcher.finger,
            searcher.finger_back,
            step,
        ));
    }

    // Harness for `CharSearcher::next_match`
    #[kani::proof]
    #[kani::stub(crate::slice::memchr::memchr, memchr_like_stub)]
    fn harness_char_searcher_next_match() {
        let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
        let haystack = any_valid_utf8_str(&bytes);
        let mut searcher = any_char_searcher_state(haystack);

        assert!(type_invariant_char_searcher(&searcher));

        let old_finger = searcher.finger;
        let old_finger_back = searcher.finger_back;

        let step = searcher.next_match();

        // The helper proves the returned range and cached-encoding relations,
        // then imports only the character-boundary consequence permitted by
        // Challenge 20's valid-UTF-8 and `str::validations` assumptions.
        assume_valid_utf8_next_match_boundaries(haystack, &searcher, step);

        assert!(type_invariant_char_searcher(&searcher));
        assert!(valid_char_next_filtered_result(
            haystack,
            old_finger,
            old_finger_back,
            searcher.finger,
            searcher.finger_back,
            step,
        ));
    }

    // Harness for `CharSearcher::next_reject`
    #[kani::proof]
    #[kani::stub_verified(CharSearcher::next)]
    fn harness_char_searcher_next_reject() {
        let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
        let haystack = any_valid_utf8_str(&bytes);
        let mut searcher = any_char_searcher_state(haystack);

        assert!(type_invariant_char_searcher(&searcher));

        let old_finger = searcher.finger;
        let old_finger_back = searcher.finger_back;

        let step = searcher.next_reject();

        assert!(type_invariant_char_searcher(&searcher));
        assert!(valid_char_next_filtered_result(
            haystack,
            old_finger,
            old_finger_back,
            searcher.finger,
            searcher.finger_back,
            step,
        ));
    }

    // Harness for `CharSearcher::next_back`
    #[kani::proof_for_contract(CharSearcher::next_back)]
    fn harness_char_searcher_next_back() {
        let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
        let haystack = any_valid_utf8_str(&bytes);
        let mut searcher = any_char_searcher_state(haystack);

        assert!(type_invariant_char_searcher(&searcher));

        let old_finger = searcher.finger;
        let old_finger_back = searcher.finger_back;

        let step = searcher.next_back();

        assume_valid_utf8_reverse_boundary(
            haystack,
            old_finger,
            old_finger_back,
            searcher.finger_back,
            step,
        );

        assert!(type_invariant_char_searcher(&searcher));
        assert!(valid_char_next_back_step(
            haystack,
            old_finger,
            old_finger_back,
            searcher.finger,
            searcher.finger_back,
            step,
        ));
    }

    // Harness for `CharSearcher::next_match_back`
    #[kani::proof]
    #[kani::stub(crate::slice::memchr::memrchr, memchr_like_stub)]
    fn harness_char_searcher_next_match_back() {
        let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
        let haystack = any_valid_utf8_str(&bytes);
        let mut searcher = any_char_searcher_state(haystack);

        assert!(type_invariant_char_searcher(&searcher));

        let old_finger = searcher.finger;
        let old_finger_back = searcher.finger_back;

        let step = searcher.next_match_back();

        // The helper proves the reverse result's state, range, and complete
        // cached-encoding relations, then imports only the character-boundary
        // consequence allowed by Challenge 20's valid-UTF-8 assumptions.
        assume_valid_utf8_next_match_back_boundaries(
            haystack,
            old_finger,
            old_finger_back,
            &searcher,
            step,
        );

        assert!(type_invariant_char_searcher(&searcher));
        assert!(valid_char_next_filtered_back_result(
            haystack,
            old_finger,
            old_finger_back,
            searcher.finger,
            searcher.finger_back,
            step,
        ));
    }

    // Harness for `CharSearcher::next_reject_back`
    #[kani::proof]
    #[kani::stub_verified(CharSearcher::next_back)]
    fn harness_char_searcher_next_reject_back() {
        let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
        let haystack = any_valid_utf8_str(&bytes);
        let mut searcher = any_char_searcher_state(haystack);

        assert!(type_invariant_char_searcher(&searcher));

        let old_finger = searcher.finger;
        let old_finger_back = searcher.finger_back;

        let step = searcher.next_reject_back();

        assert!(type_invariant_char_searcher(&searcher));
        assert!(valid_char_next_filtered_back_result(
            haystack,
            old_finger,
            old_finger_back,
            searcher.finger,
            searcher.finger_back,
            step,
        ));
    }

    // Generate the same seven harnesses for `MultiCharEqSearcher` and each
    // public wrapper around it.
    //
    // Each invocation provides:
    // - `flavor`: `direct` for `MultiCharEqSearcher`, `wrapper` for tuple wrappers.
    // - `names`: the concrete harness names exposed to Kani.
    // - `setup`: construction code for one searcher type.
    // - `invariant`: the type-specific view of invariant C.
    //
    // `setup` is expanded inside every harness. This keeps borrowed arrays and
    // slices alive for the full harness instead of returning them from a helper.
    // The constructor harness checks initialization. Each method harness then
    // selects an arbitrary valid window, snapshots it, calls one method, and
    // checks invariant preservation plus the direction-specific postcondition.
    macro_rules! generate_multi_char_eq_harnesses {
        (
            flavor: $flavor:ident,
            names {
                into_searcher: $into_searcher:ident,
                next: $next:ident,
                next_match: $next_match:ident,
                next_reject: $next_reject:ident,
                next_back: $next_back:ident,
                next_match_back: $next_match_back:ident,
                next_reject_back: $next_reject_back:ident,
            },
            setup |$haystack:ident, $searcher:ident| {
                $($setup:tt)*
            },
            invariant: $invariant:path $(,)?
        ) => {
            #[kani::proof]
            fn $into_searcher() {
                let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
                let $haystack = any_valid_utf8_str(&bytes);
                $($setup)*

                assert!($invariant(&$searcher));
            }

            #[kani::proof]
            fn $next() {
                let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
                let $haystack = any_valid_utf8_str(&bytes);
                $($setup)*
                let mut $searcher = $searcher;

                generate_multi_char_eq_harnesses!(
                    @set_active_window $flavor,
                    $searcher
                );
                assert!($invariant(&$searcher));

                let old_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);
                let step = $searcher.next();
                let new_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);

                assume_valid_utf8_forward_boundary(
                    $haystack,
                    old_state.front,
                    old_state.back,
                    new_state.front,
                );

                assert!($invariant(&$searcher));
                generate_multi_char_eq_harnesses!(
                    @assert_forward_projection $flavor,
                    old_state,
                    new_state,
                    step,
                    $haystack
                );
                assert_forward_step(old_state, new_state, step, $haystack);
            }

            #[kani::proof]
            fn $next_match() {
                let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
                let $haystack = any_valid_utf8_str(&bytes);
                $($setup)*
                let mut $searcher = $searcher;

                generate_multi_char_eq_harnesses!(
                    @set_active_window $flavor,
                    $searcher
                );
                assert!($invariant(&$searcher));

                let old_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);
                let result = $searcher.next_match();
                let new_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);

                assert!($invariant(&$searcher));
                assert_forward_filtered(old_state, new_state, result, $haystack);
            }

            #[kani::proof]
            fn $next_reject() {
                let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
                let $haystack = any_valid_utf8_str(&bytes);
                $($setup)*
                let mut $searcher = $searcher;

                generate_multi_char_eq_harnesses!(
                    @set_active_window $flavor,
                    $searcher
                );
                assert!($invariant(&$searcher));

                let old_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);
                let result = $searcher.next_reject();
                let new_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);

                assert!($invariant(&$searcher));
                // The Kani path rebuilds the concrete CharIndices state after
                // every modeled step, so this checks state preservation as well
                // as the returned-range safety obligation.
                assert_forward_filtered(old_state, new_state, result, $haystack);
            }

            #[kani::proof]
            fn $next_back() {
                let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
                let $haystack = any_valid_utf8_str(&bytes);
                $($setup)*
                let mut $searcher = $searcher;

                generate_multi_char_eq_harnesses!(
                    @set_active_window $flavor,
                    $searcher
                );
                assert!($invariant(&$searcher));

                let old_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);
                let step = $searcher.next_back();
                let new_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);

                assume_valid_utf8_reverse_boundary(
                    $haystack,
                    old_state.front,
                    old_state.back,
                    new_state.back,
                    step,
                );

                assert!($invariant(&$searcher));
                generate_multi_char_eq_harnesses!(
                    @assert_reverse_projection $flavor,
                    old_state,
                    new_state,
                    step,
                    $haystack
                );
                assert_reverse_step(old_state, new_state, step, $haystack);
            }

            #[kani::proof]
            fn $next_match_back() {
                let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
                let $haystack = any_valid_utf8_str(&bytes);
                $($setup)*
                let mut $searcher = $searcher;

                generate_multi_char_eq_harnesses!(
                    @set_active_window $flavor,
                    $searcher
                );
                assert!($invariant(&$searcher));

                let old_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);
                let result = $searcher.next_match_back();
                let new_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);

                assert!($invariant(&$searcher));
                assert_reverse_filtered(old_state, new_state, result, $haystack);
            }

            #[kani::proof]
            fn $next_reject_back() {
                let bytes: [u8; MAX_UTF8_BYTES] = kani::any();
                let $haystack = any_valid_utf8_str(&bytes);
                $($setup)*
                let mut $searcher = $searcher;

                generate_multi_char_eq_harnesses!(
                    @set_active_window $flavor,
                    $searcher
                );
                assert!($invariant(&$searcher));

                let old_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);
                let result = $searcher.next_reject_back();
                let new_state =
                    generate_multi_char_eq_harnesses!(@state $flavor, $searcher);

                assert!($invariant(&$searcher));
                assert_reverse_filtered(old_state, new_state, result, $haystack);
            }
        };

        // Normalize the different layouts used by the shared harness body.
        // The direct searcher owns `char_indices`; wrappers store it in field 0.
        (@set_active_window direct, $searcher:ident) => {
            set_any_multi_char_eq_active_window(&mut $searcher)
        };
        (@set_active_window wrapper, $searcher:ident) => {
            set_any_multi_char_eq_active_window(&mut $searcher.0)
        };

        (@state direct, $searcher:ident) => {
            char_indices_state(&$searcher.char_indices)
        };
        (@state wrapper, $searcher:ident) => {
            char_indices_state(&$searcher.0.char_indices)
        };

        // These stronger projection checks describe the direct implementation.
        // Wrapper harnesses use the shared public range checks instead.
        (
            @assert_forward_projection direct,
            $old_state:ident,
            $new_state:ident,
            $step:ident,
            $haystack:ident
        ) => {
            assert!(valid_multi_char_eq_forward_projection(
                $old_state,
                $new_state,
                $step,
                $haystack,
            ))
        };
        (
            @assert_forward_projection wrapper,
            $old_state:ident,
            $new_state:ident,
            $step:ident,
            $haystack:ident
        ) => {};

        (
            @assert_reverse_projection direct,
            $old_state:ident,
            $new_state:ident,
            $step:ident,
            $haystack:ident
        ) => {
            assert!(valid_multi_char_eq_reverse_projection(
                $old_state,
                $new_state,
                $step,
                $haystack,
            ))
        };
        (
            @assert_reverse_projection wrapper,
            $old_state:ident,
            $new_state:ident,
            $step:ident,
            $haystack:ident
        ) => {};
    }

    // Internal generic searcher used by all char-set patterns.
    generate_multi_char_eq_harnesses! {
        flavor: direct,
        names {
            into_searcher: harness_multi_char_eq_into_searcher,
            next: harness_multi_char_eq_next,
            next_match: harness_multi_char_eq_next_match,
            next_reject: harness_multi_char_eq_next_reject,
            next_back: harness_multi_char_eq_next_back,
            next_match_back: harness_multi_char_eq_next_match_back,
            next_reject_back: harness_multi_char_eq_next_reject_back,
        },
        setup |haystack, searcher| {
            let pattern: [char; 4] = kani::any();
            let searcher = MultiCharEqPattern(pattern).into_searcher(haystack);
        },
        invariant: type_invariant_multi_char_eq_searcher,
    }

    // Owned `[char; N]` pattern.
    generate_multi_char_eq_harnesses! {
        flavor: wrapper,
        names {
            into_searcher: harness_char_array_into_searcher,
            next: harness_char_array_next,
            next_match: harness_char_array_next_match,
            next_reject: harness_char_array_next_reject,
            next_back: harness_char_array_next_back,
            next_match_back: harness_char_array_next_match_back,
            next_reject_back: harness_char_array_next_reject_back,
        },
        setup |haystack, searcher| {
            let pattern: [char; 4] = kani::any();
            let searcher: CharArraySearcher<'_, 4> = pattern.into_searcher(haystack);
        },
        invariant: type_invariant_char_array,
    }

    // Borrowed `&[char; N]` pattern.
    generate_multi_char_eq_harnesses! {
        flavor: wrapper,
        names {
            into_searcher: harness_char_array_ref_into_searcher,
            next: harness_char_array_ref_next,
            next_match: harness_char_array_ref_next_match,
            next_reject: harness_char_array_ref_next_reject,
            next_back: harness_char_array_ref_next_back,
            next_match_back: harness_char_array_ref_next_match_back,
            next_reject_back: harness_char_array_ref_next_reject_back,
        },
        setup |haystack, searcher| {
            let pattern: [char; 4] = kani::any();
            let searcher: CharArrayRefSearcher<'_, '_, 4> =
                (&pattern).into_searcher(haystack);
        },
        invariant: type_invariant_char_array_ref,
    }

    // Borrowed `&[char]` pattern with symbolic length.
    generate_multi_char_eq_harnesses! {
        flavor: wrapper,
        names {
            into_searcher: harness_char_slice_into_searcher,
            next: harness_char_slice_next,
            next_match: harness_char_slice_next_match,
            next_reject: harness_char_slice_next_reject,
            next_back: harness_char_slice_next_back,
            next_match_back: harness_char_slice_next_match_back,
            next_reject_back: harness_char_slice_next_reject_back,
        },
        setup |haystack, searcher| {
            let chars: [char; 4] = kani::any();
            let pattern: &[char] = kani::slice::any_slice_of_array(&chars);
            let searcher: CharSliceSearcher<'_, '_> = pattern.into_searcher(haystack);
        },
        invariant: type_invariant_char_slice,
    }

    // Construct one concrete stateful `FnMut` whose return value is
    // unconstrained on every call. For normally returning predicates and
    // range-safety purposes, this over-approximates every Match/Reject output
    // sequence while exercising a mutable captured-state update. It does not
    // model arbitrary predicate side effects, panics, or state transitions.
    fn any_stateful_char_predicate() -> impl FnMut(char) -> bool {
        let mut calls: u8 = kani::any();
        move |_c: char| {
            calls = calls.wrapping_add(1);
            kani::any()
        }
    }

    // Stateful `FnMut(char) -> bool` pattern.
    generate_multi_char_eq_harnesses! {
        flavor: wrapper,
        names {
            into_searcher: harness_char_predicate_into_searcher,
            next: harness_char_predicate_next,
            next_match: harness_char_predicate_next_match,
            next_reject: harness_char_predicate_next_reject,
            next_back: harness_char_predicate_next_back,
            next_match_back: harness_char_predicate_next_match_back,
            next_reject_back: harness_char_predicate_next_reject_back,
        },
        setup |haystack, searcher| {
            let predicate = any_stateful_char_predicate();
            let searcher: CharPredicateSearcher<'_, _> = predicate.into_searcher(haystack);
        },
        invariant: type_invariant_char_predicate,
    }
}
