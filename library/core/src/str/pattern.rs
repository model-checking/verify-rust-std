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

/// Loop contracts of the provided `Searcher` and `ReverseSearcher` methods,
/// which loop over `next` / `next_back` of an arbitrary searcher. A searcher
/// states its type invariant and the cursor each direction moves by
/// specializing this; the default keeps the whole searcher assignable.
#[cfg(kani)]
pub(crate) trait SearcherLoopContract {
    /// The type invariant. Called from loop invariants only, so it uses casts
    /// and intrinsics only: Kani gives a function that is also called from
    /// ordinary code no write-set argument when an invariant calls it.
    fn kani_inv(&self) -> bool;
    /// The bytes a forward step (`next`) writes.
    fn kani_fwd_cursor(&self) -> *const [u8];
    /// The bytes a backward step (`next_back`) writes.
    fn kani_back_cursor(&self) -> *const [u8];
    /// The bytes of the pattern's own state that a step may write (a stateful
    /// predicate).
    fn kani_pred_state(&self) -> *const [u8];
}

#[cfg(kani)]
impl<T: ?Sized> SearcherLoopContract for T {
    default fn kani_inv(&self) -> bool {
        true
    }
    default fn kani_fwd_cursor(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(self as *const T as *const u8, size_of_val(self))
    }
    default fn kani_back_cursor(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(self as *const T as *const u8, size_of_val(self))
    }
    default fn kani_pred_state(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(self as *const T as *const u8, 0)
    }
}

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

/// For the step contracts of `MultiCharEqSearcher` (a replaced call returns
/// any value that the contract allows).
#[cfg(kani)]
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
        #[cfg_attr(
            kani,
            kani::loop_modifies(
                SearcherLoopContract::kani_fwd_cursor(&*self),
                SearcherLoopContract::kani_pred_state(&*self)
            )
        )]
        #[safety::loop_invariant(SearcherLoopContract::kani_inv(&*self))]
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
        #[cfg_attr(
            kani,
            kani::loop_modifies(
                SearcherLoopContract::kani_fwd_cursor(&*self),
                SearcherLoopContract::kani_pred_state(&*self)
            )
        )]
        #[safety::loop_invariant(SearcherLoopContract::kani_inv(&*self))]
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
        #[cfg_attr(
            kani,
            kani::loop_modifies(
                SearcherLoopContract::kani_back_cursor(&*self),
                SearcherLoopContract::kani_pred_state(&*self)
            )
        )]
        #[safety::loop_invariant(SearcherLoopContract::kani_inv(&*self))]
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
        #[cfg_attr(
            kani,
            kani::loop_modifies(
                SearcherLoopContract::kani_back_cursor(&*self),
                SearcherLoopContract::kani_pred_state(&*self)
            )
        )]
        #[safety::loop_invariant(SearcherLoopContract::kani_inv(&*self))]
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

#[cfg(kani)]
impl SearcherLoopContract for CharSearcher<'_> {
    /// `finger <= finger_back <= haystack.len()`, both on char boundaries
    /// (`str::len` and `str::is_char_boundary` spelled out).
    fn kani_inv(&self) -> bool {
        let p = self.haystack as *const str as *const u8;
        let len: usize = crate::intrinsics::ptr_metadata(self.haystack as *const str);
        let (f, fb) = (self.finger, self.finger_back);
        // SAFETY: both reads are guarded by `< len`.
        let f_ok = f == 0
            || f == len
            || (f < len
                && unsafe { *crate::intrinsics::arith_offset(p, f as isize) } as i8 >= -0x40);
        let fb_ok = fb == 0
            || fb == len
            || (fb < len
                && unsafe { *crate::intrinsics::arith_offset(p, fb as isize) } as i8 >= -0x40);
        f <= fb && fb <= len && f_ok && fb_ok
    }
    fn kani_fwd_cursor(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(&raw const self.finger as *const u8, size_of::<usize>())
    }
    fn kani_back_cursor(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(
            &raw const self.finger_back as *const u8,
            size_of::<usize>(),
        )
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
        // Within the loop `finger` may sit inside a character (see below).
        #[cfg_attr(kani, kani::loop_modifies(&self.finger))]
        #[safety::loop_invariant(self.finger <= self.finger_back)]
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
        // Within the loop `finger_back` may sit inside a character (see below).
        #[cfg_attr(kani, kani::loop_modifies(&self.finger_back))]
        #[safety::loop_invariant(self.finger <= self.finger_back
            && self.finger_back <= crate::intrinsics::ptr_metadata(self.haystack as *const str))]
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

/// The type invariant `C` of `MultiCharEqSearcher` (and so of the four
/// searchers that wrap it): `char_indices` has exactly `haystack[front..back]`
/// left, with `front <= back <= haystack.len()` both on char boundaries. Casts
/// and intrinsics only, guarded so that it can be evaluated on any state;
/// `$parts` reads the fields of the byte iterator.
#[cfg(kani)]
macro_rules! multi_char_eq_inv {
    ($s:expr, $parts:ident) => {{
        let s = $s;
        let p = s.haystack as *const str as *const u8;
        let len: usize = crate::intrinsics::ptr_metadata(s.haystack as *const str);
        let f = s.char_indices.front_offset;
        let (start, end) = s.char_indices.iter.iter.$parts();
        let b = (end as usize).wrapping_sub(p as usize);
        // SAFETY: both reads are guarded by `< len`.
        let f_ok = f == 0
            || f == len
            || (f < len
                && unsafe { *crate::intrinsics::arith_offset(p, f as isize) } as i8 >= -0x40);
        let b_ok = b == 0
            || b == len
            || (b < len
                && unsafe { *crate::intrinsics::arith_offset(p, b as isize) } as i8 >= -0x40);
        // SAFETY: `arith_offset` is a wrapping offset, never UB.
        f <= b
            && b <= len
            && start == unsafe { crate::intrinsics::arith_offset(p, f as isize) }
            && end == unsafe { crate::intrinsics::arith_offset(p, b as isize) }
            && f_ok
            && b_ok
    }};
}

#[cfg(kani)]
impl<C: MultiCharEq> MultiCharEqSearcher<'_, C> {
    /// `C`, for the contracts of `next` / `next_back`.
    fn kani_ok(&self) -> bool {
        multi_char_eq_inv!(self, kani_raw_parts)
    }

    /// A step returns a range in bounds and on char boundaries.
    fn kani_step_ok(&self, step: SearchStep) -> bool {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                a <= b
                    && b <= self.haystack.len()
                    && self.haystack.is_char_boundary(a)
                    && self.haystack.is_char_boundary(b)
            }
            SearchStep::Done => true,
        }
    }
}

#[cfg(kani)]
impl<C: MultiCharEq> SearcherLoopContract for MultiCharEqSearcher<'_, C> {
    fn kani_inv(&self) -> bool {
        multi_char_eq_inv!(self, kani_loop_raw_parts)
    }
    fn kani_fwd_cursor(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(
            &raw const self.char_indices as *const u8,
            size_of_val(&self.char_indices),
        )
    }
    fn kani_back_cursor(&self) -> *const [u8] {
        self.kani_fwd_cursor()
    }
    default fn kani_pred_state(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(&raw const self.char_eq as *const u8, size_of::<C>())
    }
}

// A set of characters has no state of its own: `matches` only reads it.
#[cfg(kani)]
impl<const N: usize> SearcherLoopContract for MultiCharEqSearcher<'_, [char; N]> {
    fn kani_pred_state(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(&raw const self.char_eq as *const u8, 0)
    }
}

#[cfg(kani)]
impl<const N: usize> SearcherLoopContract for MultiCharEqSearcher<'_, &[char; N]> {
    fn kani_pred_state(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(&raw const self.char_eq as *const u8, 0)
    }
}

#[cfg(kani)]
impl SearcherLoopContract for MultiCharEqSearcher<'_, &[char]> {
    fn kani_pred_state(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(&raw const self.char_eq as *const u8, 0)
    }
}

// Nor does a function pointer: a call through it does not write it.
#[cfg(kani)]
impl SearcherLoopContract for MultiCharEqSearcher<'_, fn(char) -> bool> {
    fn kani_pred_state(&self) -> *const [u8] {
        crate::ptr::slice_from_raw_parts(&raw const self.char_eq as *const u8, 0)
    }
}

unsafe impl<'a, C: MultiCharEq> Searcher<'a> for MultiCharEqSearcher<'a, C> {
    #[inline]
    fn haystack(&self) -> &'a str {
        self.haystack
    }

    #[inline]
    #[cfg_attr(
        kani,
        kani::modifies(
            SearcherLoopContract::kani_fwd_cursor(self),
            SearcherLoopContract::kani_pred_state(self)
        )
    )]
    #[safety::requires(self.kani_ok())]
    #[safety::ensures(|step| self.kani_ok() && self.kani_step_ok(*step))]
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
    #[cfg_attr(
        kani,
        kani::modifies(
            SearcherLoopContract::kani_fwd_cursor(self),
            SearcherLoopContract::kani_pred_state(self)
        )
    )]
    #[safety::requires(self.kani_ok())]
    #[safety::ensures(|step| self.kani_ok() && self.kani_step_ok(*step))]
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
            StrSearcherImpl::Empty(..) => loop {
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
            StrSearcherImpl::Empty(..) => loop {
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

/// Challenge 20: unbounded proofs for `CharSearcher`, and for
/// `MultiCharEqSearcher` through its four wrappers.
///
/// # Haystack
///
/// Every harness runs on a haystack of symbolic length (up to the CBMC object
/// model, as in the accepted VecDeque solution) and arbitrary contents, with no
/// unwind bound: the loops are discharged by their loop contracts. UTF-8
/// validity is never stated as a quantified property. `utf8_ok_at(i)` is the
/// local rule that every valid UTF-8 string satisfies at every position `i`,
/// and the harnesses assume it only where a position is consumed: where the
/// decoder starts (the decoder models below), and at the start of a match
/// that `next_match{,_back}` returns. Each assumption holds for every valid
/// haystack (assumption 3), so no execution on a valid haystack is lost.
///
/// # Models
///
/// * `next_code_point{,_reverse}` (assumption 2): assume the local rule where
///   the decode starts, then the upstream body with its helpers inlined. The
///   `unwrap_unchecked`s stay checked, so a decode that does not start on a
///   char boundary is still caught. `check_*_model_matches_upstream` shows the
///   models only add assumptions.
/// * `memchr` / `memrchr` (assumption 1): return a matching index, or `None`.
///   This allows more behaviors than the real functions (`None` while a match
///   exists, a match that is not the first/last), which is sound for safety.
/// * slice equality of bytes (assumption 1): a recursive byte comparison in
///   place of `compare_bytes`. `check_slice_eq_model_matches_upstream` shows it
///   returns what upstream returns.
/// * `<[char]>::contains` (assumption 1): any result. The searchers use only
///   this result, so a character set is never read and may have any size.
///
/// # Predicates
///
/// A predicate returns any result on every call, with no state of its own
/// (`fn(char) -> bool`) or with state that it writes on every call (`Toggle`).
#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub mod verify_char_searcher {
    use super::*;
    use crate::slice::Iter;
    use crate::str::validations::utf8_is_cont_byte;

    /// CBMC's object model: with `--object-bits 12` an object has 52 offset
    /// bits. Same bound as the accepted VecDeque solution. It only excludes
    /// allocations no real machine could back either.
    const MAX_ALLOCATION_BYTES: usize = 1 << 48;

    unsafe extern "C" {
        /// CBMC's `malloc` model (`-Z c-ffi`): `core` has no allocator, and a
        /// fixed-size array this large cannot be flattened.
        fn malloc(size: usize) -> *mut u8;
    }

    /// The haystack the decoder models read. Set by `any_haystack`.
    static mut GHOST: (*const u8, usize) = (crate::ptr::null(), 0);

    unsafe fn byte(i: usize) -> u8 {
        // SAFETY: callers keep `i < GHOST.1`.
        unsafe { *GHOST.0.wrapping_add(i) }
    }

    /// Width of the sequence a lead byte starts; 0 for any other byte.
    fn lead_width(b: u8) -> usize {
        match b {
            0x00..=0x7F => 1,
            0xC2..=0xDF => 2,
            0xE0..=0xEF => 3,
            0xF0..=0xF4 => 4,
            _ => 0,
        }
    }

    /// The second byte of a sequence (Unicode Table 3-7).
    fn second_ok(lead: u8, b: u8) -> bool {
        match lead {
            0xE0 => (0xA0..=0xBF).contains(&b),
            0xED => (0x80..=0x9F).contains(&b),
            0xF0 => (0x90..=0xBF).contains(&b),
            0xF4 => (0x80..=0x8F).contains(&b),
            _ => utf8_is_cont_byte(b),
        }
    }

    /// Local UTF-8 well-formedness at byte `i` of the ghost haystack. It holds
    /// at every position of a valid UTF-8 string, and holding at every
    /// position is equivalent to validity.
    fn utf8_ok_at(i: usize) -> bool {
        let len = unsafe { GHOST.1 };
        if i >= len {
            return true;
        }
        // SAFETY: every read below is at an index `< len`.
        unsafe {
            let b = byte(i);
            let w = lead_width(b);
            if w >= 1 {
                // a lead byte: its sequence is in bounds and well formed, and
                // the next byte starts a new character
                i + w <= len
                    && (w < 2 || second_ok(b, byte(i + 1)))
                    && (w < 3 || utf8_is_cont_byte(byte(i + 2)))
                    && (w < 4 || utf8_is_cont_byte(byte(i + 3)))
                    && (i + w == len || !utf8_is_cont_byte(byte(i + w)))
            } else if utf8_is_cont_byte(b) {
                // a continuation byte: its lead is at most 3 bytes back
                (i >= 1 && lead_width(byte(i - 1)) >= 2)
                    || (i >= 2 && utf8_is_cont_byte(byte(i - 1)) && lead_width(byte(i - 2)) >= 3)
                    || (i >= 3
                        && utf8_is_cont_byte(byte(i - 1))
                        && utf8_is_cont_byte(byte(i - 2))
                        && lead_width(byte(i - 3)) == 4)
            } else {
                false // C0, C1, F5..FF never occur
            }
        }
    }

    /// The range of the ghost haystack a byte iterator still covers.
    trait GhostRange {
        fn ghost_range(&self) -> Option<(usize, usize)>;
    }
    impl<I: ?Sized> GhostRange for I {
        default fn ghost_range(&self) -> Option<(usize, usize)> {
            None
        }
    }
    impl GhostRange for Iter<'_, u8> {
        fn ghost_range(&self) -> Option<(usize, usize)> {
            let rest = self.as_slice();
            let (base, len) = unsafe { GHOST };
            let start = (rest.as_ptr() as usize).wrapping_sub(base as usize);
            let end = start.wrapping_add(rest.len());
            (start <= end && end <= len).then_some((start, end))
        }
    }

    const CONT_MASK: u8 = 0b0011_1111;

    /// Model of `next_code_point`: the local rule where the decode starts,
    /// then the upstream body.
    unsafe fn model_next_code_point<'a, I: Iterator<Item = &'a u8>>(bytes: &mut I) -> Option<u32> {
        // `&*bytes`: `bytes.ghost_range()` would pick the blanket impl for `&mut I`
        if let Some((start, _)) = GhostRange::ghost_range(&*bytes) {
            kani::assume(utf8_ok_at(start));
        }
        // ---- upstream body, `utf8_first_byte` / `utf8_acc_cont_byte` inlined ----
        let x = *bytes.next()?;
        if x < 128 {
            return Some(x as u32);
        }
        let init = (x & (0x7F >> 2)) as u32;
        // SAFETY: as upstream.
        let y = unsafe { *bytes.next().unwrap_unchecked() };
        let mut ch = (init << 6) | (y & CONT_MASK) as u32;
        if x >= 0xE0 {
            // SAFETY: as upstream.
            let z = unsafe { *bytes.next().unwrap_unchecked() };
            let y_z = (((y & CONT_MASK) as u32) << 6) | (z & CONT_MASK) as u32;
            ch = init << 12 | y_z;
            if x >= 0xF0 {
                // SAFETY: as upstream.
                let w = unsafe { *bytes.next().unwrap_unchecked() };
                ch = (init & 7) << 18 | (y_z << 6) | (w & CONT_MASK) as u32;
            }
        }
        Some(ch)
    }

    /// Model of `next_code_point_reverse`: the local rule on the (up to four)
    /// bytes the decode can read, then the upstream body.
    unsafe fn model_next_code_point_reverse<'a, I>(bytes: &mut I) -> Option<u32>
    where
        I: DoubleEndedIterator<Item = &'a u8>,
    {
        if let Some((_, end)) = GhostRange::ghost_range(&*bytes) {
            kani::assume(end < 1 || utf8_ok_at(end - 1));
            kani::assume(end < 2 || utf8_ok_at(end - 2));
            kani::assume(end < 3 || utf8_ok_at(end - 3));
            kani::assume(end < 4 || utf8_ok_at(end - 4));
        }
        // ---- upstream body, `utf8_first_byte` / `utf8_acc_cont_byte` inlined ----
        let w = match *bytes.next_back()? {
            next_byte if next_byte < 128 => return Some(next_byte as u32),
            back_byte => back_byte,
        };
        let mut ch;
        // SAFETY: as upstream.
        let z = unsafe { *bytes.next_back().unwrap_unchecked() };
        ch = (z & (0x7F >> 2)) as u32;
        if utf8_is_cont_byte(z) {
            // SAFETY: as upstream.
            let y = unsafe { *bytes.next_back().unwrap_unchecked() };
            ch = (y & (0x7F >> 3)) as u32;
            if utf8_is_cont_byte(y) {
                // SAFETY: as upstream.
                let x = unsafe { *bytes.next_back().unwrap_unchecked() };
                ch = (x & (0x7F >> 4)) as u32;
                ch = (ch << 6) | (y & CONT_MASK) as u32;
            }
            ch = (ch << 6) | (z & CONT_MASK) as u32;
        }
        ch = (ch << 6) | (w & CONT_MASK) as u32;
        Some(ch)
    }

    /// Model of `memchr` (assumption 1): some index of `x` in `text`, or `None`.
    fn model_memchr(x: u8, text: &[u8]) -> Option<usize> {
        if kani::any() {
            return None;
        }
        let i: usize = kani::any();
        kani::assume(i < text.len() && text[i] == x);
        Some(i)
    }

    /// Model of `memrchr` (assumption 1): some index of `x` in `text`, or `None`.
    fn model_memrchr(x: u8, text: &[u8]) -> Option<usize> {
        model_memchr(x, text)
    }

    /// Model of the byte-wise slice equality `compare_bytes(lhs, rhs, size) == 0`
    /// (assumption 1). It recurses instead of looping: CBMC 6.11 rejects writes
    /// to the locals of a contract-less loop in a callee of a contracted loop
    /// (kani#4790, fixed after 6.11), which also rules out the `memcmp` builtin.
    unsafe fn model_equal_same_length<A, B>(lhs: *const A, rhs: *const B, len: usize) -> bool {
        // SAFETY: as upstream, both are readable for `len` elements.
        let size = unsafe { crate::intrinsics::unchecked_mul(len, crate::mem::size_of::<A>()) };
        // SAFETY: as above, both are readable for `size` bytes.
        unsafe { bytes_equal(lhs as *const u8, rhs as *const u8, size) }
    }

    /// # Safety
    /// `lhs` and `rhs` are readable for `n` bytes.
    unsafe fn bytes_equal(lhs: *const u8, rhs: *const u8, n: usize) -> bool {
        // SAFETY: if `n > 0`, the first byte and the `n - 1` after it are readable.
        n == 0 || unsafe { *lhs == *rhs && bytes_equal(lhs.add(1), rhs.add(1), n - 1) }
    }

    /// Model of `<[T]>::contains` (assumption 1): any result. The searchers use
    /// only this result, so the set is never read and its size is unbounded.
    fn model_contains<T>(_set: &[T], _x: &T) -> bool {
        kani::any()
    }

    /// A character set of symbolic length. Its contents are never read (see
    /// `model_contains`).
    fn any_char_slice() -> &'static [char] {
        let len: usize = kani::any();
        kani::assume(len <= MAX_ALLOCATION_BYTES / 4);
        let p: *const char = if len == 0 {
            crate::ptr::NonNull::<char>::dangling().as_ptr()
        } else {
            // SAFETY: CBMC's `malloc` model.
            let p = unsafe { malloc(len * 4) } as *const char;
            kani::assume(!p.is_null());
            p
        };
        // SAFETY: `p` is valid for `len` chars; they are never read.
        unsafe { crate::slice::from_raw_parts(p, len) }
    }

    /// Symbolic length, arbitrary contents: no validity assumption at all.
    fn any_haystack() -> &'static str {
        let len: usize = kani::any();
        kani::assume(len <= MAX_ALLOCATION_BYTES);
        let p: *const u8 = if len == 0 {
            crate::ptr::NonNull::<u8>::dangling().as_ptr()
        } else {
            // SAFETY: CBMC's `malloc` model.
            let p = unsafe { malloc(len) };
            kani::assume(!p.is_null());
            p
        };
        unsafe { GHOST = (p, len) };
        // SAFETY: `p` is valid for `len` reads; UTF-8 validity is imported
        // where it is relied on (see the module documentation).
        unsafe { super::super::from_utf8_unchecked(crate::slice::from_raw_parts(p, len)) }
    }

    /// The type invariant `C` of `CharSearcher`. The encoding is compared byte
    /// by byte: a slice `==` is a `memcmp` loop of symbolic length.
    fn char_searcher_inv(s: &CharSearcher<'_>) -> bool {
        let mut utf8 = [0; 4];
        let n = s.needle.encode_utf8(&mut utf8).len();
        let e = &s.utf8_encoded;
        s.finger <= s.finger_back
            && s.finger_back <= s.haystack.len()
            && s.haystack.is_char_boundary(s.finger)
            && s.haystack.is_char_boundary(s.finger_back)
            && s.utf8_size() == n
            && e[0] == utf8[0]
            && (n < 2 || e[1] == utf8[1])
            && (n < 3 || e[2] == utf8[2])
            && (n < 4 || e[3] == utf8[3])
    }

    /// An arbitrary `CharSearcher` over `haystack` that satisfies `C`.
    fn any_char_searcher(haystack: &'static str) -> CharSearcher<'static> {
        let needle: char = kani::any();
        let mut utf8_encoded = [0; 4];
        let utf8_size = needle.encode_utf8(&mut utf8_encoded).len() as u8;
        let s = CharSearcher {
            haystack,
            finger: kani::any(),
            finger_back: kani::any(),
            needle,
            utf8_size,
            utf8_encoded,
        };
        kani::assume(char_searcher_inv(&s));
        s
    }

    /// The returned range is in bounds and on char boundaries (safety
    /// property 2), and `C` still holds.
    fn check_result(s: &CharSearcher<'_>, range: Option<(usize, usize)>) {
        if let Some((a, b)) = range {
            assert!(a <= b && b <= s.haystack.len());
            assert!(s.haystack.is_char_boundary(a) && s.haystack.is_char_boundary(b));
        }
        assert!(char_searcher_inv(s));
    }

    fn step_range(step: SearchStep) -> Option<(usize, usize)> {
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => Some((a, b)),
            SearchStep::Done => None,
        }
    }

    /// `C` holds for every searcher created from a haystack (criterion 1).
    #[kani::proof]
    fn check_char_searcher_into_searcher() {
        let haystack = any_haystack();
        let needle: char = kani::any();
        let s = needle.into_searcher(haystack);
        assert!(char_searcher_inv(&s));
    }

    #[kani::proof]
    #[kani::stub(crate::str::validations::next_code_point, model_next_code_point)]
    fn check_char_searcher_next() {
        let mut s = any_char_searcher(any_haystack());
        let r = step_range(s.next());
        check_result(&s, r);
        kani::cover(r.is_some_and(|(_, b)| b > 4096), "a step far into the haystack");
    }

    #[kani::proof]
    #[kani::stub(crate::str::validations::next_code_point_reverse, model_next_code_point_reverse)]
    fn check_char_searcher_next_back() {
        let mut s = any_char_searcher(any_haystack());
        let r = step_range(s.next_back());
        check_result(&s, r);
        kani::cover(r.is_some_and(|(a, _)| a > 4096), "a step far into the haystack");
    }

    #[kani::proof]
    #[kani::stub(crate::str::validations::next_code_point, model_next_code_point)]
    fn check_char_searcher_next_reject() {
        let mut s = any_char_searcher(any_haystack());
        let r = s.next_reject();
        check_result(&s, r);
        kani::cover(r.is_some_and(|(_, b)| b > 4096), "a reject far into the haystack");
        kani::cover(r.is_none(), "searched to the end");
    }

    #[kani::proof]
    #[kani::stub(crate::str::validations::next_code_point_reverse, model_next_code_point_reverse)]
    fn check_char_searcher_next_reject_back() {
        let mut s = any_char_searcher(any_haystack());
        let r = s.next_reject_back();
        check_result(&s, r);
        kani::cover(r.is_some_and(|(a, _)| a > 4096), "a reject far into the haystack");
        kani::cover(r.is_none(), "searched to the start");
    }

    // `unwind(5)`: the needle comparison compares `utf8_size <= 4` bytes; the
    // search loop itself has a contract and is not unwound.
    #[kani::proof]
    #[kani::unwind(5)]
    #[kani::stub(crate::slice::memchr::memchr, model_memchr)]
    #[kani::stub(
        <u8 as crate::slice::cmp::SlicePartialEq<u8>>::equal_same_length,
        model_equal_same_length
    )]
    fn check_char_searcher_next_match() {
        let mut s = any_char_searcher(any_haystack());
        let r = s.next_match();
        if let Some((a, _)) = r {
            // The match starts at a lead byte: its sequence ends on a boundary.
            kani::assume(utf8_ok_at(a));
        }
        check_result(&s, r);
        kani::cover(r.is_some_and(|(_, b)| b > 4096), "a match far into the haystack");
        kani::cover(r.is_none(), "searched to the end");
    }

    // `unwind(5)`: as for `next_match`.
    #[kani::proof]
    #[kani::unwind(5)]
    #[kani::stub(crate::slice::memchr::memrchr, model_memrchr)]
    #[kani::stub(
        <u8 as crate::slice::cmp::SlicePartialEq<u8>>::equal_same_length,
        model_equal_same_length
    )]
    fn check_char_searcher_next_match_back() {
        let mut s = any_char_searcher(any_haystack());
        let r = s.next_match_back();
        if let Some((a, _)) = r {
            // The match starts at a lead byte: its sequence ends on a boundary.
            kani::assume(utf8_ok_at(a));
        }
        check_result(&s, r);
        kani::cover(r.is_some_and(|(a, _)| a > 4096), "a match far into the haystack");
        kani::cover(r.is_none(), "searched to the start");
    }

    /// The decoder models only add assumptions: on every valid 1..=4-byte
    /// input they return what upstream returns and consume the same bytes.
    #[kani::proof]
    #[kani::unwind(6)]
    fn check_next_code_point_model_matches_upstream() {
        let bytes: [u8; 4] = kani::any();
        let n: usize = kani::any_where(|n| *n >= 1 && *n <= 4);
        let s = &bytes[..n];
        kani::assume(crate::str::from_utf8(s).is_ok());
        unsafe { GHOST = (s.as_ptr(), n) };
        let (mut a, mut b) = (s.iter(), s.iter());
        let ra = unsafe { model_next_code_point(&mut a) };
        let rb = unsafe { crate::str::validations::next_code_point(&mut b) };
        assert!(ra == rb && a.as_slice().len() == b.as_slice().len());
        kani::cover(n == 4 && ra.is_some(), "a 4-byte character");
    }

    #[kani::proof]
    #[kani::unwind(6)]
    fn check_next_code_point_reverse_model_matches_upstream() {
        let bytes: [u8; 4] = kani::any();
        let n: usize = kani::any_where(|n| *n >= 1 && *n <= 4);
        let s = &bytes[..n];
        kani::assume(crate::str::from_utf8(s).is_ok());
        unsafe { GHOST = (s.as_ptr(), n) };
        let (mut a, mut b) = (s.iter(), s.iter());
        let ra = unsafe { model_next_code_point_reverse(&mut a) };
        let rb = unsafe { crate::str::validations::next_code_point_reverse(&mut b) };
        assert!(ra == rb && a.as_slice().len() == b.as_slice().len());
        kani::cover(n == 4 && ra.is_some(), "a 4-byte character");
    }

    /// The memchr models allow every result of the real functions.
    #[kani::proof]
    #[kani::unwind(10)]
    fn check_memchr_models_cover_upstream() {
        let text: [u8; 8] = kani::any();
        let text = kani::slice::any_slice_of_array(&text);
        let x: u8 = kani::any();
        if let Some(i) = crate::slice::memchr::memchr(x, text) {
            assert!(i < text.len() && text[i] == x);
        }
        if let Some(i) = crate::slice::memchr::memrchr(x, text) {
            assert!(i < text.len() && text[i] == x);
        }
    }

    /// The slice equality model returns what upstream returns.
    #[kani::proof]
    #[kani::unwind(5)]
    fn check_slice_eq_model_matches_upstream() {
        let (a, b): ([u8; 4], [u8; 4]) = (kani::any(), kani::any());
        let n: usize = kani::any();
        kani::assume(n <= 4);
        // SAFETY: both arrays are readable for `n <= 4` bytes.
        let model = unsafe { model_equal_same_length(a.as_ptr(), b.as_ptr(), n) };
        assert!((a[..n] == b[..n]) == model);
    }

    /// An arbitrary `MultiCharEqSearcher` over `haystack` that satisfies `C`.
    fn any_multi_char_eq_searcher<C: MultiCharEq>(
        haystack: &'static str,
        char_eq: C,
    ) -> MultiCharEqSearcher<'static, C> {
        let (f, b): (usize, usize) = (kani::any(), kani::any());
        kani::assume(f <= b && b <= haystack.len());
        kani::assume(haystack.is_char_boundary(f) && haystack.is_char_boundary(b));
        // SAFETY: `f <= b <= haystack.len()`.
        let rest = unsafe { haystack.as_bytes().get_unchecked(f..b) };
        let char_indices = crate::str::CharIndices {
            front_offset: f,
            iter: crate::str::Chars { iter: rest.iter() },
        };
        MultiCharEqSearcher { char_eq, haystack, char_indices }
    }

    /// As `check_result`, for `MultiCharEqSearcher`.
    fn check_multi_char_eq_result<C: MultiCharEq>(
        s: &MultiCharEqSearcher<'_, C>,
        range: Option<(usize, usize)>,
    ) {
        if let Some((a, b)) = range {
            assert!(a <= b && b <= s.haystack.len());
            assert!(s.haystack.is_char_boundary(a) && s.haystack.is_char_boundary(b));
        }
        assert!(s.kani_ok());
    }

    /// The proofs for one `MultiCharEq` instance, through the searcher that
    /// wraps it: creation establishes `C` (criterion 1); `next` / `next_back`
    /// meet their contracts from any state that satisfies `C` (criteria 2 and
    /// 3); the four searching methods (the provided trait methods, reached
    /// through the wrapper) run with those verified contracts in place of the
    /// steps, so their loops never read through the cursor that the loop
    /// contract havocs. The set itself is abstracted (`model_contains`), so no
    /// loop is unwound anywhere.
    macro_rules! multi_char_eq_proofs {
        ($m:ident, $wrapper:ident, $c:ty, |$set:ident| $eq:expr) => {
            mod $m {
                use super::*;

                #[kani::proof]
                fn check_into_searcher() {
                    let $set: [char; 2] = kani::any();
                    let s = $eq.into_searcher(any_haystack());
                    assert!(s.0.kani_ok());
                }

                #[kani::proof_for_contract(<MultiCharEqSearcher<$c> as Searcher>::next)]
                #[kani::stub(crate::str::validations::next_code_point, model_next_code_point)]
                #[kani::stub(<[char]>::contains, model_contains)]
                fn check_next() {
                    let $set: [char; 2] = kani::any();
                    let mut s = $wrapper(any_multi_char_eq_searcher(any_haystack(), $eq));
                    let r = step_range(s.next());
                    check_multi_char_eq_result(&s.0, r);
                    kani::cover(r.is_some_and(|(_, b)| b > 4096), "a step far into the haystack");
                }

                #[kani::proof_for_contract(<MultiCharEqSearcher<$c> as ReverseSearcher>::next_back)]
                #[kani::stub(
                    crate::str::validations::next_code_point_reverse,
                    model_next_code_point_reverse
                )]
                #[kani::stub(<[char]>::contains, model_contains)]
                fn check_next_back() {
                    let $set: [char; 2] = kani::any();
                    let mut s = $wrapper(any_multi_char_eq_searcher(any_haystack(), $eq));
                    let r = step_range(s.next_back());
                    check_multi_char_eq_result(&s.0, r);
                    kani::cover(r.is_some_and(|(a, _)| a > 4096), "a step far into the haystack");
                }

                #[kani::proof]
                #[kani::stub_verified(<MultiCharEqSearcher<$c> as Searcher>::next)]
                fn check_next_match() {
                    let $set: [char; 2] = kani::any();
                    let mut s = $wrapper(any_multi_char_eq_searcher(any_haystack(), $eq));
                    let r = s.next_match();
                    check_multi_char_eq_result(&s.0, r);
                    kani::cover(r.is_some_and(|(_, b)| b > 4096), "a match far into the haystack");
                    kani::cover(r.is_none(), "searched to the end");
                }

                #[kani::proof]
                #[kani::stub_verified(<MultiCharEqSearcher<$c> as Searcher>::next)]
                fn check_next_reject() {
                    let $set: [char; 2] = kani::any();
                    let mut s = $wrapper(any_multi_char_eq_searcher(any_haystack(), $eq));
                    let r = s.next_reject();
                    check_multi_char_eq_result(&s.0, r);
                    kani::cover(r.is_some_and(|(_, b)| b > 4096), "a reject far into the haystack");
                    kani::cover(r.is_none(), "searched to the end");
                }

                #[kani::proof]
                #[kani::stub_verified(<MultiCharEqSearcher<$c> as ReverseSearcher>::next_back)]
                fn check_next_match_back() {
                    let $set: [char; 2] = kani::any();
                    let mut s = $wrapper(any_multi_char_eq_searcher(any_haystack(), $eq));
                    let r = s.next_match_back();
                    check_multi_char_eq_result(&s.0, r);
                    kani::cover(r.is_some_and(|(a, _)| a > 4096), "a match far into the haystack");
                    kani::cover(r.is_none(), "searched to the start");
                }

                #[kani::proof]
                #[kani::stub_verified(<MultiCharEqSearcher<$c> as ReverseSearcher>::next_back)]
                fn check_next_reject_back() {
                    let $set: [char; 2] = kani::any();
                    let mut s = $wrapper(any_multi_char_eq_searcher(any_haystack(), $eq));
                    let r = s.next_reject_back();
                    check_multi_char_eq_result(&s.0, r);
                    kani::cover(r.is_some_and(|(a, _)| a > 4096), "a reject far into the haystack");
                    kani::cover(r.is_none(), "searched to the start");
                }
            }
        };
    }

    // `N` only sets the size of the set value: the set is never read.
    multi_char_eq_proofs!(char_array, CharArraySearcher, [char; 2], |set| set);
    multi_char_eq_proofs!(char_array_ref, CharArrayRefSearcher, &[char; 2], |set| &set);
    multi_char_eq_proofs!(char_slice, CharSliceSearcher, &[char], |set| {
        let _ = set;
        any_char_slice()
    });
    // Any predicate result on every call.
    multi_char_eq_proofs!(char_predicate, CharPredicateSearcher, fn(char) -> bool, |set| {
        let _ = set;
        (|_| kani::any()) as fn(char) -> bool
    });
    // A predicate that also writes state of its own (inside `char_eq`).
    multi_char_eq_proofs!(char_predicate_state, CharPredicateSearcher, Toggle, |set| {
        let _ = set;
        Toggle(kani::any())
    });

    /// A predicate with state: it flips a flag on every call, like a `move`
    /// closure that updates a capture, and returns any result.
    struct Toggle(bool);

    impl FnOnce<(char,)> for Toggle {
        type Output = bool;

        extern "rust-call" fn call_once(mut self, args: (char,)) -> bool {
            self.call_mut(args)
        }
    }

    impl FnMut<(char,)> for Toggle {
        extern "rust-call" fn call_mut(&mut self, _: (char,)) -> bool {
            self.0 = !self.0;
            kani::any()
        }
    }
}
