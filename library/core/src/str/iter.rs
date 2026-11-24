//! Iterators for `str` methods.

use safety::requires;

use super::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};
use super::validations::{next_code_point, next_code_point_reverse};
use super::{
    BytesIsNotEmpty, CharEscapeDebug, CharEscapeDefault, CharEscapeUnicode, IsAsciiWhitespace,
    IsNotEmpty, IsWhitespace, LinesMap, UnsafeBytesToStr, from_utf8_unchecked,
};
use crate::char as char_mod;
use crate::fmt::{self, Write};
use crate::iter::{
    Copied, Filter, FlatMap, FusedIterator, Map, TrustedLen, TrustedRandomAccess,
    TrustedRandomAccessNoCoerce,
};
#[cfg(kani)]
use crate::kani;
use crate::num::NonZero;
use crate::ops::Try;
use crate::slice::{self, Split as SliceSplit};

/// An iterator over the [`char`]s of a string slice.
///
///
/// This struct is created by the [`chars`] method on [`str`].
/// See its documentation for more.
///
/// [`char`]: prim@char
/// [`chars`]: str::chars
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Chars<'a> {
    pub(super) iter: slice::Iter<'a, u8>,
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        // SAFETY: `str` invariant says `self.iter` is a valid UTF-8 string and
        // the resulting `ch` is a valid Unicode Scalar Value.
        unsafe { next_code_point(&mut self.iter).map(|ch| char::from_u32_unchecked(ch)) }
    }

    #[inline]
    fn count(self) -> usize {
        super::count::count_chars(self.as_str())
    }

    #[inline]
    fn advance_by(&mut self, mut remainder: usize) -> Result<(), NonZero<usize>> {
        const CHUNK_SIZE: usize = 32;
        #[cfg(kani)]
        let input = self.iter.as_slice();
        #[cfg(kani)]
        let (cursor, requested) = (self.iter.kani_cursor_slot(), remainder);

        if remainder >= CHUNK_SIZE {
            let mut chunks = self.iter.as_slice().as_chunks::<CHUNK_SIZE>().0.iter();
            let mut bytes_skipped: usize = 0;

            // Infer the write set so it includes the temporary for `chunks.next()`.
            #[safety::loop_invariant(verify::chunks_inv(
                &raw const chunks, bytes_skipped, input, requested, remainder,
            ))]
            while remainder > CHUNK_SIZE
                && let Some(chunk) = chunks.next()
            {
                bytes_skipped += CHUNK_SIZE;

                let mut start_bytes = [false; CHUNK_SIZE];

                #[cfg(kani)]
                let (slot, is_start) = {
                    let slot = kani::any::<u8>() as usize % CHUNK_SIZE;
                    (slot, chunk[slot] & 0xc0 != 0x80)
                };
                #[cfg_attr(kani, kani::loop_invariant(
                    verify::chunk_flags_inv(&raw const start_bytes, slot, is_start, kani::index)
                ))]
                #[cfg_attr(kani, kani::loop_modifies(&raw mut start_bytes))]
                for i in 0..CHUNK_SIZE {
                    start_bytes[i] = !super::validations::utf8_is_cont_byte(chunk[i]);
                }

                #[cfg(kani)]
                let expected_remainder = remainder
                    - verify::chunk_start_count(
                        input,
                        chunk,
                        bytes_skipped,
                        start_bytes,
                        (slot, is_start),
                    );
                remainder -= start_bytes.into_iter().map(|i| i as u8).sum::<u8>() as usize;
                #[cfg(kani)]
                assert!(remainder == expected_remainder);
            }

            // SAFETY: The amount of bytes exists since we just iterated over them,
            // so advance_by will succeed.
            unsafe { self.iter.advance_by(bytes_skipped).unwrap_unchecked() };

            // skip trailing continuation bytes
            #[safety::loop_invariant(verify::bytes_inv(
                &raw const self.iter, input, bytes_skipped, false,
            ))]
            #[cfg_attr(kani, kani::loop_modifies(cursor))]
            while self.iter.len() > 0 {
                let b = self.iter.as_slice()[0];
                if !super::validations::utf8_is_cont_byte(b) {
                    break;
                }
                // SAFETY: We just peeked at the byte, therefore it exists
                unsafe { self.iter.advance_by(1).unwrap_unchecked() };
            }
        }

        #[safety::loop_invariant(
            remainder <= requested
                && verify::bytes_inv(&raw const self.iter, input, requested - remainder, true)
        )]
        #[cfg_attr(kani, kani::loop_modifies(cursor, &raw mut remainder))]
        while (remainder > 0) && (self.iter.len() > 0) {
            remainder -= 1;
            let b = self.iter.as_slice()[0];
            #[cfg(kani)]
            verify::assume_utf8_step(input, input.len() - self.iter.len(), b);
            let slurp = super::validations::utf8_char_width(b);
            // SAFETY: utf8 validity requires that the string must contain
            // the continuation bytes (if any)
            unsafe { self.iter.advance_by(slurp).unwrap_unchecked() };
        }

        NonZero::new(remainder).map_or(Ok(()), Err)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.iter.len();
        (len.div_ceil(4), Some(len))
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        // No need to go through the entire string.
        self.next_back()
    }
}

#[stable(feature = "chars_debug_impl", since = "1.38.0")]
impl fmt::Debug for Chars<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Chars(")?;
        f.debug_list().entries(self.clone()).finish()?;
        write!(f, ")")?;
        Ok(())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> DoubleEndedIterator for Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        // SAFETY: `str` invariant says `self.iter` is a valid UTF-8 string and
        // the resulting `ch` is a valid Unicode Scalar Value.
        unsafe { next_code_point_reverse(&mut self.iter).map(|ch| char::from_u32_unchecked(ch)) }
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for Chars<'_> {}

impl<'a> Chars<'a> {
    /// Views the underlying data as a subslice of the original data.
    ///
    /// This has the same lifetime as the original slice, and so the
    /// iterator can continue to be used while this exists.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut chars = "abc".chars();
    ///
    /// assert_eq!(chars.as_str(), "abc");
    /// chars.next();
    /// assert_eq!(chars.as_str(), "bc");
    /// chars.next();
    /// chars.next();
    /// assert_eq!(chars.as_str(), "");
    /// ```
    #[stable(feature = "iter_to_slice", since = "1.4.0")]
    #[must_use]
    #[inline]
    pub fn as_str(&self) -> &'a str {
        // SAFETY: `Chars` is only made from a str, which guarantees the iter is valid UTF-8.
        unsafe { from_utf8_unchecked(self.iter.as_slice()) }
    }
}

/// An iterator over the [`char`]s of a string slice, and their positions.
///
/// This struct is created by the [`char_indices`] method on [`str`].
/// See its documentation for more.
///
/// [`char`]: prim@char
/// [`char_indices`]: str::char_indices
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct CharIndices<'a> {
    pub(super) front_offset: usize,
    pub(super) iter: Chars<'a>,
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> Iterator for CharIndices<'a> {
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<(usize, char)> {
        let pre_len = self.iter.iter.len();
        match self.iter.next() {
            None => None,
            Some(ch) => {
                let index = self.front_offset;
                let len = self.iter.iter.len();
                self.front_offset += pre_len - len;
                Some((index, ch))
            }
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<(usize, char)> {
        // No need to go through the entire string.
        self.next_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> DoubleEndedIterator for CharIndices<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<(usize, char)> {
        self.iter.next_back().map(|ch| {
            let index = self.front_offset + self.iter.iter.len();
            (index, ch)
        })
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for CharIndices<'_> {}

impl<'a> CharIndices<'a> {
    /// Views the underlying data as a subslice of the original data.
    ///
    /// This has the same lifetime as the original slice, and so the
    /// iterator can continue to be used while this exists.
    #[stable(feature = "iter_to_slice", since = "1.4.0")]
    #[must_use]
    #[inline]
    pub fn as_str(&self) -> &'a str {
        self.iter.as_str()
    }

    /// Returns the byte position of the next character, or the length
    /// of the underlying string if there are no more characters.
    ///
    /// This means that, when the iterator has not been fully consumed,
    /// the returned value will match the index that will be returned
    /// by the next call to [`next()`](Self::next).
    ///
    /// # Examples
    ///
    /// ```
    /// let mut chars = "a楽".char_indices();
    ///
    /// // `next()` has not been called yet, so `offset()` returns the byte
    /// // index of the first character of the string, which is always 0.
    /// assert_eq!(chars.offset(), 0);
    /// // As expected, the first call to `next()` also returns 0 as index.
    /// assert_eq!(chars.next(), Some((0, 'a')));
    ///
    /// // `next()` has been called once, so `offset()` returns the byte index
    /// // of the second character ...
    /// assert_eq!(chars.offset(), 1);
    /// // ... which matches the index returned by the next call to `next()`.
    /// assert_eq!(chars.next(), Some((1, '楽')));
    ///
    /// // Once the iterator has been consumed, `offset()` returns the length
    /// // in bytes of the string.
    /// assert_eq!(chars.offset(), 4);
    /// assert_eq!(chars.next(), None);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "char_indices_offset", since = "1.82.0")]
    pub fn offset(&self) -> usize {
        self.front_offset
    }
}

/// An iterator over the bytes of a string slice.
///
/// This struct is created by the [`bytes`] method on [`str`].
/// See its documentation for more.
///
/// [`bytes`]: str::bytes
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Clone, Debug)]
pub struct Bytes<'a>(pub(super) Copied<slice::Iter<'a, u8>>);

#[stable(feature = "rust1", since = "1.0.0")]
impl Iterator for Bytes<'_> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.0.count()
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        self.0.last()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n)
    }

    #[inline]
    fn all<F>(&mut self, f: F) -> bool
    where
        F: FnMut(Self::Item) -> bool,
    {
        self.0.all(f)
    }

    #[inline]
    fn any<F>(&mut self, f: F) -> bool
    where
        F: FnMut(Self::Item) -> bool,
    {
        self.0.any(f)
    }

    #[inline]
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        self.0.find(predicate)
    }

    #[inline]
    fn position<P>(&mut self, predicate: P) -> Option<usize>
    where
        P: FnMut(Self::Item) -> bool,
    {
        self.0.position(predicate)
    }

    #[inline]
    fn rposition<P>(&mut self, predicate: P) -> Option<usize>
    where
        P: FnMut(Self::Item) -> bool,
    {
        self.0.rposition(predicate)
    }

    #[inline]
    #[requires(idx < self.0.len())]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> u8 {
        // SAFETY: the caller must uphold the safety contract
        // for `Iterator::__iterator_get_unchecked`.
        unsafe { self.0.__iterator_get_unchecked(idx) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl DoubleEndedIterator for Bytes<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<u8> {
        self.0.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n)
    }

    #[inline]
    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
    where
        P: FnMut(&Self::Item) -> bool,
    {
        self.0.rfind(predicate)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl ExactSizeIterator for Bytes<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for Bytes<'_> {}

#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl TrustedLen for Bytes<'_> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl TrustedRandomAccess for Bytes<'_> {}

#[doc(hidden)]
#[unstable(feature = "trusted_random_access", issue = "none")]
unsafe impl TrustedRandomAccessNoCoerce for Bytes<'_> {
    const MAY_HAVE_SIDE_EFFECT: bool = false;
}

/// This macro generates a Clone impl for string pattern API
/// wrapper types of the form X<'a, P>
macro_rules! derive_pattern_clone {
    (clone $t:ident with |$s:ident| $e:expr) => {
        impl<'a, P> Clone for $t<'a, P>
        where
            P: Pattern<Searcher<'a>: Clone>,
        {
            fn clone(&self) -> Self {
                let $s = self;
                $e
            }
        }
    };
}

/// This macro generates two public iterator structs
/// wrapping a private internal one that makes use of the `Pattern` API.
///
/// For all patterns `P: Pattern` the following items will be
/// generated (generics omitted):
///
/// struct $forward_iterator($internal_iterator);
/// struct $reverse_iterator($internal_iterator);
///
/// impl Iterator for $forward_iterator
/// { /* internal ends up calling Searcher::next_match() */ }
///
/// impl DoubleEndedIterator for $forward_iterator
///       where P::Searcher: DoubleEndedSearcher
/// { /* internal ends up calling Searcher::next_match_back() */ }
///
/// impl Iterator for $reverse_iterator
///       where P::Searcher: ReverseSearcher
/// { /* internal ends up calling Searcher::next_match_back() */ }
///
/// impl DoubleEndedIterator for $reverse_iterator
///       where P::Searcher: DoubleEndedSearcher
/// { /* internal ends up calling Searcher::next_match() */ }
///
/// The internal one is defined outside the macro, and has almost the same
/// semantic as a DoubleEndedIterator by delegating to `pattern::Searcher` and
/// `pattern::ReverseSearcher` for both forward and reverse iteration.
///
/// "Almost", because a `Searcher` and a `ReverseSearcher` for a given
/// `Pattern` might not return the same elements, so actually implementing
/// `DoubleEndedIterator` for it would be incorrect.
/// (See the docs in `str::pattern` for more details)
///
/// However, the internal struct still represents a single ended iterator from
/// either end, and depending on pattern is also a valid double ended iterator,
/// so the two wrapper structs implement `Iterator`
/// and `DoubleEndedIterator` depending on the concrete pattern type, leading
/// to the complex impls seen above.
macro_rules! generate_pattern_iterators {
    {
        // Forward iterator
        forward:
            $(#[$forward_iterator_attribute:meta])*
            struct $forward_iterator:ident;

        // Reverse iterator
        reverse:
            $(#[$reverse_iterator_attribute:meta])*
            struct $reverse_iterator:ident;

        // Stability of all generated items
        stability:
            $(#[$common_stability_attribute:meta])*

        // Internal almost-iterator that is being delegated to
        internal:
            $internal_iterator:ident yielding ($iterty:ty);

        // Kind of delegation - either single ended or double ended
        delegate $($t:tt)*
    } => {
        $(#[$forward_iterator_attribute])*
        $(#[$common_stability_attribute])*
        pub struct $forward_iterator<'a, P: Pattern>(pub(super) $internal_iterator<'a, P>);

        $(#[$common_stability_attribute])*
        impl<'a, P> fmt::Debug for $forward_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: fmt::Debug>,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple(stringify!($forward_iterator))
                    .field(&self.0)
                    .finish()
            }
        }

        $(#[$common_stability_attribute])*
        impl<'a, P: Pattern> Iterator for $forward_iterator<'a, P> {
            type Item = $iterty;

            #[inline]
            fn next(&mut self) -> Option<$iterty> {
                self.0.next()
            }
        }

        $(#[$common_stability_attribute])*
        impl<'a, P> Clone for $forward_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: Clone>,
        {
            fn clone(&self) -> Self {
                $forward_iterator(self.0.clone())
            }
        }

        $(#[$reverse_iterator_attribute])*
        $(#[$common_stability_attribute])*
        pub struct $reverse_iterator<'a, P: Pattern>(pub(super) $internal_iterator<'a, P>);

        $(#[$common_stability_attribute])*
        impl<'a, P> fmt::Debug for $reverse_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: fmt::Debug>,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple(stringify!($reverse_iterator))
                    .field(&self.0)
                    .finish()
            }
        }

        $(#[$common_stability_attribute])*
        impl<'a, P> Iterator for $reverse_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: ReverseSearcher<'a>>,
        {
            type Item = $iterty;

            #[inline]
            fn next(&mut self) -> Option<$iterty> {
                self.0.next_back()
            }
        }

        $(#[$common_stability_attribute])*
        impl<'a, P> Clone for $reverse_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: Clone>,
        {
            fn clone(&self) -> Self {
                $reverse_iterator(self.0.clone())
            }
        }

        #[stable(feature = "fused", since = "1.26.0")]
        impl<'a, P: Pattern> FusedIterator for $forward_iterator<'a, P> {}

        #[stable(feature = "fused", since = "1.26.0")]
        impl<'a, P> FusedIterator for $reverse_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: ReverseSearcher<'a>>,
        {}

        generate_pattern_iterators!($($t)* with $(#[$common_stability_attribute])*,
                                                $forward_iterator,
                                                $reverse_iterator, $iterty);
    };
    {
        double ended; with $(#[$common_stability_attribute:meta])*,
                           $forward_iterator:ident,
                           $reverse_iterator:ident, $iterty:ty
    } => {
        $(#[$common_stability_attribute])*
        impl<'a, P> DoubleEndedIterator for $forward_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: DoubleEndedSearcher<'a>>,
        {
            #[inline]
            fn next_back(&mut self) -> Option<$iterty> {
                self.0.next_back()
            }
        }

        $(#[$common_stability_attribute])*
        impl<'a, P> DoubleEndedIterator for $reverse_iterator<'a, P>
        where
            P: Pattern<Searcher<'a>: DoubleEndedSearcher<'a>>,
        {
            #[inline]
            fn next_back(&mut self) -> Option<$iterty> {
                self.0.next()
            }
        }
    };
    {
        single ended; with $(#[$common_stability_attribute:meta])*,
                           $forward_iterator:ident,
                           $reverse_iterator:ident, $iterty:ty
    } => {}
}

derive_pattern_clone! {
    clone SplitInternal
    with |s| SplitInternal { matcher: s.matcher.clone(), ..*s }
}

pub(super) struct SplitInternal<'a, P: Pattern> {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) matcher: P::Searcher<'a>,
    pub(super) allow_trailing_empty: bool,
    pub(super) finished: bool,
}

impl<'a, P> fmt::Debug for SplitInternal<'a, P>
where
    P: Pattern<Searcher<'a>: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitInternal")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("matcher", &self.matcher)
            .field("allow_trailing_empty", &self.allow_trailing_empty)
            .field("finished", &self.finished)
            .finish()
    }
}

impl<'a, P: Pattern> SplitInternal<'a, P> {
    #[inline]
    fn get_end(&mut self) -> Option<&'a str> {
        if !self.finished {
            self.finished = true;

            if self.allow_trailing_empty || self.end - self.start > 0 {
                // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
                let string = unsafe { self.matcher.haystack().get_unchecked(self.start..self.end) };
                return Some(string);
            }
        }

        None
    }

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            // SAFETY: `Searcher` guarantees that:
            // - `a` and `b` lie on unicode boundaries.
            // - `a <= b <= haystack().len()` is satisfied.
            Some((a, b)) => unsafe {
                let elt = haystack.get_unchecked(self.start..a);
                self.start = b;
                Some(elt)
            },
            None => self.get_end(),
        }
    }

    #[inline]
    fn next_inclusive(&mut self) -> Option<&'a str> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            // SAFETY: `Searcher` guarantees that:
            // - `b` lies on unicode boundary.
            // - `self.start` is either the start of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            // - `self.start <= b <= haystack().len()` is satisfied.
            Some((_, b)) => unsafe {
                let elt = haystack.get_unchecked(self.start..b);
                self.start = b;
                Some(elt)
            },
            None => self.get_end(),
        }
    }

    #[inline]
    fn next_back(&mut self) -> Option<&'a str>
    where
        P::Searcher<'a>: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            // SAFETY: `Searcher` guarantees that:
            // - `a` and `b` lie on unicode boundaries.
            // - `self.end` is either the end of the original string,
            // or `a` was assigned to it, so it also lies on unicode boundary.
            // - `a <= b <= haystack().len()` is satisfied.
            Some((a, b)) => unsafe {
                let elt = haystack.get_unchecked(b..self.end);
                self.end = a;
                Some(elt)
            },
            // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
            None => unsafe {
                self.finished = true;
                Some(haystack.get_unchecked(self.start..self.end))
            },
        }
    }

    #[inline]
    fn next_back_inclusive(&mut self) -> Option<&'a str>
    where
        P::Searcher<'a>: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back_inclusive() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            // SAFETY: `Searcher` guarantees that:
            // - `b` lies on unicode boundary.
            // - self.end is either the end of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            // - `self.end <= b <= haystack.len()` is satisfied.
            Some((_, b)) => unsafe {
                let elt = haystack.get_unchecked(b..self.end);
                self.end = b;
                Some(elt)
            },
            // SAFETY: self.start is either the start of the original string,
            // or start of a substring that represents the part of the string that hasn't
            // iterated yet. Either way, it is guaranteed to lie on unicode boundary.
            // self.end is either the end of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            None => unsafe {
                self.finished = true;
                Some(haystack.get_unchecked(self.start..self.end))
            },
        }
    }

    #[inline]
    fn remainder(&self) -> Option<&'a str> {
        // `Self::get_end` doesn't change `self.start`
        if self.finished {
            return None;
        }

        // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
        Some(unsafe { self.matcher.haystack().get_unchecked(self.start..self.end) })
    }
}

generate_pattern_iterators! {
    forward:
        /// Created with the method [`split`].
        ///
        /// [`split`]: str::split
        struct Split;
    reverse:
        /// Created with the method [`rsplit`].
        ///
        /// [`rsplit`]: str::rsplit
        struct RSplit;
    stability:
        #[stable(feature = "rust1", since = "1.0.0")]
    internal:
        SplitInternal yielding (&'a str);
    delegate double ended;
}

impl<'a, P: Pattern> Split<'a, P> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_remainder)]
    /// let mut split = "Mary had a little lamb".split(' ');
    /// assert_eq!(split.remainder(), Some("Mary had a little lamb"));
    /// split.next();
    /// assert_eq!(split.remainder(), Some("had a little lamb"));
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[unstable(feature = "str_split_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.remainder()
    }
}

impl<'a, P: Pattern> RSplit<'a, P> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_remainder)]
    /// let mut split = "Mary had a little lamb".rsplit(' ');
    /// assert_eq!(split.remainder(), Some("Mary had a little lamb"));
    /// split.next();
    /// assert_eq!(split.remainder(), Some("Mary had a little"));
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[unstable(feature = "str_split_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.remainder()
    }
}

generate_pattern_iterators! {
    forward:
        /// Created with the method [`split_terminator`].
        ///
        /// [`split_terminator`]: str::split_terminator
        struct SplitTerminator;
    reverse:
        /// Created with the method [`rsplit_terminator`].
        ///
        /// [`rsplit_terminator`]: str::rsplit_terminator
        struct RSplitTerminator;
    stability:
        #[stable(feature = "rust1", since = "1.0.0")]
    internal:
        SplitInternal yielding (&'a str);
    delegate double ended;
}

impl<'a, P: Pattern> SplitTerminator<'a, P> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_remainder)]
    /// let mut split = "A..B..".split_terminator('.');
    /// assert_eq!(split.remainder(), Some("A..B.."));
    /// split.next();
    /// assert_eq!(split.remainder(), Some(".B.."));
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[unstable(feature = "str_split_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.remainder()
    }
}

impl<'a, P: Pattern> RSplitTerminator<'a, P> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_remainder)]
    /// let mut split = "A..B..".rsplit_terminator('.');
    /// assert_eq!(split.remainder(), Some("A..B.."));
    /// split.next();
    /// assert_eq!(split.remainder(), Some("A..B"));
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[unstable(feature = "str_split_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.remainder()
    }
}

derive_pattern_clone! {
    clone SplitNInternal
    with |s| SplitNInternal { iter: s.iter.clone(), ..*s }
}

pub(super) struct SplitNInternal<'a, P: Pattern> {
    pub(super) iter: SplitInternal<'a, P>,
    /// The number of splits remaining
    pub(super) count: usize,
}

impl<'a, P> fmt::Debug for SplitNInternal<'a, P>
where
    P: Pattern<Searcher<'a>: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitNInternal")
            .field("iter", &self.iter)
            .field("count", &self.count)
            .finish()
    }
}

impl<'a, P: Pattern> SplitNInternal<'a, P> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        match self.count {
            0 => None,
            1 => {
                self.count = 0;
                self.iter.get_end()
            }
            _ => {
                self.count -= 1;
                self.iter.next()
            }
        }
    }

    #[inline]
    fn next_back(&mut self) -> Option<&'a str>
    where
        P::Searcher<'a>: ReverseSearcher<'a>,
    {
        match self.count {
            0 => None,
            1 => {
                self.count = 0;
                self.iter.get_end()
            }
            _ => {
                self.count -= 1;
                self.iter.next_back()
            }
        }
    }

    #[inline]
    fn remainder(&self) -> Option<&'a str> {
        self.iter.remainder()
    }
}

generate_pattern_iterators! {
    forward:
        /// Created with the method [`splitn`].
        ///
        /// [`splitn`]: str::splitn
        struct SplitN;
    reverse:
        /// Created with the method [`rsplitn`].
        ///
        /// [`rsplitn`]: str::rsplitn
        struct RSplitN;
    stability:
        #[stable(feature = "rust1", since = "1.0.0")]
    internal:
        SplitNInternal yielding (&'a str);
    delegate single ended;
}

impl<'a, P: Pattern> SplitN<'a, P> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_remainder)]
    /// let mut split = "Mary had a little lamb".splitn(3, ' ');
    /// assert_eq!(split.remainder(), Some("Mary had a little lamb"));
    /// split.next();
    /// assert_eq!(split.remainder(), Some("had a little lamb"));
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[unstable(feature = "str_split_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.remainder()
    }
}

impl<'a, P: Pattern> RSplitN<'a, P> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_remainder)]
    /// let mut split = "Mary had a little lamb".rsplitn(3, ' ');
    /// assert_eq!(split.remainder(), Some("Mary had a little lamb"));
    /// split.next();
    /// assert_eq!(split.remainder(), Some("Mary had a little"));
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[unstable(feature = "str_split_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.remainder()
    }
}

derive_pattern_clone! {
    clone MatchIndicesInternal
    with |s| MatchIndicesInternal(s.0.clone())
}

pub(super) struct MatchIndicesInternal<'a, P: Pattern>(pub(super) P::Searcher<'a>);

impl<'a, P> fmt::Debug for MatchIndicesInternal<'a, P>
where
    P: Pattern<Searcher<'a>: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MatchIndicesInternal").field(&self.0).finish()
    }
}

impl<'a, P: Pattern> MatchIndicesInternal<'a, P> {
    #[inline]
    fn next(&mut self) -> Option<(usize, &'a str)> {
        self.0
            .next_match()
            // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
            .map(|(start, end)| unsafe { (start, self.0.haystack().get_unchecked(start..end)) })
    }

    #[inline]
    fn next_back(&mut self) -> Option<(usize, &'a str)>
    where
        P::Searcher<'a>: ReverseSearcher<'a>,
    {
        self.0
            .next_match_back()
            // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
            .map(|(start, end)| unsafe { (start, self.0.haystack().get_unchecked(start..end)) })
    }
}

generate_pattern_iterators! {
    forward:
        /// Created with the method [`match_indices`].
        ///
        /// [`match_indices`]: str::match_indices
        struct MatchIndices;
    reverse:
        /// Created with the method [`rmatch_indices`].
        ///
        /// [`rmatch_indices`]: str::rmatch_indices
        struct RMatchIndices;
    stability:
        #[stable(feature = "str_match_indices", since = "1.5.0")]
    internal:
        MatchIndicesInternal yielding ((usize, &'a str));
    delegate double ended;
}

derive_pattern_clone! {
    clone MatchesInternal
    with |s| MatchesInternal(s.0.clone())
}

pub(super) struct MatchesInternal<'a, P: Pattern>(pub(super) P::Searcher<'a>);

impl<'a, P> fmt::Debug for MatchesInternal<'a, P>
where
    P: Pattern<Searcher<'a>: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MatchesInternal").field(&self.0).finish()
    }
}

impl<'a, P: Pattern> MatchesInternal<'a, P> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
        self.0.next_match().map(|(a, b)| unsafe {
            // Indices are known to be on utf8 boundaries
            self.0.haystack().get_unchecked(a..b)
        })
    }

    #[inline]
    fn next_back(&mut self) -> Option<&'a str>
    where
        P::Searcher<'a>: ReverseSearcher<'a>,
    {
        // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
        self.0.next_match_back().map(|(a, b)| unsafe {
            // Indices are known to be on utf8 boundaries
            self.0.haystack().get_unchecked(a..b)
        })
    }
}

generate_pattern_iterators! {
    forward:
        /// Created with the method [`matches`].
        ///
        /// [`matches`]: str::matches
        struct Matches;
    reverse:
        /// Created with the method [`rmatches`].
        ///
        /// [`rmatches`]: str::rmatches
        struct RMatches;
    stability:
        #[stable(feature = "str_matches", since = "1.2.0")]
    internal:
        MatchesInternal yielding (&'a str);
    delegate double ended;
}

/// An iterator over the lines of a string, as string slices.
///
/// This struct is created with the [`lines`] method on [`str`].
/// See its documentation for more.
///
/// [`lines`]: str::lines
#[stable(feature = "rust1", since = "1.0.0")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone, Debug)]
pub struct Lines<'a>(pub(super) Map<SplitInclusive<'a, char>, LinesMap>);

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> Iterator for Lines<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<&'a str> {
        self.next_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> DoubleEndedIterator for Lines<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.0.next_back()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for Lines<'_> {}

impl<'a> Lines<'a> {
    /// Returns the remaining lines of the split string.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_lines_remainder)]
    ///
    /// let mut lines = "a\nb\nc\nd".lines();
    /// assert_eq!(lines.remainder(), Some("a\nb\nc\nd"));
    ///
    /// lines.next();
    /// assert_eq!(lines.remainder(), Some("b\nc\nd"));
    ///
    /// lines.by_ref().for_each(drop);
    /// assert_eq!(lines.remainder(), None);
    /// ```
    #[inline]
    #[must_use]
    #[unstable(feature = "str_lines_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.iter.remainder()
    }
}

/// Created with the method [`lines_any`].
///
/// [`lines_any`]: str::lines_any
#[stable(feature = "rust1", since = "1.0.0")]
#[deprecated(since = "1.4.0", note = "use lines()/Lines instead now")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone, Debug)]
#[allow(deprecated)]
pub struct LinesAny<'a>(pub(super) Lines<'a>);

#[stable(feature = "rust1", since = "1.0.0")]
#[allow(deprecated)]
impl<'a> Iterator for LinesAny<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
#[allow(deprecated)]
impl<'a> DoubleEndedIterator for LinesAny<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.0.next_back()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
#[allow(deprecated)]
impl FusedIterator for LinesAny<'_> {}

/// An iterator over the non-whitespace substrings of a string,
/// separated by any amount of whitespace.
///
/// This struct is created by the [`split_whitespace`] method on [`str`].
/// See its documentation for more.
///
/// [`split_whitespace`]: str::split_whitespace
#[stable(feature = "split_whitespace", since = "1.1.0")]
#[derive(Clone, Debug)]
pub struct SplitWhitespace<'a> {
    pub(super) inner: Filter<Split<'a, IsWhitespace>, IsNotEmpty>,
}

/// An iterator over the non-ASCII-whitespace substrings of a string,
/// separated by any amount of ASCII whitespace.
///
/// This struct is created by the [`split_ascii_whitespace`] method on [`str`].
/// See its documentation for more.
///
/// [`split_ascii_whitespace`]: str::split_ascii_whitespace
#[stable(feature = "split_ascii_whitespace", since = "1.34.0")]
#[derive(Clone, Debug)]
pub struct SplitAsciiWhitespace<'a> {
    pub(super) inner:
        Map<Filter<SliceSplit<'a, u8, IsAsciiWhitespace>, BytesIsNotEmpty>, UnsafeBytesToStr>,
}

/// An iterator over the substrings of a string,
/// terminated by a substring matching to a predicate function.
/// Unlike `Split`, it contains the matched part as a terminator
/// of the subslice.
///
/// This struct is created by the [`split_inclusive`] method on [`str`].
/// See its documentation for more.
///
/// [`split_inclusive`]: str::split_inclusive
#[stable(feature = "split_inclusive", since = "1.51.0")]
pub struct SplitInclusive<'a, P: Pattern>(pub(super) SplitInternal<'a, P>);

#[stable(feature = "split_whitespace", since = "1.1.0")]
impl<'a> Iterator for SplitWhitespace<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.inner.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<&'a str> {
        self.next_back()
    }
}

#[stable(feature = "split_whitespace", since = "1.1.0")]
impl<'a> DoubleEndedIterator for SplitWhitespace<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.inner.next_back()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for SplitWhitespace<'_> {}

impl<'a> SplitWhitespace<'a> {
    /// Returns remainder of the split string
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_whitespace_remainder)]
    ///
    /// let mut split = "Mary had a little lamb".split_whitespace();
    /// assert_eq!(split.remainder(), Some("Mary had a little lamb"));
    ///
    /// split.next();
    /// assert_eq!(split.remainder(), Some("had a little lamb"));
    ///
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[must_use]
    #[unstable(feature = "str_split_whitespace_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.inner.iter.remainder()
    }
}

#[stable(feature = "split_ascii_whitespace", since = "1.34.0")]
impl<'a> Iterator for SplitAsciiWhitespace<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.inner.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<&'a str> {
        self.next_back()
    }
}

#[stable(feature = "split_ascii_whitespace", since = "1.34.0")]
impl<'a> DoubleEndedIterator for SplitAsciiWhitespace<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.inner.next_back()
    }
}

#[stable(feature = "split_ascii_whitespace", since = "1.34.0")]
impl FusedIterator for SplitAsciiWhitespace<'_> {}

impl<'a> SplitAsciiWhitespace<'a> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_whitespace_remainder)]
    ///
    /// let mut split = "Mary had a little lamb".split_ascii_whitespace();
    /// assert_eq!(split.remainder(), Some("Mary had a little lamb"));
    ///
    /// split.next();
    /// assert_eq!(split.remainder(), Some("had a little lamb"));
    ///
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[must_use]
    #[unstable(feature = "str_split_whitespace_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        if self.inner.iter.iter.finished {
            return None;
        }

        // SAFETY: Slice is created from str.
        Some(unsafe { crate::str::from_utf8_unchecked(self.inner.iter.iter.v) })
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, P: Pattern> Iterator for SplitInclusive<'a, P> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.0.next_inclusive()
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, P: Pattern<Searcher<'a>: fmt::Debug>> fmt::Debug for SplitInclusive<'a, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitInclusive").field("0", &self.0).finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, P: Pattern<Searcher<'a>: Clone>> Clone for SplitInclusive<'a, P> {
    fn clone(&self) -> Self {
        SplitInclusive(self.0.clone())
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, P: Pattern<Searcher<'a>: DoubleEndedSearcher<'a>>> DoubleEndedIterator
    for SplitInclusive<'a, P>
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.0.next_back_inclusive()
    }
}

#[stable(feature = "split_inclusive", since = "1.51.0")]
impl<'a, P: Pattern> FusedIterator for SplitInclusive<'a, P> {}

impl<'a, P: Pattern> SplitInclusive<'a, P> {
    /// Returns remainder of the split string.
    ///
    /// If the iterator is empty, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(str_split_inclusive_remainder)]
    /// let mut split = "Mary had a little lamb".split_inclusive(' ');
    /// assert_eq!(split.remainder(), Some("Mary had a little lamb"));
    /// split.next();
    /// assert_eq!(split.remainder(), Some("had a little lamb"));
    /// split.by_ref().for_each(drop);
    /// assert_eq!(split.remainder(), None);
    /// ```
    #[inline]
    #[unstable(feature = "str_split_inclusive_remainder", issue = "77998")]
    pub fn remainder(&self) -> Option<&'a str> {
        self.0.remainder()
    }
}

/// An iterator of [`u16`] over the string encoded as UTF-16.
///
/// This struct is created by the [`encode_utf16`] method on [`str`].
/// See its documentation for more.
///
/// [`encode_utf16`]: str::encode_utf16
#[derive(Clone)]
#[stable(feature = "encode_utf16", since = "1.8.0")]
pub struct EncodeUtf16<'a> {
    pub(super) chars: Chars<'a>,
    pub(super) extra: u16,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl fmt::Debug for EncodeUtf16<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EncodeUtf16").finish_non_exhaustive()
    }
}

#[stable(feature = "encode_utf16", since = "1.8.0")]
impl<'a> Iterator for EncodeUtf16<'a> {
    type Item = u16;

    #[inline]
    fn next(&mut self) -> Option<u16> {
        if self.extra != 0 {
            let tmp = self.extra;
            self.extra = 0;
            return Some(tmp);
        }

        let mut buf = [0; 2];
        self.chars.next().map(|ch| {
            let n = ch.encode_utf16(&mut buf).len();
            if n == 2 {
                self.extra = buf[1];
            }
            buf[0]
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.chars.iter.len();
        // The highest bytes:code units ratio occurs for 3-byte sequences,
        // since a 4-byte sequence results in 2 code units. The lower bound
        // is therefore determined by assuming the remaining bytes contain as
        // many 3-byte sequences as possible. The highest bytes:code units
        // ratio is for 1-byte sequences, so use this for the upper bound.
        if self.extra == 0 {
            (len.div_ceil(3), Some(len))
        } else {
            // We're in the middle of a surrogate pair, so add the remaining
            // surrogate to the bounds.
            (len.div_ceil(3) + 1, Some(len + 1))
        }
    }

    #[inline]
    fn count(self) -> usize {
        let extra = if self.extra == 0 { 0 } else { 1 };
        // Find UTF-8 non-continuation bytes and map:
        //
        // len_utf8() | len_utf16()
        // -----------|------------
        // 1          | 1
        // 2          | 1
        // 3          | 1
        // 4          | 2
        //
        // Because we never map to larger values the result is never larger than
        // `self.chars.as_str().len()` so the sum can never overflow
        self.chars.as_str().as_bytes().iter().fold(extra, |acc, &byte| {
            acc.wrapping_add({
                if byte < 0b1000_0000 {
                    // 0b0xxx_xxxx: ASCII-compatible U+0000 to U+007F
                    1
                } else if byte < 0b1100_0000 {
                    // 0b10xx_xxxx: UTF-8 continuation byte, skip
                    0
                } else if byte < 0b1111_0000 {
                    // 0b110x_xxxx: start of a 2-byte UTF-8 sequence for U+0080 to U+07FF
                    // 0b1110_xxxx: start of a 3-byte UTF-8 sequence for U+0800 to U+FFFF
                    1
                } else {
                    // 0b1111_0xxx: start of a 4-byte UTF-8 sequence for U+010000 to U+10FFFF
                    // This is exactly the range encoded as a surrogate pair in UTF-16
                    //
                    // 0b1111_1xxx: would fall here but never occurs in valid UTF-8
                    2
                }
            })
        })
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for EncodeUtf16<'_> {}

/// The return type of [`str::escape_debug`].
#[stable(feature = "str_escape", since = "1.34.0")]
#[derive(Clone, Debug)]
pub struct EscapeDebug<'a> {
    pub(super) inner: FlatMap<Chars<'a>, char_mod::EscapeDebug, CharEscapeDebug>,
}

/// The return type of [`str::escape_default`].
#[stable(feature = "str_escape", since = "1.34.0")]
#[derive(Clone, Debug)]
pub struct EscapeDefault<'a> {
    pub(super) inner: FlatMap<Chars<'a>, char_mod::EscapeDefault, CharEscapeDefault>,
}

impl<'a> EscapeDefault<'a> {
    /// Disassembles the iterator into its internal state.
    /// Used by alloc for an optimized to_string impl.
    #[unstable(feature = "std_internals", issue = "none")]
    pub fn into_parts(
        self,
    ) -> (Option<impl Iterator<Item = char>>, Option<Chars<'a>>, Option<impl Iterator<Item = char>>)
    {
        self.inner.into_parts()
    }
}

/// The return type of [`str::escape_unicode`].
#[stable(feature = "str_escape", since = "1.34.0")]
#[derive(Clone, Debug)]
pub struct EscapeUnicode<'a> {
    pub(super) inner: FlatMap<Chars<'a>, char_mod::EscapeUnicode, CharEscapeUnicode>,
}

macro_rules! escape_types_impls {
    ($( $Name: ident ),+) => {$(
        #[stable(feature = "str_escape", since = "1.34.0")]
        impl<'a> fmt::Display for $Name<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.clone().try_for_each(|c| f.write_char(c))
            }
        }

        #[stable(feature = "str_escape", since = "1.34.0")]
        impl<'a> Iterator for $Name<'a> {
            type Item = char;

            #[inline]
            fn next(&mut self) -> Option<char> { self.inner.next() }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }

            #[inline]
            fn try_fold<Acc, Fold, R>(&mut self, init: Acc, fold: Fold) -> R where
                Self: Sized, Fold: FnMut(Acc, Self::Item) -> R, R: Try<Output = Acc>
            {
                self.inner.try_fold(init, fold)
            }

            #[inline]
            fn fold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc
                where Fold: FnMut(Acc, Self::Item) -> Acc,
            {
                self.inner.fold(init, fold)
            }
        }

        #[stable(feature = "str_escape", since = "1.34.0")]
        impl<'a> FusedIterator for $Name<'a> {}
    )+}
}

escape_types_impls!(EscapeDebug, EscapeDefault, EscapeUnicode);

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Symbolic-length safety harnesses for Challenge 22.
    //!
    //! Slice and Pattern behavior and UTF-8 validation semantics are the explicit
    //! dependency assumptions allowed by doc/src/challenges/0022-str-iter.md.
    //! Local UTF-8 facts constrain the original input; cursor bounds and character
    //! boundaries after the actual target calls are checked, not assumed.
    //! Fixed-size fold models have independent refinement and pipeline harnesses.

    use super::super::validations::utf8_is_cont_byte;
    use super::*;

    // CI uses --object-bits 12 on a 64-bit target. This is the largest positive
    // one-past offset, not a small input bound chosen for loop unwinding.
    const MAX_ALLOCATION_BYTES: usize = (1usize << 51) - 1;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut u8;
        fn __CPROVER_havoc_object(p: *mut crate::ffi::c_void);
        fn __CPROVER_havoc_slice(p: *mut u8, len: usize);
    }

    fn symbolic_text() -> &'static str {
        symbolic_text_with_storage::<false>()
    }

    fn symbolic_text_with_storage<const ALLOCATE_EMPTY: bool>() -> &'static str {
        let len: usize = kani::any();
        kani::assume(len <= MAX_ALLOCATION_BYTES);
        kani::cover(len == MAX_ALLOCATION_BYTES, "maximum symbolic length admitted");
        let p = if len == 0 && !ALLOCATE_EMPTY {
            let address: NonZero<usize> = kani::any();
            crate::ptr::without_provenance_mut(address.get())
        } else {
            let storage_len = if ALLOCATE_EMPTY { len.max(1) } else { len };
            let p = unsafe { malloc(storage_len) };
            kani::assume(!p.is_null());
            kani::cover(true, "symbolic allocation succeeds");
            // Initialize the shadow-memory state, then give every byte an
            // independent arbitrary initialized value. Neither builtin unwinds
            // a Rust loop over the symbolic length.
            unsafe {
                p.write_bytes(0, storage_len);
                if ALLOCATE_EMPTY {
                    __CPROVER_havoc_slice(p, storage_len);
                } else {
                    __CPROVER_havoc_object(p.cast());
                }
            }
            p
        };
        let bytes = unsafe { slice::from_raw_parts(p, len) };
        // Challenge 22 assumes valid UTF-8. Every nonempty input in that
        // domain starts with a complete scalar followed by a boundary.
        kani::assume(bytes.is_empty() || utf8_sequence_width(bytes, 0) > 0);
        kani::cover(!bytes.is_empty(), "nonempty UTF-8 prefix admitted");
        // The model instantiates UTF-8 facts locally on the symbolic bytes.
        // This condition admits every valid string, and also malformed suffixes.
        unsafe { from_utf8_unchecked(bytes) }
    }

    // These witnesses follow the target call and its postcondition checks.
    fn cover_completed_text(s: &str) {
        kani::cover(s.is_empty(), "completed on empty input");
        kani::cover(s.len() > 4096, "completed beyond former input bounds");
    }

    fn modeled_utf8_width(byte: u8) -> usize {
        match byte {
            0..=0x7f => 1,
            0xc2..=0xdf => 2,
            0xe0..=0xef => 3,
            0xf0..=0xf4 => 4,
            _ => 0,
        }
    }

    fn second_ok(lead: u8, b: u8) -> bool {
        match lead {
            0xe0 => b >= 0xa0 && b <= 0xbf,
            0xed => b >= 0x80 && b <= 0x9f,
            0xf0 => b >= 0x90 && b <= 0xbf,
            0xf4 => b >= 0x80 && b <= 0x8f,
            _ => utf8_is_cont_byte(b),
        }
    }

    // Width of a complete UTF-8 scalar starting at a character boundary.
    fn utf8_sequence_width(bytes: &[u8], start: usize) -> usize {
        let lead = bytes[start];
        let width = modeled_utf8_width(lead);
        if width > 0
            && width <= bytes.len() - start
            && (width < 2 || second_ok(lead, bytes[start + 1]))
            && (width < 3 || utf8_is_cont_byte(bytes[start + 2]))
            && (width < 4 || utf8_is_cont_byte(bytes[start + 3]))
            && (start + width == bytes.len() || !utf8_is_cont_byte(bytes[start + width]))
        {
            width
        } else {
            0
        }
    }

    fn any_window(s: &str) -> (usize, usize) {
        let (a, b): (usize, usize) = (kani::any(), kani::any());
        kani::assume(a <= b && b <= s.len() && s.is_char_boundary(a) && s.is_char_boundary(b));
        kani::cover(true, "a boundary window exists");
        (a, b)
    }

    // Input-state construction: these are checked premises, not target outputs.
    // Avoid pulling panic-message string searching into every proof's call graph.
    fn window(s: &str, a: usize, b: usize) -> &str {
        assert!(a <= b && b <= s.len());
        assert!(s.is_char_boundary(a) && s.is_char_boundary(b));
        unsafe { s.get_unchecked(a..b) }
    }

    fn same_slice(a: &str, b: &str) -> bool {
        a.as_ptr() == b.as_ptr() && a.len() == b.len()
    }

    // Check bounds and provenance before using an offset in the postcondition.
    fn checked_offset(s: &str, part: &str) -> usize {
        let offset = (part.as_ptr() as usize).wrapping_sub(s.as_ptr() as usize);
        assert!(offset <= s.len() && part.len() <= s.len() - offset);
        assert!(part.as_ptr() == s.as_ptr().wrapping_add(offset));
        offset
    }

    fn check_range(s: &str, part: &str, a: usize, b: usize) {
        assert!(a <= b && b <= s.len());
        assert!(s.is_char_boundary(a) && s.is_char_boundary(b));
        assert!(part.as_ptr() == s.as_ptr().wrapping_add(a));
        assert!(part.len() == b - a);
    }

    // Loop invariants and dependency models for Chars::advance_by.

    pub(super) fn chunks_inv(
        iter: *const slice::Iter<'_, [u8; 32]>,
        skipped: usize,
        input: &[u8],
        requested: usize,
        remainder: usize,
    ) -> bool {
        let (ptr, end) = unsafe { slice::Iter::kani_loop_raw_parts(iter) };
        let base = input as *const [u8] as *const u8;
        let full = input.len() & !31;
        skipped <= full
            && skipped % 32 == 0
            && ptr as *const u8
                == unsafe { crate::intrinsics::arith_offset(base, skipped as isize) }
            && end as *const u8 == unsafe { crate::intrinsics::arith_offset(base, full as isize) }
            && remainder <= requested
            && requested - remainder <= skipped
    }

    // A loop may havoc the cursor. Keep it in the original allocation and
    // check that the scalar loop starts each iteration at a character boundary.
    pub(super) fn bytes_inv(
        iter: *const slice::Iter<'_, u8>,
        input: &[u8],
        skipped: usize,
        at_char_boundary: bool,
    ) -> bool {
        let (ptr, end) = unsafe { slice::Iter::kani_loop_raw_parts(iter) };
        let base = input as *const [u8] as *const u8;
        let len = input.len();
        let offset = crate::intrinsics::wrapping_sub(ptr as usize, base as usize);
        skipped <= offset
            && offset <= len
            && ptr == unsafe { crate::intrinsics::arith_offset(base, offset as isize) }
            && end == unsafe { crate::intrinsics::arith_offset(base, len as isize) }
            && (!at_char_boundary || offset == len || (input[offset] as i8) >= -64)
    }

    pub(super) fn assume_utf8_step(input: &[u8], offset: usize, lead: u8) {
        assert!(offset < input.len() && lead == input[offset]);
        if !utf8_is_cont_byte(lead) {
            // On valid UTF-8, any non-continuation byte begins a complete
            // scalar. This fact concerns the original bytes, even if the
            // algorithm supplies an unexpected offset.
            // The symbolic-length harness covers this path, which the empty-input harness skips.
            kani::assume(utf8_sequence_width(input, offset) > 0);
        }
    }

    // Check the branch-based model for every input to the real width table.
    #[kani::proof]
    fn check_utf8_width_model() {
        let byte: u8 = kani::any();
        assert!(modeled_utf8_width(byte) == super::super::validations::utf8_char_width(byte));
        kani::cover(byte == 0xf5, "width model checked an invalid lead byte");
    }

    // A scalar and the first byte after it suffice to check the local rule.
    #[kani::proof]
    fn check_utf8_sequence_model() {
        let storage: [u8; 5] = kani::any();
        let (width, len): (usize, usize) = (kani::any(), kani::any());
        kani::assume(1 <= width && width <= 4 && width <= len && len <= storage.len());
        kani::cover(true, "scalar window admitted");
        let bytes = &storage[..len];
        let scalar = char::from_u32(scalar_bits(bytes, 0, width)).is_some_and(|ch| {
            let mut encoded = [0; 4];
            let encoded_len = ch.encode_utf8(&mut encoded).len();
            encoded_len == width
                && encoded[0] == bytes[0]
                && (width < 2 || encoded[1] == bytes[1])
                && (width < 3 || encoded[2] == bytes[2])
                && (width < 4 || encoded[3] == bytes[3])
        });
        let boundary = width == len || bytes[width] & 0xc0 != 0x80;
        let modeled = utf8_sequence_width(bytes, 0);
        assert!(modeled <= 4 && modeled <= len);
        let admitted = modeled == width;
        assert!(admitted == (scalar && boundary));
        kani::cover(admitted && width == 1, "UTF-8 sequence: one byte");
        kani::cover(admitted && width == 2, "UTF-8 sequence: two bytes");
        kani::cover(admitted && width == 3, "UTF-8 sequence: three bytes");
        kani::cover(admitted && width == 4, "UTF-8 sequence: four bytes");
        kani::cover(scalar && !boundary, "UTF-8 sequence: stray continuation after scalar");
        kani::cover(len < modeled_utf8_width(bytes[0]), "UTF-8 sequence: truncated scalar");
    }

    pub(super) fn chunk_flags_inv(
        flags: *const [bool; 32],
        slot: usize,
        is_start: bool,
        filled: usize,
    ) -> bool {
        // Check the representations before reading any havoced value as bool.
        let bytes = unsafe { crate::intrinsics::read_via_copy(flags.cast::<[u8; 32]>()) };
        let [lo, hi]: [u128; 2] = unsafe { crate::intrinsics::transmute(bytes) };
        (lo | hi) & !0x0101_0101_0101_0101_0101_0101_0101_0101 == 0
            && bytes[slot] == u8::from(slot < filled && is_start)
    }

    pub(super) fn chunk_start_count(
        input: &[u8],
        chunk: &[u8; 32],
        skipped: usize,
        flags: [bool; 32],
        (slot, is_start): (usize, bool),
    ) -> usize {
        assert!(32 <= skipped && skipped <= input.len());
        assert!(chunk.as_ptr() == input.as_ptr().wrapping_add(skipped - 32));
        // The arbitrary slot relates all flags to the original chunk at loop exit.
        assert!(flags[slot] == is_start);
        // Sum the flags directly, independently of the iterator pipeline.
        macro_rules! count {
            ($($i:literal),+ $(,)?) => { 0u8 $(+ flags[$i] as u8)+ };
        }
        usize::from(count!(
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31,
        ))
    }

    fn count_flag_words(words: [u128; 2]) -> u32 {
        words[0].count_ones() + words[1].count_ones()
    }

    #[kani::proof]
    #[kani::stub(
        crate::array::iter::iter_inner::PolymorphicIter::fold,
        crate::array::iter::iter_inner::PolymorphicIter::kani_fold_at_most_32
    )]
    #[kani::stub(crate::str::validations::utf8_char_width, modeled_utf8_width)]
    fn harness_chars_advance_by() {
        // Every valid Chars state is a fresh iterator over its remaining valid
        // string. Both the length and requested character count are symbolic.
        // Use one allocation path for the entry view as the loops abstract the cursor.
        let text = symbolic_text_with_storage::<true>();
        let mut chars = text.chars();
        let n: usize = kani::any(); // No request/count bound.
        let result = chars.advance_by(n);
        let rest = chars.as_str();
        let skipped = checked_offset(text, rest);
        assert!(rest.len() == text.len() - skipped);
        assert!(text.is_char_boundary(skipped));
        match result {
            Ok(()) => assert!(n <= skipped),
            Err(missing) => {
                assert!(rest.is_empty());
                assert!(missing.get() <= n && n - missing.get() <= skipped);
            }
        }
        kani::cover(n == 0 && text.len() == MAX_ALLOCATION_BYTES, "maximum representable string");
        kani::cover(result.is_ok() && n == 33 && text.len() > 4096, "large input and chunk path");
        kani::cover(result.is_ok() && n == 1, "scalar path");
        kani::cover(
            n == usize::MAX && !text.is_empty() && result.is_err(),
            "maximum request on nonempty input",
        );
        kani::cover(
            text.len() == 4
                && n == 1
                && result.is_ok()
                && modeled_utf8_width(text.as_bytes()[0]) == 4,
            "four-byte input remains admitted after scalar-loop checks",
        );
    }

    // Empty slices can have arbitrary nonnull aligned addresses, not only the
    // dangling address used by symbolic_text's zero-length allocation case.
    #[kani::proof]
    #[kani::stub(
        crate::array::iter::iter_inner::PolymorphicIter::fold,
        crate::array::iter::iter_inner::PolymorphicIter::kani_fold_at_most_32
    )]
    #[kani::stub(crate::str::validations::utf8_char_width, modeled_utf8_width)]
    fn harness_chars_advance_by_empty() {
        let address: NonZero<usize> = kani::any();
        let ptr = crate::ptr::without_provenance(address.get());
        // SAFETY: the address is nonnull and aligned for u8, and the input is empty.
        let text = unsafe { from_utf8_unchecked(slice::from_raw_parts(ptr, 0)) };
        let mut chars = text.chars();
        let result = chars.advance_by(kani::any());
        let rest = chars.as_str();
        assert!(rest.is_empty() && rest.as_ptr() == ptr);
        kani::cover(result.is_ok(), "zero request on arbitrary empty pointer");
        kani::cover(result.is_err(), "positive request on arbitrary empty pointer");
    }

    // Chars decoding and view proofs.

    // Extract payload bits from a window of known width. Validity is checked separately.
    fn scalar_bits(bytes: &[u8], start: usize, width: usize) -> u32 {
        let lead = u32::from(bytes[start]);
        let tail = |i| u32::from(bytes[start + i] & 0x3f);
        match width {
            1 => lead,
            2 => ((lead & 0x1f) << 6) | tail(1),
            3 => ((lead & 0x0f) << 12) | (tail(1) << 6) | tail(2),
            4 => ((lead & 0x07) << 18) | (tail(1) << 12) | (tail(2) << 6) | tail(3),
            _ => unreachable!(),
        }
    }

    #[kani::proof]
    fn harness_chars_next() {
        let s = symbolic_text();
        let (a, b) = any_window(s);
        let bytes = s.as_bytes();
        let width = if a < b {
            // Input facts at the first sequence of this valid boundary window.
            // The decoder and its unsafe reads are executed without a stub.
            let width = utf8_sequence_width(bytes, a);
            kani::assume(width > 0 && width <= b - a);
            kani::cover(true, "complete leading scalar admitted");
            width
        } else {
            0
        };
        let mut chars = window(s, a, b).chars();
        if let Some(ch) = chars.next() {
            assert!(width > 0 && ch as u32 == scalar_bits(bytes, a, width));
            assert!(char::from_u32(ch as u32).is_some());
            assert!(ch.len_utf8() == width);
            check_range(s, chars.as_str(), a + width, b);
            kani::cover(ch.len_utf8() == 1, "one-byte scalar");
            kani::cover(ch.len_utf8() == 2, "two-byte scalar");
            kani::cover(ch.len_utf8() == 3, "three-byte scalar");
            kani::cover(ch.len_utf8() == 4, "four-byte scalar");
        } else {
            assert!(a == b);
        }
        cover_completed_text(s);
        kani::cover(a > 4096 && b - a > 4096, "completed on a large interior window");
    }

    #[kani::proof]
    fn harness_chars_next_back() {
        let s = symbolic_text();
        let (a, b) = any_window(s);
        let bytes = s.as_bytes();
        let width = if a < b {
            // A valid nonempty UTF-8 window has one final complete sequence.
            // This symbolic width is an input witness, not a decoder result.
            let width: usize = kani::any();
            kani::assume(1 <= width && width <= 4 && width <= b - a);
            kani::cover(true, "trailing scalar width admitted");
            let lead = b - width;
            kani::assume(utf8_sequence_width(bytes, lead) == width);
            kani::cover(true, "complete trailing scalar admitted");
            width
        } else {
            0
        };
        let mut chars = window(s, a, b).chars();
        if let Some(ch) = chars.next_back() {
            assert!(width > 0 && ch as u32 == scalar_bits(bytes, b - width, width));
            assert!(char::from_u32(ch as u32).is_some());
            assert!(ch.len_utf8() == width);
            check_range(s, chars.as_str(), a, b - width);
            kani::cover(ch.len_utf8() == 1, "one-byte scalar");
            kani::cover(ch.len_utf8() == 2, "two-byte scalar");
            kani::cover(ch.len_utf8() == 3, "three-byte scalar");
            kani::cover(ch.len_utf8() == 4, "four-byte scalar");
        } else {
            assert!(a == b);
        }
        cover_completed_text(s);
        kani::cover(a > 4096 && b - a > 4096, "completed on a large interior window");
    }

    #[kani::proof]
    fn harness_chars_as_str() {
        let s = symbolic_text();
        let (a, b) = any_window(s);
        let chars = window(s, a, b).chars();
        check_range(s, chars.as_str(), a, b);
        cover_completed_text(s);
        kani::cover(a > 4096 && b - a > 4096, "completed on a large interior window");
    }

    // Under the challenge's Pattern assumption, directional consumers observe
    // only the haystack and ordered match ranges on UTF-8 boundaries. The model
    // allows any such range, including empty matches and skipped rejects.
    // Forward-only and reverse-only searchers project onto a suffix and a
    // prefix respectively. No double-ended matching semantics are required.
    struct ModelPattern;

    type SearchMatch = Option<(usize, usize)>;

    struct ModelSearcher<'a> {
        haystack: &'a str,
        front: usize,
        back: usize,
        // Consumer harnesses choose the responses before calling the target.
        match_plan: Option<&'a [SearchMatch]>,
    }

    // SAFETY: `into_searcher` stores the provided `haystack` slice, and
    // `ModelSearcher::haystack` returns that same slice.
    unsafe impl Pattern for ModelPattern {
        type Searcher<'a> = ModelSearcher<'a>;

        fn into_searcher(self, haystack: &str) -> ModelSearcher<'_> {
            ModelSearcher { haystack, front: 0, back: haystack.len(), match_plan: None }
        }
    }

    fn type_invariant_searcher(s: &ModelSearcher<'_>) -> bool {
        s.front <= s.back
            && s.back <= s.haystack.len()
            && s.haystack.is_char_boundary(s.front)
            && s.haystack.is_char_boundary(s.back)
    }

    fn any_match_range(s: &str, front: usize, back: usize) -> (usize, usize) {
        let a: usize = kani::any();
        let b: usize = kani::any();
        // Challenge 22 assumption 2 gives this guarantee for search results.
        kani::assume(
            front <= a && a <= b && b <= back && s.is_char_boundary(a) && s.is_char_boundary(b),
        );
        kani::cover(true, "valid search interval admitted");
        (a, b)
    }

    fn any_search_match(s: &str, front: usize, back: usize) -> SearchMatch {
        kani::any::<bool>().then(|| any_match_range(s, front, back))
    }

    impl ModelSearcher<'_> {
        fn choose_match(&mut self) -> SearchMatch {
            let Some(plan) = self.match_plan else {
                return any_search_match(self.haystack, self.front, self.back);
            };
            let Some((&matched, rest)) = plan.split_first() else {
                panic!("unexpected search call");
            };
            self.match_plan = Some(rest);
            if let Some((a, b)) = matched {
                assert!(self.front <= a && a <= b && b <= self.back);
                assert!(self.haystack.is_char_boundary(a) && self.haystack.is_char_boundary(b));
            }
            matched
        }
    }

    // SAFETY: next emits adjacent, in-bounds UTF-8 ranges. The next_match
    // override summarizes zero or more skipped Rejects and one Match (or
    // exhaustion). Matching contents are intentionally over-approximated.
    unsafe impl<'a> Searcher<'a> for ModelSearcher<'a> {
        fn haystack(&self) -> &'a str {
            self.haystack
        }

        fn next(&mut self) -> super::super::pattern::SearchStep {
            use super::super::pattern::SearchStep;
            assert!(type_invariant_searcher(self));
            if kani::any() {
                let old = self.front;
                self.front = self.back;
                if old == self.back { SearchStep::Done } else { SearchStep::Reject(old, self.back) }
            } else {
                let (_, b) = any_match_range(self.haystack, self.front, self.back);
                let a = self.front;
                self.front = b;
                if kani::any() { SearchStep::Match(a, b) } else { SearchStep::Reject(a, b) }
            }
        }

        fn next_match(&mut self) -> SearchMatch {
            assert!(type_invariant_searcher(self));
            let matched = self.choose_match();
            self.front = matched.map_or(self.back, |(_, end)| end);
            matched
        }
    }

    // SAFETY: same range protocol, consumed from the opposite end. No claim
    // is made that independent nondeterministic choices define identical
    // forward/reverse streams, hence there is no DoubleEndedSearcher impl.
    unsafe impl<'a> ReverseSearcher<'a> for ModelSearcher<'a> {
        fn next_back(&mut self) -> super::super::pattern::SearchStep {
            use super::super::pattern::SearchStep;
            assert!(type_invariant_searcher(self));
            if kani::any() {
                let old = self.back;
                self.back = self.front;
                if old == self.front {
                    SearchStep::Done
                } else {
                    SearchStep::Reject(self.front, old)
                }
            } else {
                let (a, _) = any_match_range(self.haystack, self.front, self.back);
                let b = self.back;
                self.back = a;
                if kani::any() { SearchStep::Match(a, b) } else { SearchStep::Reject(a, b) }
            }
        }

        fn next_match_back(&mut self) -> SearchMatch {
            assert!(type_invariant_searcher(self));
            let matched = self.choose_match();
            self.back = matched.map_or(self.front, |(start, _)| start);
            matched
        }
    }

    fn type_invariant_split(iter: &SplitInternal<'_, ModelPattern>) -> bool {
        type_invariant_searcher(&iter.matcher)
            && iter.start <= iter.matcher.front
            && iter.matcher.back <= iter.end
            && iter.end <= iter.matcher.haystack.len()
            && iter.matcher.haystack.is_char_boundary(iter.start)
            && iter.matcher.haystack.is_char_boundary(iter.end)
    }

    fn any_split(s: &str) -> SplitInternal<'_, ModelPattern> {
        let (start, end) = any_window(s);
        let (front, back) = any_match_range(s, start, end);
        SplitInternal {
            start,
            end,
            matcher: ModelSearcher { haystack: s, front, back, match_plan: None },
            allow_trailing_empty: kani::any(),
            finished: kani::any(),
        }
    }

    fn check_searcher(s: &str, searcher: &ModelSearcher<'_>) {
        assert!(type_invariant_searcher(searcher));
        assert!(same_slice(searcher.haystack(), s));
    }

    // Closure of the safety invariant supports arbitrarily long iterator histories.
    fn check_split(
        s: &str,
        iter: &SplitInternal<'_, ModelPattern>,
        result: Option<&str>,
        expected: SearchMatch,
    ) {
        assert!(type_invariant_split(iter));
        assert!(same_slice(iter.matcher.haystack(), s));
        assert!(iter.matcher.match_plan.is_some_and(<[_]>::is_empty));
        assert!(result.is_some() == expected.is_some());
        if let (Some(part), Some((start, end))) = (result, expected) {
            check_range(s, part, start, end);
        }
        kani::cover(result.is_none(), "split: no remaining piece");
        kani::cover(result.is_some_and(str::is_empty), "split: empty piece");
        kani::cover(result.is_some_and(|part| part.len() > 4096), "split: large piece");
        cover_completed_text(s);
    }

    fn check_search_step(
        s: &str,
        searcher: &ModelSearcher<'_>,
        (front, back): (usize, usize),
        reverse: bool,
        matched: SearchMatch,
    ) {
        check_searcher(s, searcher);
        if let Some((a, b)) = matched {
            assert!(front <= a && a <= b && b <= back);
            assert!(s.is_char_boundary(a) && s.is_char_boundary(b));
        }
        let expected = if reverse {
            (front, matched.map_or(front, |(a, _)| a))
        } else {
            (matched.map_or(back, |(_, b)| b), back)
        };
        assert!((searcher.front, searcher.back) == expected);
    }

    #[kani::proof]
    fn harness_searcher_protocol() {
        use super::super::pattern::SearchStep;

        let s = symbolic_text();
        let (front, back) = any_window(s);
        let mut searcher = ModelSearcher { haystack: s, front, back, match_plan: None };
        let reverse: bool = kani::any();
        if kani::any() {
            let step = if reverse { searcher.next_back() } else { searcher.next() };
            let range = match step {
                SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                    assert!(if reverse { b == back } else { a == front });
                    Some((a, b))
                }
                SearchStep::Done => {
                    assert!(front == back);
                    None
                }
            };
            check_search_step(s, &searcher, (front, back), reverse, range);
            kani::cover(matches!(step, SearchStep::Match(..)), "protocol: matching step");
            kani::cover(matches!(step, SearchStep::Reject(..)), "protocol: rejecting step");
            kani::cover(matches!(step, SearchStep::Done), "protocol: exhausted step");
            kani::cover(range.is_some_and(|(a, b)| a == b), "protocol: zero-width step");
        } else {
            let result = if reverse { searcher.next_match_back() } else { searcher.next_match() };
            check_search_step(s, &searcher, (front, back), reverse, result);
            if let Some((a, b)) = result {
                kani::cover(a == b, "protocol: zero-width match");
                kani::cover(b - a > 4, "protocol: multiple-character match");
            }
        }
        cover_completed_text(s);
    }

    fn check_initial_searcher(s: &str, searcher: &ModelSearcher<'_>) {
        check_searcher(s, searcher);
        assert!(searcher.front == 0 && searcher.back == s.len());
    }

    fn check_initial_split(s: &str, split: &SplitInternal<'_, ModelPattern>, trailing: bool) {
        check_initial_searcher(s, &split.matcher);
        assert!(split.start == 0 && split.end == s.len());
        assert!(split.allow_trailing_empty == trailing && !split.finished);
        assert!(type_invariant_split(split));
    }

    #[kani::proof]
    fn harness_iterator_constructors() {
        let s = symbolic_text();
        let n = kani::any();
        let splitn = s.splitn(n, ModelPattern).0;
        let rsplitn = s.rsplitn(n, ModelPattern).0;
        check_initial_split(s, &s.split(ModelPattern).0, true);
        check_initial_split(s, &s.rsplit(ModelPattern).0, true);
        check_initial_split(s, &s.split_inclusive(ModelPattern).0, false);
        check_initial_split(s, &s.split_terminator(ModelPattern).0, false);
        check_initial_split(s, &s.rsplit_terminator(ModelPattern).0, false);
        check_initial_split(s, &splitn.iter, true);
        check_initial_split(s, &rsplitn.iter, true);
        assert!(splitn.count == n && rsplitn.count == n);
        check_initial_searcher(s, &s.matches(ModelPattern).0.0);
        check_initial_searcher(s, &s.rmatches(ModelPattern).0.0);
        check_initial_searcher(s, &s.match_indices(ModelPattern).0.0);
        check_initial_searcher(s, &s.rmatch_indices(ModelPattern).0.0);
        assert!(s.split_ascii_whitespace().remainder().is_some_and(|part| same_slice(s, part)));
        assert!(same_slice(s, s.chars().as_str()));
        cover_completed_text(s);
    }

    #[kani::proof]
    fn harness_split_get_end() {
        let s = symbolic_text();
        let mut iter = any_split(s);
        iter.matcher.match_plan = Some(&[]);
        let (start, end, trailing) = (iter.start, iter.end, iter.allow_trailing_empty);
        let search_window = (iter.matcher.front, iter.matcher.back);
        let expected = (!iter.finished && (trailing || start < end)).then_some((start, end));
        let result = iter.get_end();
        assert!(iter.finished);
        assert!((iter.start, iter.end, iter.allow_trailing_empty) == (start, end, trailing));
        assert!((iter.matcher.front, iter.matcher.back) == search_window);
        check_split(s, &iter, result, expected);
    }

    fn check_split_step<const BACK: bool, const INCLUSIVE: bool>() -> Option<SearchMatch> {
        let s = symbolic_text();
        let mut iter = any_split(s);
        let (start, end) = (iter.start, iter.end);
        let (finished, trailing) = (iter.finished, iter.allow_trailing_empty);
        let (front, back) = (iter.matcher.front, iter.matcher.back);
        let first = if finished { None } else { any_search_match(s, front, back) };
        let split_at = |(a, b)| if INCLUSIVE { b } else { a };

        // The reverse iterator suppresses one initial empty piece. A match
        // that ends at the window end leaves the searcher bounded by its start.
        let discarded = if BACK && !trailing { first.filter(|&(_, b)| b == end) } else { None };
        let second = discarded.and_then(|(a, _)| any_search_match(s, front, a));
        let steps = [first, second];
        let count = usize::from(!finished) + usize::from(discarded.is_some());
        iter.matcher.match_plan = Some(&steps[..count]);

        let piece_end = discarded.map_or(end, split_at);
        let matched = if discarded.is_some() { second } else { first };
        let (expected, new_start, new_end) = match (finished, BACK, matched) {
            (true, _, _) => (None, start, end),
            (_, false, Some((a, b))) => (Some((start, split_at((a, b)))), b, end),
            (_, true, Some((a, b))) => (Some((b, piece_end)), start, split_at((a, b))),
            (_, _, None) => {
                let keep_empty = trailing || discarded.is_some();
                ((keep_empty || start < piece_end).then_some((start, piece_end)), start, piece_end)
            }
        };
        let search_window = if finished {
            (front, back)
        } else if BACK {
            (front, matched.map_or(front, |(a, _)| a))
        } else {
            (matched.map_or(back, |(_, b)| b), back)
        };

        let result = match (BACK, INCLUSIVE) {
            (false, false) => iter.next(),
            (false, true) => iter.next_inclusive(),
            (true, false) => iter.next_back(),
            (true, true) => iter.next_back_inclusive(),
        };
        assert!((iter.start, iter.end) == (new_start, new_end));
        assert!((iter.matcher.front, iter.matcher.back) == search_window);
        assert!(iter.finished == (finished || matched.is_none()));
        assert!(iter.allow_trailing_empty == (trailing || (BACK && !finished)));
        check_split(s, &iter, result, expected);
        discarded.is_some().then_some(second)
    }

    #[kani::proof]
    fn harness_split_next() {
        let _ = check_split_step::<false, false>();
    }

    #[kani::proof]
    fn harness_split_next_inclusive() {
        let _ = check_split_step::<false, true>();
    }

    fn check_split_back_step<const INCLUSIVE: bool>() {
        let after_empty = check_split_step::<true, INCLUSIVE>();
        kani::cover(matches!(after_empty, Some(Some(_))), "matched after trailing empty");
        kani::cover(matches!(after_empty, Some(None)), "exhausted after trailing empty");
    }

    #[kani::proof]
    fn harness_split_next_back() {
        check_split_back_step::<false>();
    }

    #[kani::proof]
    fn harness_split_next_back_inclusive() {
        check_split_back_step::<true>();
    }

    #[kani::proof]
    fn harness_split_remainder() {
        let s = symbolic_text();
        let mut iter = any_split(s);
        iter.matcher.match_plan = Some(&[]);
        let expected = (!iter.finished).then_some((iter.start, iter.end));
        let result = iter.remainder();
        check_split(s, &iter, result, expected);
    }

    fn check_match_step<const BACK: bool, const INDEXED: bool>() {
        let s = symbolic_text();
        let (front, back) = any_window(s);
        let expected = any_search_match(s, front, back);
        let plan = [expected];
        let searcher = ModelSearcher { haystack: s, front, back, match_plan: Some(&plan) };
        let (part, searcher) = if INDEXED {
            let mut iter = MatchIndicesInternal::<ModelPattern>(searcher);
            let result = if BACK { iter.next_back() } else { iter.next() };
            assert!(result.map(|(index, _)| index) == expected.map(|(start, _)| start));
            (result.map(|(_, part)| part), iter.0)
        } else {
            let mut iter = MatchesInternal::<ModelPattern>(searcher);
            let result = if BACK { iter.next_back() } else { iter.next() };
            (result, iter.0)
        };
        check_search_step(s, &searcher, (front, back), BACK, expected);
        assert!(searcher.match_plan.is_some_and(<[_]>::is_empty));
        assert!(part.is_some() == expected.is_some());
        if let (Some(part), Some((a, b))) = (part, expected) {
            check_range(s, part, a, b);
        }
        kani::cover(part.is_none(), "matches: exhausted");
        kani::cover(part.is_some_and(str::is_empty), "matches: empty match");
        kani::cover(part.is_some_and(|part| part.len() > 4096), "matches: large match");
        cover_completed_text(s);
    }

    #[kani::proof]
    fn harness_match_indices_next() {
        check_match_step::<false, true>();
    }

    #[kani::proof]
    fn harness_match_indices_next_back() {
        check_match_step::<true, true>();
    }

    #[kani::proof]
    fn harness_matches_next() {
        check_match_step::<false, false>();
    }

    #[kani::proof]
    fn harness_matches_next_back() {
        check_match_step::<true, false>();
    }

    #[kani::proof]
    fn harness_split_ascii_whitespace_remainder() {
        let s = symbolic_text();
        let mut iter = s.split_ascii_whitespace();
        assert!(iter.remainder().is_some_and(|part| same_slice(part, s)));

        // Every reachable inner slice is a UTF-8-boundary window. Cutting
        // at ASCII whitespace cannot cut through a multibyte scalar.
        let (start, end) = any_window(s);
        iter.inner.iter.iter.v = window(s, start, end).as_bytes();
        iter.inner.iter.iter.finished = kani::any();
        let finished = iter.inner.iter.iter.finished;
        match iter.remainder() {
            Some(part) => {
                assert!(!finished);
                check_range(s, part, start, end);
                kani::cover(part.len() > 4096, "returned a large remainder after range checks");
                kani::cover(part.is_empty(), "ASCII whitespace remainder: empty window");
                kani::cover(!part.is_empty(), "ASCII whitespace remainder: nonempty window");
            }
            None => {
                assert!(finished);
                kani::cover(true, "ASCII whitespace remainder: finished");
            }
        }
        cover_completed_text(s);
    }

    // Main already contains #[requires(idx < self.0.len())]. The contract
    // is discharged against the original body, with Kani generating the
    // precondition rather than the harness assuming the target's safety.
    #[kani::proof_for_contract(Bytes::__iterator_get_unchecked)]
    fn harness_bytes_iterator_get_unchecked() {
        let s = symbolic_text();
        // Bytes consumes individual bytes, so a reachable cursor may lie
        // inside a scalar. No character-boundary premise belongs here.
        let (start, end): (usize, usize) = (kani::any(), kani::any());
        kani::assume(start <= end && end <= s.len());
        kani::cover(start < end, "nonempty byte window admitted");
        let window = unsafe { s.as_bytes().get_unchecked(start..end) };
        let mut iter = Bytes(window.iter().copied());
        let index: usize = kani::any();
        let item = unsafe { iter.__iterator_get_unchecked(index) };
        assert!(item == window[index]);
        kani::cover(index > 0, "bytes::get_unchecked: index past first byte");
        kani::cover(!s.is_char_boundary(start), "byte cursor inside a scalar");
        // idx < len excludes empty byte windows; cover the admissible domain.
        kani::cover(
            end - start > 4096 && index > 4096,
            "completed contract on a large byte window and index",
        );
    }

    mod auxiliary {
        //! Fixed-size fold checks and bounded real-searcher regressions.

        use super::super::super::pattern::verify::assert_char_searcher_step;
        use super::*;

        fn check_sum_flags() {
            let flags: [bool; 32] = kani::any();
            let words = unsafe { crate::intrinsics::transmute(flags) };
            let result = flags.into_iter().map(|flag| flag as u8).sum::<u8>();
            assert!(result as u32 == count_flag_words(words));
            kani::cover(result == 32, "all flags consumed after sum assertion");
        }

        #[kani::proof]
        fn check_sum_32_real() {
            check_sum_flags();
        }

        #[kani::proof]
        #[kani::stub(
            crate::array::iter::iter_inner::PolymorphicIter::fold,
            crate::array::iter::iter_inner::PolymorphicIter::kani_fold_at_most_32
        )]
        fn check_sum_32_model() {
            check_sum_flags();
        }

        const MAX_SEARCH_BYTES: usize = 16;
        const UTF8_PAD: usize = 4;

        fn verifier_utf8_valid<const N: usize>(buf: &[u8; N], len: usize) -> bool {
            let p = buf.as_ptr();
            let sequences = crate::forall!(|i in (0, N - UTF8_PAD)| unsafe {
                let i: usize = i;
                let x0 = *p.wrapping_add(i);
                let x1 = *p.wrapping_add(i.wrapping_add(1));
                let x2 = *p.wrapping_add(i.wrapping_add(2));
                let x3 = *p.wrapping_add(i.wrapping_add(3));
                let continuation0 = (x0 as i8) < -64;
                let continuation1 = (x1 as i8) < -64;
                let continuation2 = (x2 as i8) < -64;
                let continuation3 = (x3 as i8) < -64;
                let width = (x0 < 0x80) as usize
                    + (((x0 >= 0xC2) & (x0 < 0xE0)) as usize) * 2
                    + (((x0 >= 0xE0) & (x0 < 0xF0)) as usize) * 3
                    + (((x0 >= 0xF0) & (x0 < 0xF5)) as usize) * 4;
                let next_is_continuation =
                    (*p.wrapping_add(i.wrapping_add(width)) as i8) < -64;
                let second_byte_ok = ((x0 != 0xE0) | (x1 >= 0xA0))
                    & ((x0 != 0xED) | (x1 < 0xA0))
                    & ((x0 != 0xF0) | (x1 >= 0x90))
                    & ((x0 != 0xF4) | (x1 < 0x90));
                (i >= len)
                    | continuation0
                    | ((width > 0)
                        & (i.wrapping_add(width) <= len)
                        & ((width < 2) | (continuation1 & second_byte_ok))
                        & ((width < 3) | continuation2)
                        & ((width < 4) | continuation3)
                        & ((i.wrapping_add(width) == len) | !next_is_continuation))
            });
            let covered = crate::forall!(|i in (0, N - UTF8_PAD)| unsafe {
                let i: usize = i;
                (i >= len)
                    | ((*p.wrapping_add(i) as i8) >= -64)
                    | ((i >= 1) & ((*p.wrapping_add(i.saturating_sub(1)) as i8) >= -64))
                    | ((i >= 2) & ((*p.wrapping_add(i.saturating_sub(2)) as i8) >= -64))
                    | ((i >= 3) & ((*p.wrapping_add(i.saturating_sub(3)) as i8) >= -64))
            });
            sequences && covered
        }

        fn verifier_nondet_utf8<const N: usize>(buf: &[u8; N]) -> &str {
            let len: usize = kani::any();
            kani::assume(len <= N - UTF8_PAD);
            kani::cover(len == N - UTF8_PAD, "full auxiliary input length admitted");
            kani::assume(verifier_utf8_valid(buf, len));
            kani::cover(len > 0, "nonempty valid auxiliary string admitted");
            // SAFETY: verifier_utf8_valid characterizes valid UTF-8 exactly.
            unsafe { from_utf8_unchecked(&buf[..len]) }
        }

        fn verifier_last_byte(needle: u8, bytes: &[u8]) -> Option<usize> {
            verifier_find_byte(needle, bytes, true)
        }

        fn verifier_first_byte(needle: u8, bytes: &[u8]) -> Option<usize> {
            verifier_find_byte(needle, bytes, false)
        }

        fn verifier_find_byte(needle: u8, bytes: &[u8], reverse: bool) -> Option<usize> {
            assert!(bytes.len() <= MAX_SEARCH_BYTES);
            for offset in 0..MAX_SEARCH_BYTES {
                let index = if reverse { MAX_SEARCH_BYTES - 1 - offset } else { offset };
                if let Some(&byte) = bytes.get(index)
                    && byte == needle
                {
                    return Some(index);
                }
            }
            None
        }

        fn verifier_slice_eq<T: PartialEq<U>, U>(left: &[T], right: &[U]) -> bool {
            if left.len() != right.len() {
                return false;
            }
            assert!(left.len() <= MAX_SEARCH_BYTES);
            for index in 0..MAX_SEARCH_BYTES {
                if index < left.len() && left[index] != right[index] {
                    return false;
                }
            }
            true
        }

        fn fixed_char_search_step_budget() -> Option<usize> {
            // Each continued step consumes a byte. Allow one final exhausted probe.
            Some(MAX_SEARCH_BYTES + 1)
        }

        fn check_byte_slice_dependencies_at<const LEN: usize>() {
            let left: [u8; LEN] = kani::any();
            let right: [u8; LEN] = kani::any();
            let needle: u8 = kani::any();
            let actual_first = crate::slice::memchr::memchr(needle, &left);
            assert_eq!(verifier_first_byte(needle, &left), actual_first);
            assert_eq!(verifier_slice_eq(&left, &right), left[..] == right[..]);
        }

        #[kani::proof]
        fn check_byte_slice_dependencies() {
            // Exercise the real dependency bodies with every concrete length in the domain.
            const { assert!(MAX_SEARCH_BYTES == 16) }
            macro_rules! check_lengths {
                ($($len:literal),+ $(,)?) => {
                    $(check_byte_slice_dependencies_at::<$len>();)+
                };
            }
            check_lengths!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
            kani::cover(true, "checked every auxiliary byte slice length");
        }

        #[kani::proof]
        fn harness_reverse_byte_model() {
            let bytes: [u8; MAX_SEARCH_BYTES] = kani::any();
            let len: usize = kani::any();
            kani::assume(len <= bytes.len());
            kani::cover(len == bytes.len(), "full byte model input length admitted");
            let needle: u8 = kani::any();
            let result = verifier_last_byte(needle, &bytes[..len]);
            if let Some(index) = result {
                assert!(index < len);
                assert_eq!(bytes[index], needle);
            }
            let index: usize = kani::any();
            if index < len && result.is_none_or(|last| last < index) {
                assert_ne!(bytes[index], needle);
            }
            kani::cover(result.is_some(), "byte model: matching byte");
            kani::cover(result.is_none(), "byte model: no match");
            kani::cover(len > 0 && result == Some(len - 1), "byte model: final byte matches");
            kani::cover(len == 0 && result.is_none(), "byte model: empty prefix");
        }

        fn assert_char_searcher_direction(reverse: bool) {
            let buf: [u8; MAX_SEARCH_BYTES + UTF8_PAD] = kani::any();
            let s = verifier_nondet_utf8(&buf);
            let (front, back) = any_window(s);
            let needle: char = kani::any();
            let result = assert_char_searcher_step(s, needle, front, back, reverse);
            kani::cover(result.is_some(), "real char search: matching scalar");
            kani::cover(result.is_none(), "real char search: exhausted window");
            kani::cover(
                result.is_some() && needle.len_utf8() == 4,
                "real char search: four-byte match",
            );
            kani::cover(front == back && result.is_none(), "real char search: empty window");
        }

        #[kani::proof]
        #[kani::stub(
            crate::str::pattern::verify::char_search_step_budget,
            fixed_char_search_step_budget
        )]
        #[kani::stub(<[u8] as crate::cmp::PartialEq<[u8]>>::eq, verifier_slice_eq)]
        #[kani::stub(crate::slice::memchr::memchr, verifier_first_byte)]
        fn harness_char_searcher_forward_refinement() {
            assert_char_searcher_direction(false);
        }

        #[kani::proof]
        #[kani::stub(
            crate::str::pattern::verify::char_search_step_budget,
            fixed_char_search_step_budget
        )]
        #[kani::stub(<[u8] as crate::cmp::PartialEq<[u8]>>::eq, verifier_slice_eq)]
        #[kani::stub(crate::slice::memchr::memrchr, verifier_last_byte)]
        fn harness_char_searcher_reverse_refinement() {
            assert_char_searcher_direction(true);
        }
    }
}
