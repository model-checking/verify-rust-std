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

        if remainder >= CHUNK_SIZE {
            let mut chunks = self.iter.as_slice().as_chunks::<CHUNK_SIZE>().0.iter();
            let mut bytes_skipped: usize = 0;

            while remainder > CHUNK_SIZE
                && let Some(chunk) = chunks.next()
            {
                bytes_skipped += CHUNK_SIZE;

                let mut start_bytes = [false; CHUNK_SIZE];

                for i in 0..CHUNK_SIZE {
                    start_bytes[i] = !super::validations::utf8_is_cont_byte(chunk[i]);
                }

                remainder -= start_bytes.into_iter().map(|i| i as u8).sum::<u8>() as usize;
            }

            // SAFETY: The amount of bytes exists since we just iterated over them,
            // so advance_by will succeed.
            unsafe { self.iter.advance_by(bytes_skipped).unwrap_unchecked() };

            // skip trailing continuation bytes
            while self.iter.len() > 0 {
                let b = self.iter.as_slice()[0];
                if !super::validations::utf8_is_cont_byte(b) {
                    break;
                }
                // SAFETY: We just peeked at the byte, therefore it exists
                unsafe { self.iter.advance_by(1).unwrap_unchecked() };
            }
        }

        while (remainder > 0) && (self.iter.len() > 0) {
            remainder -= 1;
            let b = self.iter.as_slice()[0];
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
            // SAFETY: `Searcher` guarantees that `a` and `b` lie on unicode boundaries.
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
            // SAFETY: `Searcher` guarantees that `b` lies on unicode boundary,
            // and self.start is either the start of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
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
            // SAFETY: `Searcher` guarantees that `a` and `b` lie on unicode boundaries.
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
            // SAFETY: `Searcher` guarantees that `b` lies on unicode boundary,
            // and self.end is either the end of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
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
/// terminated by a substring matching to a predicate function
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
    use super::super::pattern::verify::{
        verifier_assert_real_char_searcher, verifier_char_searcher_invariant,
        verifier_stub_char_next_match, verifier_stub_char_next_match_back,
        verifier_stub_char_slice_next_match, verifier_stub_char_slice_next_match_back,
        verifier_stub_str_nonempty_next_match, verifier_stub_str_nonempty_next_match_back,
    };
    use super::super::pattern::{CharSearcher, CharSliceSearcher, StrSearcher};
    use super::super::validations::{utf8_char_width, utf8_is_cont_byte};
    use super::*;

    // The backing array bounds CBMC's object model, not the number of
    // iteration steps. Claims of arbitrary mathematical length require an
    // additional argument beyond this finite allocation model.
    const MAX_BYTES: usize = 256;
    const UTF8_PAD: usize = 4;
    const BUFFER_BYTES: usize = MAX_BYTES + UTF8_PAD;

    // The local UTF-8 predicate and original bounded advance checks follow
    // the input-model approach in PR #557; the interval protocol below
    // replaces its char-specific iterator proof architecture.
    // A loop-free UTF-8 validity model. For every leading byte, validate
    // the sequence width, continuation bytes, and exceptional second-byte
    // rules (E0/ED/F0/F4). Every continuation byte must be within three
    // positions after a leading byte. Combined, these are equivalent to
    // validity of buf[..len], provided len <= N - UTF8_PAD.
    // Do not use from_utf8 as a symbolic-input filter under loop-contract
    // instrumentation: it can abstract away the validation algorithm.
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
        // INPUT DOMAIN: allocated prefix or index extent.
        kani::assume(len <= N - UTF8_PAD);
        kani::cover(true, "C22-A01: verifier_nondet_utf8 assumption admitted");
        // CHALLENGE 22 assumption 4: valid UTF-8 input.
        kani::assume(verifier_utf8_valid(buf, len));
        kani::cover(true, "C22-A02: verifier_nondet_utf8 assumption admitted");
        // SAFETY: verifier_utf8_valid characterizes valid UTF-8 exactly.
        unsafe { from_utf8_unchecked(&buf[..len]) }
    }

    fn verifier_nondet_window(s: &str) -> (usize, usize) {
        let start: usize = kani::any();
        let end: usize = kani::any();
        // INPUT STATE: an ordered UTF-8 boundary window.
        kani::assume(start <= end && end <= s.len());
        kani::cover(true, "C22-A03: verifier_nondet_window assumption admitted");
        // INPUT STATE: an ordered UTF-8 boundary window.
        kani::assume(s.is_char_boundary(start) && s.is_char_boundary(end));
        kani::cover(true, "C22-A04: verifier_nondet_window assumption admitted");
        (start, end)
    }

    fn verifier_same_slice(left: &str, right: &str) -> bool {
        left.as_ptr() == right.as_ptr() && left.len() == right.len()
    }

    fn verifier_slice_offset(s: &str, subslice: &str) -> usize {
        let base = s.as_ptr().addr();
        let current = subslice.as_ptr().addr();
        assert!(base <= current);
        current - base
    }

    // Assert *both* physical range and UTF-8 boundaries. Kani's checking
    // of str::get_unchecked alone is not a substitute for the latter.
    fn verifier_assert_str_range(s: &str, result: &str, start: usize, end: usize) {
        assert!(
            start <= end && end <= s.len(),
            "slice is within the haystack"
        );
        assert!(
            s.is_char_boundary(start) && s.is_char_boundary(end),
            "slice endpoints are UTF-8 character boundaries"
        );
        assert!(
            result.as_ptr() == s.as_ptr().wrapping_add(start),
            "slice base pointer"
        );
        assert!(result.len() == end - start, "slice byte length");
    }

    // An arbitrary [start, end) window is exactly the type invariant of
    // Chars: arbitrary interleavings of next/next_back preserve this set.
    #[kani::proof]
    pub fn harness_chars_next() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (start, end) = verifier_nondet_window(s);
        let mut iter = s[start..end].chars();
        match iter.next() {
            Some(ch) => {
                let next_start = start + ch.len_utf8();
                verifier_assert_str_range(s, iter.as_str(), next_start, end);
                kani::cover(ch.len_utf8() == 1, "chars::next: ASCII");
                kani::cover(ch.len_utf8() == 2, "chars::next: two-byte scalar");
                kani::cover(ch.len_utf8() == 3, "chars::next: three-byte scalar");
                kani::cover(ch.len_utf8() == 4, "chars::next: four-byte scalar");
            }
            None => {
                assert!(start == end);
                kani::cover(true, "chars::next: exhausted");
            }
        }
        kani::cover(true, "C22-END: harness_chars_next completed");
    }

    #[kani::proof]
    pub fn harness_chars_next_back() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (start, end) = verifier_nondet_window(s);
        let mut iter = s[start..end].chars();
        match iter.next_back() {
            Some(ch) => {
                assert!(ch.len_utf8() <= end - start);
                verifier_assert_str_range(s, iter.as_str(), start, end - ch.len_utf8());
                kani::cover(ch.len_utf8() == 1, "chars::next_back: ASCII");
                kani::cover(ch.len_utf8() == 4, "chars::next_back: four-byte scalar");
            }
            None => {
                assert!(start == end);
                kani::cover(true, "chars::next_back: exhausted");
            }
        }
        kani::cover(true, "C22-END: harness_chars_next_back completed");
    }

    #[kani::proof]
    pub fn harness_chars_as_str() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (start, end) = verifier_nondet_window(s);
        let window = &s[start..end];
        let mut iter = window.chars();
        assert!(verifier_same_slice(iter.as_str(), window));
        let front = iter.next().map_or(0, char::len_utf8);
        let back = iter.next_back().map_or(0, char::len_utf8);
        verifier_assert_str_range(s, iter.as_str(), start + front, end - back);
        kani::cover(front > 0 && back > 0, "chars::as_str: both ends consumed");
        kani::cover(true, "C22-END: harness_chars_as_str completed");
    }

    const ADVANCE_MAX: usize = 8;
    const ADVANCE_BYTES: usize = 128;
    const CHUNK_MIN: usize = 33;
    const CHUNK_MAX: usize = 40;
    const CHUNK_BYTES: usize = 48;

    // Independent scalar-by-scalar reference for the bounded regression
    // checks. It uses the public decoder, not advance_by's chunk counting.
    fn verifier_reference_advance(s: &str, start: usize, end: usize, n: usize) -> (usize, usize) {
        let mut chars = s[start..end].chars();
        let mut consumed = 0;
        let mut pos = start;
        while consumed < n {
            match chars.next() {
                Some(ch) => {
                    pos += ch.len_utf8();
                    consumed += 1;
                }
                None => break,
            }
        }
        (pos, consumed)
    }

    fn verifier_check_chars_advance(s: &str, start: usize, end: usize, n: usize) {
        let (expected_end, consumed) = verifier_reference_advance(s, start, end, n);
        let mut iter = s[start..end].chars();
        let result = iter.advance_by(n); // real production body
        verifier_assert_str_range(s, iter.as_str(), expected_end, end);
        match result {
            Ok(()) => assert!(consumed == n),
            Err(remaining) => {
                assert!(consumed < n);
                assert!(expected_end == end);
                assert!(remaining.get() == n - consumed);
            }
        }
        kani::cover(
            result.is_ok() && n > 0,
            "chars::advance_by: successful skip",
        );
        kani::cover(result.is_err(), "chars::advance_by: not enough characters");
    }

    // Both the backing allocation and advance count are bounded. The
    // unwind derives from n, not string length; this is a regression proof.
    #[kani::proof]
    #[kani::unwind(9)]
    pub fn harness_chars_advance_by_small() {
        let buf: [u8; ADVANCE_BYTES + UTF8_PAD] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (start, end) = verifier_nondet_window(s);
        let n: usize = kani::any();
        // INPUT DOMAIN: this bounded request partition only.
        kani::assume(n <= ADVANCE_MAX);
        kani::cover(true, "C22-A05: harness_chars_advance_by_small assumption admitted");
        verifier_check_chars_advance(s, start, end, n);
        kani::cover(
            n == ADVANCE_MAX && start < end,
            "advance_by: maximum small count",
        );
        kani::cover(true, "C22-END: harness_chars_advance_by_small completed");
    }

    // Exercise the real chunk-skip loop (as well as its trailing-byte and
    // character loops) on a symbolic 48-byte UTF-8 string. The 48-byte
    // fixed length is a solver-budget limitation, not unbounded proof.
    #[kani::proof]
    // The scalar reference can take 40 steps; the chunk body has 32.
    #[kani::unwind(42)]
    pub fn harness_chars_advance_by_chunked() {
        let buf: [u8; CHUNK_BYTES + UTF8_PAD] = kani::any();
        // CHALLENGE 22 assumption 4: valid UTF-8 input.
        kani::assume(verifier_utf8_valid(&buf, CHUNK_BYTES));
        kani::cover(true, "C22-A06: harness_chars_advance_by_chunked assumption admitted");
        // SAFETY: the encoded prefix satisfies the exact UTF-8 predicate.
        let s = unsafe { from_utf8_unchecked(&buf[..CHUNK_BYTES]) };
        let n: usize = kani::any();
        // INPUT DOMAIN: this bounded request partition only.
        kani::assume(CHUNK_MIN <= n && n <= CHUNK_MAX);
        kani::cover(true, "C22-A07: harness_chars_advance_by_chunked assumption admitted");
        verifier_check_chars_advance(s, 0, CHUNK_BYTES, n);
        kani::cover(
            utf8_is_cont_byte(buf[32]),
            "advance_by: crosses UTF-8 chunk boundary",
        );
        kani::cover(buf[0] < 0x80 && buf[31] < 0x80, "advance_by: ASCII chunk");
        kani::cover(
            buf[0] >= 0xF0
                && buf[4] >= 0xF0
                && buf[8] >= 0xF0
                && buf[12] >= 0xF0
                && buf[16] >= 0xF0
                && buf[20] >= 0xF0
                && buf[24] >= 0xF0
                && buf[28] >= 0xF0,
            "advance_by: chunk with eight four-byte scalars",
        );
        kani::cover(true, "C22-END: harness_chars_advance_by_chunked completed");
    }

    // Challenge 22 permits assuming pattern.rs (assumption 2). This is an
    // interval-protocol abstraction, not a proof of any matching algorithm.
    // Each call may skip Reject steps and return any boundary-valid Match,
    // including a zero-width Match. Thus widths may vary between calls.
    // The common residual interval suffices for directional safety; this
    // model deliberately does NOT implement DoubleEndedSearcher. Concrete
    // double-ended instances are checked separately below.
    // Projection argument: for a forward-only concrete searcher, front/back
    // describe the unreported suffix; every real next_match return is admitted
    // here. The reverse-only argument uses the unreported prefix. Consumers
    // observe only haystack() and returned indices. This simulation argument
    // imports assumption 2; Kani does not quantify over all Rust Pattern types.
    struct ModelPattern;

    struct ModelSearcher<'a> {
        haystack: &'a str,
        front: usize,
        back: usize,
        // Fresh per-operation observers; production iterators cannot inspect
        // these fields. any_split resets them when projecting a logical state.
        last_match: Option<(usize, usize)>,
        previous_match: Option<(usize, usize)>,
        calls: usize,
    }

    impl Pattern for ModelPattern {
        type Searcher<'a> = ModelSearcher<'a>;

        fn into_searcher(self, haystack: &str) -> ModelSearcher<'_> {
            ModelSearcher {
                haystack,
                front: 0,
                back: haystack.len(),
                last_match: None,
                previous_match: None,
                calls: 0,
            }
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
        // These are Searcher guarantees imported under assumption 2, not
        // properties of SplitInternal assumed after its execution.
        // CHALLENGE 22 assumption 2: dependency Searcher range guarantee.
        kani::assume(front <= a && a <= b && b <= back);
        kani::cover(true, "C22-A08: any_match_range assumption admitted");
        // CHALLENGE 22 assumption 2: dependency Searcher range guarantee.
        kani::assume(s.is_char_boundary(a) && s.is_char_boundary(b));
        kani::cover(true, "C22-A09: any_match_range assumption admitted");
        (a, b)
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
                if old == self.back {
                    SearchStep::Done
                } else {
                    SearchStep::Reject(old, self.back)
                }
            } else {
                let (_, b) = any_match_range(self.haystack, self.front, self.back);
                let a = self.front;
                self.front = b;
                if kani::any() {
                    SearchStep::Match(a, b)
                } else {
                    SearchStep::Reject(a, b)
                }
            }
        }

        fn next_match(&mut self) -> Option<(usize, usize)> {
            assert!(type_invariant_searcher(self));
            self.previous_match = self.last_match;
            // Instrumentation must not introduce overflow on long histories.
            self.calls = self.calls.saturating_add(1);
            self.last_match = if kani::any() {
                let range = any_match_range(self.haystack, self.front, self.back);
                self.front = range.1;
                Some(range)
            } else {
                self.front = self.back;
                None
            };
            self.last_match
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
                if kani::any() {
                    SearchStep::Match(a, b)
                } else {
                    SearchStep::Reject(a, b)
                }
            }
        }

        fn next_match_back(&mut self) -> Option<(usize, usize)> {
            assert!(type_invariant_searcher(self));
            self.previous_match = self.last_match;
            // Instrumentation must not introduce overflow on long histories.
            self.calls = self.calls.saturating_add(1);
            self.last_match = if kani::any() {
                let range = any_match_range(self.haystack, self.front, self.back);
                self.back = range.0;
                Some(range)
            } else {
                self.back = self.front;
                None
            };
            self.last_match
        }
    }

    #[derive(Clone, Copy)]
    struct SplitState {
        start: usize,
        end: usize,
        front: usize,
        back: usize,
        trailing: bool,
        finished: bool,
    }

    fn split_state(iter: &SplitInternal<'_, ModelPattern>) -> SplitState {
        SplitState {
            start: iter.start,
            end: iter.end,
            front: iter.matcher.front,
            back: iter.matcher.back,
            trailing: iter.allow_trailing_empty,
            finished: iter.finished,
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
        let (start, end) = verifier_nondet_window(s);
        let (front, back) = any_match_range(s, start, end);
        SplitInternal {
            start,
            end,
            matcher: ModelSearcher {
                haystack: s,
                front,
                back,
                last_match: None,
                previous_match: None,
                calls: 0,
            },
            allow_trailing_empty: kani::any(),
            finished: kani::any(),
        }
    }

    fn assert_split_frame(s: &str, iter: &SplitInternal<'_, ModelPattern>) {
        assert!(type_invariant_split(iter));
        assert!(verifier_same_slice(iter.matcher.haystack(), s));
    }

    fn assert_valid_split_forward_transition(
        s: &str,
        old: SplitState,
        iter: &SplitInternal<'_, ModelPattern>,
        result: Option<&str>,
        inclusive: bool,
    ) {
        assert_split_frame(s, iter);
        assert_eq!(iter.end, old.end);
        assert_eq!(iter.matcher.back, old.back);
        assert_eq!(iter.allow_trailing_empty, old.trailing);
        if old.finished {
            assert!(result.is_none());
            assert_eq!(iter.start, old.start);
            assert_eq!(iter.matcher.calls, 0);
            assert_eq!(iter.matcher.front, old.front);
            assert!(iter.finished);
            return;
        }
        assert_eq!(iter.matcher.calls, 1);
        match iter.matcher.last_match {
            Some((a, b)) => {
                let part = result.unwrap();
                verifier_assert_str_range(s, part, old.start, if inclusive { b } else { a });
                assert_eq!(iter.start, b);
                assert!(!iter.finished);
                kani::cover(a == b, "split: zero-width match");
                kani::cover(b - a > 4, "split: multi-character match");
            }
            None => {
                assert!(iter.finished);
                assert_eq!(iter.start, old.start);
                if old.trailing || old.start < old.end {
                    verifier_assert_str_range(s, result.unwrap(), old.start, old.end);
                } else {
                    assert!(result.is_none());
                }
                kani::cover(true, "split: exhausted search");
            }
        }
    }

    fn assert_valid_split_reverse_transition(
        s: &str,
        old: SplitState,
        iter: &SplitInternal<'_, ModelPattern>,
        result: Option<&str>,
        inclusive: bool,
    ) {
        assert_split_frame(s, iter);
        assert_eq!(iter.start, old.start);
        assert_eq!(iter.matcher.front, old.front);
        if old.finished {
            assert!(result.is_none());
            assert_eq!(iter.end, old.end);
            assert_eq!(iter.matcher.back, old.back);
            assert_eq!(iter.matcher.calls, 0);
            assert_eq!(iter.allow_trailing_empty, old.trailing);
            assert!(iter.finished);
            return;
        }
        assert!(iter.allow_trailing_empty);
        assert!(iter.matcher.calls >= 1 && iter.matcher.calls <= 2);
        if iter.finished {
            match result {
                Some(part) => {
                    // A first empty tail may have been suppressed before
                    // returning the remaining prefix in the second search.
                    verifier_assert_str_range(s, part, old.start, iter.end);
                    assert!(iter.end <= old.end);
                }
                None => assert!(!old.trailing && iter.end == old.start),
            }
        } else {
            let (a, b) = iter.matcher.last_match.unwrap();
            let part = result.unwrap();
            let output_end = if iter.matcher.calls == 2 {
                assert!(!old.trailing);
                let (first_a, first_b) = iter.matcher.previous_match.unwrap();
                assert_eq!(first_b, old.end);
                if inclusive { first_b } else { first_a }
            } else {
                old.end
            };
            verifier_assert_str_range(s, part, b, output_end);
            assert_eq!(iter.end, if inclusive { b } else { a });
            kani::cover(a == b, "reverse split: zero-width match");
            kani::cover(b - a > 4, "reverse split: multi-character match");
        }
        kani::cover(
            iter.matcher.calls == 2,
            "reverse split: suppress empty tail then search again",
        );
        kani::cover(result.is_none(), "reverse split: no remaining part");
    }

    #[kani::proof]
    fn harness_searcher_protocol() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = any_split(s);
        let old = split_state(&iter);
        let reverse: bool = kani::any();
        let result = if reverse {
            iter.matcher.next_match_back()
        } else {
            iter.matcher.next_match()
        };
        assert!(type_invariant_searcher(&iter.matcher));
        assert!(verifier_same_slice(iter.matcher.haystack(), s));
        match result {
            Some((a, b)) => {
                assert!(old.front <= a && a <= b && b <= old.back);
                assert!(s.is_char_boundary(a) && s.is_char_boundary(b));
                if reverse {
                    assert_eq!(iter.matcher.back, a);
                } else {
                    assert_eq!(iter.matcher.front, b);
                }
                kani::cover(a == b, "protocol: zero-width match");
                kani::cover(b - a > 4, "protocol: width larger than one scalar");
            }
            None => assert_eq!(iter.matcher.front, iter.matcher.back),
        }
        if reverse {
            assert_eq!(iter.matcher.front, old.front);
        } else {
            assert_eq!(iter.matcher.back, old.back);
        }
        kani::cover(true, "C22-END: harness_searcher_protocol completed");
    }

    fn assert_initial_split<P: Pattern>(s: &str, iter: &SplitInternal<'_, P>, trailing: bool) {
        assert_eq!(iter.start, 0);
        assert_eq!(iter.end, s.len());
        assert_eq!(iter.allow_trailing_empty, trailing);
        assert!(!iter.finished);
        assert!(verifier_same_slice(iter.matcher.haystack(), s));
    }

    #[kani::proof]
    fn harness_split_constructors() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let needle: char = kani::any();
        assert_initial_split(s, &s.split(needle).0, true);
        assert_initial_split(s, &s.split_terminator(needle).0, false);
        assert_initial_split(s, &s.split_inclusive(needle).0, false);
        assert!(verifier_char_searcher_invariant(&s.split(needle).0.matcher));
        assert_initial_split(s, &s.split("").0, true);
        assert_initial_split(s, &s.split_terminator("").0, false);
        assert_initial_split(s, &s.split_inclusive("").0, false);
        let chars: [char; 2] = kani::any();
        assert_initial_split(s, &s.split(&chars[..]).0, true);
        assert_initial_split(s, &s.split_terminator(chars).0, false);
        assert_initial_split(s, &s.split_inclusive(&chars).0, false);
        let model = s.split(ModelPattern).0;
        assert_initial_split(s, &model, true);
        assert!(type_invariant_split(&model));
        let terminator = s.split_terminator(ModelPattern).0;
        let inclusive = s.split_inclusive(ModelPattern).0;
        assert_initial_split(s, &terminator, false);
        assert_initial_split(s, &inclusive, false);
        assert!(type_invariant_split(&terminator));
        assert!(type_invariant_split(&inclusive));
        kani::cover(s.is_empty(), "constructors: empty haystack");
        kani::cover(!s.is_empty(), "constructors: nonempty haystack");
        kani::cover(true, "C22-END: harness_split_constructors completed");
    }

    #[kani::proof]
    fn harness_split_get_end() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = any_split(s);
        let old = split_state(&iter);
        let result = iter.get_end();
        if !old.finished && (old.trailing || old.start < old.end) {
            verifier_assert_str_range(s, result.unwrap(), old.start, old.end);
            kani::cover(old.start == old.end, "get_end: allowed empty tail");
            kani::cover(old.start < old.end, "get_end: nonempty tail");
        } else {
            assert!(result.is_none());
            kani::cover(old.finished, "get_end: already finished");
            kani::cover(!old.finished, "get_end: suppressed empty tail");
        }
        assert!(iter.finished);
        assert_eq!(iter.start, old.start);
        assert_eq!(iter.end, old.end);
        assert_eq!(iter.matcher.front, old.front);
        assert_eq!(iter.matcher.back, old.back);
        assert_eq!(iter.matcher.calls, 0);
        assert_split_frame(s, &iter);
        kani::cover(true, "C22-END: harness_split_get_end completed");
    }

    #[kani::proof]
    fn harness_split_next() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = any_split(s);
        let old = split_state(&iter);
        let result = iter.next();
        assert_valid_split_forward_transition(s, old, &iter, result, false);
        kani::cover(true, "C22-END: harness_split_next completed");
    }

    #[kani::proof]
    fn harness_split_next_inclusive() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = any_split(s);
        let old = split_state(&iter);
        let result = iter.next_inclusive();
        assert_valid_split_forward_transition(s, old, &iter, result, true);
        kani::cover(true, "C22-END: harness_split_next_inclusive completed");
    }

    #[kani::proof]
    fn harness_split_next_back() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = any_split(s);
        let old = split_state(&iter);
        let result = iter.next_back();
        assert_valid_split_reverse_transition(s, old, &iter, result, false);
        kani::cover(true, "C22-END: harness_split_next_back completed");
    }

    #[kani::proof]
    fn harness_split_next_back_inclusive() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = any_split(s);
        let old = split_state(&iter);
        let result = iter.next_back_inclusive();
        assert_valid_split_reverse_transition(s, old, &iter, result, true);
        kani::cover(true, "C22-END: harness_split_next_back_inclusive completed");
    }

    #[kani::proof]
    fn harness_split_remainder() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let iter = any_split(s);
        let old = split_state(&iter);
        match iter.remainder() {
            Some(part) => {
                assert!(!old.finished);
                verifier_assert_str_range(s, part, old.start, old.end);
            }
            None => assert!(old.finished),
        }
        assert_split_frame(s, &iter);
        assert_eq!(iter.matcher.calls, 0);
        kani::cover(old.finished, "remainder: finished");
        kani::cover(
            !old.finished && old.start == old.end,
            "remainder: empty active interval",
        );
        kani::cover(true, "C22-END: harness_split_remainder completed");
    }

    fn assert_valid_match_transition(
        s: &str,
        old_front: usize,
        old_back: usize,
        searcher: &ModelSearcher<'_>,
        result: Option<(usize, &str)>,
        reverse: bool,
    ) {
        assert!(type_invariant_searcher(searcher));
        assert!(verifier_same_slice(searcher.haystack(), s));
        assert_eq!(searcher.calls, 1);
        match searcher.last_match {
            Some((a, b)) => {
                let (index, part) = result.unwrap();
                assert_eq!(index, a);
                verifier_assert_str_range(s, part, a, b);
                assert!(old_front <= a && b <= old_back);
                if reverse {
                    assert_eq!(searcher.back, a);
                } else {
                    assert_eq!(searcher.front, b);
                }
                kani::cover(a == b, "matches: empty match");
                kani::cover(b - a > 4, "matches: multiple-character match");
            }
            None => {
                assert!(result.is_none());
                assert_eq!(searcher.front, searcher.back);
            }
        }
        if reverse {
            assert_eq!(searcher.front, old_front);
        } else {
            assert_eq!(searcher.back, old_back);
        }
        kani::cover(result.is_none(), "matches: exhausted");
    }

    #[kani::proof]
    fn harness_match_indices_next() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let searcher = any_split(s).matcher;
        let (front, back) = (searcher.front, searcher.back);
        let mut iter = MatchIndicesInternal::<ModelPattern>(searcher);
        let result = iter.next();
        assert_valid_match_transition(s, front, back, &iter.0, result, false);
        kani::cover(true, "C22-END: harness_match_indices_next completed");
    }

    #[kani::proof]
    fn harness_match_indices_next_back() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let searcher = any_split(s).matcher;
        let (front, back) = (searcher.front, searcher.back);
        let mut iter = MatchIndicesInternal::<ModelPattern>(searcher);
        let result = iter.next_back();
        assert_valid_match_transition(s, front, back, &iter.0, result, true);
        kani::cover(true, "C22-END: harness_match_indices_next_back completed");
    }

    #[kani::proof]
    fn harness_matches_next() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let searcher = any_split(s).matcher;
        let (front, back) = (searcher.front, searcher.back);
        let mut iter = MatchesInternal::<ModelPattern>(searcher);
        let result = iter
            .next()
            .map(|part| (verifier_slice_offset(s, part), part));
        assert_valid_match_transition(s, front, back, &iter.0, result, false);
        kani::cover(true, "C22-END: harness_matches_next completed");
    }

    #[kani::proof]
    fn harness_matches_next_back() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let searcher = any_split(s).matcher;
        let (front, back) = (searcher.front, searcher.back);
        let mut iter = MatchesInternal::<ModelPattern>(searcher);
        let result = iter
            .next_back()
            .map(|part| (verifier_slice_offset(s, part), part));
        assert_valid_match_transition(s, front, back, &iter.0, result, true);
        kani::cover(true, "C22-END: harness_matches_next_back completed");
    }

    // Prove the stronger relation to the exact pre-call remaining interval.
    // For any past prefix_end <= old.start and suffix_start >= old.end,
    // these assertions imply the old ownership relation by transitivity.
    // No extra assumption on ghost history bounds is needed here.
    #[kani::proof]
    fn harness_split_history_step() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = any_split(s);
        let reverse: bool = kani::any();
        let old = split_state(&iter);
        let result = if reverse {
            iter.next_back()
        } else {
            iter.next()
        };
        if let Some(part) = result {
            let a = verifier_slice_offset(s, part);
            let b = a + part.len();
            verifier_assert_str_range(s, part, a, b);
            assert!(old.start <= a && b <= old.end);
            if !iter.finished {
                if reverse {
                    assert!(iter.end <= a);
                } else {
                    assert!(b <= iter.start);
                }
            }
        }
        if !iter.finished {
            assert!(old.start <= iter.start && iter.end <= old.end);
        } else {
            assert!(iter.next().is_none());
            assert!(iter.next_back().is_none());
        }
        assert_split_frame(s, &iter);
        kani::cover(
            reverse && !old.finished && result.is_some(),
            "history: reverse step",
        );
        kani::cover(
            !reverse && !old.finished && result.is_some(),
            "history: forward step",
        );
        kani::cover(true, "C22-END: harness_split_history_step completed");
    }

    #[kani::proof]
    pub fn harness_split_ascii_whitespace_remainder() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut iter = s.split_ascii_whitespace();
        assert!(
            iter.remainder()
                .is_some_and(|part| verifier_same_slice(part, s))
        );

        // Every reachable inner slice is a UTF-8-boundary window. Cutting
        // at ASCII whitespace cannot cut through a multibyte scalar.
        let (start, end) = verifier_nondet_window(s);
        iter.inner.iter.iter.v = s[start..end].as_bytes();
        iter.inner.iter.iter.finished = kani::any();
        let finished = iter.inner.iter.iter.finished;
        match iter.remainder() {
            Some(part) => {
                assert!(!finished);
                verifier_assert_str_range(s, part, start, end);
                kani::cover(part.is_empty(), "ASCII whitespace remainder: empty window");
                kani::cover(
                    !part.is_empty(),
                    "ASCII whitespace remainder: nonempty window",
                );
            }
            None => {
                assert!(finished);
                kani::cover(true, "ASCII whitespace remainder: finished");
            }
        }
        kani::cover(true, "C22-END: harness_split_ascii_whitespace_remainder completed");
    }

    // Main already contains #[requires(idx < self.0.len())]. The contract
    // is discharged against the original body, with Kani generating the
    // precondition rather than the harness assuming the target's safety.
    #[kani::proof_for_contract(Bytes::__iterator_get_unchecked)]
    pub fn harness_bytes_iterator_get_unchecked() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (start, end) = verifier_nondet_window(s);
        let window = &s[start..end];
        let mut iter = window.bytes();
        let index: usize = kani::any();
        let item = unsafe { iter.__iterator_get_unchecked(index) };
        assert!(item == window.as_bytes()[index]);
        kani::cover(index > 0, "bytes::get_unchecked: index past first byte");
        kani::cover(true, "C22-END: harness_bytes_iterator_get_unchecked completed");
    }
    fn assert_ordered_parts(s: &str, front: Option<&str>, back: Option<&str>) {
        if let Some(front) = front {
            let a = verifier_slice_offset(s, front);
            verifier_assert_str_range(s, front, a, a + front.len());
        }
        if let Some(back) = back {
            let a = verifier_slice_offset(s, back);
            verifier_assert_str_range(s, back, a, a + back.len());
        }
        if let (Some(front), Some(back)) = (front, back) {
            let a = verifier_slice_offset(s, front);
            let b = verifier_slice_offset(s, back);
            assert!(a + front.len() <= b, "opposite-end outputs do not overlap");
        }
    }

    fn assert_public_split_pair<'a, P>(s: &'a str, pattern: P)
    where
        P: Pattern<Searcher<'a>: DoubleEndedSearcher<'a>>,
    {
        let inclusive: bool = kani::any();
        let trailing: bool = kani::any();
        let mut iter = if inclusive {
            s.split_inclusive(pattern).0
        } else if trailing {
            s.split(pattern).0
        } else {
            s.split_terminator(pattern).0
        };
        let front_first: bool = kani::any();
        let (front, back) = if front_first {
            let front = if inclusive {
                iter.next_inclusive()
            } else {
                iter.next()
            };
            let back = if inclusive {
                iter.next_back_inclusive()
            } else {
                iter.next_back()
            };
            (front, back)
        } else {
            let back = if inclusive {
                iter.next_back_inclusive()
            } else {
                iter.next_back()
            };
            let front = if inclusive {
                iter.next_inclusive()
            } else {
                iter.next()
            };
            (front, back)
        };
        assert_ordered_parts(s, front, back);
        if let Some(rest) = iter.remainder() {
            let a = verifier_slice_offset(s, rest);
            verifier_assert_str_range(s, rest, a, iter.end);
            if let Some(front) = front {
                assert!(verifier_slice_offset(s, front) + front.len() <= a);
            }
            if let Some(back) = back {
                assert!(iter.end <= verifier_slice_offset(s, back));
            }
        } else {
            assert!(iter.finished);
            assert!(iter.next().is_none());
            assert!(iter.next_back().is_none());
        }
        kani::cover(
            front_first && front.is_some() && back.is_some(),
            "mixed: front then back",
        );
        kani::cover(
            !front_first && front.is_some() && back.is_some(),
            "mixed: back then front",
        );
        kani::cover(
            inclusive && front.is_some() && back.is_some(),
            "mixed: inclusive parts",
        );
        kani::cover(
            !inclusive && !trailing && front.is_some(),
            "mixed: terminator parts",
        );
    }

    #[kani::proof]
    #[kani::stub(<CharSearcher<'_> as Searcher<'_>>::next_match, verifier_stub_char_next_match)]
    #[kani::stub(<CharSearcher<'_> as ReverseSearcher<'_>>::next_match_back, verifier_stub_char_next_match_back)]
    fn harness_split_mixed_directions() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        assert_public_split_pair(s, kani::any::<char>());
        kani::cover(true, "C22-END: harness_split_mixed_directions completed");
    }

    #[kani::proof]
    #[kani::stub(<CharSliceSearcher<'_, '_> as Searcher<'_>>::next_match, verifier_stub_char_slice_next_match)]
    #[kani::stub(<CharSliceSearcher<'_, '_> as ReverseSearcher<'_>>::next_match_back, verifier_stub_char_slice_next_match_back)]
    fn harness_split_char_slice_mixed() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let chars: [char; 2] = kani::any();
        let len: usize = kani::any();
        // INPUT DOMAIN: allocated prefix or index extent.
        kani::assume(len <= chars.len());
        kani::cover(true, "C22-A10: harness_split_char_slice_mixed assumption admitted");
        assert_public_split_pair(s, &chars[..len]);
        kani::cover(len == 0, "character set: empty");
        kani::cover(
            len == 2 && chars[0].len_utf8() != chars[1].len_utf8(),
            "character set: different widths",
        );
        kani::cover(true, "C22-END: harness_split_char_slice_mixed completed");
    }

    // Concrete &str instances deliberately keep the two directions separate.
    // They are integration checks under assumption 2, not a proof that all
    // Pattern implementations refine the abstract protocol above.
    fn assert_str_pattern_direction(s: &str, needle: &str, reverse: bool) {
        let inclusive: bool = kani::any();
        let mut iter = if inclusive {
            s.split_inclusive(needle).0
        } else {
            s.split_terminator(needle).0
        };
        let first = if reverse {
            if inclusive {
                iter.next_back_inclusive()
            } else {
                iter.next_back()
            }
        } else if inclusive {
            iter.next_inclusive()
        } else {
            iter.next()
        };
        let second = if reverse {
            if inclusive {
                iter.next_back_inclusive()
            } else {
                iter.next_back()
            }
        } else if inclusive {
            iter.next_inclusive()
        } else {
            iter.next()
        };
        if reverse {
            assert_ordered_parts(s, second, first);
        } else {
            assert_ordered_parts(s, first, second);
        }
        if let Some(rest) = iter.remainder() {
            verifier_assert_str_range(s, rest, iter.start, iter.end);
        } else {
            assert!(iter.finished);
            let terminal = if reverse {
                if inclusive {
                    iter.next_back_inclusive()
                } else {
                    iter.next_back()
                }
            } else if inclusive {
                iter.next_inclusive()
            } else {
                iter.next()
            };
            assert!(terminal.is_none());
        }
        let mut indices = if reverse {
            s.rmatch_indices(needle).0
        } else {
            s.match_indices(needle).0
        };
        let matched = if reverse {
            indices.next_back()
        } else {
            indices.next()
        };
        if let Some((a, part)) = matched {
            verifier_assert_str_range(s, part, a, a + needle.len());
        }
        // A fresh instance also exercises the MatchesInternal wrapper.
        let mut matches = MatchesInternal::<&str>(needle.into_searcher(s));
        if let Some(part) = if reverse {
            matches.next_back()
        } else {
            matches.next()
        } {
            let a = verifier_slice_offset(s, part);
            verifier_assert_str_range(s, part, a, a + needle.len());
        }
        kani::cover(
            first.is_some() && second.is_some(),
            "str pattern: two split parts",
        );
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn harness_str_empty_forward() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        assert_str_pattern_direction(s, "", false);
        kani::cover(s.is_empty(), "empty needle: empty haystack");
        kani::cover(true, "C22-END: harness_str_empty_forward completed");
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn harness_str_empty_reverse() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        assert_str_pattern_direction(s, "", true);
        kani::cover(s.is_empty(), "empty needle reverse: empty haystack");
        kani::cover(true, "C22-END: harness_str_empty_reverse completed");
    }

    fn any_short_needle(buf: &mut [u8; 8]) -> &str {
        let first: char = kani::any();
        let mut len = first.encode_utf8(buf).len();
        if kani::any() {
            let second: char = kani::any();
            len += second.encode_utf8(&mut buf[len..]).len();
        }
        // SAFETY: concatenation of one or two scalar UTF-8 encodings.
        unsafe { from_utf8_unchecked(&buf[..len]) }
    }

    #[kani::proof]
    #[kani::unwind(20)]
    #[kani::stub(<StrSearcher<'_, '_> as Searcher<'_>>::next_match, verifier_stub_str_nonempty_next_match)]
    fn harness_str_nonempty_forward() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut needle_buf = [0u8; 8];
        let needle = any_short_needle(&mut needle_buf);
        assert_str_pattern_direction(s, needle, false);
        kani::cover(needle.len() == 1, "str pattern: byte searcher");
        kani::cover(needle.len() > 4, "str pattern: two multibyte scalars");
        kani::cover(true, "C22-END: harness_str_nonempty_forward completed");
    }

    #[kani::proof]
    #[kani::unwind(20)]
    #[kani::stub(<StrSearcher<'_, '_> as ReverseSearcher<'_>>::next_match_back, verifier_stub_str_nonempty_next_match_back)]
    fn harness_str_nonempty_reverse() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let mut needle_buf = [0u8; 8];
        let needle = any_short_needle(&mut needle_buf);
        assert_str_pattern_direction(s, needle, true);
        kani::cover(needle.len() == 1, "str pattern reverse: byte searcher");
        kani::cover(
            needle.len() > 4,
            "str pattern reverse: two multibyte scalars",
        );
        kani::cover(true, "C22-END: harness_str_nonempty_reverse completed");
    }

    // Independent streaming decoder for checking the local input predicate.
    // Its state is the expected continuation count and permitted next byte;
    // unlike the local predicate it does not inspect overlapping windows.
    fn reference_utf8_valid(bytes: &[u8]) -> bool {
        let mut pending = 0usize;
        let mut low = 0x80;
        let mut high = 0xBF;
        // Index traversal keeps this reference independent of slice iterator
        // pointer models. No encoding constraint is assumed in this loop.
        let mut index = 0usize;
        while index < bytes.len() {
            let byte = bytes[index];
            index += 1;
            if pending > 0 {
                if byte < low || byte > high {
                    return false;
                }
                pending -= 1;
                low = 0x80;
                high = 0xBF;
            } else {
                match byte {
                    0..=0x7F => {}
                    0xC2..=0xDF => pending = 1,
                    0xE0 => {
                        pending = 2;
                        low = 0xA0;
                    }
                    0xE1..=0xEC | 0xEE..=0xEF => pending = 2,
                    0xED => {
                        pending = 2;
                        high = 0x9F;
                    }
                    0xF0 => {
                        pending = 3;
                        low = 0x90;
                    }
                    0xF1..=0xF3 => pending = 3,
                    0xF4 => {
                        pending = 3;
                        high = 0x8F;
                    }
                    _ => return false,
                }
            }
        }
        pending == 0
    }

    // No UTF-8 validity filter: raw bytes include all invalid encodings.
    // This checks both soundness and completeness of the local predicate
    // against an independent streaming decoder throughout the largest
    // allocation used by these proofs. It is not an arbitrary-N theorem.
    #[kani::proof]
    #[kani::unwind(257)]
    fn harness_utf8_input_model() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let len: usize = kani::any();
        // INPUT-LENGTH: selecting a prefix within this allocation, not
        // assuming any encoding property or expected comparison result.
        // INPUT DOMAIN: allocated prefix or index extent.
        kani::assume(len <= MAX_BYTES);
        kani::cover(true, "C22-A11: harness_utf8_input_model assumption admitted");
        let local = verifier_utf8_valid(&buf, len);
        let reference = reference_utf8_valid(&buf[..len]);
        assert_eq!(local, reference);
        kani::cover(local && len == MAX_BYTES, "UTF-8 model: full valid input");
        kani::cover(
            !local && len == MAX_BYTES,
            "UTF-8 model: rejects invalid input",
        );
        kani::cover(local && len == 0, "UTF-8 model: empty input");
        kani::cover(
            !local && len == 1 && buf[0] == 0xF0,
            "UTF-8 model: truncated scalar",
        );
        kani::cover(
            local && len == 4 && buf[0] == 0xF4,
            "UTF-8 model: largest scalar block",
        );
        kani::cover(true, "C22-END: harness_utf8_input_model completed");
    }

    // Local safety lemmas for advance_by. These establish the obligations
    // of one loop step only; the production loops are not contracted or
    // replaced, so these are NOT an unbounded proof of advance_by.
    #[kani::proof]
    #[kani::unwind(33)]
    fn harness_advance_chunk_step() {
        let chunk: [u8; 32] = kani::any();
        let total_len: usize = kani::any();
        let skipped: usize = kani::any();
        let remainder: usize = kani::any();
        // LOCAL LEMMA: input precondition, not a proved production invariant.
        kani::assume(skipped <= total_len && 32 <= total_len - skipped);
        kani::cover(true, "C22-A12: harness_advance_chunk_step assumption admitted");
        // LOCAL LEMMA: input precondition, not a proved production invariant.
        kani::assume(remainder > 32);
        kani::cover(true, "C22-A13: harness_advance_chunk_step assumption admitted");
        let mut starts = [false; 32];
        for i in 0..32 {
            starts[i] = !utf8_is_cont_byte(chunk[i]);
        }
        let count = starts.into_iter().map(|x| x as u8).sum::<u8>() as usize;
        assert!(count <= 32);
        assert!(count < remainder);
        assert!(skipped + 32 <= total_len);
        assert!(remainder - count > 0);
        kani::cover(count == 32, "chunk step: all start bytes");
        kani::cover(
            count == 0,
            "chunk step: conservative invalid-byte over-approximation",
        );
        kani::cover(true, "C22-END: harness_advance_chunk_step completed");
    }

    #[kani::proof]
    fn harness_advance_character_step() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (start, end) = verifier_nondet_window(s);
        // LOCAL LEMMA: input precondition, not a proved production invariant.
        kani::assume(start < end);
        kani::cover(true, "C22-A14: harness_advance_character_step assumption admitted");
        let width = utf8_char_width(s.as_bytes()[start]);
        assert!(1 <= width && width <= 4);
        assert!(width <= end - start);
        assert!(s.is_char_boundary(start + width));
        let mut bytes = s.as_bytes()[start..end].iter();
        assert!(bytes.advance_by(width).is_ok());
        assert_eq!(bytes.len(), end - start - width);
        kani::cover(width == 4, "character step: four-byte scalar");
        kani::cover(true, "C22-END: harness_advance_character_step completed");
    }

    #[kani::proof]
    #[kani::unwind(4)]
    fn harness_advance_boundary_restore() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let pos: usize = kani::any();
        // INPUT DOMAIN: allocated prefix or index extent.
        kani::assume(pos <= s.len());
        kani::cover(true, "C22-A15: harness_advance_boundary_restore assumption admitted");
        let mut iter = s.as_bytes()[pos..].iter();
        let mut skipped = 0usize;
        while let Some(&byte) = iter.as_slice().first() {
            if !utf8_is_cont_byte(byte) {
                break;
            }
            assert!(iter.advance_by(1).is_ok());
            skipped += 1;
        }
        assert!(skipped <= 3);
        assert!(s.is_char_boundary(pos + skipped));
        kani::cover(skipped == 3, "boundary restore: three continuation bytes");
        kani::cover(skipped == 0, "boundary restore: already aligned");
        kani::cover(true, "C22-END: harness_advance_boundary_restore completed");
    }
    // Count-gap regression on a fixed chunk or an empty string. A symbolic
    // window made CBMC duplicate the unreachable chunk loop and exceeded the
    // 480-second budget. This does not cover every length/window for n=9..32.
    #[kani::proof]
    #[kani::unwind(34)]
    fn harness_chars_advance_by_medium() {
        const BYTES: usize = 32;
        let buf: [u8; BYTES + UTF8_PAD] = kani::any();
        // CHALLENGE 22 assumption 4: valid UTF-8 input.
        kani::assume(verifier_utf8_valid(&buf, BYTES));
        kani::cover(true, "C22-A16: harness_chars_advance_by_medium assumption admitted");
        // SAFETY: the local predicate establishes this fixed prefix's UTF-8.
        let s = unsafe { from_utf8_unchecked(&buf[..BYTES]) };
        let n: usize = kani::any();
        // INPUT DOMAIN: this bounded request partition only.
        kani::assume(9 <= n && n <= 32);
        kani::cover(true, "C22-A17: harness_chars_advance_by_medium assumption admitted");
        let empty: bool = kani::any();
        if empty {
            verifier_check_chars_advance("", 0, 0, n);
        } else {
            verifier_check_chars_advance(s, 0, BYTES, n);
        }
        kani::cover(n == 32 && !empty, "advance_by: threshold count");
        kani::cover(empty, "advance_by: large count on empty input");
        kani::cover(true, "C22-END: harness_chars_advance_by_medium completed");
    }

    // Exhaust two full chunks for any request larger than their byte count,
    // including usize::MAX. Only the allocation length is fixed here. The
    // reference counts UTF-8 leading bytes, independently of chunk grouping;
    // there is no character-decoding reference loop proportional to n.
    // Requests 41..=64 have a separate fixed-size rank-reference proof below.
    // Arbitrary allocation lengths are not covered here.
    #[kani::proof]
    #[kani::unwind(66)]
    fn harness_chars_advance_by_multichunk() {
        const BYTES: usize = 64;
        let buf: [u8; BYTES + UTF8_PAD] = kani::any();
        // CHALLENGE 22 assumption 4: valid UTF-8 input.
        kani::assume(verifier_utf8_valid(&buf, BYTES));
        kani::cover(true, "C22-A18: harness_chars_advance_by_multichunk assumption admitted");
        // SAFETY: the local predicate establishes this fixed prefix's UTF-8.
        let s = unsafe { from_utf8_unchecked(&buf[..BYTES]) };
        let n: usize = kani::any();
        // INPUT DOMAIN: this bounded request partition only.
        kani::assume(n > BYTES);
        kani::cover(true, "C22-A19: harness_chars_advance_by_multichunk assumption admitted");
        let mut iter = s.chars();
        let result = iter.advance_by(n);
        verifier_assert_str_range(s, iter.as_str(), BYTES, BYTES);
        let mut chars = 0usize;
        for i in 0..BYTES {
            chars += (!utf8_is_cont_byte(buf[i])) as usize;
        }
        assert!(16 <= chars && chars <= BYTES);
        let remaining = result.unwrap_err().get();
        assert_eq!(remaining, n - chars);
        kani::cover(n == usize::MAX, "advance_by: maximum request");
        kani::cover(chars == 64, "advance_by: two ASCII chunks");
        kani::cover(chars == 16, "advance_by: two chunks of four-byte scalars");
        kani::cover(
            utf8_is_cont_byte(buf[32]),
            "advance_by: second chunk starts inside a scalar",
        );
        kani::cover(true, "C22-END: harness_chars_advance_by_multichunk completed");
    }

    // A byte-rank oracle, independent of advance_by's chunk grouping and
    // continuation-restoration loop. On valid UTF-8, leading-byte rank is
    // scalar rank. Locate the first boundary whose rank equals the request;
    // if there is none, the expected residual string is empty. This oracle
    // has a fixed allocation bound, even when n ranges over all usize values.
    fn assert_advance_by_rank<const N: usize>(buf: &[u8; N], n: usize) -> (usize, usize, usize) {
        let len = N - UTF8_PAD;
        // CHALLENGE 22 assumption 4: valid UTF-8 input.
        kani::assume(verifier_utf8_valid(buf, len));
        kani::cover(true, "C22-A20: assert_advance_by_rank assumption admitted");
        // SAFETY: the exact local predicate constrains the whole prefix.
        let s = unsafe { from_utf8_unchecked(&buf[..len]) };
        let mut rank = 0usize;
        let mut expected = len;
        let mut first_chunk = 0usize;
        let mut first_two_chunks = 0usize;
        // Six verification blocks of 16 suffice for the largest input.
        // This visits every byte once; it does not summarize counts per
        // production chunk. A short inner loop allows a common unwind of
        // 34, instead of expanding the target's scalar tail 98 times.
        for block in 0..len.div_ceil(16) {
            for offset in 0..16 {
                let i = block * 16 + offset;
                if i >= len {
                    break;
                }
                if i == 32 {
                    first_chunk = rank;
                }
                if i == 64 {
                    first_two_chunks = rank;
                }
                if !utf8_is_cont_byte(buf[i]) {
                    if rank == n {
                        expected = i;
                    }
                    rank += 1;
                }
            }
        }
        let mut iter = s.chars();
        let result = iter.advance_by(n); // real production body, no stubs
        verifier_assert_str_range(s, iter.as_str(), expected, len);
        if n <= rank {
            assert!(result.is_ok());
        } else {
            assert_eq!(result.unwrap_err().get(), n - rank);
        }
        kani::cover(result.is_ok(), "rank oracle: successful skip");
        kani::cover(result.is_err(), "rank oracle: exact missing scalar count");
        (expected, first_chunk, first_two_chunks)
    }

    // Fill the request-count gap with an arbitrary valid 64-byte prefix.
    // Both success and shortage are checked, rather than constraining the
    // needle/request by an assumed postcondition on the production iterator.
    #[kani::proof]
    #[kani::unwind(34)]
    fn harness_chars_advance_by_count_gap() {
        let buf: [u8; 64 + UTF8_PAD] = kani::any();
        let n: usize = kani::any();
        // INPUT DOMAIN: this bounded request partition only.
        kani::assume(41 <= n && n <= 64);
        kani::cover(true, "C22-A21: harness_chars_advance_by_count_gap assumption admitted");
        let (end, _, _) = assert_advance_by_rank(&buf, n);
        kani::cover(n == 41 && end < 64, "count gap: lower request retains tail");
        kani::cover(n == 64, "count gap: upper request");
        kani::cover(
            utf8_is_cont_byte(buf[32]),
            "count gap: restore chunk boundary",
        );
        kani::cover(true, "C22-END: harness_chars_advance_by_count_gap completed");
    }

    // n > 64 forces at least two 32-byte scans: a chunk contains at most
    // 32 leading bytes. Unlike the exhaustion regression, this input also
    // permits a successful skip with a nonempty residual string. The rank
    // covers establish that the chunk loop exits after exactly two scans,
    // then restores a boundary and consumes a positive scalar remainder.
    #[kani::proof]
    // The real tail has at most 32 bytes after two scans. Keep unwinding
    // assertions enabled to check this bound as well as the reference loops.
    #[kani::unwind(34)]
    fn harness_chars_advance_by_multichunk_tail() {
        let buf: [u8; 96 + UTF8_PAD] = kani::any();
        let n: usize = kani::any();
        // INPUT DOMAIN: this bounded request partition only.
        kani::assume(65 <= n && n <= 96);
        kani::cover(true, "C22-A22: harness_chars_advance_by_multichunk_tail assumption admitted");
        let (end, first, first_two) = assert_advance_by_rank(&buf, n);
        let two_scans = n - first > 32 && n - first_two <= 32;
        kani::cover(two_scans && end < 96, "multi chunk: two scans retain tail");
        kani::cover(
            two_scans && end < 96 && utf8_is_cont_byte(buf[64]),
            "multi chunk: restore boundary then retain tail",
        );
        kani::cover(
            n - first_two > 32 && end == 96,
            "multi chunk: third scan exhausts input",
        );
        kani::cover(n == 96, "multi chunk: upper request");
        kani::cover(true, "C22-END: harness_chars_advance_by_multichunk_tail completed");
    }

    // Check the state generator separately. This asserts consequences of
    // its input bounds; no invariant or post-target property is assumed.
    #[kani::proof]
    fn harness_split_state_generator() {
        let buf: [u8; BUFFER_BYTES] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let iter = any_split(s);
        assert!(type_invariant_split(&iter));
        assert!(verifier_same_slice(s, iter.matcher.haystack()));
        assert_eq!(iter.matcher.calls, 0);
        assert!(iter.matcher.last_match.is_none());
        assert!(iter.matcher.previous_match.is_none());
        kani::cover(
            iter.finished && iter.start < iter.end,
            "state generator: finished nonempty interval",
        );
        kani::cover(
            !iter.finished && iter.start == iter.end,
            "state generator: active empty interval",
        );
        kani::cover(true, "C22-END: harness_split_state_generator completed");
    }

    // Challenge assumption 1 supplies the functional correctness of slice
    // byte search. This deterministic model implements its exact last-match
    // definition, not a nondeterministic return-range assumption. In particular
    // None is returned only after every byte has been checked.
    fn verifier_last_byte(needle: u8, bytes: &[u8]) -> Option<usize> {
        let mut index = bytes.len();
        while index > 0 {
            index -= 1;
            if bytes[index] == needle {
                return Some(index);
            }
        }
        None
    }

    // Check the leaf model against the complete last-index specification on
    // arbitrary raw prefixes, including non-UTF-8 data and the empty slice.
    #[kani::proof]
    #[kani::unwind(20)]
    fn harness_reverse_byte_model() {
        let bytes: [u8; 16] = kani::any();
        let len: usize = kani::any();
        // INPUT-LENGTH: only prefixes of this initialized array are inputs.
        // INPUT DOMAIN: allocated prefix or index extent.
        kani::assume(len <= bytes.len());
        kani::cover(true, "C22-A23: harness_reverse_byte_model assumption admitted");
        let needle: u8 = kani::any();
        let result = verifier_last_byte(needle, &bytes[..len]);
        if let Some(index) = result {
            assert!(index < len);
            assert_eq!(bytes[index], needle);
        }
        for index in 0..len {
            if result.is_none_or(|last| last < index) {
                assert_ne!(bytes[index], needle);
            }
        }
        kani::cover(result.is_some(), "byte model: matching byte");
        kani::cover(result.is_none(), "byte model: no match");
        kani::cover(
            len > 0 && result == Some(len - 1),
            "byte model: final byte matches",
        );
        kani::cover(len == 0 && result.is_none(), "byte model: empty prefix");
        kani::cover(true, "C22-END: harness_reverse_byte_model completed");
    }

    // Bounded inclusion evidence for the hand-written char adapters. Keep
    // the directions separate to avoid combining both search circuits; their
    // union covers the original arbitrary-direction input domain.
    fn assert_char_searcher_direction(reverse: bool) {
        let buf: [u8; 16 + UTF8_PAD] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (front, back) = verifier_nondet_window(s);
        let needle: char = kani::any();
        let result = verifier_assert_real_char_searcher(s, needle, front, back, reverse);
        kani::cover(result.is_some(), "real char search: matching scalar");
        kani::cover(result.is_none(), "real char search: exhausted window");
        kani::cover(
            result.is_some() && needle.len_utf8() == 4,
            "real char search: four-byte match",
        );
        kani::cover(
            front == back && result.is_none(),
            "real char search: empty window",
        );
    }

    // The byte window has at most 16 bytes. Every failed candidate consumes
    // a byte, so 18 includes the final exhaustion call and loop-exit check.
    #[kani::proof]
    #[kani::unwind(18)]
    fn harness_char_searcher_forward_refinement() {
        assert_char_searcher_direction(false);
        kani::cover(true, "C22-END: harness_char_searcher_forward_refinement completed");
    }

    // Neither CharSearcher method is stubbed. Only the reverse slice byte
    // leaf uses the exact deterministic model under challenge assumption 1.
    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::stub(crate::slice::memchr::memrchr, verifier_last_byte)]
    fn harness_char_searcher_reverse_refinement() {
        assert_char_searcher_direction(true);
        kani::cover(true, "C22-END: harness_char_searcher_reverse_refinement completed");
    }

    // Independent rank check for any caller-supplied UTF-8 window. The
    // caller's allocation bound is asserted, not silently assumed here.
    // A u16 counter covers all 256 bytes without truncating character counts.
    // No search, advance, or result property is assumed in this reference.
    fn assert_advance_by_window_rank(
        s: &str,
        start: usize,
        end: usize,
        n: usize,
    ) -> (usize, usize) {
        assert!(s.len() <= MAX_BYTES);
        assert!(start <= end && end <= s.len());
        assert!(s.is_char_boundary(start) && s.is_char_boundary(end));
        let mut iter = s[start..end].chars();
        let result = iter.advance_by(n); // real target, no stubs
        let remaining = iter.as_str();
        let position = verifier_slice_offset(s, remaining);
        assert!(start <= position && position <= end);
        verifier_assert_str_range(s, remaining, position, end);

        // Independently rank the returned boundary. Every UTF-8 boundary
        // has a unique scalar rank, so this characterizes the exact suffix
        // without selecting an expected pointer once for every input byte.
        let mut total = 0u16;
        let mut consumed = 0u16;
        let len = end - start;
        for block in 0..len.div_ceil(16) {
            for offset in 0..16 {
                let local = block * 16 + offset;
                if local >= len {
                    break;
                }
                let index = start + local;
                if !utf8_is_cont_byte(s.as_bytes()[index]) {
                    total += 1;
                    if index < position {
                        consumed += 1;
                    }
                }
            }
        }
        let count = usize::from(total);
        assert!(count <= len);
        assert_eq!(usize::from(consumed), n.min(count));
        if n <= count {
            assert!(result.is_ok());
        } else {
            assert_eq!(result.unwrap_err().get(), n - count);
        }
        (position, count)
    }

    // Full usize request domain, including zero and usize::MAX. Only the
    // initialized backing object and valid UTF-8 origin bound the input.
    // After chunk scanning the real scalar tail needs at most 32 iterations;
    // the reference's 16-byte blocks do not force a byte-length global bound.
    #[kani::proof]
    #[kani::unwind(34)]
    fn harness_chars_advance_by_all_counts() {
        const BYTES: usize = 40;
        let buf: [u8; BYTES + UTF8_PAD] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let n: usize = kani::any();
        let (position, _) = assert_advance_by_window_rank(s, 0, s.len(), n);
        kani::cover(n == 0 && !s.is_empty(), "all counts: zero request");
        kani::cover(
            n == 32 && position < s.len(),
            "all counts: threshold retains tail",
        );
        kani::cover(
            n == 33 && s.len() >= 36
                && !s.is_char_boundary(32)
                && !s.is_char_boundary(33)
                && !s.is_char_boundary(34)
                && position < s.len(),
            "all counts: three continuation bytes then scalar tail",
        );
        kani::cover(
            n == usize::MAX && s.len() == BYTES,
            "all counts: maximum usize nonempty input",
        );
        kani::cover(
            s.len() == BYTES && n == BYTES + 1 && position == s.len(),
            "all counts: byte capacity plus one shortage",
        );
        kani::cover(true, "C22-END: harness_chars_advance_by_all_counts completed");
    }

    // A distinct large-allocation domain: every 256-byte UTF-8 string and
    // every request above 256. This explicit request range is not a
    // postcondition assumption or a claim about requests 0..=256.
    #[kani::proof]
    #[kani::unwind(34)]
    fn harness_chars_advance_by_eight_chunks() {
        const BYTES: usize = 256;
        let buf: [u8; BYTES + UTF8_PAD] = kani::any();
        // CHALLENGE 22 assumption 4: valid UTF-8 input.
        kani::assume(verifier_utf8_valid(&buf, BYTES));
        kani::cover(true, "C22-A24: harness_chars_advance_by_eight_chunks assumption admitted");
        // SAFETY: the input predicate specifies a valid UTF-8 origin.
        let s = unsafe { from_utf8_unchecked(&buf[..BYTES]) };
        let n: usize = kani::any();
        // INPUT DOMAIN: this bounded request partition only.
        kani::assume(n > BYTES);
        kani::cover(true, "C22-A25: harness_chars_advance_by_eight_chunks assumption admitted");
        // Independent 16-byte counting blocks keep the reference's adder
        // chains smaller than a 256-step sum. The real target scans 32-byte
        // chunks. Every local upper bound below is checked, never assumed.
        let mut rank = 0u16;
        for block in 0..BYTES / 16 {
            let mut in_block = 0u8;
            for offset in 0..16 {
                let index = block * 16 + offset;
                in_block += u8::from(!utf8_is_cont_byte(s.as_bytes()[index]));
                assert!(usize::from(in_block) <= offset + 1);
            }
            rank += u16::from(in_block);
            assert!(usize::from(rank) <= (block + 1) * 16);
        }
        let count = usize::from(rank);
        let mut iter = s.chars();
        let result = iter.advance_by(n); // real target, no stubs
        verifier_assert_str_range(s, iter.as_str(), BYTES, BYTES);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().get(), n - count);
        kani::cover(n == BYTES + 1, "eight chunks: minimum request");
        kani::cover(n == usize::MAX, "eight chunks: maximum usize request");
        kani::cover(count == BYTES, "eight chunks: 256 ASCII scalars");
        kani::cover(count == BYTES / 4, "eight chunks: all four-byte scalars");
        kani::cover(true, "C22-END: harness_chars_advance_by_eight_chunks completed");
    }

    // An independently computed byte-prefix rank table. Checked local
    // UTF-8 step facts expose the relation between a boundary and its next
    // scalar before the real target runs; they are not assumptions or stubs.
    fn assert_advance_by_block_rank<const CAP: usize>(s: &str, n: usize) -> (usize, usize) {
        assert!(CAP <= MAX_BYTES && s.len() <= CAP);
        let mut ranks = [0u16; MAX_BYTES + 1];
        for block in 0..CAP.div_ceil(16) {
            for offset in 0..16 {
                let index = block * 16 + offset;
                if index >= s.len() {
                    break;
                }
                ranks[index + 1] = ranks[index]
                    + u16::from(!utf8_is_cont_byte(s.as_bytes()[index]));
                assert!(usize::from(ranks[index + 1]) <= index + 1);
            }
        }
        for block in 0..CAP.div_ceil(16) {
            for offset in 0..16 {
                let index = block * 16 + offset;
                if index >= s.len() {
                    break;
                }
                if s.is_char_boundary(index) {
                    let width = utf8_char_width(s.as_bytes()[index]) as usize;
                    assert!(width > 0 && width <= 4 && width <= s.len() - index);
                    assert!(s.is_char_boundary(index + width));
                    assert_eq!(ranks[index + width], ranks[index] + 1);
                }
            }
        }

        let count = usize::from(ranks[s.len()]);
        let mut iter = s.chars();
        let result = iter.advance_by(n); // real target, no stubs
        let remaining = iter.as_str();
        let position = verifier_slice_offset(s, remaining);
        assert!(position <= s.len());
        verifier_assert_str_range(s, remaining, position, s.len());
        assert_eq!(usize::from(ranks[position]), n.min(count));
        if n <= count {
            assert!(result.is_ok());
        } else {
            assert_eq!(result.unwrap_err().get(), n - count);
        }
        (position, count)
    }

    // Complement the retained 0..=40-byte complete-request proof with
    // explicitly new extents. The guard selects an input length domain;
    // no request or target-output condition is used as a filter.
    #[kani::proof]
    #[kani::unwind(34)]
    fn harness_chars_advance_by_extended_counts() {
        const BYTES: usize = 48;
        let buf: [u8; BYTES + UTF8_PAD] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        if s.len() <= 40 {
            return;
        }
        let n: usize = kani::any();
        let (position, _) = assert_advance_by_window_rank(s, 0, s.len(), n);
        kani::cover(
            n == 41 && s.len() == BYTES - 1 && position < s.len(),
            "extended counts: new length and request retain tail",
        );
        kani::cover(
            n == 33 && s.len() == BYTES
                && !s.is_char_boundary(32)
                && !s.is_char_boundary(33)
                && !s.is_char_boundary(34)
                && position < s.len(),
            "extended counts: three continuation bytes then scalar tail",
        );
        kani::cover(
            n == BYTES + 1 && s.len() == BYTES && position == s.len(),
            "extended counts: exact shortage beyond byte capacity",
        );
        kani::cover(true, "C22-END: harness_chars_advance_by_extended_counts completed");
    }

    // A bounded view constructor, not a filter on iterator outputs. Any
    // desired boundary window of at most LIMIT bytes is represented by
    // choosing that same window before this constructor (it is unchanged).
    fn verifier_utf8_prefix<const LIMIT: usize>(s: &str) -> &str {
        let mut end = s.len().min(LIMIT);
        for _ in 0..3 {
            if s.is_char_boundary(end) {
                break;
            }
            assert!(end > 0);
            end -= 1;
        }
        assert!(end <= LIMIT && end <= s.len());
        assert!(s.is_char_boundary(end));
        &s[..end]
    }

    #[kani::proof]
    #[kani::unwind(34)]
    fn harness_chars_advance_by_window_rank() {
        const BYTES: usize = 256;
        const WINDOW_BYTES: usize = 8;
        let buf: [u8; BYTES + UTF8_PAD] = kani::any();
        let s = verifier_nondet_utf8(&buf);
        let (front, back) = verifier_nondet_window(s);
        let selected = &s[front..back];
        let view = verifier_utf8_prefix::<WINDOW_BYTES>(selected);
        verifier_assert_str_range(s, view, front, front + view.len());
        let n: usize = kani::any();
        let (position, _) = assert_advance_by_block_rank::<WINDOW_BYTES>(view, n);
        assert!(front + position <= back);
        kani::cover(
            s.len() == BYTES && front > 0 && back < s.len()
                && n == 7 && position < view.len(),
            "window rank: interior large-allocation success",
        );
        kani::cover(
            s.len() == BYTES && front > 0 && front + view.len() < s.len()
                && !view.is_empty() && n == usize::MAX,
            "window rank: maximum request ends inside parent allocation",
        );
        kani::cover(
            view.is_empty() && front > 0 && front < s.len() && n > 0,
            "window rank: empty interior shortage",
        );
        kani::cover(
            selected.len() > WINDOW_BYTES && view.len() + 3 == WINDOW_BYTES,
            "window rank: view limit crosses three continuation bytes",
        );
        kani::cover(true, "C22-END: harness_chars_advance_by_window_rank completed");
    }
}
