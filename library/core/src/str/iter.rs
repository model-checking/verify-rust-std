//! Iterators for `str` methods.

use safety::requires;

use super::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};
use super::validations::{next_code_point, next_code_point_reverse};
use super::{
    BytesIsNotEmpty, CharEscapeDebugContinue, CharEscapeDefault, CharEscapeUnicode,
    IsAsciiWhitespace, IsNotEmpty, IsWhitespace, LinesMap, UnsafeBytesToStr, from_utf8_unchecked,
};
use crate::fmt::{self, Write};
use crate::iter::{
    Chain, Copied, Filter, FlatMap, Flatten, FusedIterator, Map, TrustedLen, TrustedRandomAccess,
    TrustedRandomAccessNoCoerce,
};
#[cfg(kani)]
use crate::kani;
use crate::num::NonZero;
use crate::ops::Try;
use crate::slice::{self, Split as SliceSplit};
use crate::{char as char_mod, option};

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
        // `(len + 3)` can't overflow, because we know that the `slice::Iter`
        // belongs to a slice in memory which has a maximum length of
        // `isize::MAX` (that's well below `usize::MAX`).
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
        Some(unsafe { crate::str::from_utf8_unchecked(&self.inner.iter.iter.v) })
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
        // `(len + 2)` can't overflow, because we know that the `slice::Iter`
        // belongs to a slice in memory which has a maximum length of
        // `isize::MAX` (that's well below `usize::MAX`)
        if self.extra == 0 {
            (len.div_ceil(3), Some(len))
        } else {
            // We're in the middle of a surrogate pair, so add the remaining
            // surrogate to the bounds.
            (len.div_ceil(3) + 1, Some(len + 1))
        }
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl FusedIterator for EncodeUtf16<'_> {}

/// The return type of [`str::escape_debug`].
#[stable(feature = "str_escape", since = "1.34.0")]
#[derive(Clone, Debug)]
pub struct EscapeDebug<'a> {
    pub(super) inner: Chain<
        Flatten<option::IntoIter<char_mod::EscapeDebug>>,
        FlatMap<Chars<'a>, char_mod::EscapeDebug, CharEscapeDebugContinue>,
    >,
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
pub mod verify {
    use super::super::pattern::verify::{
        PAD, any_char_searcher, any_utf8, cs_finger, cs_finger_back, cs_needle, type_invariant_cs,
        utf8_local,
    };
    use super::super::validations::{utf8_char_width, utf8_is_cont_byte};
    use super::*;

    // =================================================================
    // Challenge 22: verify safety of str iter functions.
    //
    // Every harness runs the real, unmodified iterator code; no product
    // code path is compiled out under Kani. The proofs are unbounded in
    // the two dimensions the challenge cares about:
    //
    //   - String length. The haystack is a symbolic-length slice of an
    //     arbitrary byte array constrained to valid UTF-8 by a loop-free
    //     byte-table predicate (`pattern::verify::any_utf8`); every valid
    //     UTF-8 string of at most HAY_MAX bytes — contents, length and
    //     character widths all symbolic — is one input. HAY_MAX is the
    //     size of the symbolic backing allocation, a CBMC memory-model
    //     parameter (as `ARR_SIZE` in
    //     `str::validations::verify::check_run_utf8_validation` and
    //     `HAY_MAX` in `str::pattern::verify`); no loop is unwound to it.
    //   - Iterator state. Following the Challenge 20 methodology, each
    //     iterator type has a type invariant `C`; a base-case harness
    //     shows the constructors establish `C`, and every method harness
    //     starts from an *arbitrary* `C`-satisfying state (a superset of
    //     the states any call sequence reaches), runs the method, asserts
    //     the safety facts the unsafe blocks rely on (`str::get_unchecked`
    //     only checks bounds, so char-boundary-ness of every produced
    //     index and slice is asserted explicitly) and re-asserts `C`.
    //
    // The pattern searchers. The `SplitInternal`/`MatchesInternal`/
    // `MatchIndicesInternal` bodies contain no loops; every loop they can
    // reach is inside `CharSearcher::next_match`/`next_match_back`
    // (`str::pattern`). Challenge 22 assumption 2 allows assuming the
    // safety and functional correctness of everything in `pattern.rs`;
    // these harnesses assume strictly less than that: the two methods are
    // replaced (`#[kani::stub_verified]`) by their *function contract*,
    // which is the `Searcher` trait's documented guarantee (indices on
    // char boundaries) plus the struct's documented finger invariant, is
    // attached to the real, byte-identical method bodies, and is checked
    // against those bodies by `pattern::verify::verify_cs_next_match`/
    // `verify_cs_next_match_back` (`#[kani::proof_for_contract]`). Under
    // `stub_verified` each call site asserts the contract's precondition
    // (`C` for the searcher) and assumes its postcondition; nothing about
    // boundaries is `kani::assume`d by these harnesses. Lifting the
    // searcher loops themselves with loop contracts is not possible with
    // the pinned Kani: the slice comparison inside them lowers to CBMC's
    // builtin `memcmp`, whose locals fail the loop-contract assigns check,
    // and neither the `compare_bytes` intrinsic ("invalid stub: function
    // does not have a body") nor `<[u8] as PartialEq>::eq` ("unable to
    // find implementation ... for [u8]") can be stubbed around it. The
    // contract proofs in `pattern::verify` therefore keep Challenge 20's
    // bounded haystack; that bound is the one accepted limitation of
    // this suite and it lives entirely inside Challenge 20's scope.
    //
    // `Chars::advance_by` is the only target function with loops. Its
    // harness is unbounded in string length and bounded only in the
    // advance count `n` (`ADVANCE_MAX`); every unwind bound derives from
    // `ADVANCE_MAX` and the constant chunk size, never from the string
    // length. See `check_chars_advance_by` for why loop contracts cannot
    // be applied to those loops with the pinned Kani.
    //
    // Harness-writing rules (both consequences of CI's `-Z loop-contracts`):
    // never filter inputs through `from_utf8` (its loop invariants make
    // the result unreliable), and never reach a `#[safety::loop_invariant]`
    // (`from_utf8`, `is_ascii`, `chars().count()`, ...) from a harness,
    // which silently switches it into loop-contract mode. Equality of
    // string slices is checked by pointer and length (`same_str`) rather
    // than `==`, which lowers to `memcmp` over the whole slice.
    // =================================================================

    /// Maximum haystack length in bytes: the size of the symbolic backing
    /// allocation, not a loop bound (see the module comment). Haystack
    /// lengths range over `0..=HAY_MAX`; 256 keeps every harness within
    /// a few minutes under CI's flags (at 1000 the loop-free harnesses
    /// take about 2 minutes each run alone, ~11x the time at 256, and
    /// `check_chars_advance_by` did not finish within an hour).
    // TODO: HAY_MAX can be much larger with cbmc argument `--arrays-uf-always`
    const HAY_MAX: usize = 256;
    /// Size of the backing array behind a `HAY_MAX`-byte haystack.
    const HAY_ARR: usize = HAY_MAX + PAD;

    /// An arbitrary haystack: a valid UTF-8 string of symbolic length
    /// `0..=N - PAD` (contents, length and character widths symbolic),
    /// via the byte-table input model shared with `str::pattern::verify`
    /// (`utf8_local`/`any_utf8`; see there for why `from_utf8` cannot be
    /// the filter).
    fn any_haystack<const N: usize>(arr: &[u8; N]) -> &str {
        let s = any_utf8(arr);
        kani::cover(s.len() == N - PAD, "a haystack of the maximum length");
        s
    }

    /// Identity of two string slices (same address and length). Used
    /// instead of `==`, which lowers to `memcmp` over the whole slice.
    fn same_str(a: &str, b: &str) -> bool {
        a.as_ptr() == b.as_ptr() && a.len() == b.len()
    }

    /// Byte offset of `sub` inside `s`; `sub` must be a subslice of `s`.
    fn offset_in(s: &str, sub: &str) -> usize {
        sub.as_ptr().addr() - s.as_ptr().addr()
    }

    /// An arbitrary in-bounds char-boundary window `k..m` of `s`.
    fn any_window(s: &str) -> (usize, usize) {
        let k: usize = kani::any();
        let m: usize = kani::any();
        kani::assume(k <= m && m <= s.len());
        kani::assume(s.is_char_boundary(k) && s.is_char_boundary(m));
        (k, m)
    }

    /// The window `k..m` of `s` as returned by `any_window`.
    fn window(s: &str, k: usize, m: usize) -> &str {
        // SAFETY: `any_window` assumed `k <= m <= s.len()` and that both
        // are char boundaries.
        unsafe { s.get_unchecked(k..m) }
    }

    // ------------------------------------------------------------------
    // Chars
    //
    // Type invariant: the iterator's bytes are a char-boundary window of
    // a valid UTF-8 string (the `str` invariant `Chars` documents). Every
    // state reachable by `next`/`next_back`/`advance_by` from `s.chars()`
    // is such a window, and every window is reachable as
    // `s[k..m].chars()`, so the harnesses start from an arbitrary window.
    // ------------------------------------------------------------------

    /// `Chars::next`: the real `next_code_point` (whose
    /// `char::from_u32_unchecked` result Kani checks for validity) on an
    /// arbitrary window; the consumed prefix is one whole character.
    #[kani::proof]
    pub fn check_chars_next() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let (k, m) = any_window(s);
        let w = window(s, k, m);
        let mut it = w.chars();
        match it.next() {
            Some(c) => {
                let rest = it.as_str();
                assert!(rest.len() + c.len_utf8() == w.len());
                assert!(offset_in(s, rest) == k + c.len_utf8());
                assert!(s.is_char_boundary(k + c.len_utf8()));
                kani::cover(c.len_utf8() == 1, "1-byte char consumed");
                kani::cover(c.len_utf8() == 2, "2-byte char consumed");
                kani::cover(c.len_utf8() == 3, "3-byte char consumed");
                kani::cover(c.len_utf8() == 4, "4-byte char consumed");
            }
            None => {
                assert!(w.is_empty());
                kani::cover(true, "empty window");
            }
        }
    }

    /// `Chars::next_back`: the real `next_code_point_reverse` on an
    /// arbitrary window; the consumed suffix is one whole character.
    #[kani::proof]
    pub fn check_chars_next_back() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let (k, m) = any_window(s);
        let w = window(s, k, m);
        let mut it = w.chars();
        match it.next_back() {
            Some(c) => {
                let rest = it.as_str();
                assert!(rest.len() + c.len_utf8() == w.len());
                assert!(offset_in(s, rest) == k);
                assert!(s.is_char_boundary(m - c.len_utf8()));
                kani::cover(c.len_utf8() == 1, "1-byte char consumed");
                kani::cover(c.len_utf8() == 2, "2-byte char consumed");
                kani::cover(c.len_utf8() == 3, "3-byte char consumed");
                kani::cover(c.len_utf8() == 4, "4-byte char consumed");
            }
            None => {
                assert!(w.is_empty());
                kani::cover(true, "empty window");
            }
        }
    }

    /// `Chars::as_str` (`from_utf8_unchecked` over the iterator's bytes)
    /// on an arbitrary window, and again after consuming from both ends.
    #[kani::proof]
    pub fn check_chars_as_str() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let (k, m) = any_window(s);
        let w = window(s, k, m);
        let mut it = w.chars();
        assert!(same_str(it.as_str(), w));
        let front = it.next().map_or(0, char::len_utf8);
        let back = it.next_back().map_or(0, char::len_utf8);
        let rest = it.as_str();
        assert!(offset_in(s, rest) == k + front);
        assert!(rest.len() + front + back == w.len());
        assert!(s.is_char_boundary(k + front) && s.is_char_boundary(m - back));
        kani::cover(front > 0 && back > 0, "consumed from both ends");
    }

    /// Advance-count bound of `check_chars_advance_by`, the per-character
    /// path of `Chars::advance_by` (counts below `CHUNK_SIZE` never enter
    /// the chunk-skip phase).
    const ADVANCE_MAX: usize = 8;
    /// Backing-array size of `check_chars_advance_by`. Its per-character
    /// loop is unwound, so unlike the loop-free harnesses its memory use
    /// grows with the array (measured peak RSS: 4.8 GB at HAY_MAX, 1.8 GB
    /// at 128); 128 keeps it inside the budget of CI's macOS runners.
    /// Like HAY_MAX it is the size of the symbolic backing allocation,
    /// not a loop bound.
    const ADVANCE_HAY_MAX: usize = 128;
    const ADVANCE_ARR: usize = ADVANCE_HAY_MAX + PAD;
    /// Advance-count range of `check_chars_advance_by_chunked`, the
    /// chunk-skip path: at least 33 so the chunk-skip loop body runs (it
    /// runs while more than 32 characters remain to be skipped and a full
    /// 32-byte chunk is available), at most 40 so it runs exactly once (a
    /// 32-byte chunk of valid UTF-8 holds at least 8 characters, so
    /// afterwards at most 32 remain and the guard fails).
    const CHUNKED_MIN: usize = 33;
    const CHUNKED_MAX: usize = 40;
    /// String length of `check_chars_advance_by_chunked`: one full 32-byte
    /// chunk plus a 16-byte tail. The length is a compile-time constant
    /// (the contents are fully symbolic) because CBMC only drops the
    /// unrolled copies of the chunk-skip loop when the chunk iterator's
    /// end is known at unwinding time: each copy of that loop body reads
    /// a whole chunk at a symbolic offset and runs two 32-iteration
    /// loops, and with a symbolic string length -- or a symbolic start of
    /// a fixed-length window -- the 33 copies the unwind bound implies
    /// exceed 11 GB of RSS (measured). So the chunk-skip path is verified for every
    /// 48-byte string; the per-character path (`check_chars_advance_by`)
    /// for arbitrary windows of strings of arbitrary length.
    const CHUNKED_WINDOW: usize = 48;
    const _: () = assert!(ADVANCE_MAX <= WALK_MAX && CHUNKED_MAX <= WALK_MAX);
    /// Number of unrolled steps in `walk`.
    const WALK_MAX: usize = 40;

    /// Reference for `advance_by`: the position reached by skipping up to
    /// `n <= WALK_MAX` characters from `off` (never past `m`) and the
    /// number of characters skipped. Loop-free: `WALK_MAX` unrolled
    /// conditional `utf8_char_width` steps, so it adds nothing to the
    /// harness's unwind bound.
    fn walk(bytes: &[u8], off: usize, m: usize, n: usize) -> (usize, usize) {
        let mut off = off;
        let mut steps = 0;
        macro_rules! step {
            () => {
                if steps < n && off < m {
                    off += utf8_char_width(bytes[off]);
                    steps += 1;
                }
            };
        }
        macro_rules! steps8 {
            () => {
                step!();
                step!();
                step!();
                step!();
                step!();
                step!();
                step!();
                step!();
            };
        }
        // WALK_MAX = 5 * 8 steps
        steps8!();
        steps8!();
        steps8!();
        steps8!();
        steps8!();
        (off, steps)
    }

    /// Shared body of the two `advance_by` harnesses: the real
    /// `Chars::advance_by` on the window `k..m` of `s` for the advance
    /// count `n`, checked against `walk`. The remainder must start exactly
    /// where the walk ends (and so on a char boundary); `Ok` iff `n`
    /// characters were available, otherwise `Err(n - characters)`.
    fn check_advance_by(s: &str, k: usize, m: usize, n: usize) -> (usize, usize) {
        let bytes = s.as_bytes();
        let (off, steps) = walk(bytes, k, m, n);

        let mut it = window(s, k, m).chars();
        let res = it.advance_by(n);
        let rest = it.as_str();
        assert!(offset_in(s, rest) == off);
        assert!(rest.len() == m - off);
        assert!(s.is_char_boundary(off));
        match res {
            Ok(()) => {
                assert!(steps == n);
                kani::cover(n > 0, "advanced by a nonzero count");
            }
            Err(rem) => {
                assert!(off == m);
                assert!(rem.get() == n - steps);
                kani::cover(true, "ran out of characters");
            }
        }
        (off, steps)
    }

    /// `Chars::advance_by`, per-character path: the real per-character
    /// loop on an arbitrary window of a string of arbitrary length, for
    /// counts up to `ADVANCE_MAX`. The unwind bound follows from
    /// `ADVANCE_MAX` alone (the loop decrements `remainder` each
    /// iteration); the string length plays no part in it.
    ///
    /// Loop contracts are not used on `advance_by`'s loops because, with
    /// the pinned Kani, the invariant of a loop that advances a
    /// `slice::Iter` through a method call cannot be stated: loop-modifies
    /// inference misses fields written by callees (Kani reference, loop
    /// contracts, limitations), and after the iterator is havocked its
    /// `len()`/`as_slice()` trip the same-allocation check in Kani's
    /// `ptr_offset_from` model before an invariant could re-pin it.
    #[kani::proof]
    #[kani::unwind(9)]
    pub fn check_chars_advance_by() {
        let arr: [u8; ADVANCE_ARR] = kani::any();
        let s = any_haystack(&arr);
        let (k, m) = any_window(s);
        let n: usize = kani::any();
        kani::assume(n <= ADVANCE_MAX);
        let (off, _) = check_advance_by(s, k, m, n);
        kani::cover(n > 0 && off - k == 4 * n, "skipped only 4-byte characters");
    }

    /// `Chars::advance_by`, chunk-skip path: the real chunk-skip loop (its
    /// body runs exactly once for these counts, see `CHUNKED_MAX`), the
    /// trailing-continuation loop and the per-character loop, on a
    /// `CHUNKED_WINDOW`-byte string of arbitrary contents. The unwind
    /// bound is 34: the two loops over a chunk run 32 times, the
    /// per-character loop at most 16 times (the bytes left after the
    /// chunk), the trailing-continuation loop at most 3 (a character has
    /// at most 3 continuation bytes); CBMC's unwinding assertions check
    /// these counts rather than assume them.
    #[kani::proof]
    #[kani::unwind(34)]
    pub fn check_chars_advance_by_chunked() {
        let arr: [u8; CHUNKED_WINDOW + PAD] = kani::any();
        kani::assume(utf8_local(&arr, CHUNKED_WINDOW));
        // SAFETY: `utf8_local` is the byte-table definition of UTF-8
        // validity of `arr[..CHUNKED_WINDOW]` (see `pattern::verify`).
        let s = unsafe { from_utf8_unchecked(&arr[..CHUNKED_WINDOW]) };
        let bytes = s.as_bytes();
        let n: usize = kani::any();
        kani::assume(CHUNKED_MIN <= n && n <= CHUNKED_MAX);
        check_advance_by(s, 0, CHUNKED_WINDOW, n);
        kani::cover(
            utf8_is_cont_byte(bytes[32]),
            "trailing-continuation loop skipped a byte after the chunk",
        );
        kani::cover(
            bytes[0] >= 0xF0
                && bytes[4] >= 0xF0
                && bytes[8] >= 0xF0
                && bytes[12] >= 0xF0
                && bytes[16] >= 0xF0
                && bytes[20] >= 0xF0
                && bytes[24] >= 0xF0
                && bytes[28] >= 0xF0,
            "chunk of eight 4-byte characters (the fewest a chunk can hold)",
        );
        kani::cover(bytes[0] < 0x80 && bytes[31] < 0x80, "chunk starting and ending in ASCII");
    }

    // ------------------------------------------------------------------
    // SplitInternal<'_, char>
    //
    // Type invariant `C`: the searcher satisfies its own invariant, the
    // unconsumed range `start..end` is a char-boundary range of the
    // haystack, and the searcher's fingers lie within it
    // (`start <= finger` and `finger_back <= end`). The constructors
    // establish it (`check_split_constructors_establish_invariant`); every
    // reachable state in fact has `start == finger`, and `finger_back ==
    // end` except after `next_back_inclusive` (which leaves `end` at the
    // match end while `finger_back` is at its start), so the arbitrary
    // `C`-states below are a superset of the reachable ones.
    // ------------------------------------------------------------------

    /// Type invariant `C` of `SplitInternal<'_, char>`.
    fn split_invariant(it: &SplitInternal<'_, char>) -> bool {
        let h = it.matcher.haystack();
        type_invariant_cs(&it.matcher)
            && it.start <= cs_finger(&it.matcher)
            && cs_finger_back(&it.matcher) <= it.end
            && it.end <= h.len()
            && h.is_char_boundary(it.start)
            && h.is_char_boundary(it.end)
    }

    /// An arbitrary `C`-satisfying `SplitInternal` over `s` with a
    /// symbolic `char` pattern and symbolic flags.
    fn any_split(s: &str) -> SplitInternal<'_, char> {
        let it = SplitInternal {
            start: kani::any(),
            end: kani::any(),
            matcher: any_char_searcher(s),
            allow_trailing_empty: kani::any(),
            finished: kani::any(),
        };
        kani::assume(split_invariant(&it));
        it
    }

    /// Snapshot of the parts of a `SplitInternal` state that a method must
    /// leave alone, checked after the call.
    struct SplitFrame {
        start: usize,
        end: usize,
        finger: usize,
        finger_back: usize,
        needle: char,
    }

    fn split_frame(it: &SplitInternal<'_, char>) -> SplitFrame {
        SplitFrame {
            start: it.start,
            end: it.end,
            finger: cs_finger(&it.matcher),
            finger_back: cs_finger_back(&it.matcher),
            needle: cs_needle(&it.matcher),
        }
    }

    /// `part` is the char-boundary range `lo..hi` of `s` (by address).
    fn assert_is_range(s: &str, part: &str, lo: usize, hi: usize) {
        assert!(offset_in(s, part) == lo);
        assert!(lo + part.len() == hi);
        assert!(hi <= s.len());
        assert!(s.is_char_boundary(lo) && s.is_char_boundary(hi));
    }

    /// Criterion 1: `split`, `split_terminator` and `split_inclusive`
    /// establish `C`.
    #[kani::proof]
    pub fn check_split_constructors_establish_invariant() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let p: char = kani::any();
        let a = s.split(p).0;
        assert!(split_invariant(&a) && a.start == 0 && a.end == s.len() && !a.finished);
        let b = s.split_terminator(p).0;
        assert!(split_invariant(&b) && b.start == 0 && b.end == s.len() && !b.finished);
        let c = s.split_inclusive(p).0;
        assert!(split_invariant(&c) && c.start == 0 && c.end == s.len() && !c.finished);
    }

    /// `SplitInternal::next` from an arbitrary `C`-state: the fragment is
    /// `start..a` for the match `a..b` the searcher contract returns, the
    /// new `start` is `b`, and on exhaustion `get_end` yields
    /// `start..end` at most once.
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match)]
    pub fn check_split_next() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it = any_split(s);
        let f = split_frame(&it);
        let finished = it.finished;
        match it.next() {
            Some(part) => {
                assert!(!finished);
                if it.finished {
                    assert_is_range(s, part, f.start, f.end);
                    assert!(it.start == f.start);
                    kani::cover(true, "next: trailing fragment from get_end");
                } else {
                    let a = f.start + part.len();
                    assert_is_range(s, part, f.start, a);
                    assert!(a >= f.finger);
                    assert!(it.start == a + f.needle.len_utf8());
                    assert!(it.start == cs_finger(&it.matcher));
                    kani::cover(part.is_empty(), "next: empty fragment between adjacent matches");
                    kani::cover(!part.is_empty(), "next: nonempty fragment");
                }
            }
            None => {
                assert!(it.finished);
                kani::cover(finished, "next: already finished");
                kani::cover(!finished, "next: exhausted without a trailing fragment");
            }
        }
        assert!(split_invariant(&it));
        assert!(it.end == f.end);
        assert!(cs_finger_back(&it.matcher) == f.finger_back);
        assert!(cs_needle(&it.matcher) == f.needle);
        assert!(same_str(it.matcher.haystack(), s));
    }

    /// `SplitInternal::next_inclusive` from an arbitrary `C`-state: the
    /// fragment is `start..b` and the new `start` is `b`.
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match)]
    pub fn check_split_next_inclusive() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it = any_split(s);
        let f = split_frame(&it);
        let finished = it.finished;
        match it.next_inclusive() {
            Some(part) => {
                assert!(!finished);
                if it.finished {
                    assert_is_range(s, part, f.start, f.end);
                    assert!(it.start == f.start);
                    kani::cover(true, "next_inclusive: trailing fragment from get_end");
                } else {
                    let b = f.start + part.len();
                    assert_is_range(s, part, f.start, b);
                    assert!(part.len() >= f.needle.len_utf8());
                    assert!(it.start == b);
                    assert!(it.start == cs_finger(&it.matcher));
                    kani::cover(
                        part.len() == f.needle.len_utf8(),
                        "next_inclusive: fragment is just the separator",
                    );
                    kani::cover(
                        part.len() > f.needle.len_utf8(),
                        "next_inclusive: fragment with content before the separator",
                    );
                }
            }
            None => {
                assert!(it.finished);
                kani::cover(finished, "next_inclusive: already finished");
                kani::cover(!finished, "next_inclusive: exhausted without a trailing fragment");
            }
        }
        assert!(split_invariant(&it));
        assert!(it.end == f.end);
        assert!(cs_finger_back(&it.matcher) == f.finger_back);
        assert!(cs_needle(&it.matcher) == f.needle);
        assert!(same_str(it.matcher.haystack(), s));
    }

    /// `SplitInternal::next_back` from an arbitrary `C`-state, including
    /// the `allow_trailing_empty == false` path that first calls itself
    /// to drop an empty trailing fragment: every fragment is a
    /// char-boundary sub-range of the unconsumed range, `end` only
    /// decreases, and `start` is untouched.
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match_back)]
    pub fn check_split_next_back() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it = any_split(s);
        let f = split_frame(&it);
        let finished = it.finished;
        let trailing = it.allow_trailing_empty;
        match it.next_back() {
            Some(part) => {
                assert!(!finished);
                let lo = offset_in(s, part);
                let hi = lo + part.len();
                assert!(f.start <= lo && hi <= f.end);
                assert!(s.is_char_boundary(lo) && s.is_char_boundary(hi));
                if it.finished {
                    // the final fragment `start..end` (of the range as it
                    // was when the searcher ran out of matches)
                    assert!(lo == f.start);
                    kani::cover(true, "next_back: final fragment");
                } else {
                    // `b..end` for a match `a..b` at or after `finger`;
                    // `end` becomes `a`
                    assert!(lo > f.finger);
                    assert!(it.end == cs_finger_back(&it.matcher));
                    assert!(it.end + f.needle.len_utf8() == lo);
                    kani::cover(part.is_empty(), "next_back: empty fragment");
                    kani::cover(!part.is_empty(), "next_back: nonempty fragment");
                }
                kani::cover(
                    !trailing && !part.is_empty(),
                    "next_back: fragment returned with allow_trailing_empty == false",
                );
            }
            None => {
                assert!(it.finished);
                kani::cover(finished, "next_back: already finished");
                kani::cover(
                    !finished && !trailing,
                    "next_back: only an empty trailing fragment remained",
                );
            }
        }
        assert!(split_invariant(&it));
        assert!(it.start == f.start);
        assert!(it.end <= f.end);
        assert!(cs_finger(&it.matcher) == f.finger);
        assert!(cs_needle(&it.matcher) == f.needle);
        assert!(same_str(it.matcher.haystack(), s));
    }

    /// `SplitInternal::next_back_inclusive` from an arbitrary `C`-state:
    /// as `next_back`, but `end` becomes the match end `b` (so
    /// `finger_back < end` afterwards, which `C` allows).
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match_back)]
    pub fn check_split_next_back_inclusive() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it = any_split(s);
        let f = split_frame(&it);
        let finished = it.finished;
        let trailing = it.allow_trailing_empty;
        match it.next_back_inclusive() {
            Some(part) => {
                assert!(!finished);
                let lo = offset_in(s, part);
                let hi = lo + part.len();
                assert!(f.start <= lo && hi <= f.end);
                assert!(s.is_char_boundary(lo) && s.is_char_boundary(hi));
                if it.finished {
                    assert!(lo == f.start);
                    kani::cover(true, "next_back_inclusive: final fragment");
                } else {
                    assert!(it.end == lo);
                    assert!(cs_finger_back(&it.matcher) + f.needle.len_utf8() == lo);
                    kani::cover(part.is_empty(), "next_back_inclusive: empty fragment");
                    kani::cover(!part.is_empty(), "next_back_inclusive: nonempty fragment");
                }
                kani::cover(
                    !trailing && !part.is_empty(),
                    "next_back_inclusive: fragment returned with allow_trailing_empty == false",
                );
            }
            None => {
                assert!(it.finished);
                kani::cover(finished, "next_back_inclusive: already finished");
                kani::cover(
                    !finished && !trailing,
                    "next_back_inclusive: only an empty trailing fragment remained",
                );
            }
        }
        assert!(split_invariant(&it));
        assert!(it.start == f.start);
        assert!(it.end <= f.end);
        assert!(cs_finger(&it.matcher) == f.finger);
        assert!(cs_needle(&it.matcher) == f.needle);
        assert!(same_str(it.matcher.haystack(), s));
    }

    /// `SplitInternal::get_end` from an arbitrary `C`-state, called
    /// directly: on an unfinished iterator it finishes it and returns
    /// `start..end` iff a trailing empty fragment is allowed or the range
    /// is nonempty; on a finished one it is a no-op returning `None`.
    #[kani::proof]
    pub fn check_split_get_end() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it = any_split(s);
        let f = split_frame(&it);
        let finished = it.finished;
        let trailing = it.allow_trailing_empty;
        let res = it.get_end();
        assert!(it.finished);
        match res {
            Some(part) => {
                assert!(!finished);
                assert!(trailing || f.end > f.start);
                assert_is_range(s, part, f.start, f.end);
                kani::cover(
                    trailing && part.is_empty(),
                    "get_end: empty trailing fragment allowed",
                );
                kani::cover(
                    !trailing && !part.is_empty(),
                    "get_end: nonempty fragment, trailing empty disallowed",
                );
            }
            None => {
                assert!(finished || (!trailing && f.end == f.start));
                kani::cover(finished, "get_end: already finished");
                kani::cover(!finished, "get_end: empty trailing fragment suppressed");
            }
        }
        assert!(split_invariant(&it));
        assert!(it.start == f.start && it.end == f.end);
        assert!(cs_finger(&it.matcher) == f.finger && cs_finger_back(&it.matcher) == f.finger_back);
    }

    /// `SplitInternal::remainder` from an arbitrary `C`-state: `None` iff
    /// finished, else `start..end`; the state is untouched.
    #[kani::proof]
    pub fn check_split_remainder() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let it = any_split(s);
        let f = split_frame(&it);
        match it.remainder() {
            Some(rem) => {
                assert!(!it.finished);
                assert_is_range(s, rem, f.start, f.end);
                kani::cover(rem.is_empty(), "remainder: empty");
                kani::cover(!rem.is_empty(), "remainder: nonempty");
            }
            None => {
                assert!(it.finished);
                kani::cover(true, "remainder: finished");
            }
        }
        assert!(split_invariant(&it));
        assert!(it.start == f.start && it.end == f.end);
    }

    // ------------------------------------------------------------------
    // MatchIndicesInternal / MatchesInternal
    //
    // Type invariant: the wrapped searcher satisfies its own invariant
    // (nothing else is stored). Arbitrary `C`-states are produced by
    // `any_char_searcher`.
    // ------------------------------------------------------------------

    /// `MatchIndicesInternal::next`: the returned index is the match
    /// start, a char boundary, and the slice is the match.
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match)]
    pub fn check_match_indices_next() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it: MatchIndicesInternal<'_, char> = MatchIndicesInternal(any_char_searcher(s));
        let (finger, finger_back, needle) =
            (cs_finger(&it.0), cs_finger_back(&it.0), cs_needle(&it.0));
        match it.next() {
            Some((i, m)) => {
                assert!(finger <= i);
                assert_is_range(s, m, i, i + needle.len_utf8());
                assert!(i + m.len() <= finger_back);
                assert!(cs_finger(&it.0) == i + m.len());
                kani::cover(m.len() > 1, "match_indices next: multibyte match");
                kani::cover(i > 0, "match_indices next: match after the start");
            }
            None => {
                assert!(cs_finger(&it.0) == finger_back);
                kani::cover(true, "match_indices next: no match");
            }
        }
        assert!(type_invariant_cs(&it.0));
        assert!(cs_finger_back(&it.0) == finger_back && cs_needle(&it.0) == needle);
        assert!(same_str(it.0.haystack(), s));
    }

    /// `MatchIndicesInternal::next_back`: as `next`, searching backwards.
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match_back)]
    pub fn check_match_indices_next_back() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it: MatchIndicesInternal<'_, char> = MatchIndicesInternal(any_char_searcher(s));
        let (finger, finger_back, needle) =
            (cs_finger(&it.0), cs_finger_back(&it.0), cs_needle(&it.0));
        match it.next_back() {
            Some((i, m)) => {
                assert!(finger <= i);
                assert_is_range(s, m, i, i + needle.len_utf8());
                assert!(i + m.len() <= finger_back);
                assert!(cs_finger_back(&it.0) == i);
                kani::cover(m.len() > 1, "match_indices next_back: multibyte match");
                kani::cover(
                    i + m.len() < finger_back,
                    "match_indices next_back: match before the end",
                );
            }
            None => {
                assert!(cs_finger_back(&it.0) == finger);
                kani::cover(true, "match_indices next_back: no match");
            }
        }
        assert!(type_invariant_cs(&it.0));
        assert!(cs_finger(&it.0) == finger && cs_needle(&it.0) == needle);
        assert!(same_str(it.0.haystack(), s));
    }

    /// `MatchesInternal::next`: the returned slice is the match.
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match)]
    pub fn check_matches_next() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it: MatchesInternal<'_, char> = MatchesInternal(any_char_searcher(s));
        let (finger, finger_back, needle) =
            (cs_finger(&it.0), cs_finger_back(&it.0), cs_needle(&it.0));
        match it.next() {
            Some(m) => {
                let i = offset_in(s, m);
                assert!(finger <= i);
                assert_is_range(s, m, i, i + needle.len_utf8());
                assert!(i + m.len() <= finger_back);
                assert!(cs_finger(&it.0) == i + m.len());
                kani::cover(m.len() > 1, "matches next: multibyte match");
            }
            None => {
                assert!(cs_finger(&it.0) == finger_back);
                kani::cover(true, "matches next: no match");
            }
        }
        assert!(type_invariant_cs(&it.0));
        assert!(cs_finger_back(&it.0) == finger_back && cs_needle(&it.0) == needle);
        assert!(same_str(it.0.haystack(), s));
    }

    /// `MatchesInternal::next_back`: as `next`, searching backwards.
    #[kani::proof]
    #[kani::stub_verified(crate::str::pattern::CharSearcher::next_match_back)]
    pub fn check_matches_next_back() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it: MatchesInternal<'_, char> = MatchesInternal(any_char_searcher(s));
        let (finger, finger_back, needle) =
            (cs_finger(&it.0), cs_finger_back(&it.0), cs_needle(&it.0));
        match it.next_back() {
            Some(m) => {
                let i = offset_in(s, m);
                assert!(finger <= i);
                assert_is_range(s, m, i, i + needle.len_utf8());
                assert!(i + m.len() <= finger_back);
                assert!(cs_finger_back(&it.0) == i);
                kani::cover(m.len() > 1, "matches next_back: multibyte match");
            }
            None => {
                assert!(cs_finger_back(&it.0) == finger);
                kani::cover(true, "matches next_back: no match");
            }
        }
        assert!(type_invariant_cs(&it.0));
        assert!(cs_finger(&it.0) == finger && cs_needle(&it.0) == needle);
        assert!(same_str(it.0.haystack(), s));
    }

    // ------------------------------------------------------------------
    // SplitAsciiWhitespace
    //
    // Type invariant: the inner `slice::Split`'s unconsumed slice `v` is a
    // char-boundary window of the string. `split_ascii_whitespace`
    // starts with the whole string; each `next` (`next_back`) cuts `v`
    // after (before) an ASCII-whitespace byte, which is a one-byte
    // character, so every reachable `v` is such a window, and every
    // window is one `C`-state.
    // ------------------------------------------------------------------

    /// `SplitAsciiWhitespace::remainder` (`from_utf8_unchecked` over `v`)
    /// on the fresh iterator and on an arbitrary `C`-state.
    #[kani::proof]
    pub fn check_split_ascii_whitespace_remainder() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let mut it = s.split_ascii_whitespace();
        assert!(it.remainder().is_some_and(|rem| same_str(rem, s)));
        let (k, m) = any_window(s);
        it.inner.iter.iter.v = window(s, k, m).as_bytes();
        it.inner.iter.iter.finished = kani::any();
        match it.remainder() {
            Some(rem) => {
                assert!(!it.inner.iter.iter.finished);
                assert_is_range(s, rem, k, m);
                kani::cover(!rem.is_empty(), "split_ascii_whitespace remainder: nonempty");
            }
            None => {
                assert!(it.inner.iter.iter.finished);
                kani::cover(true, "split_ascii_whitespace remainder: finished");
            }
        }
    }

    // ------------------------------------------------------------------
    // Bytes
    // ------------------------------------------------------------------

    /// Contract harness for `Bytes::__iterator_get_unchecked`: its
    /// `#[requires(idx < self.0.len())]` rules out UB in the body, for a
    /// `Bytes` over any window of a string of arbitrary length. Under
    /// CI's `--no-assert-contracts` a contract is only checked by a
    /// `proof_for_contract` harness.
    #[kani::proof_for_contract(Bytes::__iterator_get_unchecked)]
    pub fn check_bytes_iterator_get_unchecked() {
        let arr: [u8; HAY_ARR] = kani::any();
        let s = any_haystack(&arr);
        let (k, m) = any_window(s);
        let w = window(s, k, m);
        let mut bytes = w.bytes();
        let idx: usize = kani::any();
        let b = unsafe { bytes.__iterator_get_unchecked(idx) };
        assert!(b == w.as_bytes()[idx]);
        kani::cover(idx > 0, "bytes get_unchecked: index past the start");
    }
}
