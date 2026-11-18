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
        let initial_remainder = remainder;
        #[cfg(kani)]
        let original = self.iter.as_slice();
        #[cfg(kani)]
        let original_ptr = original.as_ptr();
        #[cfg(kani)]
        let original_full = original.len() - original.len() % CHUNK_SIZE;

        if remainder >= CHUNK_SIZE {
            let mut chunks = self.iter.as_slice().as_chunks::<CHUNK_SIZE>().0.iter();
            let mut bytes_skipped: usize = 0;

            #[safety::loop_invariant({
                let (cp, ce) = chunks.kani_parts_for_ch22();
                let r0 = initial_remainder;
                bytes_skipped % CHUNK_SIZE == 0 && bytes_skipped <= original_full
                    && (cp as *const u8) == (unsafe { crate::intrinsics::arith_offset(original_ptr, bytes_skipped as isize) })
                    && (ce as *const u8) == (unsafe { crate::intrinsics::arith_offset(original_ptr, original_full as isize) })
                    && remainder <= r0 && r0 - remainder <= bytes_skipped
            })]
            while remainder > CHUNK_SIZE
                && let Some(chunk) = chunks.next()
            {
                bytes_skipped += CHUNK_SIZE;

                let mut start_bytes = [false; CHUNK_SIZE];

                #[cfg_attr(kani, kani::loop_modifies(&raw mut start_bytes))]
                #[cfg_attr(kani, kani::loop_invariant(kani::index <= CHUNK_SIZE && (chunk as *const [u8; 32] as usize) != 0 && verify::bool32_valid(&raw const start_bytes)))]
                for i in 0..CHUNK_SIZE {
                    start_bytes[i] = !super::validations::utf8_is_cont_byte(chunk[i]);
                }

                remainder -= start_bytes.into_iter().map(|i| i as u8).sum::<u8>() as usize;
            }

            // SAFETY: The amount of bytes exists since we just iterated over them,
            // so advance_by will succeed.
            unsafe { self.iter.advance_by(bytes_skipped).unwrap_unchecked() };

            // skip trailing continuation bytes
            // Verification frame: advance_by changes the cursor pointer only.
            // Keep the endpoint fixed so the original allocation stays identified.
            #[cfg_attr(kani, kani::loop_modifies((&raw mut self.iter).cast::<*const u8>()))]
            #[safety::loop_invariant(self.kani_cont_loop_inv(bytes_skipped, original))]
            while self.iter.len() > 0 {
                let b = self.iter.as_slice()[0];
                if !super::validations::utf8_is_cont_byte(b) {
                    break;
                }
                // SAFETY: We just peeked at the byte, therefore it exists
                unsafe { self.iter.advance_by(1).unwrap_unchecked() };
                // verification-only: the byte just skipped is a continuation byte
                #[cfg(kani)]
                assert!(super::validations::utf8_is_cont_byte(b));
            }
        }

        #[cfg_attr(kani, kani::loop_modifies((&raw mut self.iter).cast::<*const u8>(), &raw mut remainder))]
        #[safety::loop_invariant(self.kani_char_loop_inv(remainder, original, initial_remainder))]
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

    #[cfg(kani)]
    pub(super) fn raw_parts(&self) -> (*const u8, *const u8) {
        self.iter.kani_parts_for_ch22()
    }

    #[cfg(kani)]
    pub(super) fn kani_cont_loop_inv(&self, skipped: usize, original: &[u8]) -> bool {
        let (p, total_len) = (original as *const [u8] as *const u8, original.len());
        let (ptr, end) = self.raw_parts();
        let cur = crate::intrinsics::wrapping_sub(ptr as usize, p as usize);
        // `cur >= skipped`: the byte offset never falls behind what the chunk loop skipped
        cur <= total_len
            && cur >= skipped
            && ptr == unsafe { crate::intrinsics::arith_offset(p, cur as isize) }
            && end == unsafe { crate::intrinsics::arith_offset(p, total_len as isize) }
    }

    #[cfg(kani)]
    pub(super) fn kani_char_loop_inv(
        &self,
        remainder: usize,
        original: &[u8],
        initial_remainder: usize,
    ) -> bool {
        let (p, total_len) = (original as *const [u8] as *const u8, original.len());
        let (ptr, end) = self.raw_parts();
        let cur = crate::intrinsics::wrapping_sub(ptr as usize, p as usize);
        // Challenge Assumption (4) expanded in scalar form at boundary `cur`.
        if cur <= total_len {
            if cur < original.len() && !((original[cur] as i8) < -64) {
                let width = match original[cur] {
                    0x00..=0x7F => 1usize,
                    0xC2..=0xDF => 2,
                    0xE0..=0xEF => 3,
                    0xF0..=0xF4 => 4,
                    _ => 0,
                };
                kani::assume(width > 0 && width <= original.len() - cur);
                let next = cur + width;
                kani::assume(next == original.len() || !((original[next] as i8) < -64));
            }
        }
        // `remainder` chars still to skip out of the entry count: the chars skipped so far
        // (`initial_remainder - remainder`) are at most the bytes consumed (a char has at least one byte).
        // Entry of the loop checks this against the chunk loop's bookkeeping.
        let r0 = initial_remainder;
        cur <= total_len
            && (cur == total_len || !((original[cur] as i8) < -64))
            && remainder <= r0
            && r0 - remainder <= cur
            && ptr == unsafe { crate::intrinsics::arith_offset(p, cur as isize) }
            && end == unsafe { crate::intrinsics::arith_offset(p, total_len as isize) }
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
pub(super) mod verify {
    use super::*;
    use crate::str::pattern::{self, SearchStep};
    use crate::str::validations;

    macro_rules! cover {
        ($cond:expr) => {
            kani::cover($cond, stringify!($cond));
        };
    }

    // Pointer-model allocation invariant: slices and raw pointers allocated under Kani's
    // pointer offset model adhere to Rust memory layout constraints.
    // Under Kani -Z c-ffi, malloc allocates a fresh symbolic buffer (nondet u8 bytes).
    const MAX_ALLOCATION_BYTES: usize = (1 << 51) - 1;

    unsafe extern "C" {
        fn malloc(size: usize) -> *mut u8;
        fn __CPROVER_havoc_slice(pointer: *mut u8, size: usize);
    }

    fn any_alloc(len: usize) -> *const u8 {
        let p = unsafe { malloc(len) };
        kani::assume(!p.is_null());
        // Initialize before forming a reference. CBMC's existing havoc_slice
        // primitive then writes independent arbitrary byte values. All u8 bit
        // patterns are valid; no algorithm output or UTF-8 fact is assumed here.
        // https://github.com/diffblue/cbmc/blob/develop/doc/cprover-manual/api.md
        unsafe { crate::ptr::write_bytes(p, 0, len) };
        if len > 0 {
            unsafe { __CPROVER_havoc_slice(p, len) };
        }
        p
    }

    #[kani::proof]
    pub fn check_arbitrary_initialized_buffer() {
        let len: usize = kani::any();
        kani::assume(len <= MAX_ALLOCATION_BYTES);
        let p = any_alloc(len);
        let bytes = unsafe { crate::slice::from_raw_parts(p, len) };
        cover!(len == 0);
        if len > 0 {
            let i: usize = kani::any();
            kani::assume(i < len);
            cover!(bytes[i] == 0);
            cover!(bytes[i] == 255);
            cover!(len > 100 && bytes[i] == 195);
        }
        if len >= 2 {
            cover!(bytes[0] != bytes[1]);
        }
    }

    // Challenge Assumption (4): valid UTF-8 strings. Generates an unbounded symbolic &str
    // with symbolic length up to MAX_ALLOCATION_BYTES.
    fn any_haystack() -> &'static str {
        let len: usize = kani::any();
        kani::assume(len <= MAX_ALLOCATION_BYTES);
        let p = any_alloc(len);
        unsafe { crate::str::from_utf8_unchecked(crate::slice::from_raw_parts(p, len)) }
    }

    #[inline]
    fn raw_utf8_char_width(b: u8) -> usize {
        match b {
            0x00..=0x7F => 1,
            0xC2..=0xDF => 2,
            0xE0..=0xEF => 3,
            0xF0..=0xF4 => 4,
            _ => 0,
        }
    }

    // Pure table replacement, checked against the real table on all 256 inputs.
    // No assumption about the calling algorithm or remaining buffer is made.
    fn stub_utf8_char_width(b: u8) -> usize {
        raw_utf8_char_width(b)
    }

    // Explicit instance of Challenge Assumption (4), queried only against the
    // captured original immutable input, never against the byte passed to width.
    // The implication is true at EVERY offset of a valid UTF-8 string, including
    // offsets chosen by an incorrect algorithm. It does not assume that the
    // algorithm is at a boundary, advances correctly, or returns the right result.
    pub(super) fn assume_original_utf8_at(original: &[u8], pos: usize) {
        if pos < original.len() && !validations::utf8_is_cont_byte(original[pos]) {
            let width = validations::utf8_char_width(original[pos]);
            kani::assume(width > 0 && width <= original.len() - pos);
            let next = pos + width;
            kani::assume(next == original.len() || !validations::utf8_is_cont_byte(original[next]));
        }
    }

    // Loop-free RFC 3629 UTF-8 validation predicates for decoders
    #[inline]
    fn is_valid_first_utf8_char(b: &[u8]) -> bool {
        if b.is_empty() {
            return true;
        }
        match b[0] {
            0x00..=0x7F => true,
            0xC2..=0xDF => b.len() >= 2 && validations::utf8_is_cont_byte(b[1]),
            0xE0 => {
                b.len() >= 3
                    && (b[1] >= 0xA0 && b[1] <= 0xBF)
                    && validations::utf8_is_cont_byte(b[2])
            }
            0xE1..=0xEC | 0xEE..=0xEF => {
                b.len() >= 3
                    && validations::utf8_is_cont_byte(b[1])
                    && validations::utf8_is_cont_byte(b[2])
            }
            0xED => {
                b.len() >= 3
                    && (b[1] >= 0x80 && b[1] <= 0x9F)
                    && validations::utf8_is_cont_byte(b[2])
            }
            0xF0 => {
                b.len() >= 4
                    && (b[1] >= 0x90 && b[1] <= 0xBF)
                    && validations::utf8_is_cont_byte(b[2])
                    && validations::utf8_is_cont_byte(b[3])
            }
            0xF1..=0xF3 => {
                b.len() >= 4
                    && validations::utf8_is_cont_byte(b[1])
                    && validations::utf8_is_cont_byte(b[2])
                    && validations::utf8_is_cont_byte(b[3])
            }
            0xF4 => {
                b.len() >= 4
                    && (b[1] >= 0x80 && b[1] <= 0x8F)
                    && validations::utf8_is_cont_byte(b[2])
                    && validations::utf8_is_cont_byte(b[3])
            }
            _ => false,
        }
    }

    // The last char of `b` is complete and valid: the nearest non-continuation byte within the last
    // four bytes is a valid lead byte whose char ends exactly at the end of `b`.
    #[inline]
    fn is_valid_last_utf8_char(b: &[u8]) -> bool {
        let n = b.len();
        if n == 0 {
            return true;
        }
        let k = last_char_len(b);
        n >= k && is_valid_first_utf8_char(&b[n - k..]) && raw_utf8_char_width(b[n - k]) == k
    }

    #[derive(Clone, Copy)]
    pub struct ModelPattern;

    pub struct ModelSearcher<'a> {
        pub haystack: &'a str,
        pub front: usize,
        pub back: usize,
        pub last_match: Option<(usize, usize)>,
        pub nmb_calls: usize,
        pub nmb_res: [Option<(usize, usize)>; 2],
    }

    // See verify-rust-std#753 (rust-lang/rust#165681): `Pattern` is still a safe trait on
    // the pinned toolchain; update to `unsafe impl Pattern for ModelPattern` once synced past rust#165681.
    impl Pattern for ModelPattern {
        type Searcher<'a> = ModelSearcher<'a>;
        fn into_searcher(self, haystack: &str) -> ModelSearcher<'_> {
            ModelSearcher {
                haystack,
                front: 0,
                back: haystack.len(),
                last_match: None,
                nmb_calls: 0,
                nmb_res: [None, None],
            }
        }
    }

    // Challenge Assumption (2): pattern.rs is safe and correct. This is a
    // nondeterministic over-approximation of its documented range guarantees,
    // not an implementation of the matching semantics of one fixed pattern.
    // Both Match and Reject may be empty (Searcher::next, ReverseSearcher::next_back).
    fn assume_search_range(s: &str, lo: usize, hi: usize, a: usize, b: usize) {
        // Adjacent, non-overlapping ranges remain in the unsearched interval.
        kani::assume(lo <= a && a <= b && b <= hi);
        // Searcher safety requirement: both endpoints are UTF-8 boundaries.
        kani::assume(s.is_char_boundary(a) && s.is_char_boundary(b));
        cover!(a == b);
        cover!(a < b);
    }

    unsafe impl<'a> Searcher<'a> for ModelSearcher<'a> {
        fn haystack(&self) -> &'a str {
            self.haystack
        }

        fn next(&mut self) -> crate::str::pattern::SearchStep {
            use crate::str::pattern::SearchStep;
            // Done is allowed only after every byte has been visited. Equality
            // alone does not force Done: an empty match/reject can still follow.
            if self.front == self.back && kani::any() {
                return SearchStep::Done;
            }
            let a = self.front;
            let b = kani::any();
            assume_search_range(self.haystack, self.front, self.back, a, b);
            self.front = b;
            if kani::any() { SearchStep::Match(a, b) } else { SearchStep::Reject(a, b) }
        }

        fn next_match(&mut self) -> Option<(usize, usize)> {
            let result = if kani::any() {
                // Abstract any sequence of rejects followed by Done.
                self.front = self.back;
                None
            } else {
                let a = kani::any();
                let b = kani::any();
                assume_search_range(self.haystack, self.front, self.back, a, b);
                self.front = b;
                Some((a, b))
            };
            self.last_match = result;
            result
        }
    }

    unsafe impl<'a> ReverseSearcher<'a> for ModelSearcher<'a> {
        fn next_back(&mut self) -> crate::str::pattern::SearchStep {
            use crate::str::pattern::SearchStep;
            if self.front == self.back && kani::any() {
                return SearchStep::Done;
            }
            let a = kani::any();
            let b = self.back;
            assume_search_range(self.haystack, self.front, self.back, a, b);
            self.back = a;
            if kani::any() { SearchStep::Match(a, b) } else { SearchStep::Reject(a, b) }
        }

        fn next_match_back(&mut self) -> Option<(usize, usize)> {
            let call = self.nmb_calls;
            self.nmb_calls = call.saturating_add(1);
            let result = if kani::any() {
                self.back = self.front;
                None
            } else {
                let a = kani::any();
                let b = kani::any();
                assume_search_range(self.haystack, self.front, self.back, a, b);
                self.back = a;
                Some((a, b))
            };
            self.last_match = result;
            if call < 2 {
                self.nmb_res[call] = result;
            }
            result
        }
    }

    impl<'a> DoubleEndedSearcher<'a> for ModelSearcher<'a> {}

    fn searcher_invariant(m: &ModelSearcher<'_>) -> bool {
        m.front <= m.back
            && m.back <= m.haystack.len()
            && m.haystack.is_char_boundary(m.front)
            && m.haystack.is_char_boundary(m.back)
    }

    // One arbitrary transition from an arbitrary valid state proves inductive
    // preservation of the range invariant; no bound on the number of steps.
    #[kani::proof]
    pub fn check_model_searcher_step() {
        use crate::str::pattern::SearchStep;
        let s = any_haystack();
        let mut m = any_split(s).matcher;
        let (lo, hi) = (m.front, m.back);
        let direction: u8 = kani::any();
        let step = match direction % 4 {
            0 => m.next(),
            1 => m.next_back(),
            2 => m.next_match().map_or(SearchStep::Done, |(a, b)| SearchStep::Match(a, b)),
            _ => m.next_match_back().map_or(SearchStep::Done, |(a, b)| SearchStep::Match(a, b)),
        };
        assert!(searcher_invariant(&m));
        assert!(lo <= m.front && m.back <= hi);
        assert_eq!(m.haystack.as_ptr(), s.as_ptr());
        assert_eq!(m.haystack.len(), s.len());
        match step {
            SearchStep::Match(a, b) | SearchStep::Reject(a, b) => {
                assert!(lo <= a && a <= b && b <= hi);
                assert!(s.is_char_boundary(a) && s.is_char_boundary(b));
                if direction % 4 == 0 {
                    assert_eq!(a, lo);
                }
                if direction % 4 == 1 {
                    assert_eq!(b, hi);
                }
                cover!(lo == hi && a == b);
                cover!(a < b);
            }
            SearchStep::Done => {
                assert_eq!(m.front, m.back);
            }
        }
        cover!(matches!(step, SearchStep::Done));
        cover!(matches!(step, SearchStep::Reject(_, _)));
        cover!(matches!(step, SearchStep::Match(_, _)));
    }

    #[kani::proof]
    pub fn check_str_iter_initial_invariants() {
        let s = any_haystack();
        let n: usize = kani::any();

        let sp = s.split(ModelPattern);
        assert!(split_invariant(&sp.0));
        assert_eq!(sp.0.start, 0);
        assert_eq!(sp.0.end, s.len());
        assert!(sp.0.allow_trailing_empty);
        assert!(!sp.0.finished);
        let sp_rem = sp.remainder().unwrap();
        assert!(sp_rem.as_ptr() == s.as_ptr() && sp_rem.len() == s.len());

        let rsp = s.rsplit(ModelPattern);
        assert!(split_invariant(&rsp.0));
        assert!(rsp.0.allow_trailing_empty);
        assert!(!rsp.0.finished);
        let rsp_rem = rsp.remainder().unwrap();
        assert!(rsp_rem.as_ptr() == s.as_ptr() && rsp_rem.len() == s.len());

        let spi = s.split_inclusive(ModelPattern);
        assert!(split_invariant(&spi.0));
        assert!(!spi.0.allow_trailing_empty);
        assert!(!spi.0.finished);
        let spi_rem = spi.remainder().unwrap();
        assert!(spi_rem.as_ptr() == s.as_ptr() && spi_rem.len() == s.len());

        let st = s.split_terminator(ModelPattern);
        assert!(split_invariant(&st.0));
        assert!(!st.0.allow_trailing_empty);
        assert!(!st.0.finished);
        let st_rem = st.remainder().unwrap();
        assert!(st_rem.as_ptr() == s.as_ptr() && st_rem.len() == s.len());

        let rst = s.rsplit_terminator(ModelPattern);
        assert!(split_invariant(&rst.0));
        assert!(!rst.0.allow_trailing_empty);
        assert!(!rst.0.finished);
        let rst_rem = rst.remainder().unwrap();
        assert!(rst_rem.as_ptr() == s.as_ptr() && rst_rem.len() == s.len());

        let sn = s.splitn(n, ModelPattern);
        assert!(split_invariant(&sn.0.iter));
        assert_eq!(sn.0.count, n);
        let sn_rem = sn.remainder().unwrap();
        assert!(sn_rem.as_ptr() == s.as_ptr() && sn_rem.len() == s.len());

        let rsn = s.rsplitn(n, ModelPattern);
        assert!(split_invariant(&rsn.0.iter));
        assert_eq!(rsn.0.count, n);
        let rsn_rem = rsn.remainder().unwrap();
        assert!(rsn_rem.as_ptr() == s.as_ptr() && rsn_rem.len() == s.len());

        let mt = s.matches(ModelPattern);
        assert!(searcher_invariant(&mt.0.0));
        assert_eq!(mt.0.0.front, 0);
        assert_eq!(mt.0.0.back, s.len());

        let rmt = s.rmatches(ModelPattern);
        assert!(searcher_invariant(&rmt.0.0));
        assert_eq!(rmt.0.0.front, 0);
        assert_eq!(rmt.0.0.back, s.len());

        let mi = s.match_indices(ModelPattern);
        assert!(searcher_invariant(&mi.0.0));
        assert_eq!(mi.0.0.front, 0);
        assert_eq!(mi.0.0.back, s.len());

        let rmi = s.rmatch_indices(ModelPattern);
        assert!(searcher_invariant(&rmi.0.0));
        assert_eq!(rmi.0.0.front, 0);
        assert_eq!(rmi.0.0.back, s.len());

        let ws = s.split_ascii_whitespace();
        assert!(!ws.inner.iter.iter.finished);
        let ws_rem = ws.remainder().unwrap();
        assert!(ws_rem.as_ptr() == s.as_ptr() && ws_rem.len() == s.len());

        let chs = s.chars();
        let chs_str = chs.as_str();
        assert!(chs_str.as_ptr() == s.as_ptr() && chs_str.len() == s.len());

        cover!(s.is_empty());
        cover!(!s.is_empty() && s.len() <= 32);
        cover!(s.len() > (1usize << 48));
    }

    fn split_invariant(it: &SplitInternal<'_, ModelPattern>) -> bool {
        searcher_invariant(&it.matcher)
            && it.start <= it.matcher.front
            && it.matcher.back <= it.end
            && it.end <= it.matcher.haystack.len()
            && it.matcher.haystack.is_char_boundary(it.start)
            && it.matcher.haystack.is_char_boundary(it.end)
    }

    fn assert_valid_subslice(s: &str, sub: &str) {
        let base = s.as_ptr() as usize;
        let sub_ptr = sub.as_ptr() as usize;
        let start = sub_ptr.wrapping_sub(base);
        let end = start.wrapping_add(sub.len());
        assert!(start <= end && end <= s.len());
        assert!(sub.as_ptr() == unsafe { s.as_ptr().add(start) });
        assert!(s.is_char_boundary(start) && s.is_char_boundary(end));
    }

    // `sub` is exactly the piece s[lo..hi] (same pointer, same length).
    fn assert_piece(s: &str, sub: &str, lo: usize, hi: usize) {
        assert!(lo <= hi && hi <= s.len());
        assert!(sub.as_ptr() == unsafe { s.as_ptr().add(lo) });
        assert_eq!(sub.len(), hi - lo);
    }

    // Exact spec of one next_back / next_back_inclusive call, from the matches the searcher
    // recorded (nmb_calls searches, nmb_res results). Piece = s[b..end] and new end = a
    // (exclusive) or b (inclusive); with !allow_trailing_empty the first search may only produce
    // the (skipped) empty trailing piece, then a second search follows.
    fn assert_next_back_spec(
        s: &str,
        split: &SplitInternal<'static, ModelPattern>,
        res: Option<&str>,
        so: usize,
        eo: usize,
        was_finished: bool,
        skip: bool,
        inclusive: bool,
    ) {
        let n = split.matcher.nmb_calls;
        let r1 = split.matcher.nmb_res[0];
        let r2 = split.matcher.nmb_res[1];
        if was_finished {
            assert!(res.is_none());
            assert_eq!(n, 0);
            assert!(split.finished);
            return;
        }
        assert!(split.allow_trailing_empty);
        assert_eq!(split.start, so);
        let new_end = |m: (usize, usize)| if inclusive { m.1 } else { m.0 };
        if !skip {
            assert_eq!(n, 1);
            match r1 {
                Some(m) => {
                    assert_piece(s, res.unwrap(), m.1, eo);
                    assert_eq!(split.end, new_end(m));
                    assert!(!split.finished);
                }
                None => {
                    assert_piece(s, res.unwrap(), so, eo);
                    assert!(split.finished);
                    assert_eq!(split.end, eo);
                }
            }
        } else if n == 1 {
            match r1 {
                Some(m) => {
                    assert!(m.1 < eo);
                    assert_piece(s, res.unwrap(), m.1, eo);
                    assert_eq!(split.end, new_end(m));
                    assert!(!split.finished);
                }
                None => {
                    assert!(split.finished);
                    assert_eq!(split.end, eo);
                    if so < eo {
                        assert_piece(s, res.unwrap(), so, eo);
                    } else {
                        assert!(res.is_none());
                    }
                }
            }
        } else {
            assert_eq!(n, 2);
            let m1 = r1.unwrap();
            assert_eq!(m1.1, eo);
            let e1 = new_end(m1);
            match r2 {
                Some(m) => {
                    assert_piece(s, res.unwrap(), m.1, e1);
                    assert_eq!(split.end, new_end(m));
                    assert!(!split.finished);
                }
                None => {
                    assert_piece(s, res.unwrap(), so, e1);
                    assert!(split.finished);
                    assert_eq!(split.end, e1);
                }
            }
        }
    }

    fn any_split(s: &'static str) -> SplitInternal<'static, ModelPattern> {
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end && end <= s.len());
        kani::assume(s.is_char_boundary(start) && s.is_char_boundary(end));
        let front: usize = kani::any();
        let back: usize = kani::any();
        kani::assume(start <= front && front <= back && back <= end);
        kani::assume(s.is_char_boundary(front) && s.is_char_boundary(back));
        let split = SplitInternal {
            start,
            end,
            matcher: ModelSearcher {
                haystack: s,
                front,
                back,
                last_match: None,
                nmb_calls: 0,
                nmb_res: [None, None],
            },
            allow_trailing_empty: kani::any(),
            finished: kani::any(),
        };
        kani::assume(split_invariant(&split));
        split
    }

    // Loop-free independent decoders (RFC 3629), used only as specifications, written from the
    // encoding table and not from validations.rs.
    // Requires: is_valid_first_utf8_char(b) and b non-empty.
    fn decode_first(b: &[u8]) -> u32 {
        let b0 = b[0] as u32;
        if b0 < 0x80 {
            b0
        } else if b0 < 0xE0 {
            ((b0 - 0xC0) << 6) | (b[1] as u32 & 0x3F)
        } else if b0 < 0xF0 {
            ((b0 - 0xE0) << 12) | ((b[1] as u32 & 0x3F) << 6) | (b[2] as u32 & 0x3F)
        } else {
            ((b0 - 0xF0) << 18)
                | ((b[1] as u32 & 0x3F) << 12)
                | ((b[2] as u32 & 0x3F) << 6)
                | (b[3] as u32 & 0x3F)
        }
    }

    // Number of bytes of the last char of `b` (b non-empty): 1 if the last byte is ASCII, else the
    // distance to the nearest non-continuation byte within the last four bytes (4 if none).
    fn last_char_len(b: &[u8]) -> usize {
        let n = b.len();
        if b[n - 1] < 128 {
            1
        } else if n >= 2 && !validations::utf8_is_cont_byte(b[n - 2]) {
            2
        } else if n >= 3 && !validations::utf8_is_cont_byte(b[n - 3]) {
            3
        } else {
            4
        }
    }

    #[kani::proof]
    pub fn check_chars_next() {
        let s = any_haystack();
        kani::assume(is_valid_first_utf8_char(s.as_bytes()));
        let mut chars = Chars { iter: s.as_bytes().iter() };
        let res = chars.next();
        if let Some(ch) = res {
            let u = ch as u32;
            assert!(u <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&u));
            assert_eq!(chars.iter.len(), s.len() - ch.len_utf8());
            // decoded value against an independent loop-free decoder
            assert_eq!(ch as u32, decode_first(s.as_bytes()));
            cover!(ch.len_utf8() == 2);
            cover!(ch.len_utf8() == 3);
            cover!(ch.len_utf8() == 4);
        } else {
            assert_eq!(s.len(), 0);
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_chars_next_back() {
        let s = any_haystack();
        kani::assume(is_valid_last_utf8_char(s.as_bytes()));
        let mut chars = Chars { iter: s.as_bytes().iter() };
        let res = chars.next_back();
        if let Some(ch) = res {
            let u = ch as u32;
            assert!(u <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&u));
            let consumed = s.len() - chars.iter.len();
            let k = last_char_len(s.as_bytes());
            assert_eq!(consumed, k);
            assert_eq!(consumed, ch.len_utf8());
            // decoded value against the independent decoder applied to the last k bytes
            assert_eq!(ch as u32, decode_first(&s.as_bytes()[s.len() - k..]));
            cover!(k == 2);
            cover!(k == 3);
            cover!(k == 4);
        } else {
            assert_eq!(s.len(), 0);
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_char_indices_next() {
        let s = any_haystack();
        let start: usize = kani::any();
        kani::assume(start <= s.len());
        kani::assume(is_valid_first_utf8_char(&s.as_bytes()[start..]));
        let mut ci =
            CharIndices { front_offset: start, iter: Chars { iter: s.as_bytes()[start..].iter() } };
        let res = ci.next();
        if let Some((idx, ch)) = res {
            let u = ch as u32;
            assert!(u <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&u));
            assert_eq!(idx, start);
            assert_eq!(ci.offset(), start + ch.len_utf8());
            assert_eq!(u, decode_first(&s.as_bytes()[start..]));
            cover!(ch.len_utf8() == 2);
            cover!(ch.len_utf8() == 3);
            cover!(ch.len_utf8() == 4);
        } else {
            assert_eq!(start, s.len());
        }
        cover!(res.is_some());
        cover!(res.is_none());
        cover!(start > 0 && res.is_some());
    }

    #[kani::proof]
    pub fn check_char_indices_next_back() {
        let s = any_haystack();
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end && end <= s.len());
        kani::assume(is_valid_last_utf8_char(&s.as_bytes()[start..end]));
        let mut ci = CharIndices {
            front_offset: start,
            iter: Chars { iter: s.as_bytes()[start..end].iter() },
        };
        let res = ci.next_back();
        if let Some((idx, ch)) = res {
            let u = ch as u32;
            assert!(u <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&u));
            let k = last_char_len(&s.as_bytes()[start..end]);
            assert_eq!(idx, end - k);
            assert_eq!(ch.len_utf8(), k);
            assert_eq!(ci.iter.iter.len(), (end - start) - k);
            assert_eq!(u, decode_first(&s.as_bytes()[end - k..end]));
            cover!(k == 2);
            cover!(k == 3);
            cover!(k == 4);
        } else {
            assert_eq!(start, end);
        }
        cover!(res.is_some());
        cover!(res.is_none());
        cover!(start > 0 && res.is_some());
    }

    #[kani::proof]
    pub fn check_chars_as_str() {
        let s = any_haystack();
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end && end <= s.len());
        kani::assume(s.is_char_boundary(start) && s.is_char_boundary(end));
        let w = unsafe { s.get_unchecked(start..end) };
        let chars = Chars { iter: w.as_bytes().iter() };
        let sub = chars.as_str();
        assert_valid_subslice(s, sub);
        assert_eq!(sub.len(), end - start);
        cover!(sub.len() > 0);
        cover!(sub.len() == 0);
    }

    // Exact replacement check: compare all 256 byte inputs with the original
    // width function. The replacement contains no assumptions about the caller,
    // the remaining buffer, or the returned result.
    #[kani::proof]
    pub fn check_utf8_char_width_refinement() {
        let b: u8 = kani::any();
        assert_eq!(validations::utf8_char_width(b), raw_utf8_char_width(b));
        cover!(b < 0x80);
        cover!(b >= 0xF0);
        cover!(raw_utf8_char_width(b) == 0);
    }

    unsafe fn write_utf8_scalar(dst: *mut u8, off: usize, ch: char) -> usize {
        let u = ch as u32;
        if u < 0x80 {
            unsafe { *dst.add(off) = u as u8 };
            1
        } else if u < 0x800 {
            unsafe {
                *dst.add(off) = (0xC0 | (u >> 6)) as u8;
                *dst.add(off + 1) = (0x80 | (u & 0x3F)) as u8;
            }
            2
        } else if u < 0x10000 {
            unsafe {
                *dst.add(off) = (0xE0 | (u >> 12)) as u8;
                *dst.add(off + 1) = (0x80 | ((u >> 6) & 0x3F)) as u8;
                *dst.add(off + 2) = (0x80 | (u & 0x3F)) as u8;
            }
            3
        } else {
            unsafe {
                *dst.add(off) = (0xF0 | (u >> 18)) as u8;
                *dst.add(off + 1) = (0x80 | ((u >> 12) & 0x3F)) as u8;
                *dst.add(off + 2) = (0x80 | ((u >> 6) & 0x3F)) as u8;
                *dst.add(off + 3) = (0x80 | (u & 0x3F)) as u8;
            }
            4
        }
    }

    // Verify `Chars::advance_by` via an independent `Chars::nth` caller over an 8-byte buffer
    // with two arbitrary Unicode scalars (`kani::any::<char>()`) at fixed offsets 0 and 4,
    // symbolic ASCII fill bytes, and unbounded `k`, with zero concrete string/char literals.
    #[kani::proof]
    #[kani::stub(crate::str::validations::utf8_char_width, stub_utf8_char_width)]
    pub fn check_chars_nth_caller() {
        let c0: char = kani::any();
        let c1: char = kani::any();
        let k: usize = kani::any();

        let p = unsafe { malloc(8) };
        kani::assume(!p.is_null());
        unsafe {
            *p = kani::any::<u8>() & 0x7F;
            *p.add(1) = kani::any::<u8>() & 0x7F;
            *p.add(2) = kani::any::<u8>() & 0x7F;
            *p.add(3) = kani::any::<u8>() & 0x7F;
            *p.add(4) = kani::any::<u8>() & 0x7F;
            *p.add(5) = kani::any::<u8>() & 0x7F;
            *p.add(6) = kani::any::<u8>() & 0x7F;
            *p.add(7) = kani::any::<u8>() & 0x7F;
        }
        let _w0 = unsafe { write_utf8_scalar(p, 0, c0) };
        let _w1 = unsafe { write_utf8_scalar(p, 4, c1) };

        let s = unsafe { crate::str::from_utf8_unchecked(crate::slice::from_raw_parts(p, 8)) };
        let res = s.chars().nth(k);
        let mut res_len = 0usize;
        if let Some(ch) = res {
            let u = ch as u32;
            assert!(u <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&u));
            assert!(ch == c0 || ch == c1 || ch.is_ascii());
            res_len = ch.len_utf8();
        }
        cover!(res_len == 1);
        cover!(res_len == 2);
        cover!(res_len == 3);
        cover!(res_len == 4);
        cover!(k >= 32 && res.is_none());
        cover!(k > 0 && res == Some(c1));
    }

    #[kani::proof_for_contract(Bytes::__iterator_get_unchecked)]
    pub fn check_bytes_iterator_get_unchecked() {
        let s = any_haystack();
        let mut bytes = s.bytes();
        let idx: usize = kani::any();
        let val = unsafe { bytes.__iterator_get_unchecked(idx) };
        assert_eq!(val, s.as_bytes()[idx]);
        cover!(idx > 0);
        cover!(idx == 0);
    }

    #[kani::proof]
    pub fn check_split_internal_get_end() {
        let s = any_haystack();
        let mut split = any_split(s);
        let (start, end) = (split.start, split.end);
        let expect_some = !split.finished && (split.allow_trailing_empty || end - start > 0);
        let res = split.get_end();
        assert!(split_invariant(&split));
        // functional result: the trailing piece [start, end) exactly when it is due; always finished
        assert!(split.finished);
        assert_eq!(res.is_some(), expect_some);
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
            assert!(sub.as_ptr() == unsafe { s.as_ptr().add(start) });
            assert_eq!(sub.len(), end - start);
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_split_internal_next() {
        let s = any_haystack();
        let mut split = any_split(s);
        let was_finished = split.finished;
        let (so, eo) = (split.start, split.end);
        // next/next_inclusive never write allow_trailing_empty (neither the match arm nor get_end does)
        let ate0 = split.allow_trailing_empty;
        let res = split.next();
        assert_eq!(split.allow_trailing_empty, ate0);
        assert!(split_invariant(&split));
        // a finished iterator yields nothing and stays finished; None means finished
        if was_finished {
            assert!(res.is_none() && split.finished);
        }
        if res.is_none() {
            assert!(split.finished);
        }
        // exact piece and new start, from the match the searcher reported (None: get_end)
        assert_eq!(split.end, eo);
        match split.matcher.last_match {
            Some((a, b)) => {
                assert!(!was_finished);
                assert_piece(s, res.unwrap(), so, a);
                assert_eq!(split.start, b);
                assert!(!split.finished);
            }
            None => {
                assert_eq!(split.start, so);
                if !was_finished {
                    assert!(split.finished);
                    assert_eq!(res.is_some(), split.allow_trailing_empty || eo > so);
                    if let Some(sub) = res {
                        assert_piece(s, sub, so, eo);
                    }
                }
            }
        }
        cover!(was_finished);
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_split_internal_next_inclusive() {
        let s = any_haystack();
        let mut split = any_split(s);
        let was_finished = split.finished;
        let (so, eo) = (split.start, split.end);
        // next/next_inclusive never write allow_trailing_empty (neither the match arm nor get_end does)
        let ate0 = split.allow_trailing_empty;
        let res = split.next_inclusive();
        assert_eq!(split.allow_trailing_empty, ate0);
        assert!(split_invariant(&split));
        if was_finished {
            assert!(res.is_none() && split.finished);
        }
        if res.is_none() {
            assert!(split.finished);
        }
        assert_eq!(split.end, eo);
        match split.matcher.last_match {
            Some((_, b)) => {
                assert!(!was_finished);
                assert_piece(s, res.unwrap(), so, b);
                assert_eq!(split.start, b);
                assert!(!split.finished);
            }
            None => {
                assert_eq!(split.start, so);
                if !was_finished {
                    assert!(split.finished);
                    assert_eq!(res.is_some(), split.allow_trailing_empty || eo > so);
                    if let Some(sub) = res {
                        assert_piece(s, sub, so, eo);
                    }
                }
            }
        }
        cover!(was_finished);
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    // Covers `SplitInternal::next_back`'s first-search arm, the one that asks the pattern
    // matcher for a match backwards (`self.matcher.next_match_back()`). `SplitInternal` has no
    // method of that name (issue #279 notes the challenge page's wording); the harness name
    // follows the call it exercises.
    #[kani::proof]
    pub fn check_split_internal_next_back_via_matcher() {
        let s = any_haystack();
        let mut split = any_split(s);
        let skip_trailing = !split.allow_trailing_empty;
        let was_finished = split.finished;
        let (so, eo) = (split.start, split.end);
        let res = split.next_back();
        assert!(split_invariant(&split));
        assert_next_back_spec(s, &split, res, so, eo, was_finished, skip_trailing, false);
        // with !allow_trailing_empty an empty piece may only come from the second search
        // (the empty trailing piece itself is skipped)
        if skip_trailing {
            if let Some(sub) = res {
                if sub.is_empty() {
                    assert!(split.matcher.nmb_calls >= 2);
                }
            }
        }
        cover!(skip_trailing && res.map_or(false, |r| r.is_empty()));
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
        }
        cover!(res.is_some());
        cover!(res.is_none());
        // a finished iterator yields nothing more
        if split.finished {
            assert!(split.next_back().is_none());
        }
        cover!(split.finished);
    }

    #[kani::proof]
    pub fn check_split_internal_next_back_inclusive() {
        let s = any_haystack();
        let mut split = any_split(s);
        let skip_trailing = !split.allow_trailing_empty;
        let was_finished = split.finished;
        let (so, eo) = (split.start, split.end);
        let res = split.next_back_inclusive();
        assert!(split_invariant(&split));
        assert_next_back_spec(s, &split, res, so, eo, was_finished, skip_trailing, true);
        if skip_trailing {
            if let Some(sub) = res {
                if sub.is_empty() {
                    assert!(split.matcher.nmb_calls >= 2);
                }
            }
        }
        cover!(skip_trailing && res.map_or(false, |r| r.is_empty()));
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
        }
        cover!(res.is_some());
        cover!(res.is_none());
        // a finished iterator yields nothing more
        if split.finished {
            assert!(split.next_back_inclusive().is_none());
        }
        cover!(split.finished);
    }

    #[kani::proof]
    pub fn check_split_internal_remainder() {
        let s = any_haystack();
        let split = any_split(s);
        let res = split.remainder();
        assert!(split_invariant(&split));
        // functional result: [start, end) unless the iterator is finished
        assert_eq!(res.is_some(), !split.finished);
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
            assert!(sub.as_ptr() == unsafe { s.as_ptr().add(split.start) });
            assert_eq!(sub.len(), split.end - split.start);
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_match_indices_internal_next() {
        let s = any_haystack();
        let split = any_split(s);
        let mut iter = MatchIndicesInternal::<ModelPattern>(split.matcher);
        let res = iter.next();
        assert!(searcher_invariant(&iter.0));
        if let Some((idx, sub)) = res {
            assert_valid_subslice(s, sub);
            assert!(s.is_char_boundary(idx));
            assert_eq!(sub.as_ptr(), unsafe { s.as_ptr().add(idx) });
        }
        // exactly the match the searcher reported: index a, substring [a, b)
        match iter.0.last_match {
            Some((a, b)) => {
                let (idx, sub) = res.unwrap();
                assert_eq!(idx, a);
                assert_piece(s, sub, a, b);
            }
            None => assert!(res.is_none()),
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_match_indices_internal_next_back() {
        let s = any_haystack();
        let split = any_split(s);
        let mut iter = MatchIndicesInternal::<ModelPattern>(split.matcher);
        let res = iter.next_back();
        assert!(searcher_invariant(&iter.0));
        if let Some((idx, sub)) = res {
            assert_valid_subslice(s, sub);
            assert!(s.is_char_boundary(idx));
            assert_eq!(sub.as_ptr(), unsafe { s.as_ptr().add(idx) });
        }
        // exactly the match the searcher reported: index a, substring [a, b)
        match iter.0.last_match {
            Some((a, b)) => {
                let (idx, sub) = res.unwrap();
                assert_eq!(idx, a);
                assert_piece(s, sub, a, b);
            }
            None => assert!(res.is_none()),
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_matches_internal_next() {
        let s = any_haystack();
        let split = any_split(s);
        let mut iter = MatchesInternal::<ModelPattern>(split.matcher);
        let res = iter.next();
        assert!(searcher_invariant(&iter.0));
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
        }
        // exactly the match the searcher reported: substring [a, b)
        match iter.0.last_match {
            Some((a, b)) => assert_piece(s, res.unwrap(), a, b),
            None => assert!(res.is_none()),
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_matches_internal_next_back() {
        let s = any_haystack();
        let split = any_split(s);
        let mut iter = MatchesInternal::<ModelPattern>(split.matcher);
        let res = iter.next_back();
        assert!(searcher_invariant(&iter.0));
        if let Some(sub) = res {
            assert_valid_subslice(s, sub);
        }
        // exactly the match the searcher reported: substring [a, b)
        match iter.0.last_match {
            Some((a, b)) => assert_piece(s, res.unwrap(), a, b),
            None => assert!(res.is_none()),
        }
        cover!(res.is_some());
        cover!(res.is_none());
    }

    #[kani::proof]
    pub fn check_split_ascii_whitespace_remainder() {
        let s = any_haystack();
        let mut iter = s.split_ascii_whitespace();
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end && end <= s.len());
        kani::assume(s.is_char_boundary(start) && s.is_char_boundary(end));
        iter.inner.iter.iter.v = unsafe { s.get_unchecked(start..end).as_bytes() };
        iter.inner.iter.iter.finished = kani::any();
        let was_finished = iter.inner.iter.iter.finished;
        let rem = iter.remainder();
        // functional result: the view [start, end) unless the iterator is finished
        assert_eq!(rem.is_some(), !was_finished);
        if let Some(sub) = rem {
            assert_valid_subslice(s, sub);
            assert!(sub.as_ptr() == unsafe { s.as_ptr().add(start) });
            assert_eq!(sub.len(), end - start);
        }
        cover!(rem.is_some());
        cover!(rem.is_none());
    }

    // The fill-loop caller supplies live, initialized 32-byte local storage.
    // This predicate checks representation validity only, not allocation.
    pub(super) fn bool32_valid(ptr: *const [bool; 32]) -> bool {
        // Reading initialized storage as u8 permits every representation;
        // bitwise OR <= 1 holds iff every byte is 0 or 1.
        let b = unsafe { &*(ptr as *const [u8; 32]) };
        ((b[0] | b[1] | b[2] | b[3] | b[4] | b[5] | b[6] | b[7])
            | (b[8] | b[9] | b[10] | b[11] | b[12] | b[13] | b[14] | b[15])
            | (b[16] | b[17] | b[18] | b[19] | b[20] | b[21] | b[22] | b[23])
            | (b[24] | b[25] | b[26] | b[27] | b[28] | b[29] | b[30] | b[31]))
            <= 1
    }

    #[kani::proof]
    pub fn check_bool32_valid_equivalence() {
        let bytes: [u8; 32] = [
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
            kani::any::<u8>(),
        ];
        let ptr = (&raw const bytes).cast::<[bool; 32]>();
        let actual = bool32_valid(ptr);
        let expected = kani::mem::can_dereference(ptr);
        assert_eq!(actual, expected);
        cover!(actual);
        cover!(!actual);
        cover!(bytes[0] == 0 && bytes[31] == 1 && actual);
        cover!(bytes[0] > 1);
        cover!(bytes[31] > 1);
    }

    #[kani::proof]
    pub fn check_chunk_pointer_expression() {
        let byte: u8 = kani::any();
        let p = &raw const byte;
        let count: usize = kani::any();
        let expected = p.wrapping_add(count);
        let actual = unsafe { crate::intrinsics::arith_offset(p, count as isize) };
        assert!(actual == expected);
        cover!(count == 0);
        cover!(count == usize::MAX);
        cover!(count > 32 && count < isize::MAX as usize);
    }

    #[kani::proof]
    #[kani::stub(crate::str::validations::utf8_char_width, stub_utf8_char_width)]
    #[kani::stub(
        crate::array::iter::iter_inner::PolymorphicIter::fold,
        crate::array::iter::iter_inner::PolymorphicIter::kani_fold_arity32
    )]
    pub fn check_chars_advance_by() {
        let s = any_haystack();
        let total_len = s.len();
        // Challenge Assumption (4): a valid UTF-8 string begins at a character boundary.
        kani::assume(s.is_empty() || !validations::utf8_is_cont_byte(s.as_bytes()[0]));
        assume_original_utf8_at(s.as_bytes(), 0);
        let mut chars = Chars { iter: s.as_bytes().iter() };
        let remainder: usize = kani::any();

        let res = chars.advance_by(remainder);
        let consumed = total_len - chars.iter.len();
        assert!(consumed <= total_len);
        match res {
            // `remainder` chars were skipped, each takes at least one byte
            Ok(()) => assert!(consumed >= remainder),
            // fewer chars than asked for: everything is consumed, the payload is what is missing
            Err(n) => {
                assert_eq!(chars.iter.len(), 0);
                assert!(n.get() <= remainder);
                assert!(remainder - n.get() <= total_len);
            }
        }

        cover!(total_len >= 32 && remainder > 32);
        cover!(total_len < 32 && remainder >= 32);
        cover!(total_len - chars.iter.len() >= 64);
        cover!(remainder > 64);
        cover!(res.is_ok());
        cover!(res.is_err());
    }
}
