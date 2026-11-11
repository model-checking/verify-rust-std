#[verus_verify]
impl StrCharBoundary for str {
    verus! {
    spec fn bytes(&self) -> Seq<u8> { self.spec_bytes() }
    }
    fn floor_char_boundary(&self, index: usize) -> usize {
        proof! {
            lemma_str_char_boundaries(self);
            axiom_str_len_le_isize_max(self);
            if index < self.spec_bytes().len() {
                lemma_enclosing_char_boundaries(self.spec_bytes(), index as int);
            }
        }
        if index >= self.len() {
            return self.len();
        }
        if self.as_bytes()[index].is_utf8_char_boundary() {
            return index;
        }
        // Unlike `ceil_char_boundary`, the loop is unrolled manually to prevent the compiler from
        // generating excessive unrolled loop bodies when `index` is statically known.

        // The first byte of `&str` must always be a char boundary, so we can assume `i > 0` below
        // for any `i` where `self.as_bytes()[i]` is not a char boundary.
        debug_assert!(self.as_bytes()[0].is_utf8_char_boundary());

        // SAFETY: `self.as_bytes()[0]` is always a char boundary with valid `&str`
        unsafe { assert_unchecked(index >= 1) };
        if self.as_bytes()[index - 1].is_utf8_char_boundary() {
            return index - 1;
        }

        // SAFETY: `self.as_bytes()[0]` is always a char boundary with valid `&str`
        unsafe { assert_unchecked(index >= 2) };
        if self.as_bytes()[index - 2].is_utf8_char_boundary() {
            return index - 2;
        }

        // `self.as_bytes()[0]` is always a char boundary with valid `&str`
        debug_assert!(index >= 3);
        // The character boundary will be within four bytes of the index
        debug_assert!(self.as_bytes()[index - 3].is_utf8_char_boundary());
        index - 3
    }

    fn ceil_char_boundary(&self, index: usize) -> usize {
        proof! {
            lemma_str_char_boundaries(self);
            axiom_str_len_le_isize_max(self);
            if index <= self.spec_bytes().len() {
                lemma_enclosing_char_boundaries(self.spec_bytes(), index as int);
            }
        }
        if index >= self.len() {
            self.len()
        } else {
            let mut i = index;
            #[verus_spec(
                invariant
                    is_char_boundary(self.spec_bytes(), self.spec_bytes().len() as int),
                    forall|byte_index: int|
                        0 <= byte_index < self.spec_bytes().len()
                            ==> (#[trigger] is_char_boundary(self.spec_bytes(), byte_index)
                                <==> !is_continuation_byte(self.spec_bytes()[byte_index])),
                    index <= i <= self.spec_bytes().len(),
                    forall|candidate_index: int|
                        index <= candidate_index < i
                            ==> !#[trigger] is_char_boundary(self.spec_bytes(), candidate_index),
                invariant_except_break
                    i < self.spec_bytes().len(),
                ensures
                    index <= i <= self.spec_bytes().len(),
                    is_char_boundary(self.spec_bytes(), i as int),
                    forall|candidate_index: int|
                        index <= candidate_index < i
                            ==> !#[trigger] is_char_boundary(self.spec_bytes(), candidate_index),
                decreases
                    self.spec_bytes().len() - i,
            )]
            while !self.as_bytes()[i].is_utf8_char_boundary() {
                i += 1;
                if i >= self.len() {
                    break;
                }
            }

            // The character boundary will be within four bytes of the index
            debug_assert!(i <= index + 3);

            i
        }
    }
}

#[verus_verify]
impl U8CharBoundary for u8 {
    verus! {
    spec fn byte(&self) -> u8 { *self }
    }
    fn is_utf8_char_boundary(self) -> bool {
        // This is bit magic equivalent to: b < 128 || b >= 192
        proof! {
            assert(((self as i8) >= -0x40) == !(0x80 <= self <= 0xbf)) by (bit_vector);
        }
        (self as i8) >= -0x40
    }
}
