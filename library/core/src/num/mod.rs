//! Numeric traits and functions for the built-in numeric types.

#![stable(feature = "rust1", since = "1.0.0")]

use safety::{ensures, requires};

#[cfg(kani)]
use crate::kani;
use crate::panic::const_panic;
use crate::str::FromStr;
use crate::ub_checks::assert_unsafe_precondition;
use crate::{ascii, intrinsics, mem};

// FIXME(const-hack): Used because the `?` operator is not allowed in a const context.
macro_rules! try_opt {
    ($e:expr) => {
        match $e {
            Some(x) => x,
            None => return None,
        }
    };
}

// Use this when the generated code should differ between signed and unsigned types.
macro_rules! sign_dependent_expr {
    (signed ? if signed { $signed_case:expr } if unsigned { $unsigned_case:expr } ) => {
        $signed_case
    };
    (unsigned ? if signed { $signed_case:expr } if unsigned { $unsigned_case:expr } ) => {
        $unsigned_case
    };
}

// All these modules are technically private and only exposed for coretests:
#[cfg(not(no_fp_fmt_parse))]
pub mod bignum;
#[cfg(not(no_fp_fmt_parse))]
pub mod dec2flt;
#[cfg(not(no_fp_fmt_parse))]
pub mod diy_float;
#[cfg(not(no_fp_fmt_parse))]
pub mod flt2dec;
pub mod fmt;

#[macro_use]
mod int_macros; // import int_impl!
#[macro_use]
mod uint_macros; // import uint_impl!

mod error;
mod int_log10;
mod int_sqrt;
mod nonzero;
mod overflow_panic;
mod saturating;
mod wrapping;

/// 100% perma-unstable
#[doc(hidden)]
pub mod niche_types;

#[stable(feature = "rust1", since = "1.0.0")]
#[cfg(not(no_fp_fmt_parse))]
pub use dec2flt::ParseFloatError;
#[stable(feature = "int_error_matching", since = "1.55.0")]
pub use error::IntErrorKind;
#[stable(feature = "rust1", since = "1.0.0")]
pub use error::ParseIntError;
#[stable(feature = "try_from", since = "1.34.0")]
pub use error::TryFromIntError;
#[stable(feature = "generic_nonzero", since = "1.79.0")]
pub use nonzero::NonZero;
#[unstable(
    feature = "nonzero_internals",
    reason = "implementation detail which may disappear or be replaced at any time",
    issue = "none"
)]
pub use nonzero::ZeroablePrimitive;
#[stable(feature = "signed_nonzero", since = "1.34.0")]
pub use nonzero::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
#[stable(feature = "nonzero", since = "1.28.0")]
pub use nonzero::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};
#[stable(feature = "saturating_int_impl", since = "1.74.0")]
pub use saturating::Saturating;
#[stable(feature = "rust1", since = "1.0.0")]
pub use wrapping::Wrapping;

macro_rules! u8_xe_bytes_doc {
    () => {
        "

**Note**: This function is meaningless on `u8`. Byte order does not exist as a
concept for byte-sized integers. This function is only provided in symmetry
with larger integer types.

"
    };
}

macro_rules! i8_xe_bytes_doc {
    () => {
        "

**Note**: This function is meaningless on `i8`. Byte order does not exist as a
concept for byte-sized integers. This function is only provided in symmetry
with larger integer types. You can cast from and to `u8` using `as i8` and `as
u8`.

"
    };
}

macro_rules! usize_isize_to_xe_bytes_doc {
    () => {
        "

**Note**: This function returns an array of length 2, 4 or 8 bytes
depending on the target pointer size.

"
    };
}

macro_rules! usize_isize_from_xe_bytes_doc {
    () => {
        "

**Note**: This function takes an array of length 2, 4 or 8 bytes
depending on the target pointer size.

"
    };
}

macro_rules! midpoint_impl {
    ($SelfT:ty, unsigned) => {
        /// Calculates the middle point of `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
        /// sufficiently-large unsigned integral type. This implies that the result is
        /// always rounded towards zero and that no overflow will ever occur.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(4), 2);")]
        #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".midpoint(4), 2);")]
        /// ```
        #[stable(feature = "num_midpoint", since = "1.85.0")]
        #[rustc_const_stable(feature = "num_midpoint", since = "1.85.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn midpoint(self, rhs: $SelfT) -> $SelfT {
            // Use the well known branchless algorithm from Hacker's Delight to compute
            // `(a + b) / 2` without overflowing: `((a ^ b) >> 1) + (a & b)`.
            ((self ^ rhs) >> 1) + (self & rhs)
        }
    };
    ($SelfT:ty, signed) => {
        /// Calculates the middle point of `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
        /// sufficiently-large signed integral type. This implies that the result is
        /// always rounded towards zero and that no overflow will ever occur.
        ///
        /// # Examples
        ///
        /// ```
        /// #![feature(num_midpoint_signed)]
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(4), 2);")]
        #[doc = concat!("assert_eq!((-1", stringify!($SelfT), ").midpoint(2), 0);")]
        #[doc = concat!("assert_eq!((-7", stringify!($SelfT), ").midpoint(0), -3);")]
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(-7), -3);")]
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(7), 3);")]
        /// ```
        #[unstable(feature = "num_midpoint_signed", issue = "110840")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn midpoint(self, rhs: Self) -> Self {
            // Use the well known branchless algorithm from Hacker's Delight to compute
            // `(a + b) / 2` without overflowing: `((a ^ b) >> 1) + (a & b)`.
            let t = ((self ^ rhs) >> 1) + (self & rhs);
            // Except that it fails for integers whose sum is an odd negative number as
            // their floor is one less than their average. So we adjust the result.
            t + (if t < 0 { 1 } else { 0 } & (self ^ rhs))
        }
    };
    ($SelfT:ty, $WideT:ty, unsigned) => {
        /// Calculates the middle point of `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
        /// sufficiently-large unsigned integral type. This implies that the result is
        /// always rounded towards zero and that no overflow will ever occur.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(4), 2);")]
        #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".midpoint(4), 2);")]
        /// ```
        #[stable(feature = "num_midpoint", since = "1.85.0")]
        #[rustc_const_stable(feature = "num_midpoint", since = "1.85.0")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn midpoint(self, rhs: $SelfT) -> $SelfT {
            ((self as $WideT + rhs as $WideT) / 2) as $SelfT
        }
    };
    ($SelfT:ty, $WideT:ty, signed) => {
        /// Calculates the middle point of `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
        /// sufficiently-large signed integral type. This implies that the result is
        /// always rounded towards zero and that no overflow will ever occur.
        ///
        /// # Examples
        ///
        /// ```
        /// #![feature(num_midpoint_signed)]
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(4), 2);")]
        #[doc = concat!("assert_eq!((-1", stringify!($SelfT), ").midpoint(2), 0);")]
        #[doc = concat!("assert_eq!((-7", stringify!($SelfT), ").midpoint(0), -3);")]
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(-7), -3);")]
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".midpoint(7), 3);")]
        /// ```
        #[unstable(feature = "num_midpoint_signed", issue = "110840")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn midpoint(self, rhs: $SelfT) -> $SelfT {
            ((self as $WideT + rhs as $WideT) / 2) as $SelfT
        }
    };
}

impl i8 {
    int_impl! {
        Self = i8,
        ActualT = i8,
        UnsignedT = u8,
        BITS = 8,
        BITS_MINUS_ONE = 7,
        Min = -128,
        Max = 127,
        rot = 2,
        rot_op = "-0x7e",
        rot_result = "0xa",
        swap_op = "0x12",
        swapped = "0x12",
        reversed = "0x48",
        le_bytes = "[0x12]",
        be_bytes = "[0x12]",
        to_xe_bytes_doc = i8_xe_bytes_doc!(),
        from_xe_bytes_doc = i8_xe_bytes_doc!(),
        bound_condition = "",
    }
    midpoint_impl! { i8, i16, signed }
}

impl i16 {
    int_impl! {
        Self = i16,
        ActualT = i16,
        UnsignedT = u16,
        BITS = 16,
        BITS_MINUS_ONE = 15,
        Min = -32768,
        Max = 32767,
        rot = 4,
        rot_op = "-0x5ffd",
        rot_result = "0x3a",
        swap_op = "0x1234",
        swapped = "0x3412",
        reversed = "0x2c48",
        le_bytes = "[0x34, 0x12]",
        be_bytes = "[0x12, 0x34]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { i16, i32, signed }
}

impl i32 {
    int_impl! {
        Self = i32,
        ActualT = i32,
        UnsignedT = u32,
        BITS = 32,
        BITS_MINUS_ONE = 31,
        Min = -2147483648,
        Max = 2147483647,
        rot = 8,
        rot_op = "0x10000b3",
        rot_result = "0xb301",
        swap_op = "0x12345678",
        swapped = "0x78563412",
        reversed = "0x1e6a2c48",
        le_bytes = "[0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { i32, i64, signed }
}

impl i64 {
    int_impl! {
        Self = i64,
        ActualT = i64,
        UnsignedT = u64,
        BITS = 64,
        BITS_MINUS_ONE = 63,
        Min = -9223372036854775808,
        Max = 9223372036854775807,
        rot = 12,
        rot_op = "0xaa00000000006e1",
        rot_result = "0x6e10aa",
        swap_op = "0x1234567890123456",
        swapped = "0x5634129078563412",
        reversed = "0x6a2c48091e6a2c48",
        le_bytes = "[0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { i64, signed }
}

impl i128 {
    int_impl! {
        Self = i128,
        ActualT = i128,
        UnsignedT = u128,
        BITS = 128,
        BITS_MINUS_ONE = 127,
        Min = -170141183460469231731687303715884105728,
        Max = 170141183460469231731687303715884105727,
        rot = 16,
        rot_op = "0x13f40000000000000000000000004f76",
        rot_result = "0x4f7613f4",
        swap_op = "0x12345678901234567890123456789012",
        swapped = "0x12907856341290785634129078563412",
        reversed = "0x48091e6a2c48091e6a2c48091e6a2c48",
        le_bytes = "[0x12, 0x90, 0x78, 0x56, 0x34, 0x12, 0x90, 0x78, \
            0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56, \
            0x78, 0x90, 0x12, 0x34, 0x56, 0x78, 0x90, 0x12]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { i128, signed }
}

#[cfg(target_pointer_width = "16")]
impl isize {
    int_impl! {
        Self = isize,
        ActualT = i16,
        UnsignedT = usize,
        BITS = 16,
        BITS_MINUS_ONE = 15,
        Min = -32768,
        Max = 32767,
        rot = 4,
        rot_op = "-0x5ffd",
        rot_result = "0x3a",
        swap_op = "0x1234",
        swapped = "0x3412",
        reversed = "0x2c48",
        le_bytes = "[0x34, 0x12]",
        be_bytes = "[0x12, 0x34]",
        to_xe_bytes_doc = usize_isize_to_xe_bytes_doc!(),
        from_xe_bytes_doc = usize_isize_from_xe_bytes_doc!(),
        bound_condition = " on 16-bit targets",
    }
    midpoint_impl! { isize, i32, signed }
}

#[cfg(target_pointer_width = "32")]
impl isize {
    int_impl! {
        Self = isize,
        ActualT = i32,
        UnsignedT = usize,
        BITS = 32,
        BITS_MINUS_ONE = 31,
        Min = -2147483648,
        Max = 2147483647,
        rot = 8,
        rot_op = "0x10000b3",
        rot_result = "0xb301",
        swap_op = "0x12345678",
        swapped = "0x78563412",
        reversed = "0x1e6a2c48",
        le_bytes = "[0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78]",
        to_xe_bytes_doc = usize_isize_to_xe_bytes_doc!(),
        from_xe_bytes_doc = usize_isize_from_xe_bytes_doc!(),
        bound_condition = " on 32-bit targets",
    }
    midpoint_impl! { isize, i64, signed }
}

#[cfg(target_pointer_width = "64")]
impl isize {
    int_impl! {
        Self = isize,
        ActualT = i64,
        UnsignedT = usize,
        BITS = 64,
        BITS_MINUS_ONE = 63,
        Min = -9223372036854775808,
        Max = 9223372036854775807,
        rot = 12,
        rot_op = "0xaa00000000006e1",
        rot_result = "0x6e10aa",
        swap_op = "0x1234567890123456",
        swapped = "0x5634129078563412",
        reversed = "0x6a2c48091e6a2c48",
        le_bytes = "[0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56]",
        to_xe_bytes_doc = usize_isize_to_xe_bytes_doc!(),
        from_xe_bytes_doc = usize_isize_from_xe_bytes_doc!(),
        bound_condition = " on 64-bit targets",
    }
    midpoint_impl! { isize, signed }
}

/// If the bit selected by this mask is set, ascii is lower case.
const ASCII_CASE_MASK: u8 = 0b0010_0000;

impl u8 {
    uint_impl! {
        Self = u8,
        ActualT = u8,
        SignedT = i8,
        BITS = 8,
        BITS_MINUS_ONE = 7,
        MAX = 255,
        rot = 2,
        rot_op = "0x82",
        rot_result = "0xa",
        swap_op = "0x12",
        swapped = "0x12",
        reversed = "0x48",
        le_bytes = "[0x12]",
        be_bytes = "[0x12]",
        to_xe_bytes_doc = u8_xe_bytes_doc!(),
        from_xe_bytes_doc = u8_xe_bytes_doc!(),
        bound_condition = "",
    }
    midpoint_impl! { u8, u16, unsigned }

    /// Checks if the value is within the ASCII range.
    ///
    /// # Examples
    ///
    /// ```
    /// let ascii = 97u8;
    /// let non_ascii = 150u8;
    ///
    /// assert!(ascii.is_ascii());
    /// assert!(!non_ascii.is_ascii());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[rustc_const_stable(feature = "const_u8_is_ascii", since = "1.43.0")]
    #[inline]
    pub const fn is_ascii(&self) -> bool {
        *self <= 127
    }

    /// If the value of this byte is within the ASCII range, returns it as an
    /// [ASCII character](ascii::Char).  Otherwise, returns `None`.
    #[must_use]
    #[unstable(feature = "ascii_char", issue = "110998")]
    #[inline]
    pub const fn as_ascii(&self) -> Option<ascii::Char> {
        ascii::Char::from_u8(*self)
    }

    /// Makes a copy of the value in its ASCII upper case equivalent.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To uppercase the value in-place, use [`make_ascii_uppercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// let lowercase_a = 97u8;
    ///
    /// assert_eq!(65, lowercase_a.to_ascii_uppercase());
    /// ```
    ///
    /// [`make_ascii_uppercase`]: Self::make_ascii_uppercase
    #[must_use = "to uppercase the value in-place, use `make_ascii_uppercase()`"]
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[rustc_const_stable(feature = "const_ascii_methods_on_intrinsics", since = "1.52.0")]
    #[inline]
    pub const fn to_ascii_uppercase(&self) -> u8 {
        // Toggle the 6th bit if this is a lowercase letter
        *self ^ ((self.is_ascii_lowercase() as u8) * ASCII_CASE_MASK)
    }

    /// Makes a copy of the value in its ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = 65u8;
    ///
    /// assert_eq!(97, uppercase_a.to_ascii_lowercase());
    /// ```
    ///
    /// [`make_ascii_lowercase`]: Self::make_ascii_lowercase
    #[must_use = "to lowercase the value in-place, use `make_ascii_lowercase()`"]
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[rustc_const_stable(feature = "const_ascii_methods_on_intrinsics", since = "1.52.0")]
    #[inline]
    pub const fn to_ascii_lowercase(&self) -> u8 {
        // Set the 6th bit if this is an uppercase letter
        *self | (self.is_ascii_uppercase() as u8 * ASCII_CASE_MASK)
    }

    /// Assumes self is ascii
    #[inline]
    pub(crate) const fn ascii_change_case_unchecked(&self) -> u8 {
        *self ^ ASCII_CASE_MASK
    }

    /// Checks that two values are an ASCII case-insensitive match.
    ///
    /// This is equivalent to `to_ascii_lowercase(a) == to_ascii_lowercase(b)`.
    ///
    /// # Examples
    ///
    /// ```
    /// let lowercase_a = 97u8;
    /// let uppercase_a = 65u8;
    ///
    /// assert!(lowercase_a.eq_ignore_ascii_case(&uppercase_a));
    /// ```
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[rustc_const_stable(feature = "const_ascii_methods_on_intrinsics", since = "1.52.0")]
    #[inline]
    pub const fn eq_ignore_ascii_case(&self, other: &u8) -> bool {
        self.to_ascii_lowercase() == other.to_ascii_lowercase()
    }

    /// Converts this value to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new uppercased value without modifying the existing one, use
    /// [`to_ascii_uppercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// let mut byte = b'a';
    ///
    /// byte.make_ascii_uppercase();
    ///
    /// assert_eq!(b'A', byte);
    /// ```
    ///
    /// [`to_ascii_uppercase`]: Self::to_ascii_uppercase
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[rustc_const_stable(feature = "const_make_ascii", since = "1.84.0")]
    #[inline]
    pub const fn make_ascii_uppercase(&mut self) {
        *self = self.to_ascii_uppercase();
    }

    /// Converts this value to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new lowercased value without modifying the existing one, use
    /// [`to_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// let mut byte = b'A';
    ///
    /// byte.make_ascii_lowercase();
    ///
    /// assert_eq!(b'a', byte);
    /// ```
    ///
    /// [`to_ascii_lowercase`]: Self::to_ascii_lowercase
    #[stable(feature = "ascii_methods_on_intrinsics", since = "1.23.0")]
    #[rustc_const_stable(feature = "const_make_ascii", since = "1.84.0")]
    #[inline]
    pub const fn make_ascii_lowercase(&mut self) {
        *self = self.to_ascii_lowercase();
    }

    /// Checks if the value is an ASCII alphabetic character:
    ///
    /// - U+0041 'A' ..= U+005A 'Z', or
    /// - U+0061 'a' ..= U+007A 'z'.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_alphabetic());
    /// assert!(uppercase_g.is_ascii_alphabetic());
    /// assert!(a.is_ascii_alphabetic());
    /// assert!(g.is_ascii_alphabetic());
    /// assert!(!zero.is_ascii_alphabetic());
    /// assert!(!percent.is_ascii_alphabetic());
    /// assert!(!space.is_ascii_alphabetic());
    /// assert!(!lf.is_ascii_alphabetic());
    /// assert!(!esc.is_ascii_alphabetic());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_alphabetic(&self) -> bool {
        matches!(*self, b'A'..=b'Z' | b'a'..=b'z')
    }

    /// Checks if the value is an ASCII uppercase character:
    /// U+0041 'A' ..= U+005A 'Z'.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_uppercase());
    /// assert!(uppercase_g.is_ascii_uppercase());
    /// assert!(!a.is_ascii_uppercase());
    /// assert!(!g.is_ascii_uppercase());
    /// assert!(!zero.is_ascii_uppercase());
    /// assert!(!percent.is_ascii_uppercase());
    /// assert!(!space.is_ascii_uppercase());
    /// assert!(!lf.is_ascii_uppercase());
    /// assert!(!esc.is_ascii_uppercase());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_uppercase(&self) -> bool {
        matches!(*self, b'A'..=b'Z')
    }

    /// Checks if the value is an ASCII lowercase character:
    /// U+0061 'a' ..= U+007A 'z'.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_lowercase());
    /// assert!(!uppercase_g.is_ascii_lowercase());
    /// assert!(a.is_ascii_lowercase());
    /// assert!(g.is_ascii_lowercase());
    /// assert!(!zero.is_ascii_lowercase());
    /// assert!(!percent.is_ascii_lowercase());
    /// assert!(!space.is_ascii_lowercase());
    /// assert!(!lf.is_ascii_lowercase());
    /// assert!(!esc.is_ascii_lowercase());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_lowercase(&self) -> bool {
        matches!(*self, b'a'..=b'z')
    }

    /// Checks if the value is an ASCII alphanumeric character:
    ///
    /// - U+0041 'A' ..= U+005A 'Z', or
    /// - U+0061 'a' ..= U+007A 'z', or
    /// - U+0030 '0' ..= U+0039 '9'.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_alphanumeric());
    /// assert!(uppercase_g.is_ascii_alphanumeric());
    /// assert!(a.is_ascii_alphanumeric());
    /// assert!(g.is_ascii_alphanumeric());
    /// assert!(zero.is_ascii_alphanumeric());
    /// assert!(!percent.is_ascii_alphanumeric());
    /// assert!(!space.is_ascii_alphanumeric());
    /// assert!(!lf.is_ascii_alphanumeric());
    /// assert!(!esc.is_ascii_alphanumeric());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_alphanumeric(&self) -> bool {
        matches!(*self, b'0'..=b'9') | matches!(*self, b'A'..=b'Z') | matches!(*self, b'a'..=b'z')
    }

    /// Checks if the value is an ASCII decimal digit:
    /// U+0030 '0' ..= U+0039 '9'.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_digit());
    /// assert!(!uppercase_g.is_ascii_digit());
    /// assert!(!a.is_ascii_digit());
    /// assert!(!g.is_ascii_digit());
    /// assert!(zero.is_ascii_digit());
    /// assert!(!percent.is_ascii_digit());
    /// assert!(!space.is_ascii_digit());
    /// assert!(!lf.is_ascii_digit());
    /// assert!(!esc.is_ascii_digit());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_digit(&self) -> bool {
        matches!(*self, b'0'..=b'9')
    }

    /// Checks if the value is an ASCII octal digit:
    /// U+0030 '0' ..= U+0037 '7'.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(is_ascii_octdigit)]
    ///
    /// let uppercase_a = b'A';
    /// let a = b'a';
    /// let zero = b'0';
    /// let seven = b'7';
    /// let nine = b'9';
    /// let percent = b'%';
    /// let lf = b'\n';
    ///
    /// assert!(!uppercase_a.is_ascii_octdigit());
    /// assert!(!a.is_ascii_octdigit());
    /// assert!(zero.is_ascii_octdigit());
    /// assert!(seven.is_ascii_octdigit());
    /// assert!(!nine.is_ascii_octdigit());
    /// assert!(!percent.is_ascii_octdigit());
    /// assert!(!lf.is_ascii_octdigit());
    /// ```
    #[must_use]
    #[unstable(feature = "is_ascii_octdigit", issue = "101288")]
    #[inline]
    pub const fn is_ascii_octdigit(&self) -> bool {
        matches!(*self, b'0'..=b'7')
    }

    /// Checks if the value is an ASCII hexadecimal digit:
    ///
    /// - U+0030 '0' ..= U+0039 '9', or
    /// - U+0041 'A' ..= U+0046 'F', or
    /// - U+0061 'a' ..= U+0066 'f'.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_hexdigit());
    /// assert!(!uppercase_g.is_ascii_hexdigit());
    /// assert!(a.is_ascii_hexdigit());
    /// assert!(!g.is_ascii_hexdigit());
    /// assert!(zero.is_ascii_hexdigit());
    /// assert!(!percent.is_ascii_hexdigit());
    /// assert!(!space.is_ascii_hexdigit());
    /// assert!(!lf.is_ascii_hexdigit());
    /// assert!(!esc.is_ascii_hexdigit());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_hexdigit(&self) -> bool {
        matches!(*self, b'0'..=b'9') | matches!(*self, b'A'..=b'F') | matches!(*self, b'a'..=b'f')
    }

    /// Checks if the value is an ASCII punctuation character:
    ///
    /// - U+0021 ..= U+002F `! " # $ % & ' ( ) * + , - . /`, or
    /// - U+003A ..= U+0040 `: ; < = > ? @`, or
    /// - U+005B ..= U+0060 `` [ \ ] ^ _ ` ``, or
    /// - U+007B ..= U+007E `{ | } ~`
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_punctuation());
    /// assert!(!uppercase_g.is_ascii_punctuation());
    /// assert!(!a.is_ascii_punctuation());
    /// assert!(!g.is_ascii_punctuation());
    /// assert!(!zero.is_ascii_punctuation());
    /// assert!(percent.is_ascii_punctuation());
    /// assert!(!space.is_ascii_punctuation());
    /// assert!(!lf.is_ascii_punctuation());
    /// assert!(!esc.is_ascii_punctuation());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_punctuation(&self) -> bool {
        matches!(*self, b'!'..=b'/')
            | matches!(*self, b':'..=b'@')
            | matches!(*self, b'['..=b'`')
            | matches!(*self, b'{'..=b'~')
    }

    /// Checks if the value is an ASCII graphic character:
    /// U+0021 '!' ..= U+007E '~'.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_graphic());
    /// assert!(uppercase_g.is_ascii_graphic());
    /// assert!(a.is_ascii_graphic());
    /// assert!(g.is_ascii_graphic());
    /// assert!(zero.is_ascii_graphic());
    /// assert!(percent.is_ascii_graphic());
    /// assert!(!space.is_ascii_graphic());
    /// assert!(!lf.is_ascii_graphic());
    /// assert!(!esc.is_ascii_graphic());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_graphic(&self) -> bool {
        matches!(*self, b'!'..=b'~')
    }

    /// Checks if the value is an ASCII whitespace character:
    /// U+0020 SPACE, U+0009 HORIZONTAL TAB, U+000A LINE FEED,
    /// U+000C FORM FEED, or U+000D CARRIAGE RETURN.
    ///
    /// Rust uses the WhatWG Infra Standard's [definition of ASCII
    /// whitespace][infra-aw]. There are several other definitions in
    /// wide use. For instance, [the POSIX locale][pct] includes
    /// U+000B VERTICAL TAB as well as all the above characters,
    /// but—from the very same specification—[the default rule for
    /// "field splitting" in the Bourne shell][bfs] considers *only*
    /// SPACE, HORIZONTAL TAB, and LINE FEED as whitespace.
    ///
    /// If you are writing a program that will process an existing
    /// file format, check what that format's definition of whitespace is
    /// before using this function.
    ///
    /// [infra-aw]: https://infra.spec.whatwg.org/#ascii-whitespace
    /// [pct]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap07.html#tag_07_03_01
    /// [bfs]: https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_06_05
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_whitespace());
    /// assert!(!uppercase_g.is_ascii_whitespace());
    /// assert!(!a.is_ascii_whitespace());
    /// assert!(!g.is_ascii_whitespace());
    /// assert!(!zero.is_ascii_whitespace());
    /// assert!(!percent.is_ascii_whitespace());
    /// assert!(space.is_ascii_whitespace());
    /// assert!(lf.is_ascii_whitespace());
    /// assert!(!esc.is_ascii_whitespace());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_whitespace(&self) -> bool {
        matches!(*self, b'\t' | b'\n' | b'\x0C' | b'\r' | b' ')
    }

    /// Checks if the value is an ASCII control character:
    /// U+0000 NUL ..= U+001F UNIT SEPARATOR, or U+007F DELETE.
    /// Note that most ASCII whitespace characters are control
    /// characters, but SPACE is not.
    ///
    /// # Examples
    ///
    /// ```
    /// let uppercase_a = b'A';
    /// let uppercase_g = b'G';
    /// let a = b'a';
    /// let g = b'g';
    /// let zero = b'0';
    /// let percent = b'%';
    /// let space = b' ';
    /// let lf = b'\n';
    /// let esc = b'\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_control());
    /// assert!(!uppercase_g.is_ascii_control());
    /// assert!(!a.is_ascii_control());
    /// assert!(!g.is_ascii_control());
    /// assert!(!zero.is_ascii_control());
    /// assert!(!percent.is_ascii_control());
    /// assert!(!space.is_ascii_control());
    /// assert!(lf.is_ascii_control());
    /// assert!(esc.is_ascii_control());
    /// ```
    #[must_use]
    #[stable(feature = "ascii_ctype_on_intrinsics", since = "1.24.0")]
    #[rustc_const_stable(feature = "const_ascii_ctype_on_intrinsics", since = "1.47.0")]
    #[inline]
    pub const fn is_ascii_control(&self) -> bool {
        matches!(*self, b'\0'..=b'\x1F' | b'\x7F')
    }

    /// Returns an iterator that produces an escaped version of a `u8`,
    /// treating it as an ASCII character.
    ///
    /// The behavior is identical to [`ascii::escape_default`].
    ///
    /// # Examples
    ///
    /// ```
    ///
    /// assert_eq!("0", b'0'.escape_ascii().to_string());
    /// assert_eq!("\\t", b'\t'.escape_ascii().to_string());
    /// assert_eq!("\\r", b'\r'.escape_ascii().to_string());
    /// assert_eq!("\\n", b'\n'.escape_ascii().to_string());
    /// assert_eq!("\\'", b'\''.escape_ascii().to_string());
    /// assert_eq!("\\\"", b'"'.escape_ascii().to_string());
    /// assert_eq!("\\\\", b'\\'.escape_ascii().to_string());
    /// assert_eq!("\\x9d", b'\x9d'.escape_ascii().to_string());
    /// ```
    #[must_use = "this returns the escaped byte as an iterator, \
                  without modifying the original"]
    #[stable(feature = "inherent_ascii_escape", since = "1.60.0")]
    #[inline]
    pub fn escape_ascii(self) -> ascii::EscapeDefault {
        ascii::escape_default(self)
    }

    #[inline]
    pub(crate) const fn is_utf8_char_boundary(self) -> bool {
        // This is bit magic equivalent to: b < 128 || b >= 192
        (self as i8) >= -0x40
    }
}

impl u16 {
    uint_impl! {
        Self = u16,
        ActualT = u16,
        SignedT = i16,
        BITS = 16,
        BITS_MINUS_ONE = 15,
        MAX = 65535,
        rot = 4,
        rot_op = "0xa003",
        rot_result = "0x3a",
        swap_op = "0x1234",
        swapped = "0x3412",
        reversed = "0x2c48",
        le_bytes = "[0x34, 0x12]",
        be_bytes = "[0x12, 0x34]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { u16, u32, unsigned }

    /// Checks if the value is a Unicode surrogate code point, which are disallowed values for [`char`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(utf16_extra)]
    ///
    /// let low_non_surrogate = 0xA000u16;
    /// let low_surrogate = 0xD800u16;
    /// let high_surrogate = 0xDC00u16;
    /// let high_non_surrogate = 0xE000u16;
    ///
    /// assert!(!low_non_surrogate.is_utf16_surrogate());
    /// assert!(low_surrogate.is_utf16_surrogate());
    /// assert!(high_surrogate.is_utf16_surrogate());
    /// assert!(!high_non_surrogate.is_utf16_surrogate());
    /// ```
    #[must_use]
    #[unstable(feature = "utf16_extra", issue = "94919")]
    #[inline]
    pub const fn is_utf16_surrogate(self) -> bool {
        matches!(self, 0xD800..=0xDFFF)
    }
}

impl u32 {
    uint_impl! {
        Self = u32,
        ActualT = u32,
        SignedT = i32,
        BITS = 32,
        BITS_MINUS_ONE = 31,
        MAX = 4294967295,
        rot = 8,
        rot_op = "0x10000b3",
        rot_result = "0xb301",
        swap_op = "0x12345678",
        swapped = "0x78563412",
        reversed = "0x1e6a2c48",
        le_bytes = "[0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { u32, u64, unsigned }
}

impl u64 {
    uint_impl! {
        Self = u64,
        ActualT = u64,
        SignedT = i64,
        BITS = 64,
        BITS_MINUS_ONE = 63,
        MAX = 18446744073709551615,
        rot = 12,
        rot_op = "0xaa00000000006e1",
        rot_result = "0x6e10aa",
        swap_op = "0x1234567890123456",
        swapped = "0x5634129078563412",
        reversed = "0x6a2c48091e6a2c48",
        le_bytes = "[0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { u64, u128, unsigned }
}

impl u128 {
    uint_impl! {
        Self = u128,
        ActualT = u128,
        SignedT = i128,
        BITS = 128,
        BITS_MINUS_ONE = 127,
        MAX = 340282366920938463463374607431768211455,
        rot = 16,
        rot_op = "0x13f40000000000000000000000004f76",
        rot_result = "0x4f7613f4",
        swap_op = "0x12345678901234567890123456789012",
        swapped = "0x12907856341290785634129078563412",
        reversed = "0x48091e6a2c48091e6a2c48091e6a2c48",
        le_bytes = "[0x12, 0x90, 0x78, 0x56, 0x34, 0x12, 0x90, 0x78, \
            0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56, \
            0x78, 0x90, 0x12, 0x34, 0x56, 0x78, 0x90, 0x12]",
        to_xe_bytes_doc = "",
        from_xe_bytes_doc = "",
        bound_condition = "",
    }
    midpoint_impl! { u128, unsigned }
}

#[cfg(target_pointer_width = "16")]
impl usize {
    uint_impl! {
        Self = usize,
        ActualT = u16,
        SignedT = isize,
        BITS = 16,
        BITS_MINUS_ONE = 15,
        MAX = 65535,
        rot = 4,
        rot_op = "0xa003",
        rot_result = "0x3a",
        swap_op = "0x1234",
        swapped = "0x3412",
        reversed = "0x2c48",
        le_bytes = "[0x34, 0x12]",
        be_bytes = "[0x12, 0x34]",
        to_xe_bytes_doc = usize_isize_to_xe_bytes_doc!(),
        from_xe_bytes_doc = usize_isize_from_xe_bytes_doc!(),
        bound_condition = " on 16-bit targets",
    }
    midpoint_impl! { usize, u32, unsigned }
}

#[cfg(target_pointer_width = "32")]
impl usize {
    uint_impl! {
        Self = usize,
        ActualT = u32,
        SignedT = isize,
        BITS = 32,
        BITS_MINUS_ONE = 31,
        MAX = 4294967295,
        rot = 8,
        rot_op = "0x10000b3",
        rot_result = "0xb301",
        swap_op = "0x12345678",
        swapped = "0x78563412",
        reversed = "0x1e6a2c48",
        le_bytes = "[0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78]",
        to_xe_bytes_doc = usize_isize_to_xe_bytes_doc!(),
        from_xe_bytes_doc = usize_isize_from_xe_bytes_doc!(),
        bound_condition = " on 32-bit targets",
    }
    midpoint_impl! { usize, u64, unsigned }
}

#[cfg(target_pointer_width = "64")]
impl usize {
    uint_impl! {
        Self = usize,
        ActualT = u64,
        SignedT = isize,
        BITS = 64,
        BITS_MINUS_ONE = 63,
        MAX = 18446744073709551615,
        rot = 12,
        rot_op = "0xaa00000000006e1",
        rot_result = "0x6e10aa",
        swap_op = "0x1234567890123456",
        swapped = "0x5634129078563412",
        reversed = "0x6a2c48091e6a2c48",
        le_bytes = "[0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]",
        be_bytes = "[0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56]",
        to_xe_bytes_doc = usize_isize_to_xe_bytes_doc!(),
        from_xe_bytes_doc = usize_isize_from_xe_bytes_doc!(),
        bound_condition = " on 64-bit targets",
    }
    midpoint_impl! { usize, u128, unsigned }
}

impl usize {
    /// Returns an `usize` where every byte is equal to `x`.
    #[inline]
    pub(crate) const fn repeat_u8(x: u8) -> usize {
        usize::from_ne_bytes([x; mem::size_of::<usize>()])
    }

    /// Returns an `usize` where every byte pair is equal to `x`.
    #[inline]
    pub(crate) const fn repeat_u16(x: u16) -> usize {
        let mut r = 0usize;
        let mut i = 0;
        while i < mem::size_of::<usize>() {
            // Use `wrapping_shl` to make it work on targets with 16-bit `usize`
            r = r.wrapping_shl(16) | (x as usize);
            i += 2;
        }
        r
    }
}

/// A classification of floating point numbers.
///
/// This `enum` is used as the return type for [`f32::classify`] and [`f64::classify`]. See
/// their documentation for more.
///
/// # Examples
///
/// ```
/// use std::num::FpCategory;
///
/// let num = 12.4_f32;
/// let inf = f32::INFINITY;
/// let zero = 0f32;
/// let sub: f32 = 1.1754942e-38;
/// let nan = f32::NAN;
///
/// assert_eq!(num.classify(), FpCategory::Normal);
/// assert_eq!(inf.classify(), FpCategory::Infinite);
/// assert_eq!(zero.classify(), FpCategory::Zero);
/// assert_eq!(sub.classify(), FpCategory::Subnormal);
/// assert_eq!(nan.classify(), FpCategory::Nan);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[stable(feature = "rust1", since = "1.0.0")]
pub enum FpCategory {
    /// NaN (not a number): this value results from calculations like `(-1.0).sqrt()`.
    ///
    /// See [the documentation for `f32`](f32) for more information on the unusual properties
    /// of NaN.
    #[stable(feature = "rust1", since = "1.0.0")]
    Nan,

    /// Positive or negative infinity, which often results from dividing a nonzero number
    /// by zero.
    #[stable(feature = "rust1", since = "1.0.0")]
    Infinite,

    /// Positive or negative zero.
    ///
    /// See [the documentation for `f32`](f32) for more information on the signedness of zeroes.
    #[stable(feature = "rust1", since = "1.0.0")]
    Zero,

    /// “Subnormal” or “denormal” floating point representation (less precise, relative to
    /// their magnitude, than [`Normal`]).
    ///
    /// Subnormal numbers are larger in magnitude than [`Zero`] but smaller in magnitude than all
    /// [`Normal`] numbers.
    ///
    /// [`Normal`]: Self::Normal
    /// [`Zero`]: Self::Zero
    #[stable(feature = "rust1", since = "1.0.0")]
    Subnormal,

    /// A regular floating point number, not any of the exceptional categories.
    ///
    /// The smallest positive normal numbers are [`f32::MIN_POSITIVE`] and [`f64::MIN_POSITIVE`],
    /// and the largest positive normal numbers are [`f32::MAX`] and [`f64::MAX`]. (Unlike signed
    /// integers, floating point numbers are symmetric in their range, so negating any of these
    /// constants will produce their negative counterpart.)
    #[stable(feature = "rust1", since = "1.0.0")]
    Normal,
}

/// Determines if a string of text of that length of that radix could be guaranteed to be
/// stored in the given type T.
/// Note that if the radix is known to the compiler, it is just the check of digits.len that
/// is done at runtime.
#[doc(hidden)]
#[inline(always)]
#[unstable(issue = "none", feature = "std_internals")]
pub const fn can_not_overflow<T>(radix: u32, is_signed_ty: bool, digits: &[u8]) -> bool {
    radix <= 16 && digits.len() <= mem::size_of::<T>() * 2 - is_signed_ty as usize
}

#[cfg_attr(not(feature = "panic_immediate_abort"), inline(never))]
#[cfg_attr(feature = "panic_immediate_abort", inline)]
#[cold]
#[track_caller]
const fn from_ascii_radix_panic(radix: u32) -> ! {
    const_panic!(
        "from_ascii_radix: radix must lie in the range `[2, 36]`",
        "from_ascii_radix: radix must lie in the range `[2, 36]` - found {radix}",
        radix: u32 = radix,
    )
}

macro_rules! from_str_int_impl {
    ($signedness:ident $($int_ty:ty)+) => {$(
        #[stable(feature = "rust1", since = "1.0.0")]
        impl FromStr for $int_ty {
            type Err = ParseIntError;

            /// Parses an integer from a string slice with decimal digits.
            ///
            /// The characters are expected to be an optional
            #[doc = sign_dependent_expr!{
                $signedness ?
                if signed {
                    " `+` or `-` "
                }
                if unsigned {
                    " `+` "
                }
            }]
            /// sign followed by only digits. Leading and trailing non-digit characters (including
            /// whitespace) represent an error. Underscores (which are accepted in Rust literals)
            /// also represent an error.
            ///
            /// # Examples
            ///
            /// Basic usage:
            /// ```
            /// use std::str::FromStr;
            ///
            #[doc = concat!("assert_eq!(", stringify!($int_ty), "::from_str(\"+10\"), Ok(10));")]
            /// ```
            /// Trailing space returns error:
            /// ```
            /// # use std::str::FromStr;
            /// #
            #[doc = concat!("assert!(", stringify!($int_ty), "::from_str(\"1 \").is_err());")]
            /// ```
            #[inline]
            fn from_str(src: &str) -> Result<$int_ty, ParseIntError> {
                <$int_ty>::from_str_radix(src, 10)
            }
        }

        impl $int_ty {
            /// Parses an integer from a string slice with digits in a given base.
            ///
            /// The string is expected to be an optional
            #[doc = sign_dependent_expr!{
                $signedness ?
                if signed {
                    " `+` or `-` "
                }
                if unsigned {
                    " `+` "
                }
            }]
            /// sign followed by only digits. Leading and trailing non-digit characters (including
            /// whitespace) represent an error. Underscores (which are accepted in Rust literals)
            /// also represent an error.
            ///
            /// Digits are a subset of these characters, depending on `radix`:
            /// * `0-9`
            /// * `a-z`
            /// * `A-Z`
            ///
            /// # Panics
            ///
            /// This function panics if `radix` is not in the range from 2 to 36.
            ///
            /// # Examples
            ///
            /// Basic usage:
            /// ```
            #[doc = concat!("assert_eq!(", stringify!($int_ty), "::from_str_radix(\"A\", 16), Ok(10));")]
            /// ```
            /// Trailing space returns error:
            /// ```
            #[doc = concat!("assert!(", stringify!($int_ty), "::from_str_radix(\"1 \", 10).is_err());")]
            /// ```
            #[stable(feature = "rust1", since = "1.0.0")]
            #[rustc_const_stable(feature = "const_int_from_str", since = "1.82.0")]
            #[inline]
            pub const fn from_str_radix(src: &str, radix: u32) -> Result<$int_ty, ParseIntError> {
                <$int_ty>::from_ascii_radix(src.as_bytes(), radix)
            }

            /// Parses an integer from an ASCII-byte slice with decimal digits.
            ///
            /// The characters are expected to be an optional
            #[doc = sign_dependent_expr!{
                $signedness ?
                if signed {
                    " `+` or `-` "
                }
                if unsigned {
                    " `+` "
                }
            }]
            /// sign followed by only digits. Leading and trailing non-digit characters (including
            /// whitespace) represent an error. Underscores (which are accepted in Rust literals)
            /// also represent an error.
            ///
            /// # Examples
            ///
            /// Basic usage:
            /// ```
            /// #![feature(int_from_ascii)]
            ///
            #[doc = concat!("assert_eq!(", stringify!($int_ty), "::from_ascii(b\"+10\"), Ok(10));")]
            /// ```
            /// Trailing space returns error:
            /// ```
            /// # #![feature(int_from_ascii)]
            /// #
            #[doc = concat!("assert!(", stringify!($int_ty), "::from_ascii(b\"1 \").is_err());")]
            /// ```
            #[unstable(feature = "int_from_ascii", issue = "134821")]
            #[inline]
            pub const fn from_ascii(src: &[u8]) -> Result<$int_ty, ParseIntError> {
                <$int_ty>::from_ascii_radix(src, 10)
            }

            /// Parses an integer from an ASCII-byte slice with digits in a given base.
            ///
            /// The characters are expected to be an optional
            #[doc = sign_dependent_expr!{
                $signedness ?
                if signed {
                    " `+` or `-` "
                }
                if unsigned {
                    " `+` "
                }
            }]
            /// sign followed by only digits. Leading and trailing non-digit characters (including
            /// whitespace) represent an error. Underscores (which are accepted in Rust literals)
            /// also represent an error.
            ///
            /// Digits are a subset of these characters, depending on `radix`:
            /// * `0-9`
            /// * `a-z`
            /// * `A-Z`
            ///
            /// # Panics
            ///
            /// This function panics if `radix` is not in the range from 2 to 36.
            ///
            /// # Examples
            ///
            /// Basic usage:
            /// ```
            /// #![feature(int_from_ascii)]
            ///
            #[doc = concat!("assert_eq!(", stringify!($int_ty), "::from_ascii_radix(b\"A\", 16), Ok(10));")]
            /// ```
            /// Trailing space returns error:
            /// ```
            /// # #![feature(int_from_ascii)]
            /// #
            #[doc = concat!("assert!(", stringify!($int_ty), "::from_ascii_radix(b\"1 \", 10).is_err());")]
            /// ```
            #[unstable(feature = "int_from_ascii", issue = "134821")]
            #[inline]
            pub const fn from_ascii_radix(src: &[u8], radix: u32) -> Result<$int_ty, ParseIntError> {
                use self::IntErrorKind::*;
                use self::ParseIntError as PIE;

                if 2 > radix || radix > 36 {
                    from_ascii_radix_panic(radix);
                }

                if src.is_empty() {
                    return Err(PIE { kind: Empty });
                }

                #[allow(unused_comparisons)]
                let is_signed_ty = 0 > <$int_ty>::MIN;

                let (is_positive, mut digits) = match src {
                    [b'+' | b'-'] => {
                        return Err(PIE { kind: InvalidDigit });
                    }
                    [b'+', rest @ ..] => (true, rest),
                    [b'-', rest @ ..] if is_signed_ty => (false, rest),
                    _ => (true, src),
                };

                let mut result = 0;

                macro_rules! unwrap_or_PIE {
                    ($option:expr, $kind:ident) => {
                        match $option {
                            Some(value) => value,
                            None => return Err(PIE { kind: $kind }),
                        }
                    };
                }

                if can_not_overflow::<$int_ty>(radix, is_signed_ty, digits) {
                    // If the len of the str is short compared to the range of the type
                    // we are parsing into, then we can be certain that an overflow will not occur.
                    // This bound is when `radix.pow(digits.len()) - 1 <= T::MAX` but the condition
                    // above is a faster (conservative) approximation of this.
                    //
                    // Consider radix 16 as it has the highest information density per digit and will thus overflow the earliest:
                    // `u8::MAX` is `ff` - any str of len 2 is guaranteed to not overflow.
                    // `i8::MAX` is `7f` - only a str of len 1 is guaranteed to not overflow.
                    macro_rules! run_unchecked_loop {
                        ($unchecked_additive_op:tt) => {{
                            while let [c, rest @ ..] = digits {
                                result = result * (radix as $int_ty);
                                let x = unwrap_or_PIE!((*c as char).to_digit(radix), InvalidDigit);
                                result = result $unchecked_additive_op (x as $int_ty);
                                digits = rest;
                            }
                        }};
                    }
                    if is_positive {
                        run_unchecked_loop!(+)
                    } else {
                        run_unchecked_loop!(-)
                    };
                } else {
                    macro_rules! run_checked_loop {
                        ($checked_additive_op:ident, $overflow_err:ident) => {{
                            while let [c, rest @ ..] = digits {
                                // When `radix` is passed in as a literal, rather than doing a slow `imul`
                                // the compiler can use shifts if `radix` can be expressed as a
                                // sum of powers of 2 (x*10 can be written as x*8 + x*2).
                                // When the compiler can't use these optimisations,
                                // the latency of the multiplication can be hidden by issuing it
                                // before the result is needed to improve performance on
                                // modern out-of-order CPU as multiplication here is slower
                                // than the other instructions, we can get the end result faster
                                // doing multiplication first and let the CPU spends other cycles
                                // doing other computation and get multiplication result later.
                                let mul = result.checked_mul(radix as $int_ty);
                                let x = unwrap_or_PIE!((*c as char).to_digit(radix), InvalidDigit) as $int_ty;
                                result = unwrap_or_PIE!(mul, $overflow_err);
                                result = unwrap_or_PIE!(<$int_ty>::$checked_additive_op(result, x), $overflow_err);
                                digits = rest;
                            }
                        }};
                    }
                    if is_positive {
                        run_checked_loop!(checked_add, PosOverflow)
                    } else {
                        run_checked_loop!(checked_sub, NegOverflow)
                    };
                }
                Ok(result)
            }
        }
    )*}
}

from_str_int_impl! { signed isize i8 i16 i32 i64 i128 }
from_str_int_impl! { unsigned usize u8 u16 u32 u64 u128 }

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    // Verify `unchecked_{add, sub, mul}`
    macro_rules! generate_unchecked_math_harness {
        ($type:ty, $method:ident, $harness_name:ident) => {
            #[kani::proof_for_contract($type::$method)]
            pub fn $harness_name() {
                let num1: $type = kani::any::<$type>();
                let num2: $type = kani::any::<$type>();

                unsafe {
                    num1.$method(num2);
                }
            }
        };
    }

    // Improve unchecked_mul performance for {32, 64, 128}-bit integer types
    // by adding upper and lower limits for inputs
    macro_rules! generate_unchecked_mul_intervals {
        ($type:ty, $method:ident, $($harness_name:ident, $min:expr, $max:expr),+) => {
            $(
                #[kani::proof_for_contract($type::$method)]
                pub fn $harness_name() {
                    let num1: $type = kani::any::<$type>();
                    let num2: $type = kani::any::<$type>();

                    kani::assume(num1 >= $min && num1 <= $max);
                    kani::assume(num2 >= $min && num2 <= $max);

                    // Ensure that multiplication does not overflow
                    kani::assume(!num1.overflowing_mul(num2).1);

                    unsafe {
                        num1.$method(num2);
                    }
                }
            )+
        }
    }

    // Verify `unchecked_{shl, shr}`
    macro_rules! generate_unchecked_shift_harness {
        ($type:ty, $method:ident, $harness_name:ident) => {
            #[kani::proof_for_contract($type::$method)]
            pub fn $harness_name() {
                let num1: $type = kani::any::<$type>();
                let num2: u32 = kani::any::<u32>();

                unsafe {
                    num1.$method(num2);
                }
            }
        };
    }

    macro_rules! generate_unchecked_neg_harness {
        ($type:ty, $harness_name:ident) => {
            #[kani::proof_for_contract($type::unchecked_neg)]
            pub fn $harness_name() {
                let num1: $type = kani::any::<$type>();

                unsafe {
                    num1.unchecked_neg();
                }
            }
        };
    }

    /// A macro to generate Kani proof harnesses for the `carrying_mul` method,
    ///
    /// The macro creates multiple harnesses for different ranges of input values,
    /// allowing testing of both small and large inputs.
    ///
    /// # Parameters:
    /// - `$type`: The integer type (e.g., u8, u16) for which the `carrying_mul` function is being tested.
    /// - `$wide_type`: A wider type to simulate the multiplication (e.g., u16 for u8, u32 for u16).
    /// - `$harness_name`: The name of the Kani harness to be generated.
    /// - `$min`: The minimum value for the range of inputs for `lhs`, `rhs`, and `carry_in`.
    /// - `$max`: The maximum value for the range of inputs for `lhs`, `rhs`, and `carry_in`.
    macro_rules! generate_carrying_mul_intervals {
        ($type:ty, $wide_type:ty, $($harness_name:ident, $min:expr, $max:expr),+) => {
            $(
                #[kani::proof]
                #[kani::solver(kissat)]
                pub fn $harness_name() {
                    let lhs: $type = kani::any::<$type>();
                    let rhs: $type = kani::any::<$type>();
                    let carry_in: $type = kani::any::<$type>();

                    kani::assume(lhs >= $min && lhs <= $max);
                    kani::assume(rhs >= $min && rhs <= $max);
                    kani::assume(carry_in >= $min && carry_in <= $max);

                    // Perform the carrying multiplication
                    let (result, carry_out) = lhs.carrying_mul(rhs, carry_in);

                    // Manually compute the expected result and carry using wider type
                    let wide_result = (lhs as $wide_type)
                        .wrapping_mul(rhs as $wide_type)
                        .wrapping_add(carry_in as $wide_type);

                    let expected_result = wide_result as $type;
                    let expected_carry = (wide_result >> <$type>::BITS) as $type;

                    // Assert the result and carry are correct
                    assert_eq!(result, expected_result);
                    assert_eq!(carry_out, expected_carry);
                }
            )+
        }
    }

    // Part 2 : Nested unsafe functions Generation Macros --> https://github.com/verify-rust-std/blob/main/doc/src/challenges/0011-floats-ints.md

    // Verify `widening_mul`, which internally uses `unchecked_mul`
    macro_rules! generate_widening_mul_intervals {
        ($type:ty, $wide_type:ty, $($harness_name:ident, $min:expr, $max:expr),+) => {
            $(
                #[kani::proof]
                pub fn $harness_name() {
                    let lhs: $type = kani::any::<$type>();
                    let rhs: $type = kani::any::<$type>();

                    kani::assume(lhs >= $min && lhs <= $max);
                    kani::assume(rhs >= $min && rhs <= $max);

                    let (result_low, result_high) = lhs.widening_mul(rhs);

                    // Compute expected result using wider type
                    let expected = (lhs as $wide_type) * (rhs as $wide_type);

                    let expected_low = expected as $type;
                    let expected_high = (expected >> <$type>::BITS) as $type;

                    assert_eq!(result_low, expected_low);
                    assert_eq!(result_high, expected_high);
                }
            )+
        }
    }

    // Verify `wrapping_{shl, shr}` which internally uses `unchecked_{shl,shr}`
    macro_rules! generate_wrapping_shift_harness {
        ($type:ty, $method:ident, $harness_name:ident) => {
            #[kani::proof_for_contract($type::$method)]
            pub fn $harness_name() {
                let num1: $type = kani::any::<$type>();
                let num2: u32 = kani::any::<u32>();

                let _ = num1.$method(num2);
            }
        };
    }

    // Part 3: Float to Integer Conversion function Harness Generation Macro
    macro_rules! generate_to_int_unchecked_harness {
        ($floatType:ty, $($intType:ty, $harness_name:ident),+) => {
            $(
                #[kani::proof_for_contract($floatType::to_int_unchecked)]
                pub fn $harness_name() {
                    let num1: $floatType = kani::any::<$floatType>();
                    let result = unsafe { num1.to_int_unchecked::<$intType>() };

                    assert_eq!(result, num1 as $intType);
                }
            )+
        }
    }

    // `unchecked_add` proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total
    //
    // Target contracts:
    // Preconditions: No overflow should occur
    // #[requires(!self.overflowing_add(rhs).1)]
    //
    // Target function:
    // pub const unsafe fn unchecked_add(self, rhs: Self) -> Self
    generate_unchecked_math_harness!(i8, unchecked_add, checked_unchecked_add_i8);
    generate_unchecked_math_harness!(i16, unchecked_add, checked_unchecked_add_i16);
    generate_unchecked_math_harness!(i32, unchecked_add, checked_unchecked_add_i32);
    generate_unchecked_math_harness!(i64, unchecked_add, checked_unchecked_add_i64);
    generate_unchecked_math_harness!(i128, unchecked_add, checked_unchecked_add_i128);
    generate_unchecked_math_harness!(isize, unchecked_add, checked_unchecked_add_isize);
    generate_unchecked_math_harness!(u8, unchecked_add, checked_unchecked_add_u8);
    generate_unchecked_math_harness!(u16, unchecked_add, checked_unchecked_add_u16);
    generate_unchecked_math_harness!(u32, unchecked_add, checked_unchecked_add_u32);
    generate_unchecked_math_harness!(u64, unchecked_add, checked_unchecked_add_u64);
    generate_unchecked_math_harness!(u128, unchecked_add, checked_unchecked_add_u128);
    generate_unchecked_math_harness!(usize, unchecked_add, checked_unchecked_add_usize);

    // `unchecked_neg` proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} -- 6 types in total
    //
    // Target contracts:
    // #[requires(self != $SelfT::MIN)]
    //
    // Target function:
    // pub const unsafe fn unchecked_neg(self) -> Self
    generate_unchecked_neg_harness!(i8, checked_unchecked_neg_i8);
    generate_unchecked_neg_harness!(i16, checked_unchecked_neg_i16);
    generate_unchecked_neg_harness!(i32, checked_unchecked_neg_i32);
    generate_unchecked_neg_harness!(i64, checked_unchecked_neg_i64);
    generate_unchecked_neg_harness!(i128, checked_unchecked_neg_i128);
    generate_unchecked_neg_harness!(isize, checked_unchecked_neg_isize);

    // `unchecked_mul` proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total, with different interval checks for each.
    // Total types of checks including intervals -- 36
    //
    // Target contracts:
    // Preconditions: No overflow should occur
    // #[requires(!self.overflowing_mul(rhs).1)]
    //
    // Target function:
    // pub const unsafe fn unchecked_mul(self, rhs: Self) -> Self
    // exponential state spaces for 32,64 and 128, hence provided limited range for verification.
    generate_unchecked_math_harness!(i8, unchecked_mul, checked_unchecked_mul_i8);
    generate_unchecked_math_harness!(i16, unchecked_mul, checked_unchecked_mul_i16);

    // ====================== i32 Harnesses ======================
    generate_unchecked_mul_intervals!(
        i32,
        unchecked_mul,
        unchecked_mul_i32_small,
        -10i32,
        10i32,
        unchecked_mul_i32_large_pos,
        i32::MAX - 1000i32,
        i32::MAX,
        unchecked_mul_i32_large_neg,
        i32::MIN,
        i32::MIN + 1000i32,
        unchecked_mul_i32_edge_pos,
        i32::MAX / 2,
        i32::MAX,
        unchecked_mul_i32_edge_neg,
        i32::MIN,
        i32::MIN / 2
    );
    // ====================== i64 Harnesses ======================
    generate_unchecked_mul_intervals!(
        i64,
        unchecked_mul,
        unchecked_mul_i64_small,
        -10i64,
        10i64,
        unchecked_mul_i64_large_pos,
        i64::MAX - 1000i64,
        i64::MAX,
        unchecked_mul_i64_large_neg,
        i64::MIN,
        i64::MIN + 1000i64,
        unchecked_mul_i64_edge_pos,
        i64::MAX / 2,
        i64::MAX,
        unchecked_mul_i64_edge_neg,
        i64::MIN,
        i64::MIN / 2
    );
    // ====================== i128 Harnesses ======================
    generate_unchecked_mul_intervals!(
        i128,
        unchecked_mul,
        unchecked_mul_i128_small,
        -10i128,
        10i128,
        unchecked_mul_i128_large_pos,
        i128::MAX - 1000i128,
        i128::MAX,
        unchecked_mul_i128_large_neg,
        i128::MIN,
        i128::MIN + 1000i128,
        unchecked_mul_i128_edge_pos,
        i128::MAX / 2,
        i128::MAX,
        unchecked_mul_i128_edge_neg,
        i128::MIN,
        i128::MIN / 2
    );
    // ====================== isize Harnesses ======================
    generate_unchecked_mul_intervals!(
        isize,
        unchecked_mul,
        unchecked_mul_isize_small,
        -10isize,
        10isize,
        unchecked_mul_isize_large_pos,
        isize::MAX - 1000isize,
        isize::MAX,
        unchecked_mul_isize_large_neg,
        isize::MIN,
        isize::MIN + 1000isize,
        unchecked_mul_isize_edge_pos,
        isize::MAX / 2,
        isize::MAX,
        unchecked_mul_isize_edge_neg,
        isize::MIN,
        isize::MIN / 2
    );

    generate_unchecked_math_harness!(u8, unchecked_mul, checked_unchecked_mul_u8);
    generate_unchecked_math_harness!(u16, unchecked_mul, checked_unchecked_mul_u16);

    // ====================== u32 Harnesses ======================
    generate_unchecked_mul_intervals!(
        u32,
        unchecked_mul,
        unchecked_mul_u32_small,
        0u32,
        10u32,
        unchecked_mul_u32_large,
        u32::MAX - 1000u32,
        u32::MAX,
        unchecked_mul_u32_edge,
        u32::MAX / 2,
        u32::MAX
    );
    // ====================== u64 Harnesses ======================
    generate_unchecked_mul_intervals!(
        u64,
        unchecked_mul,
        unchecked_mul_u64_small,
        0u64,
        10u64,
        unchecked_mul_u64_large,
        u64::MAX - 1000u64,
        u64::MAX,
        unchecked_mul_u64_edge,
        u64::MAX / 2,
        u64::MAX
    );
    // ====================== u128 Harnesses ======================
    generate_unchecked_mul_intervals!(
        u128,
        unchecked_mul,
        unchecked_mul_u128_small,
        0u128,
        10u128,
        unchecked_mul_u128_large,
        u128::MAX - 1000u128,
        u128::MAX,
        unchecked_mul_u128_edge,
        u128::MAX / 2,
        u128::MAX
    );
    // ====================== usize Harnesses ======================
    generate_unchecked_mul_intervals!(
        usize,
        unchecked_mul,
        unchecked_mul_usize_small,
        0usize,
        10usize,
        unchecked_mul_usize_large,
        usize::MAX - 1000usize,
        usize::MAX,
        unchecked_mul_usize_edge,
        usize::MAX / 2,
        usize::MAX
    );

    // unchecked_shr proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total
    //
    // Target contracts:
    // #[requires(rhs < <$ActualT>::BITS)]
    //
    // Target function:
    // pub const unsafe fn unchecked_shr(self, rhs: u32) -> Self
    generate_unchecked_shift_harness!(i8, unchecked_shr, checked_unchecked_shr_i8);
    generate_unchecked_shift_harness!(i16, unchecked_shr, checked_unchecked_shr_i16);
    generate_unchecked_shift_harness!(i32, unchecked_shr, checked_unchecked_shr_i32);
    generate_unchecked_shift_harness!(i64, unchecked_shr, checked_unchecked_shr_i64);
    generate_unchecked_shift_harness!(i128, unchecked_shr, checked_unchecked_shr_i128);
    generate_unchecked_shift_harness!(isize, unchecked_shr, checked_unchecked_shr_isize);
    generate_unchecked_shift_harness!(u8, unchecked_shr, checked_unchecked_shr_u8);
    generate_unchecked_shift_harness!(u16, unchecked_shr, checked_unchecked_shr_u16);
    generate_unchecked_shift_harness!(u32, unchecked_shr, checked_unchecked_shr_u32);
    generate_unchecked_shift_harness!(u64, unchecked_shr, checked_unchecked_shr_u64);
    generate_unchecked_shift_harness!(u128, unchecked_shr, checked_unchecked_shr_u128);
    generate_unchecked_shift_harness!(usize, unchecked_shr, checked_unchecked_shr_usize);

    // `unchecked_shl` proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total
    //
    // Target contracts:
    // #[requires(shift < Self::BITS)]
    //
    // Target function:
    // pub const unsafe fn unchecked_shl(self, shift: u32) -> Self
    //
    // This function performs an unchecked bitwise left shift operation.
    generate_unchecked_shift_harness!(i8, unchecked_shl, checked_unchecked_shl_i8);
    generate_unchecked_shift_harness!(i16, unchecked_shl, checked_unchecked_shl_i16);
    generate_unchecked_shift_harness!(i32, unchecked_shl, checked_unchecked_shl_i32);
    generate_unchecked_shift_harness!(i64, unchecked_shl, checked_unchecked_shl_i64);
    generate_unchecked_shift_harness!(i128, unchecked_shl, checked_unchecked_shl_i128);
    generate_unchecked_shift_harness!(isize, unchecked_shl, checked_unchecked_shl_isize);
    generate_unchecked_shift_harness!(u8, unchecked_shl, checked_unchecked_shl_u8);
    generate_unchecked_shift_harness!(u16, unchecked_shl, checked_unchecked_shl_u16);
    generate_unchecked_shift_harness!(u32, unchecked_shl, checked_unchecked_shl_u32);
    generate_unchecked_shift_harness!(u64, unchecked_shl, checked_unchecked_shl_u64);
    generate_unchecked_shift_harness!(u128, unchecked_shl, checked_unchecked_shl_u128);
    generate_unchecked_shift_harness!(usize, unchecked_shl, checked_unchecked_shl_usize);

    // `unchecked_sub` proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total
    //
    // Target contracts:
    // Preconditions: No overflow should occur
    // #[requires(!self.overflowing_sub(rhs).1)]
    //
    // Target function:
    // pub const unsafe fn unchecked_sub(self, rhs: Self)  -> Self
    //
    // This function performs an unchecked subtraction operation.
    generate_unchecked_math_harness!(i8, unchecked_sub, checked_unchecked_sub_i8);
    generate_unchecked_math_harness!(i16, unchecked_sub, checked_unchecked_sub_i16);
    generate_unchecked_math_harness!(i32, unchecked_sub, checked_unchecked_sub_i32);
    generate_unchecked_math_harness!(i64, unchecked_sub, checked_unchecked_sub_i64);
    generate_unchecked_math_harness!(i128, unchecked_sub, checked_unchecked_sub_i128);
    generate_unchecked_math_harness!(isize, unchecked_sub, checked_unchecked_sub_isize);
    generate_unchecked_math_harness!(u8, unchecked_sub, checked_unchecked_sub_u8);
    generate_unchecked_math_harness!(u16, unchecked_sub, checked_unchecked_sub_u16);
    generate_unchecked_math_harness!(u32, unchecked_sub, checked_unchecked_sub_u32);
    generate_unchecked_math_harness!(u64, unchecked_sub, checked_unchecked_sub_u64);
    generate_unchecked_math_harness!(u128, unchecked_sub, checked_unchecked_sub_u128);
    generate_unchecked_math_harness!(usize, unchecked_sub, checked_unchecked_sub_usize);

    // Part_2 `carrying_mul` proofs
    //
    // ====================== u8 Harnesses ======================
    /// Kani proof harness for `carrying_mul` on `u8` type with full range of values.
    generate_carrying_mul_intervals!(u8, u16, carrying_mul_u8_full_range, 0u8, u8::MAX);

    // ====================== u16 Harnesses ======================
    /// Kani proof harness for `carrying_mul` on `u16` type with full range of values.
    generate_carrying_mul_intervals!(u16, u32, carrying_mul_u16_full_range, 0u16, u16::MAX);

    // ====================== u32 Harnesses ======================
    generate_carrying_mul_intervals!(
        u32,
        u64,
        carrying_mul_u32_small,
        0u32,
        10u32,
        carrying_mul_u32_large,
        u32::MAX - 10u32,
        u32::MAX,
        carrying_mul_u32_mid_edge,
        (u32::MAX / 2) - 10u32,
        (u32::MAX / 2) + 10u32
    );

    // ====================== u64 Harnesses ======================
    generate_carrying_mul_intervals!(
        u64,
        u128,
        carrying_mul_u64_small,
        0u64,
        10u64,
        carrying_mul_u64_large,
        u64::MAX - 10u64,
        u64::MAX,
        carrying_mul_u64_mid_edge,
        (u64::MAX / 2) - 10u64,
        (u64::MAX / 2) + 10u64
    );

    // Part_2 `widening_mul` proofs

    // ====================== u8 Harnesses ======================
    generate_widening_mul_intervals!(u8, u16, widening_mul_u8, 0u8, u8::MAX);

    // ====================== u16 Harnesses ======================
    generate_widening_mul_intervals!(
        u16,
        u32,
        widening_mul_u16_small,
        0u16,
        10u16,
        widening_mul_u16_large,
        u16::MAX - 10u16,
        u16::MAX,
        widening_mul_u16_mid_edge,
        (u16::MAX / 2) - 10u16,
        (u16::MAX / 2) + 10u16
    );

    // ====================== u32 Harnesses ======================
    generate_widening_mul_intervals!(
        u32,
        u64,
        widening_mul_u32_small,
        0u32,
        10u32,
        widening_mul_u32_large,
        u32::MAX - 10u32,
        u32::MAX,
        widening_mul_u32_mid_edge,
        (u32::MAX / 2) - 10u32,
        (u32::MAX / 2) + 10u32
    );

    // ====================== u64 Harnesses ======================
    generate_widening_mul_intervals!(
        u64,
        u128,
        widening_mul_u64_small,
        0u64,
        10u64,
        widening_mul_u64_large,
        u64::MAX - 10u64,
        u64::MAX,
        widening_mul_u64_mid_edge,
        (u64::MAX / 2) - 10u64,
        (u64::MAX / 2) + 10u64
    );

    // Part_2 `wrapping_shl` proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total
    //
    // Target contracts:
    // #[ensures(|result| *result == self << (rhs & (Self::BITS - 1)))]
    //
    // Target function:
    // pub const fn wrapping_shl(self, rhs: u32) -> Self
    //
    // This function performs an panic-free bitwise left shift operation.
    generate_wrapping_shift_harness!(i8, wrapping_shl, checked_wrapping_shl_i8);
    generate_wrapping_shift_harness!(i16, wrapping_shl, checked_wrapping_shl_i16);
    generate_wrapping_shift_harness!(i32, wrapping_shl, checked_wrapping_shl_i32);
    generate_wrapping_shift_harness!(i64, wrapping_shl, checked_wrapping_shl_i64);
    generate_wrapping_shift_harness!(i128, wrapping_shl, checked_wrapping_shl_i128);
    generate_wrapping_shift_harness!(isize, wrapping_shl, checked_wrapping_shl_isize);
    generate_wrapping_shift_harness!(u8, wrapping_shl, checked_wrapping_shl_u8);
    generate_wrapping_shift_harness!(u16, wrapping_shl, checked_wrapping_shl_u16);
    generate_wrapping_shift_harness!(u32, wrapping_shl, checked_wrapping_shl_u32);
    generate_wrapping_shift_harness!(u64, wrapping_shl, checked_wrapping_shl_u64);
    generate_wrapping_shift_harness!(u128, wrapping_shl, checked_wrapping_shl_u128);
    generate_wrapping_shift_harness!(usize, wrapping_shl, checked_wrapping_shl_usize);

    // Part_2 `wrapping_shr` proofs
    //
    // Target types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total
    //
    // Target contracts:
    // #[ensures(|result| *result == self >> (rhs & (Self::BITS - 1)))]
    // Target function:
    // pub const fn wrapping_shr(self, rhs: u32) -> Self {
    //
    // This function performs an panic-free bitwise right shift operation.
    generate_wrapping_shift_harness!(i8, wrapping_shr, checked_wrapping_shr_i8);
    generate_wrapping_shift_harness!(i16, wrapping_shr, checked_wrapping_shr_i16);
    generate_wrapping_shift_harness!(i32, wrapping_shr, checked_wrapping_shr_i32);
    generate_wrapping_shift_harness!(i64, wrapping_shr, checked_wrapping_shr_i64);
    generate_wrapping_shift_harness!(i128, wrapping_shr, checked_wrapping_shr_i128);
    generate_wrapping_shift_harness!(isize, wrapping_shr, checked_wrapping_shr_isize);
    generate_wrapping_shift_harness!(u8, wrapping_shr, checked_wrapping_shr_u8);
    generate_wrapping_shift_harness!(u16, wrapping_shr, checked_wrapping_shr_u16);
    generate_wrapping_shift_harness!(u32, wrapping_shr, checked_wrapping_shr_u32);
    generate_wrapping_shift_harness!(u64, wrapping_shr, checked_wrapping_shr_u64);
    generate_wrapping_shift_harness!(u128, wrapping_shr, checked_wrapping_shr_u128);
    generate_wrapping_shift_harness!(usize, wrapping_shr, checked_wrapping_shr_usize);

    // `f{16,32,64,128}::to_int_unchecked` proofs
    //
    // Target integer types:
    // i{8,16,32,64,128,size} and u{8,16,32,64,128,size} -- 12 types in total
    //
    // Target contracts:
    // 1. Float is not `NaN` and infinite
    // 2. Float is representable in the return type `Int`, after truncating
    //    off its fractional part
    // [requires(self.is_finite() && kani::float::float_to_int_in_range::<Self, Int>(self))]
    //
    // Target function:
    // pub unsafe fn to_int_unchecked<Int>(self) -> Int where Self: FloatToInt<Int>
    generate_to_int_unchecked_harness!(
        f32,
        i8,
        checked_f32_to_int_unchecked_i8,
        i16,
        checked_f32_to_int_unchecked_i16,
        i32,
        checked_f32_to_int_unchecked_i32,
        i64,
        checked_f32_to_int_unchecked_i64,
        i128,
        checked_f32_to_int_unchecked_i128,
        isize,
        checked_f32_to_int_unchecked_isize,
        u8,
        checked_f32_to_int_unchecked_u8,
        u16,
        checked_f32_to_int_unchecked_u16,
        u32,
        checked_f32_to_int_unchecked_u32,
        u64,
        checked_f32_to_int_unchecked_u64,
        u128,
        checked_f32_to_int_unchecked_u128,
        usize,
        checked_f32_to_int_unchecked_usize
    );

    generate_to_int_unchecked_harness!(
        f64,
        i8,
        checked_f64_to_int_unchecked_i8,
        i16,
        checked_f64_to_int_unchecked_i16,
        i32,
        checked_f64_to_int_unchecked_i32,
        i64,
        checked_f64_to_int_unchecked_i64,
        i128,
        checked_f64_to_int_unchecked_i128,
        isize,
        checked_f64_to_int_unchecked_isize,
        u8,
        checked_f64_to_int_unchecked_u8,
        u16,
        checked_f64_to_int_unchecked_u16,
        u32,
        checked_f64_to_int_unchecked_u32,
        u64,
        checked_f64_to_int_unchecked_u64,
        u128,
        checked_f64_to_int_unchecked_u128,
        usize,
        checked_f64_to_int_unchecked_usize
    );

    generate_to_int_unchecked_harness!(
        f16,
        i8,
        checked_f16_to_int_unchecked_i8,
        i16,
        checked_f16_to_int_unchecked_i16,
        i32,
        checked_f16_to_int_unchecked_i32,
        i64,
        checked_f16_to_int_unchecked_i64,
        i128,
        checked_f16_to_int_unchecked_i128,
        isize,
        checked_f16_to_int_unchecked_isize,
        u8,
        checked_f16_to_int_unchecked_u8,
        u16,
        checked_f16_to_int_unchecked_u16,
        u32,
        checked_f16_to_int_unchecked_u32,
        u64,
        checked_f16_to_int_unchecked_u64,
        u128,
        checked_f16_to_int_unchecked_u128,
        usize,
        checked_f16_to_int_unchecked_usize
    );

    generate_to_int_unchecked_harness!(
        f128,
        i8,
        checked_f128_to_int_unchecked_i8,
        i16,
        checked_f128_to_int_unchecked_i16,
        i32,
        checked_f128_to_int_unchecked_i32,
        i64,
        checked_f128_to_int_unchecked_i64,
        i128,
        checked_f128_to_int_unchecked_i128,
        isize,
        checked_f128_to_int_unchecked_isize,
        u8,
        checked_f128_to_int_unchecked_u8,
        u16,
        checked_f128_to_int_unchecked_u16,
        u32,
        checked_f128_to_int_unchecked_u32,
        u64,
        checked_f128_to_int_unchecked_u64,
        u128,
        checked_f128_to_int_unchecked_u128,
        usize,
        checked_f128_to_int_unchecked_usize
    );
}
