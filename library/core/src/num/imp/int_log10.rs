//! These functions compute the integer logarithm of their type, assuming
//! that someone has already checked that the value is strictly positive.

use safety::{ensures, requires};

#[cfg(kani)]
use crate::kani;
use crate::num::NonZero;

// 0 < val <= u8::MAX
#[requires(val > 0)]
#[ensures(|result: &u32| *result == verify::decimal_log(val as u128))]
#[inline]
const fn u8_impl(val: u8) -> u32 {
    let val = val as u32;

    // For better performance, avoid branches by assembling the solution
    // in the bits above the low 8 bits.

    // Adding c1 to val gives 10 in the top bits for val < 10, 11 for val >= 10
    const C1: u32 = 0b11_00000000 - 10; // 758
    // Adding c2 to val gives 01 in the top bits for val < 100, 10 for val >= 100
    const C2: u32 = 0b10_00000000 - 100; // 412

    // Value of top bits:
    //            +c1  +c2  1&2
    //     0..=9   10   01   00 = 0
    //   10..=99   11   01   01 = 1
    // 100..=255   11   10   10 = 2
    ((val + C1) & (val + C2)) >> 8
}

// 0 < val < 100_000
#[requires(val > 0 && val < 100_000)]
#[ensures(|result: &u32| *result == verify::decimal_log(val as u128))]
#[inline]
const fn less_than_5(val: u32) -> u32 {
    // Similar to u8, when adding one of these constants to val,
    // we get two possible bit patterns above the low 17 bits,
    // depending on whether val is below or above the threshold.
    const C1: u32 = 0b011_00000000000000000 - 10; // 393206
    const C2: u32 = 0b100_00000000000000000 - 100; // 524188
    const C3: u32 = 0b111_00000000000000000 - 1000; // 916504
    const C4: u32 = 0b100_00000000000000000 - 10000; // 514288

    // Value of top bits:
    //                +c1  +c2  1&2  +c3  +c4  3&4   ^
    //         0..=9  010  011  010  110  011  010  000 = 0
    //       10..=99  011  011  011  110  011  010  001 = 1
    //     100..=999  011  100  000  110  011  010  010 = 2
    //   1000..=9999  011  100  000  111  011  011  011 = 3
    // 10000..=99999  011  100  000  111  100  100  100 = 4
    (((val + C1) & (val + C2)) ^ ((val + C3) & (val + C4))) >> 17
}

// 0 < val <= u16::MAX
#[requires(val > 0)]
#[ensures(|result: &u32| *result == verify::decimal_log(val as u128))]
#[inline]
const fn u16_impl(val: u16) -> u32 {
    less_than_5(val as u32)
}

// 0 < val <= u32::MAX
#[requires(val > 0)]
#[ensures(|result: &u32| *result == verify::decimal_log(val as u128))]
#[inline]
const fn u32_impl(mut val: u32) -> u32 {
    let mut log = 0;
    if val >= 100_000 {
        val /= 100_000;
        log += 5;
    }
    log + less_than_5(val)
}

// 0 < val <= u64::MAX
#[requires(val > 0)]
#[ensures(|result: &u32| *result == verify::decimal_log(val as u128))]
#[inline]
const fn u64_impl(mut val: u64) -> u32 {
    let mut log = 0;
    if val >= 10_000_000_000 {
        val /= 10_000_000_000;
        log += 10;
    }
    if val >= 100_000 {
        val /= 100_000;
        log += 5;
    }
    log + less_than_5(val as u32)
}

// 0 < val <= u128::MAX
#[requires(val > 0)]
#[ensures(|result: &u32| *result == verify::decimal_log(val as u128))]
#[inline]
const fn u128_impl(mut val: u128) -> u32 {
    let mut log = 0;
    if val >= 100_000_000_000_000_000_000_000_000_000_000 {
        val /= 100_000_000_000_000_000_000_000_000_000_000;
        log += 32;
        return log + u32_impl(val as u32);
    }
    if val >= 10_000_000_000_000_000 {
        val /= 10_000_000_000_000_000;
        log += 16;
    }
    log + u64_impl(val as u64)
}

macro_rules! define_unsigned_ilog10 {
    ($($ty:ident => $impl_fn:ident,)*) => {$(
        #[inline]
        #[ensures(|result: &u32| *result == verify::decimal_log(val.get() as u128))]
        pub(in crate::num) const fn $ty(val: NonZero<$ty>) -> u32 {
            let result = $impl_fn(val.get());

            // SAFETY: Integer logarithm is monotonic non-decreasing, so the computed `result` cannot
            // exceed the value produced for the maximum input.
            unsafe { crate::hint::assert_unchecked(result <= const { $impl_fn($ty::MAX) }) };

            result
        }
    )*};
}

define_unsigned_ilog10! {
    u8 => u8_impl,
    u16 => u16_impl,
    u32 => u32_impl,
    u64 => u64_impl,
    u128 => u128_impl,
}

#[ensures(|result: &u32| *result == verify::decimal_log(val.get() as u128))]
#[inline]
pub(in crate::num) const fn usize(val: NonZero<usize>) -> u32 {
    #[cfg(target_pointer_width = "16")]
    let impl_fn = u16;

    #[cfg(target_pointer_width = "32")]
    let impl_fn = u32;

    #[cfg(target_pointer_width = "64")]
    let impl_fn = u64;

    // SAFETY: Each configuration selects an unsigned type with the same width as usize
    // (u16, u32, or u64). The cast therefore preserves the positive value, so the
    // NonZero conversion is safe on all three pointer widths. The u16/u32/u64
    // wrapper contracts are verified separately; CI verifies this conversion on 64-bit targets.
    impl_fn(unsafe { NonZero::new_unchecked(val.get() as _) })
}

macro_rules! define_signed_ilog10 {
    ($($ty:ident => $impl_fn:ident,)*) => {$(
        // 0 < val <= $ty::MAX
        #[inline]
        #[ensures(|result: &Option<u32>| match *result {
            Some(log) => val > 0 && log == verify::decimal_log(val as u128),
            None => val <= 0,
        })]
        pub(in crate::num) const fn $ty(val: $ty) -> Option<u32> {
            if val > 0 {
                let result = $impl_fn(val.cast_unsigned());

                // SAFETY: Integer logarithm is monotonic non-decreasing, so the computed `result`
                // cannot exceed the value produced for the maximum input.
                unsafe {
                    crate::hint::assert_unchecked(result <= const { $impl_fn($ty::MAX.cast_unsigned()) });
                }

                Some(result)
            } else {
                None
            }
        }
    )*};
}

define_signed_ilog10! {
    i8 => u8_impl,
    i16 => u16_impl,
    i32 => u32_impl,
    i64 => u64_impl,
    i128 => u128_impl,
}

/// Instantiate this panic logic once, rather than for all the ilog methods
/// on every single primitive type.
#[cold]
#[track_caller]
pub(in crate::num) const fn panic_for_nonpositive_argument() -> ! {
    panic!("argument of integer logarithm must be positive")
}

#[cfg(kani)]
mod verify {
    use crate::kani;

    // Verify the safety contract used to discharge the wrappers' bound assertions.
    #[kani::proof_for_contract(crate::hint::assert_unchecked)]
    fn check_assert_unchecked_contract() {
        unsafe { crate::hint::assert_unchecked(kani::any()) };
    }

    // Independent specification for positive inputs across all integer widths.
    // Thresholds avoid computing 10^39, which would overflow u128.
    pub(super) fn decimal_log(n: u128) -> u32 {
        if n < 10 {
            0
        } else if n < 100 {
            1
        } else if n < 1_000 {
            2
        } else if n < 10_000 {
            3
        } else if n < 100_000 {
            4
        } else if n < 1_000_000 {
            5
        } else if n < 10_000_000 {
            6
        } else if n < 100_000_000 {
            7
        } else if n < 1_000_000_000 {
            8
        } else if n < 10_000_000_000 {
            9
        } else if n < 100_000_000_000 {
            10
        } else if n < 1_000_000_000_000 {
            11
        } else if n < 10_000_000_000_000 {
            12
        } else if n < 100_000_000_000_000 {
            13
        } else if n < 1_000_000_000_000_000 {
            14
        } else if n < 10_000_000_000_000_000 {
            15
        } else if n < 100_000_000_000_000_000 {
            16
        } else if n < 1_000_000_000_000_000_000 {
            17
        } else if n < 10_000_000_000_000_000_000 {
            18
        } else if n < 100_000_000_000_000_000_000 {
            19
        } else if n < 1_000_000_000_000_000_000_000 {
            20
        } else if n < 10_000_000_000_000_000_000_000 {
            21
        } else if n < 100_000_000_000_000_000_000_000 {
            22
        } else if n < 1_000_000_000_000_000_000_000_000 {
            23
        } else if n < 10_000_000_000_000_000_000_000_000 {
            24
        } else if n < 100_000_000_000_000_000_000_000_000 {
            25
        } else if n < 1_000_000_000_000_000_000_000_000_000 {
            26
        } else if n < 10_000_000_000_000_000_000_000_000_000 {
            27
        } else if n < 100_000_000_000_000_000_000_000_000_000 {
            28
        } else if n < 1_000_000_000_000_000_000_000_000_000_000 {
            29
        } else if n < 10_000_000_000_000_000_000_000_000_000_000 {
            30
        } else if n < 100_000_000_000_000_000_000_000_000_000_000 {
            31
        } else if n < 1_000_000_000_000_000_000_000_000_000_000_000 {
            32
        } else if n < 10_000_000_000_000_000_000_000_000_000_000_000 {
            33
        } else if n < 100_000_000_000_000_000_000_000_000_000_000_000 {
            34
        } else if n < 1_000_000_000_000_000_000_000_000_000_000_000_000 {
            35
        } else if n < 10_000_000_000_000_000_000_000_000_000_000_000_000 {
            36
        } else if n < 100_000_000_000_000_000_000_000_000_000_000_000_000 {
            37
        } else {
            38
        }
    }

    #[kani::proof_for_contract(super::u8_impl)]
    fn check_u8_impl() {
        super::u8_impl(kani::any());
    }

    #[kani::proof_for_contract(super::less_than_5)]
    fn check_less_than_5() {
        super::less_than_5(kani::any());
    }

    #[kani::proof_for_contract(super::u16_impl)]
    #[kani::stub_verified(super::less_than_5)]
    fn check_u16_impl() {
        super::u16_impl(kani::any());
    }

    #[kani::proof_for_contract(super::u32_impl)]
    #[kani::stub_verified(super::less_than_5)]
    fn check_u32_impl() {
        super::u32_impl(kani::any());
    }

    #[kani::proof_for_contract(super::u64_impl)]
    #[kani::stub_verified(super::less_than_5)]
    fn check_u64_impl() {
        super::u64_impl(kani::any());
    }

    #[kani::proof_for_contract(super::u128_impl)]
    #[kani::stub_verified(super::u32_impl)]
    #[kani::stub_verified(super::u64_impl)]
    fn check_u128_impl() {
        super::u128_impl(kani::any());
    }

    // Construct every valid NonZero input from an unconstrained primitive.
    // The assumption expresses a type invariant, not a restricted wrapper domain.
    macro_rules! check_unsigned_wrapper {
        ($ty:ident, $helper:ident, $name:ident) => {
            #[kani::proof_for_contract(super::$ty)]
            #[kani::stub_verified(super::$helper)]
            #[kani::stub_verified(crate::hint::assert_unchecked)]
            fn $name() {
                let n: $ty = kani::any();
                kani::assume(n > 0);
                super::$ty(crate::num::NonZero::new(n).unwrap());
            }
        };
    }

    macro_rules! check_signed_wrapper {
        ($ty:ident, $helper:ident, $name:ident) => {
            #[kani::proof_for_contract(super::$ty)]
            #[kani::stub_verified(super::$helper)]
            #[kani::stub_verified(crate::hint::assert_unchecked)]
            fn $name() {
                super::$ty(kani::any());
            }
        };
    }
    check_unsigned_wrapper!(u8, u8_impl, check_u8_wrapper);
    check_unsigned_wrapper!(u16, u16_impl, check_u16_wrapper);
    check_unsigned_wrapper!(u32, u32_impl, check_u32_wrapper);
    check_unsigned_wrapper!(u64, u64_impl, check_u64_wrapper);
    check_unsigned_wrapper!(u128, u128_impl, check_u128_wrapper);
    check_signed_wrapper!(i8, u8_impl, check_i8_wrapper);
    check_signed_wrapper!(i16, u16_impl, check_i16_wrapper);
    check_signed_wrapper!(i32, u32_impl, check_i32_wrapper);
    check_signed_wrapper!(i64, u64_impl, check_i64_wrapper);
    check_signed_wrapper!(i128, u128_impl, check_i128_wrapper);

    #[kani::proof_for_contract(super::usize)]
    #[cfg_attr(target_pointer_width = "16", kani::stub_verified(super::u16))]
    #[cfg_attr(target_pointer_width = "32", kani::stub_verified(super::u32))]
    #[cfg_attr(target_pointer_width = "64", kani::stub_verified(super::u64))]
    fn check_usize_wrapper() {
        let n: usize = kani::any();
        kani::assume(n > 0);
        super::usize(crate::num::NonZero::new(n).unwrap());
    }

    // Verify public bodies while reusing the corresponding internal wrapper contract.
    macro_rules! check_decimal_public {
        ($ty:ident, $wrapper:ident, $name:ident) => {
            #[kani::proof]
            #[kani::stub_verified(super::$wrapper)]
            fn $name() {
                let n: $ty = kani::any();
                let expected = if n > 0 {
                    Some(decimal_log(n as u128))
                } else {
                    None
                };
                assert_eq!(n.checked_ilog10(), expected);
                if n > 0 {
                    assert_eq!(n.ilog10(), decimal_log(n as u128));
                }
            }
        };
    }

    macro_rules! check_decimal_nonzero {
        ($ty:ident, $name:ident) => {
            #[kani::proof]
            #[kani::stub_verified(super::$ty)]
            fn $name() {
                let n: $ty = kani::any();
                kani::assume(n > 0);
                let nz = crate::num::NonZero::new(n).unwrap();
                assert_eq!(nz.ilog10(), decimal_log(n as u128));
            }
        };
    }

    // This no-argument, straight-line function always panics. There is no
    // symbolic input for should_panic to select a favorable case from.
    #[kani::proof]
    #[kani::should_panic]
    fn check_decimal_panic_helper() {
        super::panic_for_nonpositive_argument();
    }

    // Model the proven panic helper as a terminal path. Only this helper is
    // replaced: any other panic or UB remains a verification failure.
    fn decimal_panic_terminal() -> ! {
        kani::assume(false);
        unreachable!()
    }

    macro_rules! check_decimal_invalid {
        ($ty:ident, $wrapper:ident, $name:ident) => {
            #[kani::proof]
            #[kani::stub_verified(super::$wrapper)]
            #[kani::stub(super::panic_for_nonpositive_argument, decimal_panic_terminal)]
            fn $name() {
                let n: $ty = kani::any();
                kani::assume(n <= 0);
                let _ = n.ilog10();
                assert!(
                    false,
                    "every nonpositive input must reach the decimal panic helper"
                );
            }
        };
    }
    check_decimal_public!(u8, u8, check_public_decimal_u8);
    check_decimal_invalid!(u8, u8, check_invalid_decimal_u8);
    check_decimal_nonzero!(u8, check_nonzero_decimal_u8);
    check_decimal_public!(u16, u16, check_public_decimal_u16);
    check_decimal_invalid!(u16, u16, check_invalid_decimal_u16);
    check_decimal_nonzero!(u16, check_nonzero_decimal_u16);
    check_decimal_public!(u32, u32, check_public_decimal_u32);
    check_decimal_invalid!(u32, u32, check_invalid_decimal_u32);
    check_decimal_nonzero!(u32, check_nonzero_decimal_u32);
    check_decimal_public!(u64, u64, check_public_decimal_u64);
    check_decimal_invalid!(u64, u64, check_invalid_decimal_u64);
    check_decimal_nonzero!(u64, check_nonzero_decimal_u64);
    check_decimal_public!(u128, u128, check_public_decimal_u128);
    check_decimal_invalid!(u128, u128, check_invalid_decimal_u128);
    check_decimal_nonzero!(u128, check_nonzero_decimal_u128);
    check_decimal_public!(usize, usize, check_public_decimal_usize);
    check_decimal_invalid!(usize, usize, check_invalid_decimal_usize);
    check_decimal_nonzero!(usize, check_nonzero_decimal_usize);
    check_decimal_public!(i8, i8, check_public_decimal_i8);
    check_decimal_invalid!(i8, i8, check_invalid_decimal_i8);
    check_decimal_public!(i16, i16, check_public_decimal_i16);
    check_decimal_invalid!(i16, i16, check_invalid_decimal_i16);
    check_decimal_public!(i32, i32, check_public_decimal_i32);
    check_decimal_invalid!(i32, i32, check_invalid_decimal_i32);
    check_decimal_public!(i64, i64, check_public_decimal_i64);
    check_decimal_invalid!(i64, i64, check_invalid_decimal_i64);
    check_decimal_public!(i128, i128, check_public_decimal_i128);
    check_decimal_invalid!(i128, i128, check_invalid_decimal_i128);
    // isize delegates to the signed wrapper matching the target pointer width.
    #[cfg(target_pointer_width = "16")]
    check_decimal_public!(isize, i16, check_public_decimal_isize);
    #[cfg(target_pointer_width = "32")]
    check_decimal_public!(isize, i32, check_public_decimal_isize);
    #[cfg(target_pointer_width = "64")]
    check_decimal_public!(isize, i64, check_public_decimal_isize);
    // isize delegates to the signed wrapper matching the target pointer width.
    #[cfg(target_pointer_width = "16")]
    check_decimal_invalid!(isize, i16, check_invalid_decimal_isize);
    #[cfg(target_pointer_width = "32")]
    check_decimal_invalid!(isize, i32, check_invalid_decimal_isize);
    #[cfg(target_pointer_width = "64")]
    check_decimal_invalid!(isize, i64, check_invalid_decimal_isize);
}
