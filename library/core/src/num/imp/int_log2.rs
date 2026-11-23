//! Binary-logarithm proofs. Public method bodies and their intrinsics are checked directly.

use crate::kani;

// n >> r == 1 means exactly 2^r <= n < 2^(r+1). Unlike computing
// the upper power in u128, this remains representable when r == 127.
fn assert_binary_log(n: u128, r: u32) {
    assert!(r < 128);
    assert_eq!(n >> r, 1);
}

macro_rules! check_public {
    ($ty:ident, $name:ident) => {
        #[kani::proof]
        fn $name() {
            let n: $ty = kani::any();
            match n.checked_ilog2() {
                Some(r) => {
                    assert!(n > 0);
                    assert_binary_log(n as u128, r);
                }
                None => assert!(n <= 0),
            }
            if n > 0 {
                // Also verify the panicking API on its positive input domain.
                assert_binary_log(n as u128, n.ilog2());
            }
        }
    };
}

macro_rules! check_nonzero {
    ($ty:ident, $name:ident) => {
        #[kani::proof]
        fn $name() {
            let n: $ty = kani::any();
            kani::assume(n > 0);
            let nz = crate::num::NonZero::new(n).unwrap();
            assert_binary_log(n as u128, nz.ilog2());
        }
    };
}

// The no-argument panic helper is checked by int_log10::verify::check_decimal_panic_helper.
// This terminal model proves that every invalid input reaches that helper,
// rather than merely finding one input that panics with should_panic.
fn panic_terminal() -> ! {
    kani::assume(false);
    unreachable!()
}

macro_rules! check_invalid {
    ($ty:ident, $name:ident) => {
        #[kani::proof]
        #[kani::stub(super::int_log10::panic_for_nonpositive_argument, panic_terminal)]
        fn $name() {
            let n: $ty = kani::any();
            kani::assume(n <= 0);
            let _ = n.ilog2();
            assert!(
                false,
                "every nonpositive input must reach the logarithm panic helper"
            );
        }
    };
}

check_public!(u8, check_public_u8);
check_public!(u16, check_public_u16);
check_public!(u32, check_public_u32);
check_public!(u64, check_public_u64);
check_public!(u128, check_public_u128);
check_public!(usize, check_public_usize);
check_public!(i8, check_public_i8);
check_public!(i16, check_public_i16);
check_public!(i32, check_public_i32);
check_public!(i64, check_public_i64);
check_public!(i128, check_public_i128);
check_public!(isize, check_public_isize);

check_nonzero!(u8, check_nonzero_u8);
check_nonzero!(u16, check_nonzero_u16);
check_nonzero!(u32, check_nonzero_u32);
check_nonzero!(u64, check_nonzero_u64);
check_nonzero!(u128, check_nonzero_u128);
check_nonzero!(usize, check_nonzero_usize);

check_invalid!(u8, check_invalid_u8);
check_invalid!(u16, check_invalid_u16);
check_invalid!(u32, check_invalid_u32);
check_invalid!(u64, check_invalid_u64);
check_invalid!(u128, check_invalid_u128);
check_invalid!(usize, check_invalid_usize);
check_invalid!(i8, check_invalid_i8);
check_invalid!(i16, check_invalid_i16);
check_invalid!(i32, check_invalid_i32);
check_invalid!(i64, check_invalid_i64);
check_invalid!(i128, check_invalid_i128);
check_invalid!(isize, check_invalid_isize);
