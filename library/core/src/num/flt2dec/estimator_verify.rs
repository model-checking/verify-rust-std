//! An exact exponent-estimator model with a separate equivalence proof.

use crate::kani;

fn scale_from_bits(bits: i64, exp: i16) -> i16 {
    (((bits + exp as i64) * 1292913986) >> 32) as i16
}

// Compute the original formula in each leaf, before merging the branches.
// When the binary exponent is fixed, equal decimal exponents can then fold
// together without expanding unreachable bigint scaling paths.
pub(crate) fn estimate_scaling_factor(mant: u64, exp: i16) -> i16 {
    assert!(mant > 0);

    macro_rules! choose_bits {
        ($base:expr;) => {
            scale_from_bits($base, exp)
        };
        ($base:expr; $half:literal $(, $rest:literal)*) => {
            if mant <= (1_u64 << ($base + $half - 1)) {
                choose_bits!($base; $($rest),*)
            } else {
                choose_bits!($base + $half; $($rest),*)
            }
        };
    }

    // The remaining tree has exactly the 64 leaves for bit counts 0..=63.
    // Every shift in it is at most 62, and mant == 1 selects bit count zero.
    if mant > (1_u64 << 63) {
        scale_from_bits(64, exp)
    } else {
        choose_bits!(0; 32, 16, 8, 4, 2, 1)
    }
}

// Partition mant - 1 by bit length. Zero gives mant == 1; bit lengths 1..=64
// cover every other nonzero u64 mantissa. Only the predecessor u64::MAX is
// excluded, since adding one would produce the out-of-domain mantissa zero.
fn check_estimator_model_agrees<const BITS: u32>() {
    assert!(BITS <= 64);
    let mant = if BITS == 0 {
        1
    } else {
        let leading = 1_u64 << (BITS - 1);
        let predecessor = leading | (kani::any::<u64>() & (leading - 1));
        kani::assume(predecessor < u64::MAX);
        predecessor + 1
    };
    let exp: i16 = kani::any();

    assert_eq!(
        estimate_scaling_factor(mant, exp),
        super::estimator::estimate_scaling_factor(mant, exp)
    );
    if BITS == 0 {
        kani::cover(mant == 1, "smallest nonzero mantissa");
    }
    if BITS == 63 {
        kani::cover(mant == (1_u64 << 63), "largest power-of-two boundary");
    }
    if BITS == 64 {
        kani::cover(mant == u64::MAX, "largest mantissa");
    }
    kani::cover(exp == i16::MIN, "smallest binary exponent");
    kani::cover(exp == i16::MAX, "largest binary exponent");
}

macro_rules! check_bit_count {
    ($name:ident, $bits:literal) => {
        #[kani::proof]
        #[kani::solver(kissat)]
        fn $name() {
            check_estimator_model_agrees::<$bits>();
        }
    };
}

check_bit_count!(check_estimator_model_agrees_00, 0);
check_bit_count!(check_estimator_model_agrees_01, 1);
check_bit_count!(check_estimator_model_agrees_02, 2);
check_bit_count!(check_estimator_model_agrees_03, 3);
check_bit_count!(check_estimator_model_agrees_04, 4);
check_bit_count!(check_estimator_model_agrees_05, 5);
check_bit_count!(check_estimator_model_agrees_06, 6);
check_bit_count!(check_estimator_model_agrees_07, 7);
check_bit_count!(check_estimator_model_agrees_08, 8);
check_bit_count!(check_estimator_model_agrees_09, 9);
check_bit_count!(check_estimator_model_agrees_10, 10);
check_bit_count!(check_estimator_model_agrees_11, 11);
check_bit_count!(check_estimator_model_agrees_12, 12);
check_bit_count!(check_estimator_model_agrees_13, 13);
check_bit_count!(check_estimator_model_agrees_14, 14);
check_bit_count!(check_estimator_model_agrees_15, 15);
check_bit_count!(check_estimator_model_agrees_16, 16);
check_bit_count!(check_estimator_model_agrees_17, 17);
check_bit_count!(check_estimator_model_agrees_18, 18);
check_bit_count!(check_estimator_model_agrees_19, 19);
check_bit_count!(check_estimator_model_agrees_20, 20);
check_bit_count!(check_estimator_model_agrees_21, 21);
check_bit_count!(check_estimator_model_agrees_22, 22);
check_bit_count!(check_estimator_model_agrees_23, 23);
check_bit_count!(check_estimator_model_agrees_24, 24);
check_bit_count!(check_estimator_model_agrees_25, 25);
check_bit_count!(check_estimator_model_agrees_26, 26);
check_bit_count!(check_estimator_model_agrees_27, 27);
check_bit_count!(check_estimator_model_agrees_28, 28);
check_bit_count!(check_estimator_model_agrees_29, 29);
check_bit_count!(check_estimator_model_agrees_30, 30);
check_bit_count!(check_estimator_model_agrees_31, 31);
check_bit_count!(check_estimator_model_agrees_32, 32);
check_bit_count!(check_estimator_model_agrees_33, 33);
check_bit_count!(check_estimator_model_agrees_34, 34);
check_bit_count!(check_estimator_model_agrees_35, 35);
check_bit_count!(check_estimator_model_agrees_36, 36);
check_bit_count!(check_estimator_model_agrees_37, 37);
check_bit_count!(check_estimator_model_agrees_38, 38);
check_bit_count!(check_estimator_model_agrees_39, 39);
check_bit_count!(check_estimator_model_agrees_40, 40);
check_bit_count!(check_estimator_model_agrees_41, 41);
check_bit_count!(check_estimator_model_agrees_42, 42);
check_bit_count!(check_estimator_model_agrees_43, 43);
check_bit_count!(check_estimator_model_agrees_44, 44);
check_bit_count!(check_estimator_model_agrees_45, 45);
check_bit_count!(check_estimator_model_agrees_46, 46);
check_bit_count!(check_estimator_model_agrees_47, 47);
check_bit_count!(check_estimator_model_agrees_48, 48);
check_bit_count!(check_estimator_model_agrees_49, 49);
check_bit_count!(check_estimator_model_agrees_50, 50);
check_bit_count!(check_estimator_model_agrees_51, 51);
check_bit_count!(check_estimator_model_agrees_52, 52);
check_bit_count!(check_estimator_model_agrees_53, 53);
check_bit_count!(check_estimator_model_agrees_54, 54);
check_bit_count!(check_estimator_model_agrees_55, 55);
check_bit_count!(check_estimator_model_agrees_56, 56);
check_bit_count!(check_estimator_model_agrees_57, 57);
check_bit_count!(check_estimator_model_agrees_58, 58);
check_bit_count!(check_estimator_model_agrees_59, 59);
check_bit_count!(check_estimator_model_agrees_60, 60);
check_bit_count!(check_estimator_model_agrees_61, 61);
check_bit_count!(check_estimator_model_agrees_62, 62);
check_bit_count!(check_estimator_model_agrees_63, 63);
check_bit_count!(check_estimator_model_agrees_64, 64);
