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

#[kani::proof]
#[kani::solver(kissat)]
fn check_estimator_model_agrees() {
    let mant: u64 = kani::any();
    let exp: i16 = kani::any();
    kani::assume(mant > 0);

    assert_eq!(
        estimate_scaling_factor(mant, exp),
        super::estimator::estimate_scaling_factor(mant, exp)
    );
    kani::cover(mant == 1, "smallest nonzero mantissa");
    kani::cover(mant == (1_u64 << 63), "largest power-of-two boundary");
    kani::cover(mant == u64::MAX, "largest mantissa");
    kani::cover(exp == i16::MIN, "smallest binary exponent");
    kani::cover(exp == i16::MAX, "largest binary exponent");
}
