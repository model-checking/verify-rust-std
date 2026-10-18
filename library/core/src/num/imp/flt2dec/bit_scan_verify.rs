//! Exact bit-scan models for the flt2dec generator proofs.

use crate::kani;

// Expose fixed shifts to symbolic execution before expanding normalization and
// scaling. The independent proof below checks every input, including zero.
pub(crate) fn leading_zeros_u64(mut value: u64) -> u32 {
    if value == 0 {
        64
    } else {
        let mut count = 0;
        macro_rules! scan_half {
            ($bits:literal) => {
                if value >> (64 - $bits) == 0 {
                    count += $bits;
                    value <<= $bits;
                }
            };
        }
        scan_half!(32);
        scan_half!(16);
        scan_half!(8);
        scan_half!(4);
        scan_half!(2);
        count + u32::from(value >> 63 == 0)
    }
}

pub(crate) fn leading_zeros_u32(value: u32) -> u32 {
    leading_zeros_u64(u64::from(value)) - 32
}

#[kani::proof]
#[kani::solver(kissat)]
fn check_leading_zeros_models_agree() {
    let wide: u64 = kani::any();
    let narrow: u32 = kani::any();
    assert!(leading_zeros_u64(wide) == wide.leading_zeros());
    assert!(leading_zeros_u32(narrow) == narrow.leading_zeros());
    kani::cover(wide == 0, "u64 zero has 64 leading zeros");
    kani::cover(wide == 1, "u64 one has 63 leading zeros");
    kani::cover(wide == 1 << 63, "u64 top bit has no leading zeros");
    kani::cover(narrow == 0, "u32 zero has 32 leading zeros");
    kani::cover(narrow == 1, "u32 one has 31 leading zeros");
    kani::cover(narrow == 1 << 31, "u32 top bit has no leading zeros");
}
