//! A bounded contract for the rounding helper used by the strategy proofs.

use super::round_up;
use crate::kani;

const PROOF_BUFLEN: usize = 32;

// A fixed array gives the contract a sized write set. The adapter below copies
// only the active prefix back, so the contract cannot initialize unused bytes
// in a generator's MaybeUninit buffer.
#[kani::requires(
    len <= PROOF_BUFLEN && digits.iter().take(len).all(|&digit| digit < u8::MAX)
)]
#[kani::ensures(|result| {
    *result == old(
        digits.iter().take(len).all(|&digit| digit == b'9')
            .then_some(if len == 0 { b'1' } else { b'0' })
    )
})]
#[kani::modifies(digits)]
pub(crate) fn round_up_contract(digits: &mut [u8; PROOF_BUFLEN], len: usize) -> Option<u8> {
    round_up(&mut digits[..len])
}

// The caller's proof uses the contract for round_up_contract. No assumptions
// are made here: the contract checks the input byte constraint, and this
// adapter checks the bound before copying the caller's prefix.
pub(crate) fn stub_round_up(digits: &mut [u8]) -> Option<u8> {
    let len = digits.len();
    assert!(len <= PROOF_BUFLEN);
    let mut storage = [0; PROOF_BUFLEN];
    storage[..len].copy_from_slice(digits);
    let result = round_up_contract(&mut storage, len);
    digits.copy_from_slice(&storage[..len]);
    result
}

#[kani::proof_for_contract(round_up_contract)]
#[kani::unwind(33)]
fn check_round_up_contract() {
    let mut digits: [u8; PROOF_BUFLEN] = kani::any();
    let len: usize = kani::any();
    let result = round_up_contract(&mut digits, len);
    kani::cover(len == 0, "rounding accepts an empty prefix");
    kani::cover(
        len == PROOF_BUFLEN && result == Some(b'0'),
        "rounding carries across the full buffer",
    );
    kani::cover(
        len == PROOF_BUFLEN && result.is_none(),
        "rounding can preserve the full buffer length",
    );
}
