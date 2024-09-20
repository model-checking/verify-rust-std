#[cfg(kani)]
kani_core::kani_lib!(core);
use safety::{ensures, requires};

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    #[kani::proof]
    pub fn harness() {
        kani::assert(true, "yay");
    }

    #[kani::proof_for_contract(trivial_function)]
    fn dummy_proof() {
        trivial_function(true);
    }

    #[kani::requires(x == true)]
    fn trivial_function(x: bool) -> bool {
        x
    }
}