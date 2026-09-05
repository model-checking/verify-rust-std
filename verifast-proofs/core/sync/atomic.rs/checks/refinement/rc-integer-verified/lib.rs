#![allow(non_snake_case)]

fn identity<const N: usize>(value: [u8; N]) -> [u8; N] { value }

mod bridge {
    pub fn array_identity__VeriFast_wrapper(value: [u8; 3]) -> [u8; 3] {
        super::identity::<3>(value)
    }
}

pub fn array_identity(value: [u8; 3]) -> [u8; 3] {
    bridge::array_identity__VeriFast_wrapper(value)
}
