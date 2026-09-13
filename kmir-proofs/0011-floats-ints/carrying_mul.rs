#![feature(bigint_helper_methods)]

fn main() {
    carrying_mul_u8(0, 0, 0);
    carrying_mul_u16(0, 0, 0);
    carrying_mul_u32(0, 0, 0);
    carrying_mul_u64(0, 0, 0);
}

fn carrying_mul_u8(a: u8, b: u8, c: u8) {
    let (lo, hi) = a.carrying_mul(b, c);
    let expected = (a as u16) * (b as u16) + (c as u16);
    assert!(lo == (expected as u8));
    assert!(hi == ((expected >> u8::BITS) as u8));
}

fn carrying_mul_u16(a: u16, b: u16, c: u16) {
    let (lo, hi) = a.carrying_mul(b, c);
    let expected = (a as u32) * (b as u32) + (c as u32);
    assert!(lo == (expected as u16));
    assert!(hi == ((expected >> u16::BITS) as u16));
}

fn carrying_mul_u32(a: u32, b: u32, c: u32) {
    let (lo, hi) = a.carrying_mul(b, c);
    let expected = (a as u64) * (b as u64) + (c as u64);
    assert!(lo == (expected as u32));
    assert!(hi == ((expected >> u32::BITS) as u32));
}

fn carrying_mul_u64(a: u64, b: u64, c: u64) {
    let (lo, hi) = a.carrying_mul(b, c);
    let expected = (a as u128) * (b as u128) + (c as u128);
    assert!(lo == (expected as u64));
    assert!(hi == ((expected >> u64::BITS) as u64));
}
