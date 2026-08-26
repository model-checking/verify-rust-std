#![feature(unchecked_math)]

fn main() {
    unchecked_sub_u8(0, 0);
    unchecked_sub_u16(0, 0);
    unchecked_sub_u32(0, 0);
    unchecked_sub_u64(0, 0);
    unchecked_sub_u128(0, 0);
    unchecked_sub_i8(0, 0);
    unchecked_sub_i16(0, 0);
    unchecked_sub_i32(0, 0);
    unchecked_sub_i64(0, 0);
    unchecked_sub_i128(0, 0);
}

fn unchecked_sub_u8(a: u8, b: u8) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_u16(a: u16, b: u16) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_u32(a: u32, b: u32) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_u64(a: u64, b: u64) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_u128(a: u128, b: u128) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_i8(a: i8, b: i8) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_i16(a: i16, b: i16) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_i32(a: i32, b: i32) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_i64(a: i64, b: i64) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}

fn unchecked_sub_i128(a: i128, b: i128) {
    let result = unsafe { a.unchecked_sub(b) };
    assert!(result == a.wrapping_sub(b));
}
