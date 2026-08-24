#![feature(unchecked_neg)]

fn main() {
    unchecked_neg_i8(0);
    unchecked_neg_i16(0);
    unchecked_neg_i32(0);
    unchecked_neg_i64(0);
    unchecked_neg_i128(0);
}

fn unchecked_neg_i8(a: i8) {
    let result = unsafe { a.unchecked_neg() };
    assert!(result == a.wrapping_neg());
}

fn unchecked_neg_i16(a: i16) {
    let result = unsafe { a.unchecked_neg() };
    assert!(result == a.wrapping_neg());
}

fn unchecked_neg_i32(a: i32) {
    let result = unsafe { a.unchecked_neg() };
    assert!(result == a.wrapping_neg());
}

fn unchecked_neg_i64(a: i64) {
    let result = unsafe { a.unchecked_neg() };
    assert!(result == a.wrapping_neg());
}

fn unchecked_neg_i128(a: i128) {
    let result = unsafe { a.unchecked_neg() };
    assert!(result == a.wrapping_neg());
}
