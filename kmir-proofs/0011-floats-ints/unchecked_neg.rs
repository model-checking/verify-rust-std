#![feature(unchecked_neg)]

fn main() {
    unchecked_neg_i8(0);
    unchecked_neg_i16(0);
    unchecked_neg_i32(0);
    unchecked_neg_i64(0);
    unchecked_neg_i128(0);
}

fn unchecked_neg_i8(a: i8) {
    if let Some(expected) = a.checked_neg() {
        let result = unsafe { a.unchecked_neg() };
        assert!(result == expected);
    }
}

fn unchecked_neg_i16(a: i16) {
    if let Some(expected) = a.checked_neg() {
        let result = unsafe { a.unchecked_neg() };
        assert!(result == expected);
    }
}

fn unchecked_neg_i32(a: i32) {
    if let Some(expected) = a.checked_neg() {
        let result = unsafe { a.unchecked_neg() };
        assert!(result == expected);
    }
}

fn unchecked_neg_i64(a: i64) {
    if let Some(expected) = a.checked_neg() {
        let result = unsafe { a.unchecked_neg() };
        assert!(result == expected);
    }
}

fn unchecked_neg_i128(a: i128) {
    if let Some(expected) = a.checked_neg() {
        let result = unsafe { a.unchecked_neg() };
        assert!(result == expected);
    }
}
