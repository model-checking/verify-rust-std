#![feature(unchecked_math)]

fn main() {
    unchecked_mul_u8(0, 0);
    unchecked_mul_u16(0, 0);
    unchecked_mul_u32(0, 0);
    unchecked_mul_u64(0, 0);
    unchecked_mul_u128(0, 0);
    unchecked_mul_i8(0, 0);
    unchecked_mul_i16(0, 0);
    unchecked_mul_i32(0, 0);
    unchecked_mul_i64(0, 0);
    unchecked_mul_i128(0, 0);
}

fn unchecked_mul_u8(a: u8, b: u8) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_u16(a: u16, b: u16) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_u32(a: u32, b: u32) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_u64(a: u64, b: u64) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_u128(a: u128, b: u128) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_i8(a: i8, b: i8) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_i16(a: i16, b: i16) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_i32(a: i32, b: i32) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_i64(a: i64, b: i64) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}

fn unchecked_mul_i128(a: i128, b: i128) {
    if let Some(expected) = a.checked_mul(b) {
        let result = unsafe { a.unchecked_mul(b) };
        assert!(result == expected);
    }
}
