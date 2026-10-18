#![feature(unchecked_shifts)]

fn main() {
    unchecked_shr_u8(0, 0);
    unchecked_shr_u16(0, 0);
    unchecked_shr_u32(0, 0);
    unchecked_shr_u64(0, 0);
    unchecked_shr_u128(0, 0);
    unchecked_shr_i8(0, 0);
    unchecked_shr_i16(0, 0);
    unchecked_shr_i32(0, 0);
    unchecked_shr_i64(0, 0);
    unchecked_shr_i128(0, 0);
}

fn unchecked_shr_u8(a: u8, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_u16(a: u16, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_u32(a: u32, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_u64(a: u64, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_u128(a: u128, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_i8(a: i8, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_i16(a: i16, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_i32(a: i32, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_i64(a: i64, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}

fn unchecked_shr_i128(a: i128, b: u32) {
    if let Some(expected) = a.checked_shr(b) {
        let result = unsafe { a.unchecked_shr(b) };
        assert!(result == expected);
    }
}
