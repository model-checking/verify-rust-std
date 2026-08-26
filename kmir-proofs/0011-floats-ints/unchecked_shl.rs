#![feature(unchecked_shifts)]

fn main() {
    unchecked_shl_u8(0, 0);
    unchecked_shl_u16(0, 0);
    unchecked_shl_u32(0, 0);
    unchecked_shl_u64(0, 0);
    unchecked_shl_u128(0, 0);
    unchecked_shl_i8(0, 0);
    unchecked_shl_i16(0, 0);
    unchecked_shl_i32(0, 0);
    unchecked_shl_i64(0, 0);
    unchecked_shl_i128(0, 0);
}

fn unchecked_shl_u8(a: u8, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_u16(a: u16, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_u32(a: u32, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_u64(a: u64, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_u128(a: u128, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_i8(a: i8, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_i16(a: i16, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_i32(a: i32, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_i64(a: i64, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}

fn unchecked_shl_i128(a: i128, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        let result = unsafe { a.unchecked_shl(b) };
        assert!(result == expected);
    }
}
