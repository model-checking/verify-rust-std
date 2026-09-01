fn main() {
    wrapping_shl_u8(0, 0);
    wrapping_shl_u16(0, 0);
    wrapping_shl_u32(0, 0);
    wrapping_shl_u64(0, 0);
    wrapping_shl_u128(0, 0);
    wrapping_shl_i8(0, 0);
    wrapping_shl_i16(0, 0);
    wrapping_shl_i32(0, 0);
    wrapping_shl_i64(0, 0);
    wrapping_shl_i128(0, 0);
}

fn wrapping_shl_u8(a: u8, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_u16(a: u16, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_u32(a: u32, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_u64(a: u64, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_u128(a: u128, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_i8(a: i8, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_i16(a: i16, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_i32(a: i32, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_i64(a: i64, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}

fn wrapping_shl_i128(a: i128, b: u32) {
    if let Some(expected) = a.checked_shl(b) {
        assert!(a.wrapping_shl(b) == expected);
    }
}
