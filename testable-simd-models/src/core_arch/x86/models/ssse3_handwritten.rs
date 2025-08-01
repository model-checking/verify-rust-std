use crate::abstractions::simd::*;
pub fn pshufb128(a: u8x16, b: u8x16) -> u8x16 {
    u8x16::from_fn(|i| if b[i] > 127 { 0 } else { a[(b[i] % 16) as u32] })
}

pub fn phaddw128(a: i16x8, b: i16x8) -> i16x8 {
    i16x8::from_fn(|i| {
        if i < 4 {
            a[2 * i].wrapping_add(a[2 * i + 1])
        } else {
            b[2 * (i - 4)].wrapping_add(b[2 * (i - 4) + 1])
        }
    })
}

pub fn phaddsw128(a: i16x8, b: i16x8) -> i16x8 {
    i16x8::from_fn(|i| {
        if i < 4 {
            a[2 * i].saturating_add(a[2 * i + 1])
        } else {
            b[2 * (i - 4)].saturating_add(b[2 * (i - 4) + 1])
        }
    })
}

pub fn phaddd128(a: i32x4, b: i32x4) -> i32x4 {
    i32x4::from_fn(|i| {
        if i < 2 {
            a[2 * i].wrapping_add(a[2 * i + 1])
        } else {
            b[2 * (i - 2)].wrapping_add(b[2 * (i - 2) + 1])
        }
    })
}

pub fn phsubw128(a: i16x8, b: i16x8) -> i16x8 {
    i16x8::from_fn(|i| {
        if i < 4 {
            a[2 * i].wrapping_sub(a[2 * i + 1])
        } else {
            b[2 * (i - 4)].wrapping_sub(b[2 * (i - 4) + 1])
        }
    })
}

pub fn phsubsw128(a: i16x8, b: i16x8) -> i16x8 {
    i16x8::from_fn(|i| {
        if i < 4 {
            a[2 * i].saturating_sub(a[2 * i + 1])
        } else {
            b[2 * (i - 4)].saturating_sub(b[2 * (i - 4) + 1])
        }
    })
}

pub fn phsubd128(a: i32x4, b: i32x4) -> i32x4 {
    i32x4::from_fn(|i| {
        if i < 2 {
            a[2 * i].wrapping_sub(a[2 * i + 1])
        } else {
            b[2 * (i - 2)].wrapping_sub(b[2 * (i - 2) + 1])
        }
    })
}

pub fn pmaddubsw128(a: u8x16, b: i8x16) -> i16x8 {
    i16x8::from_fn(|i| {
        ((a[2 * i] as u8 as u16 as i16) * (b[2 * i] as i8 as i16))
            .saturating_add((a[2 * i + 1] as u8 as u16 as i16) * (b[2 * i + 1] as i8 as i16))
    })
}

pub fn pmulhrsw128(a: i16x8, b: i16x8) -> i16x8 {
    i16x8::from_fn(|i| {
        let temp = (a[i] as i32) * (b[i] as i32);
        let temp = (temp >> 14).wrapping_add(1) >> 1;
        temp as i16
    })
}

pub fn psignb128(a: i8x16, b: i8x16) -> i8x16 {
    i8x16::from_fn(|i| {
        if b[i] < 0 {
            if a[i] == i8::MIN {
                a[i]
            } else {
                -a[i]
            }
        } else if b[i] > 0 {
            a[i]
        } else {
            0
        }
    })
}

pub fn psignw128(a: i16x8, b: i16x8) -> i16x8 {
    i16x8::from_fn(|i| {
        if b[i] < 0 {
            if a[i] == i16::MIN {
                a[i]
            } else {
                -a[i]
            }
        } else if b[i] > 0 {
            a[i]
        } else {
            0
        }
    })
}

pub fn psignd128(a: i32x4, b: i32x4) -> i32x4 {
    i32x4::from_fn(|i| {
        if b[i] < 0 {
            if a[i] == i32::MIN {
                a[i]
            } else {
                -a[i]
            }
        } else if b[i] > 0 {
            a[i]
        } else {
            0
        }
    })
}
