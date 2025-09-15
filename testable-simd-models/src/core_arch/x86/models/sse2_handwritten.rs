use crate::abstractions::{bit::MachineInteger, simd::*};
pub fn packsswb(a: i16x8, b: i16x8) -> i8x16 {
    i8x16::from_fn(|i| {
        if i < 8 {
            if a[i] > (i8::MAX as i16) {
                i8::MAX
            } else if a[i] < (i8::MIN as i16) {
                i8::MIN
            } else {
                a[i] as i8
            }
        } else {
            if b[i - 8] > (i8::MAX as i16) {
                i8::MAX
            } else if b[i - 8] < (i8::MIN as i16) {
                i8::MIN
            } else {
                b[i - 8] as i8
            }
        }
    })
}
pub fn pmaddwd(a: i16x8, b: i16x8) -> i32x4 {
    i32x4::from_fn(|i| {
        (a[2 * i] as i32) * (b[2 * i] as i32) + (a[2 * i + 1] as i32) * (b[2 * i + 1] as i32)
    })
}
pub fn psadbw(a: u8x16, b: u8x16) -> u64x2 {
    let tmp = u8x16::from_fn(|i| a[i].wrapping_abs_diff(b[i]));
    u64x2::from_fn(|i| {
        (tmp[i * 8] as u16)
            .wrapping_add(tmp[i * 8 + 1] as u16)
            .wrapping_add(tmp[i * 8 + 2] as u16)
            .wrapping_add(tmp[i * 8 + 3] as u16)
            .wrapping_add(tmp[i * 8 + 4] as u16)
            .wrapping_add(tmp[i * 8 + 5] as u16)
            .wrapping_add(tmp[i * 8 + 6] as u16)
            .wrapping_add(tmp[i * 8 + 7] as u16) as u64
    })
}
pub fn psllw(a: i16x8, count: i16x8) -> i16x8 {
    let count4: u64 = (count[0] as u16) as u64;
    let count3: u64 = ((count[1] as u16) as u64) * 65536;
    let count2: u64 = ((count[2] as u16) as u64) * 4294967296;
    let count1: u64 = ((count[3] as u16) as u64) * 281474976710656;
    let count = count1 + count2 + count3 + count4;
    i16x8::from_fn(|i| {
        if count > 15 {
            0
        } else {
            ((a[i] as u16) << count) as i16
        }
    })
}

pub fn pslld(a: i32x4, count: i32x4) -> i32x4 {
    let count: u64 = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

    i32x4::from_fn(|i| {
        if count > 31 {
            0
        } else {
            ((a[i] as u32) << count) as i32
        }
    })
}

pub fn psllq(a: i64x2, count: i64x2) -> i64x2 {
    let count: u64 = count[0] as u64;

    i64x2::from_fn(|i| {
        if count > 63 {
            0
        } else {
            ((a[i] as u64) << count) as i64
        }
    })
}

pub fn psraw(a: i16x8, count: i16x8) -> i16x8 {
    let count: u64 = ((count[3] as u16) as u64) * 281474976710656
        + ((count[2] as u16) as u64) * 4294967296
        + ((count[1] as u16) as u64) * 65536
        + ((count[0] as u16) as u64);

    i16x8::from_fn(|i| {
        if count > 15 {
            if a[i] < 0 {
                -1
            } else {
                0
            }
        } else {
            a[i] >> count
        }
    })
}

pub fn psrad(a: i32x4, count: i32x4) -> i32x4 {
    let count: u64 = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

    i32x4::from_fn(|i| {
        if count > 31 {
            if a[i] < 0 {
                -1
            } else {
                0
            }
        } else {
            a[i] << count
        }
    })
}

pub fn psrlw(a: i16x8, count: i16x8) -> i16x8 {
    let count: u64 = (count[3] as u16 as u64) * 281474976710656
        + (count[2] as u16 as u64) * 4294967296
        + (count[1] as u16 as u64) * 65536
        + (count[0] as u16 as u64);

    i16x8::from_fn(|i| {
        if count > 15 {
            0
        } else {
            ((a[i] as u16) >> count) as i16
        }
    })
}

pub fn psrld(a: i32x4, count: i32x4) -> i32x4 {
    let count: u64 = (count[1] as u32 as u64) * 4294967296 + (count[0] as u32 as u64);

    i32x4::from_fn(|i| {
        if count > 31 {
            0
        } else {
            ((a[i] as u32) >> count) as i32
        }
    })
}

pub fn psrlq(a: i64x2, count: i64x2) -> i64x2 {
    let count: u64 = count[0] as u64;

    i64x2::from_fn(|i| {
        if count > 63 {
            0
        } else {
            ((a[i] as u64) >> count) as i64
        }
    })
}

pub fn packssdw(a: i32x4, b: i32x4) -> i16x8 {
    i16x8::from_fn(|i| {
        if i < 4 {
            if a[i] > (i16::MAX as i32) {
                i16::MAX
            } else if a[i] < (i16::MIN as i32) {
                i16::MIN
            } else {
                a[i] as i16
            }
        } else {
            if b[i - 4] > (i16::MAX as i32) {
                i16::MAX
            } else if b[i - 4] < (i16::MIN as i32) {
                i16::MIN
            } else {
                b[i - 4] as i16
            }
        }
    })
}

pub fn packuswb(a: i16x8, b: i16x8) -> u8x16 {
    u8x16::from_fn(|i| {
        if i < 8 {
            if a[i] > (u8::MAX as i16) {
                u8::MAX
            } else if a[i] < (u8::MIN as i16) {
                u8::MIN
            } else {
                a[i] as u8
            }
        } else {
            if b[i - 8] > (u8::MAX as i16) {
                u8::MAX
            } else if b[i - 8] < (u8::MIN as i16) {
                u8::MIN
            } else {
                b[i - 8] as u8
            }
        }
    })
}
