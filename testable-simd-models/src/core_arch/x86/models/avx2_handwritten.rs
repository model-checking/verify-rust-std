use crate::abstractions::{bit::MachineInteger, simd::*};
pub fn phaddw(a: i16x16, b: i16x16) -> i16x16 {
    i16x16::from_fn(|i| {
        if i < 4 {
            a[2 * i].wrapping_add(a[2 * i + 1])
        } else if i < 8 {
            b[2 * (i - 4)].wrapping_add(b[2 * (i - 4) + 1])
        } else if i < 12 {
            a[2 * (i - 4)].wrapping_add(a[2 * (i - 4) + 1])
        } else {
            b[2 * (i - 8)].wrapping_add(b[2 * (i - 8) + 1])
        }
    })
}

pub fn phaddd(a: i32x8, b: i32x8) -> i32x8 {
    i32x8::from_fn(|i| {
        if i < 2 {
            a[2 * i].wrapping_add(a[2 * i + 1])
        } else if i < 4 {
            b[2 * (i - 2)].wrapping_add(b[2 * (i - 2) + 1])
        } else if i < 6 {
            a[2 * (i - 2)].wrapping_add(a[2 * (i - 2) + 1])
        } else {
            b[2 * (i - 4)].wrapping_add(b[2 * (i - 4) + 1])
        }
    })
}

pub fn phaddsw(a: i16x16, b: i16x16) -> i16x16 {
    i16x16::from_fn(|i| {
        if i < 4 {
            a[2 * i].saturating_add(a[2 * i + 1])
        } else if i < 8 {
            b[2 * (i - 4)].saturating_add(b[2 * (i - 4) + 1])
        } else if i < 12 {
            a[2 * (i - 4)].saturating_add(a[2 * (i - 4) + 1])
        } else {
            b[2 * (i - 8)].saturating_add(b[2 * (i - 8) + 1])
        }
    })
}

pub fn phsubw(a: i16x16, b: i16x16) -> i16x16 {
    i16x16::from_fn(|i| {
        if i < 4 {
            a[2 * i].wrapping_sub(a[2 * i + 1])
        } else if i < 8 {
            b[2 * (i - 4)].wrapping_sub(b[2 * (i - 4) + 1])
        } else if i < 12 {
            a[2 * (i - 4)].wrapping_sub(a[2 * (i - 4) + 1])
        } else {
            b[2 * (i - 8)].wrapping_sub(b[2 * (i - 8) + 1])
        }
    })
}

pub fn phsubd(a: i32x8, b: i32x8) -> i32x8 {
    i32x8::from_fn(|i| {
        if i < 2 {
            a[2 * i].wrapping_sub(a[2 * i + 1])
        } else if i < 4 {
            b[2 * (i - 2)].wrapping_sub(b[2 * (i - 2) + 1])
        } else if i < 6 {
            a[2 * (i - 2)].wrapping_sub(a[2 * (i - 2) + 1])
        } else {
            b[2 * (i - 4)].wrapping_sub(b[2 * (i - 4) + 1])
        }
    })
}

pub fn phsubsw(a: i16x16, b: i16x16) -> i16x16 {
    i16x16::from_fn(|i| {
        if i < 4 {
            a[2 * i].saturating_sub(a[2 * i + 1])
        } else if i < 8 {
            b[2 * (i - 4)].saturating_sub(b[2 * (i - 4) + 1])
        } else if i < 12 {
            a[2 * (i - 4)].saturating_sub(a[2 * (i - 4) + 1])
        } else {
            b[2 * (i - 8)].saturating_sub(b[2 * (i - 8) + 1])
        }
    })
}
pub fn pmaddwd(a: i16x16, b: i16x16) -> i32x8 {
    i32x8::from_fn(|i| {
        (a[2 * i] as i32) * (b[2 * i] as i32) + (a[2 * i + 1] as i32) * (b[2 * i + 1] as i32)
    })
}

pub fn pmaddubsw(a: u8x32, b: u8x32) -> i16x16 {
    i16x16::from_fn(|i| {
        ((a[2 * i] as u8 as u16 as i16) * (b[2 * i] as i8 as i16))
            .saturating_add((a[2 * i + 1] as u8 as u16 as i16) * (b[2 * i + 1] as i8 as i16))
    })
}
pub fn packsswb(a: i16x16, b: i16x16) -> i8x32 {
    i8x32::from_fn(|i| {
        if i < 8 {
            if a[i] > (i8::MAX as i16) {
                i8::MAX
            } else if a[i] < (i8::MIN as i16) {
                i8::MIN
            } else {
                a[i] as i8
            }
        } else if i < 16 {
            if b[i - 8] > (i8::MAX as i16) {
                i8::MAX
            } else if b[i - 8] < (i8::MIN as i16) {
                i8::MIN
            } else {
                b[i - 8] as i8
            }
        } else if i < 24 {
            if a[i - 8] > (i8::MAX as i16) {
                i8::MAX
            } else if a[i - 8] < (i8::MIN as i16) {
                i8::MIN
            } else {
                a[i - 8] as i8
            }
        } else {
            if b[i - 16] > (i8::MAX as i16) {
                i8::MAX
            } else if b[i - 16] < (i8::MIN as i16) {
                i8::MIN
            } else {
                b[i - 16] as i8
            }
        }
    })
}

pub fn packssdw(a: i32x8, b: i32x8) -> i16x16 {
    i16x16::from_fn(|i| {
        if i < 4 {
            if a[i] > (i16::MAX as i32) {
                i16::MAX
            } else if a[i] < (i16::MIN as i32) {
                i16::MIN
            } else {
                a[i] as i16
            }
        } else if i < 8 {
            if b[i - 4] > (i16::MAX as i32) {
                i16::MAX
            } else if b[i - 4] < (i16::MIN as i32) {
                i16::MIN
            } else {
                b[i - 4] as i16
            }
        } else if i < 12 {
            if a[i - 4] > (i16::MAX as i32) {
                i16::MAX
            } else if a[i - 4] < (i16::MIN as i32) {
                i16::MIN
            } else {
                a[i - 4] as i16
            }
        } else {
            if b[i - 8] > (i16::MAX as i32) {
                i16::MAX
            } else if b[i - 8] < (i16::MIN as i32) {
                i16::MIN
            } else {
                b[i - 8] as i16
            }
        }
    })
}

pub fn packuswb(a: i16x16, b: i16x16) -> u8x32 {
    u8x32::from_fn(|i| {
        if i < 8 {
            if a[i] > (u8::MAX as i16) {
                u8::MAX
            } else if a[i] < (u8::MIN as i16) {
                u8::MIN
            } else {
                a[i] as u8
            }
        } else if i < 16 {
            if b[i - 8] > (u8::MAX as i16) {
                u8::MAX
            } else if b[i - 8] < (u8::MIN as i16) {
                u8::MIN
            } else {
                b[i - 8] as u8
            }
        } else if i < 24 {
            if a[i - 8] > (u8::MAX as i16) {
                u8::MAX
            } else if a[i - 8] < (u8::MIN as i16) {
                u8::MIN
            } else {
                a[i - 8] as u8
            }
        } else {
            if b[i - 16] > (u8::MAX as i16) {
                u8::MAX
            } else if b[i - 16] < (u8::MIN as i16) {
                u8::MIN
            } else {
                b[i - 16] as u8
            }
        }
    })
}

pub fn packusdw(a: i32x8, b: i32x8) -> u16x16 {
    u16x16::from_fn(|i| {
        if i < 4 {
            if a[i] > (u16::MAX as i32) {
                u16::MAX
            } else if a[i] < (u16::MIN as i32) {
                u16::MIN
            } else {
                a[i] as u16
            }
        } else if i < 8 {
            if b[i - 4] > (u16::MAX as i32) {
                u16::MAX
            } else if b[i - 4] < (u16::MIN as i32) {
                u16::MIN
            } else {
                b[i - 4] as u16
            }
        } else if i < 12 {
            if a[i - 4] > (u16::MAX as i32) {
                u16::MAX
            } else if a[i - 4] < (u16::MIN as i32) {
                u16::MIN
            } else {
                a[i - 4] as u16
            }
        } else {
            if b[i - 8] > (u16::MAX as i32) {
                u16::MAX
            } else if b[i - 8] < (u16::MIN as i32) {
                u16::MIN
            } else {
                b[i - 8] as u16
            }
        }
    })
}

pub fn psignb(a: i8x32, b: i8x32) -> i8x32 {
    i8x32::from_fn(|i| {
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
pub fn psignw(a: i16x16, b: i16x16) -> i16x16 {
    i16x16::from_fn(|i| {
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

pub fn psignd(a: i32x8, b: i32x8) -> i32x8 {
    i32x8::from_fn(|i| {
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

pub fn psllw(a: i16x16, count: i16x8) -> i16x16 {
    let count4 = (count[0] as u16) as u64;
    let count3 = ((count[1] as u16) as u64) * 65536;
    let count2 = ((count[2] as u16) as u64) * 4294967296;
    let count1 = ((count[3] as u16) as u64) * 281474976710656;
    let count = count1 + count2 + count3 + count4;
    i16x16::from_fn(|i| {
        if count > 15 {
            0
        } else {
            ((a[i] as u16) << count) as i16
        }
    })
}

pub fn pslld(a: i32x8, count: i32x4) -> i32x8 {
    let count = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

    i32x8::from_fn(|i| {
        if count > 31 {
            0
        } else {
            ((a[i] as u32) << count) as i32
        }
    })
}
pub fn psllq(a: i64x4, count: i64x2) -> i64x4 {
    let count = count[0] as u32;

    i64x4::from_fn(|i| {
        if count > 63 {
            0
        } else {
            ((a[i] as u32) << count) as i64
        }
    })
}

pub fn psllvd(a: i32x4, count: i32x4) -> i32x4 {
    i32x4::from_fn(|i| {
        if count[i] > 31 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) << count[i]) as i32
        }
    })
}
pub fn psllvd256(a: i32x8, count: i32x8) -> i32x8 {
    i32x8::from_fn(|i| {
        if count[i] > 31 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) << count[i]) as i32
        }
    })
}

pub fn psllvq(a: i64x2, count: i64x2) -> i64x2 {
    i64x2::from_fn(|i| {
        if count[i] > 63 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) << count[i]) as i64
        }
    })
}
pub fn psllvq256(a: i64x4, count: i64x4) -> i64x4 {
    i64x4::from_fn(|i| {
        if count[i] > 63 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) << count[i]) as i64
        }
    })
}

pub fn psraw(a: i16x16, count: i16x8) -> i16x16 {
    let count = ((count[3] as u16) as u64) * 281474976710656
        + ((count[2] as u16) as u64) * 4294967296
        + ((count[1] as u16) as u64) * 65536
        + ((count[0] as u16) as u64);

    i16x16::from_fn(|i| {
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

pub fn psrad(a: i32x8, count: i32x4) -> i32x8 {
    let count = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

    i32x8::from_fn(|i| {
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

pub fn psravd(a: i32x4, count: i32x4) -> i32x4 {
    i32x4::from_fn(|i| {
        if count[i] > 31 || count[i] < 0 {
            if a[i] < 0 {
                -1
            } else {
                0
            }
        } else {
            a[i] >> count[i]
        }
    })
}

pub fn psravd256(a: i32x8, count: i32x8) -> i32x8 {
    i32x8::from_fn(|i| {
        if count[i] > 31 || count[i] < 0 {
            if a[i] < 0 {
                -1
            } else {
                0
            }
        } else {
            a[i] >> count[i]
        }
    })
}

pub fn psrlw(a: i16x16, count: i16x8) -> i16x16 {
    let count = (count[3] as u16 as u64) * 281474976710656
        + (count[2] as u16 as u64) * 4294967296
        + (count[1] as u16 as u64) * 65536
        + (count[0] as u16 as u64);

    i16x16::from_fn(|i| {
        if count > 15 {
            0
        } else {
            ((a[i] as u16) >> count) as i16
        }
    })
}

pub fn psrld(a: i32x8, count: i32x4) -> i32x8 {
    let count = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

    i32x8::from_fn(|i| {
        if count > 31 {
            0
        } else {
            ((a[i] as u32) >> count) as i32
        }
    })
}

pub fn psrlq(a: i64x4, count: i64x2) -> i64x4 {
    let count: u64 = count[0] as u64;

    i64x4::from_fn(|i| {
        if count > 63 {
            0
        } else {
            ((a[i] as u32) >> count) as i64
        }
    })
}

pub fn psrlvd(a: i32x4, count: i32x4) -> i32x4 {
    i32x4::from_fn(|i| {
        if count[i] > 31 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) >> count[i]) as i32
        }
    })
}

pub fn psrlvd256(a: i32x8, count: i32x8) -> i32x8 {
    i32x8::from_fn(|i| {
        if count[i] > 31 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) >> count[i]) as i32
        }
    })
}

pub fn psrlvq(a: i64x2, count: i64x2) -> i64x2 {
    i64x2::from_fn(|i| {
        if count[i] > 63 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) >> count[i]) as i64
        }
    })
}
pub fn psrlvq256(a: i64x4, count: i64x4) -> i64x4 {
    i64x4::from_fn(|i| {
        if count[i] > 63 || count[i] < 0 {
            0
        } else {
            ((a[i] as u32) >> count[i]) as i64
        }
    })
}

pub fn pshufb(a: u8x32, b: u8x32) -> u8x32 {
    u8x32::from_fn(|i| {
        if i < 16 {
            if b[i] > 127 {
                0
            } else {
                let index = (b[i] % 16) as u32;
                a[index]
            }
        } else {
            if b[i] > 127 {
                0
            } else {
                let index = (b[i] % 16) as u32;
                a[index + 16]
            }
        }
    })
}

pub fn permd(a: u32x8, b: u32x8) -> u32x8 {
    u32x8::from_fn(|i| {
        let id = b[i] % 8;
        a[id]
    })
}

pub fn mpsadbw(a: u8x32, b: u8x32, imm8: i8) -> u16x16 {
    u16x16::from_fn(|i| {
        if i < 8 {
            let a_offset = (((imm8 & 4) >> 2) * 4) as u32;
            let b_offset = ((imm8 & 3) * 4) as u32;
            let k = a_offset + i;
            let l = b_offset;
            ((a[k].wrapping_abs_diff(b[l]) as i8) as u8 as u16)
                + ((a[k + 1].wrapping_abs_diff(b[l + 1]) as i8) as u8 as u16)
                + ((a[k + 2].wrapping_abs_diff(b[l + 2]) as i8) as u8 as u16)
                + ((a[k + 3].wrapping_abs_diff(b[l + 3]) as i8) as u8 as u16)
        } else {
            let i = i - 8;
            let imm8 = imm8 >> 3;
            let a_offset = (((imm8 & 4) >> 2) * 4) as u32;
            let b_offset = ((imm8 & 3) * 4) as u32;
            let k = a_offset + i;
            let l = b_offset;
            ((a[16 + k].wrapping_abs_diff(b[16 + l]) as i8) as u8 as u16)
                + ((a[16 + k + 1].wrapping_abs_diff(b[16 + l + 1]) as i8) as u8 as u16)
                + ((a[16 + k + 2].wrapping_abs_diff(b[16 + l + 2]) as i8) as u8 as u16)
                + ((a[16 + k + 3].wrapping_abs_diff(b[16 + l + 3]) as i8) as u8 as u16)
        }
    })
}

pub fn vperm2i128(a: i64x4, b: i64x4, imm8: i8) -> i64x4 {
    let a = i128x2::from_fn(|i| {
        ((a[2 * i] as u64 as u128) + ((a[2 * i + 1] as u64 as u128) << 64)) as i128
    });
    let b = i128x2::from_fn(|i| {
        ((b[2 * i] as u64 as u128) + ((b[2 * i + 1] as u64 as u128) << 64)) as i128
    });
    let imm8 = imm8 as u8 as u32 as i32;
    let r = i128x2::from_fn(|i| {
        let control = imm8 >> (i * 4);
        if (control >> 3) % 2 == 1 {
            0
        } else {
            match control % 4 {
                0 => a[0],
                1 => a[1],
                2 => b[0],
                3 => b[1],
                _ => unreachable!(),
            }
        }
    });
    i64x4::from_fn(|i| {
        let index = i >> 1;
        let hilo = i.rem_euclid(2);
        let val = r[index];
        if hilo == 0 {
            i64::cast(val)
        } else {
            i64::cast(val >> 64)
        }
    })
}
pub fn pmulhrsw(a: i16x16, b: i16x16) -> i16x16 {
    i16x16::from_fn(|i| {
        let temp = (a[i] as i32) * (b[i] as i32);
        let temp = (temp >> 14).wrapping_add(1) >> 1;
        temp as i16
    })
}

pub fn psadbw(a: u8x32, b: u8x32) -> u64x4 {
    let tmp = u8x32::from_fn(|i| a[i].wrapping_abs_diff(b[i]));
    u64x4::from_fn(|i| {
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
