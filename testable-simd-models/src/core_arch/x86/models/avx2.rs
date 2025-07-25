//! Advanced Vector Extensions 2 (AVX)
//!
//!
//! This module contains models for AVX2 intrinsics.
//! AVX2 expands most AVX commands to 256-bit wide vector registers and
//! adds [FMA](https://en.wikipedia.org/wiki/Fused_multiply-accumulate).
//!
//! The references are:
//!
//! - [Intel 64 and IA-32 Architectures Software Developer's Manual Volume 2:
//!   Instruction Set Reference, A-Z][intel64_ref].
//! - [AMD64 Architecture Programmer's Manual, Volume 3: General-Purpose and
//!   System Instructions][amd64_ref].
//!
//! Wikipedia's [AVX][wiki_avx] and [FMA][wiki_fma] pages provide a quick
//! overview of the instructions available.
//!
//! [intel64_ref]: http://www.intel.de/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-instruction-set-reference-manual-325383.pdf
//! [amd64_ref]: http://support.amd.com/TechDocs/24594.pdf
//! [wiki_avx]: https://en.wikipedia.org/wiki/Advanced_Vector_Extensions
//! [wiki_fma]: https://en.wikipedia.org/wiki/Fused_multiply-accumulate
use crate::abstractions::{bitvec::BitVec, simd::*};

mod c_extern {
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
        let count4: u64 = (count[0] as u16) as u64;
        let count3: u64 = ((count[1] as u16) as u64) * 65536;
        let count2: u64 = ((count[2] as u16) as u64) * 4294967296;
        let count1: u64 = ((count[3] as u16) as u64) * 281474976710656;
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
        let count: u64 = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

        i32x8::from_fn(|i| {
            if count > 31 {
                0
            } else {
                ((a[i] as u32) << count) as i32
            }
        })
    }
    pub fn psllq(a: i64x4, count: i64x2) -> i64x4 {
        let count: u64 = count[0] as u64;

        i64x4::from_fn(|i| {
            if count > 63 {
                0
            } else {
                ((a[i] as u64) << count) as i64
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
                ((a[i] as u64) << count[i]) as i64
            }
        })
    }
    pub fn psllvq256(a: i64x4, count: i64x4) -> i64x4 {
        i64x4::from_fn(|i| {
            if count[i] > 63 || count[i] < 0 {
                0
            } else {
                ((a[i] as u64) << count[i]) as i64
            }
        })
    }

    pub fn psraw(a: i16x16, count: i16x8) -> i16x16 {
        let count: u64 = ((count[3] as u16) as u64) * 281474976710656
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
        let count: u64 = ((count[1] as u32) as u64) * 4294967296 + ((count[0] as u32) as u64);

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
        dbg!(a, count);
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
        let count: u64 = (count[3] as u16 as u64) * 281474976710656
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
        let count: u64 = (count[1] as u32 as u64) * 4294967296 + (count[0] as u32 as u64);

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
                ((a[i] as u64) >> count) as i64
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
                ((a[i] as u64) >> count[i]) as i64
            }
        })
    }
    pub fn psrlvq256(a: i64x4, count: i64x4) -> i64x4 {
        i64x4::from_fn(|i| {
            if count[i] > 63 || count[i] < 0 {
                0
            } else {
                ((a[i] as u64) >> count[i]) as i64
            }
        })
    }

    pub fn pshufb(a: u8x32, b: u8x32) -> u8x32 {
        u8x32::from_fn(|i| {
            if i < 16 {
                if b[i] > 127 {
                    0
                } else {
                    let index: u64 = (b[i] % 16) as u64;
                    a[index]
                }
            } else {
                if b[i] > 127 {
                    0
                } else {
                    let index: u64 = (b[i] % 16) as u64;
                    a[index + 16]
                }
            }
        })
    }

    pub fn permd(a: u32x8, b: u32x8) -> u32x8 {
        u32x8::from_fn(|i| {
            let id = b[i] % 8;
            a[id as u64]
        })
    }

    pub fn mpsadbw(a: u8x32, b: u8x32, imm8: i32) -> u16x16 {
        u16x16::from_fn(|i| {
            if i < 8 {
                let a_offset = (((imm8 & 4) >> 2) * 4) as u32 as u64;
                let b_offset = ((imm8 & 3) * 4) as u32 as u64;
                let k = a_offset + i;
                let l = b_offset;
                ((a[k].absolute_diff(b[l]) as i8) as u8 as u16)
                    + ((a[k + 1].absolute_diff(b[l + 1]) as i8) as u8 as u16)
                    + ((a[k + 2].absolute_diff(b[l + 2]) as i8) as u8 as u16)
                    + ((a[k + 3].absolute_diff(b[l + 3]) as i8) as u8 as u16)
            } else {
                let i = i - 8;
                let imm8 = imm8 >> 3;
                let a_offset = (((imm8 & 4) >> 2) * 4) as u32 as u64;
                let b_offset = ((imm8 & 3) * 4) as u32 as u64;
                let k = a_offset + i;
                let l = b_offset;
                ((a[16 + k].absolute_diff(b[16 + l]) as i8) as u8 as u16)
                    + ((a[16 + k + 1].absolute_diff(b[16 + l + 1]) as i8) as u8 as u16)
                    + ((a[16 + k + 2].absolute_diff(b[16 + l + 2]) as i8) as u8 as u16)
                    + ((a[16 + k + 3].absolute_diff(b[16 + l + 3]) as i8) as u8 as u16)
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
        let tmp = u8x32::from_fn(|i| a[i].absolute_diff(b[i]));
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
}
use c_extern::*;

use super::avx::*;
use super::types::*;
use crate::abstractions::simd::*;
/// Computes the absolute values of packed 32-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi32)

pub fn _mm256_abs_epi32(a: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let r = simd_select(simd_lt(a, i32x8::from_fn(|_| 0)), simd_neg(a), a);
    BitVec::from_i32x8(r)
}

/// Computes the absolute values of packed 16-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi16)

pub fn _mm256_abs_epi16(a: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let r = simd_select(simd_lt(a, i16x16::from_fn(|_| 0)), simd_neg(a), a);
    BitVec::from_i16x16(r)
}

/// Computes the absolute values of packed 8-bit integers in `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi8)

pub fn _mm256_abs_epi8(a: __m256i) -> __m256i {
    let a = BitVec::to_i8x32(a);
    let r = simd_select(simd_lt(a, i8x32::from_fn(|_| 0)), simd_neg(a), a);
    BitVec::from_i8x32(r)
}

/// Adds packed 64-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi64)

pub fn _mm256_add_epi64(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_i64x4(simd_add(BitVec::to_i64x4(a), BitVec::to_i64x4(b)))
}

/// Adds packed 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi32)

pub fn _mm256_add_epi32(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_i32x8(simd_add(BitVec::to_i32x8(a), BitVec::to_i32x8(b)))
}

/// Adds packed 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi16)

pub fn _mm256_add_epi16(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_i16x16(simd_add(BitVec::to_i16x16(a), BitVec::to_i16x16(b)))
}

/// Adds packed 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi8)

pub fn _mm256_add_epi8(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_i8x32(simd_add(BitVec::to_i8x32(a), BitVec::to_i8x32(b)))
}

/// Adds packed 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epi8)

pub fn _mm256_adds_epi8(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_i8x32(simd_saturating_add(
        BitVec::to_i8x32(a),
        BitVec::to_i8x32(b),
    ))
}

/// Adds packed 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epi16)

pub fn _mm256_adds_epi16(a: __m256i, b: __m256i) -> __m256i {
    BitVec::from_i16x16(simd_saturating_add(
        BitVec::to_i16x16(a),
        BitVec::to_i16x16(b),
    ))
}

/// Adds packed unsigned 8-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epu8)

pub fn _mm256_adds_epu8(a: __m256i, b: __m256i) -> __m256i {
    simd_saturating_add(BitVec::to_u8x32(a), BitVec::to_u8x32(b)).into()
}

/// Adds packed unsigned 16-bit integers in `a` and `b` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epu16)

pub fn _mm256_adds_epu16(a: __m256i, b: __m256i) -> __m256i {
    simd_saturating_add(BitVec::to_u16x16(a), BitVec::to_u16x16(b)).into()
}

/// Concatenates pairs of 16-byte blocks in `a` and `b` into a 32-byte temporary
/// result, shifts the result right by `n` bytes, and returns the low 16 bytes.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_alignr_epi8)

pub fn _mm256_alignr_epi8<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    // If palignr is shifting the pair of vectors more than the size of two
    // lanes, emit zero.
    if IMM8 >= 32 {
        return _mm256_setzero_si256();
    }
    // If palignr is shifting the pair of input vectors more than one lane,
    // but less than two lanes, convert to shifting in zeroes.
    let (a, b) = if IMM8 > 16 {
        (_mm256_setzero_si256(), a)
    } else {
        (a, b)
    };

    let a = BitVec::to_i8x32(a);
    let b = BitVec::to_i8x32(b);

    if IMM8 == 16 {
        return a.into();
    }

    let r: i8x32 = match IMM8 % 16 {
        0 => simd_shuffle(
            b,
            a,
            [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 26, 27, 28, 29, 30, 31,
            ],
        ),
        1 => simd_shuffle(
            b,
            a,
            [
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 48,
            ],
        ),
        2 => simd_shuffle(
            b,
            a,
            [
                2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 18, 19, 20, 21, 22, 23, 24,
                25, 26, 27, 28, 29, 30, 31, 48, 49,
            ],
        ),
        3 => simd_shuffle(
            b,
            a,
            [
                3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 19, 20, 21, 22, 23, 24,
                25, 26, 27, 28, 29, 30, 31, 48, 49, 50,
            ],
        ),
        4 => simd_shuffle(
            b,
            a,
            [
                4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 20, 21, 22, 23, 24, 25,
                26, 27, 28, 29, 30, 31, 48, 49, 50, 51,
            ],
        ),
        5 => simd_shuffle(
            b,
            a,
            [
                5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 21, 22, 23, 24, 25, 26,
                27, 28, 29, 30, 31, 48, 49, 50, 51, 52,
            ],
        ),
        6 => simd_shuffle(
            b,
            a,
            [
                6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 22, 23, 24, 25, 26, 27,
                28, 29, 30, 31, 48, 49, 50, 51, 52, 53,
            ],
        ),
        7 => simd_shuffle(
            b,
            a,
            [
                7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 23, 24, 25, 26, 27,
                28, 29, 30, 31, 48, 49, 50, 51, 52, 53, 54,
            ],
        ),
        8 => simd_shuffle(
            b,
            a,
            [
                8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 24, 25, 26, 27, 28,
                29, 30, 31, 48, 49, 50, 51, 52, 53, 54, 55,
            ],
        ),
        9 => simd_shuffle(
            b,
            a,
            [
                9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 25, 26, 27, 28, 29,
                30, 31, 48, 49, 50, 51, 52, 53, 54, 55, 56,
            ],
        ),
        10 => simd_shuffle(
            b,
            a,
            [
                10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 26, 27, 28, 29, 30,
                31, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
            ],
        ),
        11 => simd_shuffle(
            b,
            a,
            [
                11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 27, 28, 29, 30, 31,
                48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58,
            ],
        ),
        12 => simd_shuffle(
            b,
            a,
            [
                12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 28, 29, 30, 31, 48,
                49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
            ],
        ),
        13 => simd_shuffle(
            b,
            a,
            [
                13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 29, 30, 31, 48, 49,
                50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
            ],
        ),
        14 => simd_shuffle(
            b,
            a,
            [
                14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 30, 31, 48, 49, 50,
                51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
            ],
        ),
        15 => simd_shuffle(
            b,
            a,
            [
                15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 31, 48, 49, 50, 51,
                52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62,
            ],
        ),
        _ => unreachable!(),
    };
    r.into()
}

/// Computes the bitwise AND of 256 bits (representing integer data)
/// in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_and_si256)

pub fn _mm256_and_si256(a: __m256i, b: __m256i) -> __m256i {
    simd_and(BitVec::to_i64x4(a), BitVec::to_i64x4(b)).into()
}

/// Computes the bitwise NOT of 256 bits (representing integer data)
/// in `a` and then AND with `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_andnot_si256)

pub fn _mm256_andnot_si256(a: __m256i, b: __m256i) -> __m256i {
    let all_ones = _mm256_set1_epi8(-1);
    simd_and(
        simd_xor(BitVec::to_i64x4(a), BitVec::to_i64x4(all_ones)),
        BitVec::to_i64x4(b),
    )
    .into()
}

/// Averages packed unsigned 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_avg_epu16)

pub fn _mm256_avg_epu16(a: __m256i, b: __m256i) -> __m256i {
    let a = simd_cast::<16, _, u32>(BitVec::to_u16x16(a));
    let b = simd_cast::<16, _, u32>(BitVec::to_u16x16(b));
    let r = simd_shr(simd_add(simd_add(a, b), u32x16::splat(1)), u32x16::splat(1));
    simd_cast::<16, _, u16>(r).into()
}

/// Averages packed unsigned 8-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_avg_epu8)

pub fn _mm256_avg_epu8(a: __m256i, b: __m256i) -> __m256i {
    let a = simd_cast::<32, _, u16>(BitVec::to_u8x32(a));
    let b = simd_cast::<32, _, u16>(BitVec::to_u8x32(b));
    let r = simd_shr(simd_add(simd_add(a, b), u16x32::splat(1)), u16x32::splat(1));
    simd_cast::<32, _, u8>(r).into()
}

/// Blends packed 32-bit integers from `a` and `b` using control mask `IMM4`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_blend_epi32)

pub fn _mm_blend_epi32<const IMM4: i32>(a: __m128i, b: __m128i) -> __m128i {
    let a = BitVec::to_i32x4(a);
    let b = BitVec::to_i32x4(b);
    let r: i32x4 = simd_shuffle(
        a,
        b,
        [
            [0, 4, 0, 4][IMM4 as usize & 0b11],
            [1, 1, 5, 5][IMM4 as usize & 0b11],
            [2, 6, 2, 6][(IMM4 as usize >> 2) & 0b11],
            [3, 3, 7, 7][(IMM4 as usize >> 2) & 0b11],
        ],
    );
    r.into()
}

/// Blends packed 32-bit integers from `a` and `b` using control mask `IMM8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi32)

pub fn _mm256_blend_epi32<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);
    let r: i32x8 = simd_shuffle(
        a,
        b,
        [
            [0, 8, 0, 8][IMM8 as usize & 0b11],
            [1, 1, 9, 9][IMM8 as usize & 0b11],
            [2, 10, 2, 10][(IMM8 as usize >> 2) & 0b11],
            [3, 3, 11, 11][(IMM8 as usize >> 2) & 0b11],
            [4, 12, 4, 12][(IMM8 as usize >> 4) & 0b11],
            [5, 5, 13, 13][(IMM8 as usize >> 4) & 0b11],
            [6, 14, 6, 14][(IMM8 as usize >> 6) & 0b11],
            [7, 7, 15, 15][(IMM8 as usize >> 6) & 0b11],
        ],
    );
    r.into()
}

/// Blends packed 16-bit integers from `a` and `b` using control mask `IMM8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi16)
pub fn _mm256_blend_epi16<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let b = BitVec::to_i16x16(b);

    let r: i16x16 = simd_shuffle(
        a,
        b,
        [
            [0, 16, 0, 16][IMM8 as usize & 0b11],
            [1, 1, 17, 17][IMM8 as usize & 0b11],
            [2, 18, 2, 18][(IMM8 as usize >> 2) & 0b11],
            [3, 3, 19, 19][(IMM8 as usize >> 2) & 0b11],
            [4, 20, 4, 20][(IMM8 as usize >> 4) & 0b11],
            [5, 5, 21, 21][(IMM8 as usize >> 4) & 0b11],
            [6, 22, 6, 22][(IMM8 as usize >> 6) & 0b11],
            [7, 7, 23, 23][(IMM8 as usize >> 6) & 0b11],
            [8, 24, 8, 24][IMM8 as usize & 0b11],
            [9, 9, 25, 25][IMM8 as usize & 0b11],
            [10, 26, 10, 26][(IMM8 as usize >> 2) & 0b11],
            [11, 11, 27, 27][(IMM8 as usize >> 2) & 0b11],
            [12, 28, 12, 28][(IMM8 as usize >> 4) & 0b11],
            [13, 13, 29, 29][(IMM8 as usize >> 4) & 0b11],
            [14, 30, 14, 30][(IMM8 as usize >> 6) & 0b11],
            [15, 15, 31, 31][(IMM8 as usize >> 6) & 0b11],
        ],
    );
    r.into()
}

/// Blends packed 8-bit integers from `a` and `b` using `mask`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_epi8)
pub fn _mm256_blendv_epi8(a: __m256i, b: __m256i, mask: __m256i) -> __m256i {
    let mask: i8x32 = simd_lt(BitVec::to_i8x32(mask), i8x32::from_fn(|_| 0));
    simd_select(mask, BitVec::to_i8x32(b), BitVec::to_i8x32(a)).into()
}

/// Broadcasts the low packed 8-bit integer from `a` to all elements of
/// the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastb_epi8)
pub fn _mm_broadcastb_epi8(a: __m128i) -> __m128i {
    let ret = simd_shuffle(BitVec::to_i8x16(a), i8x16::from_fn(|_| 0), [0_u64; 16]);
    ret.into()
}

/// Broadcasts the low packed 8-bit integer from `a` to all elements of
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastb_epi8)
pub fn _mm256_broadcastb_epi8(a: __m128i) -> __m256i {
    let ret = simd_shuffle(BitVec::to_i8x16(a), i8x16::from_fn(|_| 0), [0_u64; 32]);
    ret.into()
}

// N.B., `simd_shuffle4` with integer data types for `a` and `b` is
// often compiled to `vbroadcastss`.
/// Broadcasts the low packed 32-bit integer from `a` to all elements of
/// the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastd_epi32)

pub fn _mm_broadcastd_epi32(a: __m128i) -> __m128i {
    let ret = simd_shuffle(BitVec::to_i32x4(a), i32x4::from_fn(|_| 0), [0_u64; 4]);
    ret.into()
}

// N.B., `simd_shuffle4`` with integer data types for `a` and `b` is
// often compiled to `vbroadcastss`.
/// Broadcasts the low packed 32-bit integer from `a` to all elements of
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastd_epi32)

pub fn _mm256_broadcastd_epi32(a: __m128i) -> __m256i {
    let ret = simd_shuffle(BitVec::to_i32x4(a), i32x4::from_fn(|_| 0), [0_u64; 8]);
    ret.into()
}

/// Broadcasts the low packed 64-bit integer from `a` to all elements of
/// the 128-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastq_epi64)

// Emits `vmovddup` instead of `vpbroadcastq`
// See https://github.com/rust-lang/stdarch/issues/791

pub fn _mm_broadcastq_epi64(a: __m128i) -> __m128i {
    let ret = simd_shuffle(BitVec::to_i64x2(a), BitVec::to_i64x2(a), [0_u64; 2]);
    ret.into()
}

/// Broadcasts the low packed 64-bit integer from `a` to all elements of
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastq_epi64)

pub fn _mm256_broadcastq_epi64(a: __m128i) -> __m256i {
    let ret = simd_shuffle(BitVec::to_i64x2(a), BitVec::to_i64x2(a), [0_u64; 4]);
    ret.into()
}

/// Broadcasts 128 bits of integer data from a to all 128-bit lanes in
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastsi128_si256)

pub fn _mm_broadcastsi128_si256(a: __m128i) -> __m256i {
    let ret = simd_shuffle(BitVec::to_i64x2(a), i64x2::from_fn(|_| 0), [0, 1, 0, 1]);
    ret.into()
}

// N.B., `broadcastsi128_si256` is often compiled to `vinsertf128` or
// `vbroadcastf128`.
/// Broadcasts 128 bits of integer data from a to all 128-bit lanes in
/// the 256-bit returned value.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastsi128_si256)

pub fn _mm256_broadcastsi128_si256(a: __m128i) -> __m256i {
    let ret = simd_shuffle(BitVec::to_i64x2(a), i64x2::from_fn(|_| 0), [0, 1, 0, 1]);
    ret.into()
}

/// Broadcasts the low packed 16-bit integer from a to all elements of
/// the 128-bit returned value
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastw_epi16)

pub fn _mm_broadcastw_epi16(a: __m128i) -> __m128i {
    let ret = simd_shuffle(BitVec::to_i16x8(a), i16x8::from_fn(|_| 0), [0_u64; 8]);
    ret.into()
}

/// Broadcasts the low packed 16-bit integer from a to all elements of
/// the 256-bit returned value
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastw_epi16)

pub fn _mm256_broadcastw_epi16(a: __m128i) -> __m256i {
    let ret = simd_shuffle(BitVec::to_i16x8(a), i16x8::from_fn(|_| 0), [0_u64; 16]);
    ret.into()
}

/// Compares packed 64-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi64)

pub fn _mm256_cmpeq_epi64(a: __m256i, b: __m256i) -> __m256i {
    simd_eq(BitVec::to_i64x4(a), BitVec::to_i64x4(b)).into()
}

/// Compares packed 32-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi32)

pub fn _mm256_cmpeq_epi32(a: __m256i, b: __m256i) -> __m256i {
    simd_eq(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Compares packed 16-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi16)

pub fn _mm256_cmpeq_epi16(a: __m256i, b: __m256i) -> __m256i {
    simd_eq(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Compares packed 8-bit integers in `a` and `b` for equality.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi8)

pub fn _mm256_cmpeq_epi8(a: __m256i, b: __m256i) -> __m256i {
    simd_eq(BitVec::to_i8x32(a), BitVec::to_i8x32(b)).into()
}

/// Compares packed 64-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi64)

pub fn _mm256_cmpgt_epi64(a: __m256i, b: __m256i) -> __m256i {
    simd_gt(BitVec::to_i64x4(a), BitVec::to_i64x4(b)).into()
}

/// Compares packed 32-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi32)

pub fn _mm256_cmpgt_epi32(a: __m256i, b: __m256i) -> __m256i {
    simd_gt(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Compares packed 16-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi16)

pub fn _mm256_cmpgt_epi16(a: __m256i, b: __m256i) -> __m256i {
    simd_gt(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Compares packed 8-bit integers in `a` and `b` for greater-than.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi8)

pub fn _mm256_cmpgt_epi8(a: __m256i, b: __m256i) -> __m256i {
    simd_gt(BitVec::to_i8x32(a), BitVec::to_i8x32(b)).into()
}

/// Sign-extend 16-bit integers to 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi32)

pub fn _mm256_cvtepi16_epi32(a: __m128i) -> __m256i {
    simd_cast::<8, _, i32>(BitVec::to_i16x8(a)).into()
}

/// Sign-extend 16-bit integers to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi64)

pub fn _mm256_cvtepi16_epi64(a: __m128i) -> __m256i {
    let a = BitVec::to_i16x8(a);
    let v64: i16x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
    simd_cast::<4, i16, i64>(v64).into()
}

/// Sign-extend 32-bit integers to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi32_epi64)

pub fn _mm256_cvtepi32_epi64(a: __m128i) -> __m256i {
    simd_cast::<4, i32, i64>(BitVec::to_i32x4(a)).into()
}

/// Sign-extend 8-bit integers to 16-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi16)

pub fn _mm256_cvtepi8_epi16(a: __m128i) -> __m256i {
    simd_cast::<16, i8, i16>(BitVec::to_i8x16(a)).into()
}

/// Sign-extend 8-bit integers to 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi32)

pub fn _mm256_cvtepi8_epi32(a: __m128i) -> __m256i {
    let a = BitVec::to_i8x16(a);
    let v64: i8x8 = simd_shuffle(a, a, [0, 1, 2, 3, 4, 5, 6, 7]);
    simd_cast::<8, i8, i32>(v64).into()
}

/// Sign-extend 8-bit integers to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi64)
pub fn _mm256_cvtepi8_epi64(a: __m128i) -> __m256i {
    let a = BitVec::to_i8x16(a);
    let v32: i8x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
    simd_cast::<4, i8, i64>(v32).into()
}

/// Zeroes extend packed unsigned 16-bit integers in `a` to packed 32-bit
/// integers, and stores the results in `dst`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu16_epi32)

pub fn _mm256_cvtepu16_epi32(a: __m128i) -> __m256i {
    simd_cast::<8, u16, u32>(BitVec::to_u16x8(a)).into()
}

/// Zero-extend the lower four unsigned 16-bit integers in `a` to 64-bit
/// integers. The upper four elements of `a` are unused.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu16_epi64)

pub fn _mm256_cvtepu16_epi64(a: __m128i) -> __m256i {
    let a = BitVec::to_u16x8(a);
    let v64: u16x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
    simd_cast::<4, u16, u64>(v64).into()
}

/// Zero-extend unsigned 32-bit integers in `a` to 64-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu32_epi64)

pub fn _mm256_cvtepu32_epi64(a: __m128i) -> __m256i {
    simd_cast::<4, u32, u64>(BitVec::to_u32x4(a)).into()
}

/// Zero-extend unsigned 8-bit integers in `a` to 16-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi16)

pub fn _mm256_cvtepu8_epi16(a: __m128i) -> __m256i {
    simd_cast::<16, u8, u16>(BitVec::to_u8x16(a)).into()
}

/// Zero-extend the lower eight unsigned 8-bit integers in `a` to 32-bit
/// integers. The upper eight elements of `a` are unused.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi32)

pub fn _mm256_cvtepu8_epi32(a: __m128i) -> __m256i {
    let a = BitVec::to_u8x16(a);
    let v64: u8x8 = simd_shuffle(a, a, [0, 1, 2, 3, 4, 5, 6, 7]);
    simd_cast::<8, u8, u32>(v64).into()
}

/// Zero-extend the lower four unsigned 8-bit integers in `a` to 64-bit
/// integers. The upper twelve elements of `a` are unused.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi64)

pub fn _mm256_cvtepu8_epi64(a: __m128i) -> __m256i {
    let a = BitVec::to_u8x16(a);
    let v32: u8x4 = simd_shuffle(a, a, [0, 1, 2, 3]);
    simd_cast::<4, u8, u64>(v32).into()
}

/// Extracts 128 bits (of integer data) from `a` selected with `IMM1`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extracti128_si256)

pub fn _mm256_extracti128_si256<const IMM1: i32>(a: __m256i) -> __m128i {
    let a = BitVec::to_i64x4(a);
    let b = i64x4::from_fn(|_| 0);
    let dst: i64x2 = simd_shuffle(a, b, [[0, 1], [2, 3]][IMM1 as usize]);
    dst.into()
}

/// Horizontally adds adjacent pairs of 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadd_epi16)

pub fn _mm256_hadd_epi16(a: __m256i, b: __m256i) -> __m256i {
    phaddw(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Horizontally adds adjacent pairs of 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadd_epi32)

pub fn _mm256_hadd_epi32(a: __m256i, b: __m256i) -> __m256i {
    phaddd(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Horizontally adds adjacent pairs of 16-bit integers in `a` and `b`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadds_epi16)

pub fn _mm256_hadds_epi16(a: __m256i, b: __m256i) -> __m256i {
    phaddsw(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Horizontally subtract adjacent pairs of 16-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsub_epi16)

pub fn _mm256_hsub_epi16(a: __m256i, b: __m256i) -> __m256i {
    phsubw(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Horizontally subtract adjacent pairs of 32-bit integers in `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsub_epi32)

pub fn _mm256_hsub_epi32(a: __m256i, b: __m256i) -> __m256i {
    phsubd(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Horizontally subtract adjacent pairs of 16-bit integers in `a` and `b`
/// using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsubs_epi16)

pub fn _mm256_hsubs_epi16(a: __m256i, b: __m256i) -> __m256i {
    phsubsw(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Copies `a` to `dst`, then insert 128 bits (of integer data) from `b` at the
/// location specified by `IMM1`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_inserti128_si256)

pub fn _mm256_inserti128_si256<const IMM1: i32>(a: __m256i, b: __m128i) -> __m256i {
    let a = BitVec::to_i64x4(a);
    let b = BitVec::to_i64x4(_mm256_castsi128_si256(b));
    let dst: i64x4 = simd_shuffle(a, b, [[4, 5, 2, 3], [0, 1, 4, 5]][IMM1 as usize]);
    dst.into()
}

/// Multiplies packed signed 16-bit integers in `a` and `b`, producing
/// intermediate signed 32-bit integers. Horizontally add adjacent pairs
/// of intermediate 32-bit integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_madd_epi16)

pub fn _mm256_madd_epi16(a: __m256i, b: __m256i) -> __m256i {
    pmaddwd(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Vertically multiplies each unsigned 8-bit integer from `a` with the
/// corresponding signed 8-bit integer from `b`, producing intermediate
/// signed 16-bit integers. Horizontally add adjacent pairs of intermediate
/// signed 16-bit integers
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_maddubs_epi16)

pub fn _mm256_maddubs_epi16(a: __m256i, b: __m256i) -> __m256i {
    pmaddubsw(BitVec::to_u8x32(a), BitVec::to_u8x32(b)).into()
}

/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi16)

pub fn _mm256_max_epi16(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let b = BitVec::to_i16x16(b);
    simd_select::<16, i16, _>(simd_gt(a, b), a, b).into()
}

/// Compares packed 32-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi32)

pub fn _mm256_max_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);
    simd_select::<8, i32, _>(simd_gt(a, b), a, b).into()
}

/// Compares packed 8-bit integers in `a` and `b`, and returns the packed
/// maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi8)

pub fn _mm256_max_epi8(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i8x32(a);
    let b = BitVec::to_i8x32(b);
    simd_select::<32, i8, _>(simd_gt(a, b), a, b).into()
}

/// Compares packed unsigned 16-bit integers in `a` and `b`, and returns
/// the packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu16)

pub fn _mm256_max_epu16(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u16x16(a);
    let b = BitVec::to_u16x16(b);
    simd_select::<16, _, u16>(simd_gt(a, b), a, b).into()
}

/// Compares packed unsigned 32-bit integers in `a` and `b`, and returns
/// the packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu32)

pub fn _mm256_max_epu32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u32x8(a);
    let b = BitVec::to_u32x8(b);
    simd_select::<8, _, u32>(simd_gt(a, b), a, b).into()
}

/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns
/// the packed maximum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu8)

pub fn _mm256_max_epu8(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u8x32(a);
    let b = BitVec::to_u8x32(b);
    simd_select::<32, _, u8>(simd_gt(a, b), a, b).into()
}

/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi16)

pub fn _mm256_min_epi16(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let b = BitVec::to_i16x16(b);
    simd_select::<16, _, i16>(simd_lt(a, b), a, b).into()
}

/// Compares packed 32-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi32)

pub fn _mm256_min_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i32x8(a);
    let b = BitVec::to_i32x8(b);
    simd_select::<8, i32, _>(simd_lt(a, b), a, b).into()
}

/// Compares packed 8-bit integers in `a` and `b`, and returns the packed
/// minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi8)

pub fn _mm256_min_epi8(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_i8x32(a);
    let b = BitVec::to_i8x32(b);
    simd_select::<32, i8, _>(simd_lt(a, b), a, b).into()
}

/// Compares packed unsigned 16-bit integers in `a` and `b`, and returns
/// the packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu16)

pub fn _mm256_min_epu16(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u16x16(a);
    let b = BitVec::to_u16x16(b);
    simd_select::<16, _, u16>(simd_lt(a, b), a, b).into()
}

/// Compares packed unsigned 32-bit integers in `a` and `b`, and returns
/// the packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu32)

pub fn _mm256_min_epu32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u32x8(a);
    let b = BitVec::to_u32x8(b);
    simd_select::<8, _, u32>(simd_lt(a, b), a, b).into()
}

/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns
/// the packed minimum values.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu8)

pub fn _mm256_min_epu8(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u8x32(a);
    let b = BitVec::to_u8x32(b);
    simd_select::<32, _, u8>(simd_lt(a, b), a, b).into()
}

/// Creates mask from the most significant bit of each 8-bit element in `a`,
/// return the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_epi8)

pub fn _mm256_movemask_epi8(a: __m256i) -> i32 {
    let z = i8x32::from_fn(|_| 0);
    let m: i8x32 = simd_lt(BitVec::to_i8x32(a), z);
    let r = simd_bitmask_little!(31, m, u32);
    r as i32
}

/// Computes the sum of absolute differences (SADs) of quadruplets of unsigned
/// 8-bit integers in `a` compared to those in `b`, and stores the 16-bit
/// results in dst. Eight SADs are performed for each 128-bit lane using one
/// quadruplet from `b` and eight quadruplets from `a`. One quadruplet is
/// selected from `b` starting at on the offset specified in `imm8`. Eight
/// quadruplets are formed from sequential 8-bit integers selected from `a`
/// starting at the offset specified in `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mpsadbw_epu8)

pub fn _mm256_mpsadbw_epu8<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    mpsadbw(BitVec::to_u8x32(a), BitVec::to_u8x32(b), IMM8).into()
}

/// Multiplies the low 32-bit integers from each packed 64-bit element in
/// `a` and `b`
///
/// Returns the 64-bit results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epi32)

pub fn _mm256_mul_epi32(a: __m256i, b: __m256i) -> __m256i {
    let a = simd_cast::<4, _, i64>(simd_cast::<4, _, i32>(BitVec::to_i64x4(a)));
    let b = simd_cast::<4, _, i64>(simd_cast::<4, _, i32>(BitVec::to_i64x4(b)));
    simd_mul(a, b).into()
}

/// Multiplies the low unsigned 32-bit integers from each packed 64-bit
/// element in `a` and `b`
///
/// Returns the unsigned 64-bit results.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epu32)

pub fn _mm256_mul_epu32(a: __m256i, b: __m256i) -> __m256i {
    let a = BitVec::to_u64x4(a);
    let b = BitVec::to_u64x4(b);
    let mask = u64x4::splat(u32::MAX.into());
    BitVec::from_u64x4(simd_mul(simd_and(a, mask), simd_and(b, mask)))
}

/// Multiplies the packed 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers and returning the high 16 bits of the
/// intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epi16)

pub fn _mm256_mulhi_epi16(a: __m256i, b: __m256i) -> __m256i {
    let a = simd_cast::<16, _, i32>(BitVec::to_i16x16(a));
    let b = simd_cast::<16, _, i32>(BitVec::to_i16x16(b));
    let r = simd_shr(simd_mul(a, b), i32x16::splat(16));
    simd_cast::<16, i32, i16>(r).into()
}

/// Multiplies the packed unsigned 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers and returning the high 16 bits of the
/// intermediate integers.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epu16)

pub fn _mm256_mulhi_epu16(a: __m256i, b: __m256i) -> __m256i {
    let a = simd_cast::<16, _, u32>(BitVec::to_u16x16(a));
    let b = simd_cast::<16, _, u32>(BitVec::to_u16x16(b));
    let r = simd_shr(simd_mul(a, b), u32x16::splat(16));
    simd_cast::<16, u32, u16>(r).into()
}

/// Multiplies the packed 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers, and returns the low 16 bits of the
/// intermediate integers
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi16)

pub fn _mm256_mullo_epi16(a: __m256i, b: __m256i) -> __m256i {
    simd_mul(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Multiplies the packed 32-bit integers in `a` and `b`, producing
/// intermediate 64-bit integers, and returns the low 32 bits of the
/// intermediate integers
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi32)

pub fn _mm256_mullo_epi32(a: __m256i, b: __m256i) -> __m256i {
    simd_mul(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Multiplies packed 16-bit integers in `a` and `b`, producing
/// intermediate signed 32-bit integers. Truncate each intermediate
/// integer to the 18 most significant bits, round by adding 1, and
/// return bits `[16:1]`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhrs_epi16)

pub fn _mm256_mulhrs_epi16(a: __m256i, b: __m256i) -> __m256i {
    pmulhrsw(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Computes the bitwise OR of 256 bits (representing integer data) in `a`
/// and `b`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_or_si256)

pub fn _mm256_or_si256(a: __m256i, b: __m256i) -> __m256i {
    simd_or(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using signed saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi16)

pub fn _mm256_packs_epi16(a: __m256i, b: __m256i) -> __m256i {
    packsswb(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using signed saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi32)

pub fn _mm256_packs_epi32(a: __m256i, b: __m256i) -> __m256i {
    packssdw(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using unsigned saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packus_epi16)

pub fn _mm256_packus_epi16(a: __m256i, b: __m256i) -> __m256i {
    packuswb(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using unsigned saturation
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packus_epi32)

pub fn _mm256_packus_epi32(a: __m256i, b: __m256i) -> __m256i {
    packusdw(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Permutes packed 32-bit integers from `a` according to the content of `b`.
///
/// The last 3 bits of each integer of `b` are used as addresses into the 8
/// integers of `a`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permutevar8x32_epi32)

pub fn _mm256_permutevar8x32_epi32(a: __m256i, b: __m256i) -> __m256i {
    permd(BitVec::to_u32x8(a), BitVec::to_u32x8(b)).into()
}

/// Permutes 64-bit integers from `a` using control mask `imm8`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute4x64_epi64)

pub fn _mm256_permute4x64_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    let zero = i64x4::from_fn(|_| 0);
    let r: i64x4 = simd_shuffle(
        BitVec::to_i64x4(a),
        zero,
        [
            IMM8 as u64 & 0b11,
            (IMM8 as u64 >> 2) & 0b11,
            (IMM8 as u64 >> 4) & 0b11,
            (IMM8 as u64 >> 6) & 0b11,
        ],
    );
    r.into()
}

/// Shuffles 128-bits of integer data selected by `imm8` from `a` and `b`.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute2x128_si256)

pub fn _mm256_permute2x128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    vperm2i128(BitVec::to_i64x4(a), BitVec::to_i64x4(b), IMM8 as i8).into()
}

/// Computes the absolute differences of packed unsigned 8-bit integers in `a`
/// and `b`, then horizontally sum each consecutive 8 differences to
/// produce four unsigned 16-bit integers, and pack these unsigned 16-bit
/// integers in the low 16 bits of the 64-bit return value
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sad_epu8)

pub fn _mm256_sad_epu8(a: __m256i, b: __m256i) -> __m256i {
    psadbw(BitVec::to_u8x32(a), BitVec::to_u8x32(b)).into()
}

/// Shuffles bytes from `a` according to the content of `b`.
///
/// For each of the 128-bit low and high halves of the vectors, the last
/// 4 bits of each byte of `b` are used as addresses into the respective
/// low or high 16 bytes of `a`. That is, the halves are shuffled separately.
///
/// In addition, if the highest significant bit of a byte of `b` is set, the
/// respective destination byte is set to 0.
///
/// Picturing `a` and `b` as `[u8; 32]`, `_mm256_shuffle_epi8` is logically
/// equivalent to:
///
/// ```
/// fn mm256_shuffle_epi8(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
///     let mut r = [0; 32];
///     for i in 0..16 {
///         if b[i] & 0x80 == 0u8 {
///             r[i] = a[(b[i] % 16) as usize];
///         }
///         if b[i + 16] & 0x80 == 0u8 {
///             r[i + 16] = a[(b[i + 16] % 16 + 16) as usize];
///         }
///     }
///     r
/// }
/// ```
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi8)

pub fn _mm256_shuffle_epi8(a: __m256i, b: __m256i) -> __m256i {
    pshufb(BitVec::to_u8x32(a), BitVec::to_u8x32(b)).into()
}

/// Shuffles 32-bit integers in 128-bit lanes of `a` using the control in
/// `imm8`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi32)

pub fn _mm256_shuffle_epi32<const MASK: i32>(a: __m256i) -> __m256i {
    let r: i32x8 = simd_shuffle(
        BitVec::to_i32x8(a),
        BitVec::to_i32x8(a),
        [
            MASK as u64 & 0b11,
            (MASK as u64 >> 2) & 0b11,
            (MASK as u64 >> 4) & 0b11,
            (MASK as u64 >> 6) & 0b11,
            (MASK as u64 & 0b11) + 4,
            ((MASK as u64 >> 2) & 0b11) + 4,
            ((MASK as u64 >> 4) & 0b11) + 4,
            ((MASK as u64 >> 6) & 0b11) + 4,
        ],
    );
    r.into()
}

/// Shuffles 16-bit integers in the high 64 bits of 128-bit lanes of `a` using
/// the control in `imm8`. The low 64 bits of 128-bit lanes of `a` are copied
/// to the output.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shufflehi_epi16)

pub fn _mm256_shufflehi_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let r: i16x16 = simd_shuffle(
        a,
        a,
        [
            0,
            1,
            2,
            3,
            4 + (IMM8 as u64 & 0b11),
            4 + ((IMM8 as u64 >> 2) & 0b11),
            4 + ((IMM8 as u64 >> 4) & 0b11),
            4 + ((IMM8 as u64 >> 6) & 0b11),
            8,
            9,
            10,
            11,
            12 + (IMM8 as u64 & 0b11),
            12 + ((IMM8 as u64 >> 2) & 0b11),
            12 + ((IMM8 as u64 >> 4) & 0b11),
            12 + ((IMM8 as u64 >> 6) & 0b11),
        ],
    );
    r.into()
}

/// Shuffles 16-bit integers in the low 64 bits of 128-bit lanes of `a` using
/// the control in `imm8`. The high 64 bits of 128-bit lanes of `a` are copied
/// to the output.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shufflelo_epi16)

pub fn _mm256_shufflelo_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    let a = BitVec::to_i16x16(a);
    let r: i16x16 = simd_shuffle(
        a,
        a,
        [
            0 + (IMM8 as u64 & 0b11),
            0 + ((IMM8 as u64 >> 2) & 0b11),
            0 + ((IMM8 as u64 >> 4) & 0b11),
            0 + ((IMM8 as u64 >> 6) & 0b11),
            4,
            5,
            6,
            7,
            8 + (IMM8 as u64 & 0b11),
            8 + ((IMM8 as u64 >> 2) & 0b11),
            8 + ((IMM8 as u64 >> 4) & 0b11),
            8 + ((IMM8 as u64 >> 6) & 0b11),
            12,
            13,
            14,
            15,
        ],
    );
    r.into()
}

/// Negates packed 16-bit integers in `a` when the corresponding signed
/// 16-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi16)

pub fn _mm256_sign_epi16(a: __m256i, b: __m256i) -> __m256i {
    psignw(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Negates packed 32-bit integers in `a` when the corresponding signed
/// 32-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi32)

pub fn _mm256_sign_epi32(a: __m256i, b: __m256i) -> __m256i {
    psignd(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Negates packed 8-bit integers in `a` when the corresponding signed
/// 8-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi8)

pub fn _mm256_sign_epi8(a: __m256i, b: __m256i) -> __m256i {
    psignb(BitVec::to_i8x32(a), BitVec::to_i8x32(b)).into()
}

/// Shifts packed 16-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi16)

pub fn _mm256_sll_epi16(a: __m256i, count: __m128i) -> __m256i {
    psllw(BitVec::to_i16x16(a), BitVec::to_i16x8(count)).into()
}

/// Shifts packed 32-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi32)

pub fn _mm256_sll_epi32(a: __m256i, count: __m128i) -> __m256i {
    pslld(BitVec::to_i32x8(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 64-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi64)

pub fn _mm256_sll_epi64(a: __m256i, count: __m128i) -> __m256i {
    psllq(BitVec::to_i64x4(a), BitVec::to_i64x2(count)).into()
}

/// Shifts packed 16-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi16)

pub fn _mm256_slli_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    if IMM8 >= 16 {
        _mm256_setzero_si256()
    } else {
        simd_shl(BitVec::to_u16x16(a), u16x16::splat(IMM8 as u16)).into()
    }
}

/// Shifts packed 32-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi32)

pub fn _mm256_slli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    if IMM8 >= 32 {
        _mm256_setzero_si256()
    } else {
        simd_shl(BitVec::to_u32x8(a), u32x8::splat(IMM8 as u32)).into()
    }
}

/// Shifts packed 64-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi64)

pub fn _mm256_slli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    if IMM8 >= 64 {
        _mm256_setzero_si256()
    } else {
        simd_shl(BitVec::to_u64x4(a), u64x4::splat(IMM8 as u64)).into()
    }
}

/// Shifts 128-bit lanes in `a` left by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_si256)

pub fn _mm256_slli_si256<const IMM8: i32>(a: __m256i) -> __m256i {
    _mm256_bslli_epi128::<IMM8>(a)
}

/// Shifts 128-bit lanes in `a` left by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bslli_epi128)

pub fn _mm256_bslli_epi128<const IMM8: i32>(a: __m256i) -> __m256i {
    const fn mask(shift: i32, i: u32) -> u32 {
        let shift = shift as u32 & 0xff;
        if shift > 15 || i % 16 < shift {
            0
        } else {
            32 + (i - shift)
        }
    }
    let a = BitVec::to_i8x32(a);
    let r: i8x32 = simd_shuffle(
        i8x32::from_fn(|_| 0),
        a,
        [
            mask(IMM8, 0) as u64,
            mask(IMM8, 1) as u64,
            mask(IMM8, 2) as u64,
            mask(IMM8, 3) as u64,
            mask(IMM8, 4) as u64,
            mask(IMM8, 5) as u64,
            mask(IMM8, 6) as u64,
            mask(IMM8, 7) as u64,
            mask(IMM8, 8) as u64,
            mask(IMM8, 9) as u64,
            mask(IMM8, 10) as u64,
            mask(IMM8, 11) as u64,
            mask(IMM8, 12) as u64,
            mask(IMM8, 13) as u64,
            mask(IMM8, 14) as u64,
            mask(IMM8, 15) as u64,
            mask(IMM8, 16) as u64,
            mask(IMM8, 17) as u64,
            mask(IMM8, 18) as u64,
            mask(IMM8, 19) as u64,
            mask(IMM8, 20) as u64,
            mask(IMM8, 21) as u64,
            mask(IMM8, 22) as u64,
            mask(IMM8, 23) as u64,
            mask(IMM8, 24) as u64,
            mask(IMM8, 25) as u64,
            mask(IMM8, 26) as u64,
            mask(IMM8, 27) as u64,
            mask(IMM8, 28) as u64,
            mask(IMM8, 29) as u64,
            mask(IMM8, 30) as u64,
            mask(IMM8, 31) as u64,
        ],
    );
    r.into()
}

/// Shifts packed 32-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi32)

pub fn _mm_sllv_epi32(a: __m128i, count: __m128i) -> __m128i {
    psllvd(BitVec::to_i32x4(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 32-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi32)

pub fn _mm256_sllv_epi32(a: __m256i, count: __m256i) -> __m256i {
    psllvd256(BitVec::to_i32x8(a), BitVec::to_i32x8(count)).into()
}

/// Shifts packed 64-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi64)

pub fn _mm_sllv_epi64(a: __m128i, count: __m128i) -> __m128i {
    psllvq(BitVec::to_i64x2(a), BitVec::to_i64x2(count)).into()
}

/// Shifts packed 64-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi64)

pub fn _mm256_sllv_epi64(a: __m256i, count: __m256i) -> __m256i {
    psllvq256(BitVec::to_i64x4(a), BitVec::to_i64x4(count)).into()
}

/// Shifts packed 16-bit integers in `a` right by `count` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sra_epi16)

pub fn _mm256_sra_epi16(a: __m256i, count: __m128i) -> __m256i {
    psraw(BitVec::to_i16x16(a), BitVec::to_i16x8(count)).into()
}

/// Shifts packed 32-bit integers in `a` right by `count` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sra_epi32)

pub fn _mm256_sra_epi32(a: __m256i, count: __m128i) -> __m256i {
    psrad(BitVec::to_i32x8(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 16-bit integers in `a` right by `IMM8` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi16)

pub fn _mm256_srai_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    simd_shr(BitVec::to_i16x16(a), i16x16::splat(IMM8.min(15) as i16)).into()
}

/// Shifts packed 32-bit integers in `a` right by `IMM8` while
/// shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi32)

pub fn _mm256_srai_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    simd_shr(BitVec::to_i32x8(a), i32x8::splat(IMM8.min(31))).into()
}

/// Shifts packed 32-bit integers in `a` right by the amount specified by the
/// corresponding element in `count` while shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srav_epi32)

pub fn _mm_srav_epi32(a: __m128i, count: __m128i) -> __m128i {
    psravd(BitVec::to_i32x4(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 32-bit integers in `a` right by the amount specified by the
/// corresponding element in `count` while shifting in sign bits.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srav_epi32)

pub fn _mm256_srav_epi32(a: __m256i, count: __m256i) -> __m256i {
    psravd256(BitVec::to_i32x8(a), BitVec::to_i32x8(count)).into()
}

/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_si256)

pub fn _mm256_srli_si256<const IMM8: i32>(a: __m256i) -> __m256i {
    _mm256_bsrli_epi128::<IMM8>(a)
}

/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)

pub fn _mm256_bsrli_epi128<const IMM8: i32>(a: __m256i) -> __m256i {
    const fn mask(shift: i32, i: u32) -> u64 {
        let shift = shift as u32 & 0xff;
        if shift > 15 || (15 - (i % 16)) < shift {
            0 as u64
        } else {
            (32 + (i + shift)) as u64
        }
    }

    let a = BitVec::to_i8x32(a);
    let r: i8x32 = simd_shuffle(
        i8x32::from_fn(|_| 0),
        a,
        [
            mask(IMM8, 0),
            mask(IMM8, 1),
            mask(IMM8, 2),
            mask(IMM8, 3),
            mask(IMM8, 4),
            mask(IMM8, 5),
            mask(IMM8, 6),
            mask(IMM8, 7),
            mask(IMM8, 8),
            mask(IMM8, 9),
            mask(IMM8, 10),
            mask(IMM8, 11),
            mask(IMM8, 12),
            mask(IMM8, 13),
            mask(IMM8, 14),
            mask(IMM8, 15),
            mask(IMM8, 16),
            mask(IMM8, 17),
            mask(IMM8, 18),
            mask(IMM8, 19),
            mask(IMM8, 20),
            mask(IMM8, 21),
            mask(IMM8, 22),
            mask(IMM8, 23),
            mask(IMM8, 24),
            mask(IMM8, 25),
            mask(IMM8, 26),
            mask(IMM8, 27),
            mask(IMM8, 28),
            mask(IMM8, 29),
            mask(IMM8, 30),
            mask(IMM8, 31),
        ],
    );

    r.into()
}

/// Shifts packed 16-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi16)

pub fn _mm256_srl_epi16(a: __m256i, count: __m128i) -> __m256i {
    psrlw(BitVec::to_i16x16(a), BitVec::to_i16x8(count)).into()
}

/// Shifts packed 32-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi32)

pub fn _mm256_srl_epi32(a: __m256i, count: __m128i) -> __m256i {
    psrld(BitVec::to_i32x8(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 64-bit integers in `a` right by `count` while shifting in
/// zeros.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi64)

pub fn _mm256_srl_epi64(a: __m256i, count: __m128i) -> __m256i {
    psrlq(BitVec::to_i64x4(a), BitVec::to_i64x2(count)).into()
}

/// Shifts packed 16-bit integers in `a` right by `IMM8` while shifting in
/// zeros
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi16)

pub fn _mm256_srli_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    if IMM8 >= 16 {
        _mm256_setzero_si256()
    } else {
        simd_shr(BitVec::to_u16x16(a), u16x16::splat(IMM8 as u16)).into()
    }
}

/// Shifts packed 32-bit integers in `a` right by `IMM8` while shifting in
/// zeros
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi32)

pub fn _mm256_srli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    if IMM8 >= 32 {
        _mm256_setzero_si256()
    } else {
        simd_shr(BitVec::to_u32x8(a), u32x8::splat(IMM8 as u32)).into()
    }
}

/// Shifts packed 64-bit integers in `a` right by `IMM8` while shifting in
/// zeros
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi64)

pub fn _mm256_srli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    if IMM8 >= 64 {
        _mm256_setzero_si256()
    } else {
        simd_shr(BitVec::to_u64x4(a), u64x4::splat(IMM8 as u64)).into()
    }
}

/// Shifts packed 32-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srlv_epi32)

pub fn _mm_srlv_epi32(a: __m128i, count: __m128i) -> __m128i {
    psrlvd(BitVec::to_i32x4(a), BitVec::to_i32x4(count)).into()
}

/// Shifts packed 32-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi32)

pub fn _mm256_srlv_epi32(a: __m256i, count: __m256i) -> __m256i {
    psrlvd256(BitVec::to_i32x8(a), BitVec::to_i32x8(count)).into()
}

/// Shifts packed 64-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srlv_epi64)

pub fn _mm_srlv_epi64(a: __m128i, count: __m128i) -> __m128i {
    psrlvq(BitVec::to_i64x2(a), BitVec::to_i64x2(count)).into()
}

/// Shifts packed 64-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi64)

pub fn _mm256_srlv_epi64(a: __m256i, count: __m256i) -> __m256i {
    psrlvq256(BitVec::to_i64x4(a), BitVec::to_i64x4(count)).into()
}

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi16)

pub fn _mm256_sub_epi16(a: __m256i, b: __m256i) -> __m256i {
    simd_sub(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Subtract packed 32-bit integers in `b` from packed 32-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi32)

pub fn _mm256_sub_epi32(a: __m256i, b: __m256i) -> __m256i {
    simd_sub(BitVec::to_i32x8(a), BitVec::to_i32x8(b)).into()
}

/// Subtract packed 64-bit integers in `b` from packed 64-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi64)

pub fn _mm256_sub_epi64(a: __m256i, b: __m256i) -> __m256i {
    simd_sub(BitVec::to_i64x4(a), BitVec::to_i64x4(b)).into()
}

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi8)

pub fn _mm256_sub_epi8(a: __m256i, b: __m256i) -> __m256i {
    simd_sub(BitVec::to_i8x32(a), BitVec::to_i8x32(b)).into()
}

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in
/// `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epi16)

pub fn _mm256_subs_epi16(a: __m256i, b: __m256i) -> __m256i {
    simd_saturating_sub(BitVec::to_i16x16(a), BitVec::to_i16x16(b)).into()
}

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in
/// `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epi8)

pub fn _mm256_subs_epi8(a: __m256i, b: __m256i) -> __m256i {
    simd_saturating_sub(BitVec::to_i8x32(a), BitVec::to_i8x32(b)).into()
}

/// Subtract packed unsigned 16-bit integers in `b` from packed 16-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epu16)

pub fn _mm256_subs_epu16(a: __m256i, b: __m256i) -> __m256i {
    simd_saturating_sub(BitVec::to_u16x16(a), BitVec::to_u16x16(b)).into()
}

/// Subtract packed unsigned 8-bit integers in `b` from packed 8-bit
/// integers in `a` using saturation.
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epu8)

pub fn _mm256_subs_epu8(a: __m256i, b: __m256i) -> __m256i {
    simd_saturating_sub(BitVec::to_u8x32(a), BitVec::to_u8x32(b)).into()
}

/// Unpacks and interleave 8-bit integers from the high half of each
/// 128-bit lane in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi8)

pub fn _mm256_unpackhi_epi8(a: __m256i, b: __m256i) -> __m256i {
    #[rustfmt::skip]
    let r: i8x32 = simd_shuffle(BitVec::to_i8x32(a), BitVec::to_i8x32(b), [
            8, 40, 9, 41, 10, 42, 11, 43,
            12, 44, 13, 45, 14, 46, 15, 47,
            24, 56, 25, 57, 26, 58, 27, 59,
            28, 60, 29, 61, 30, 62, 31, 63,
    ]);
    r.into()
}

/// Unpacks and interleave 8-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi8)

pub fn _mm256_unpacklo_epi8(a: __m256i, b: __m256i) -> __m256i {
    #[rustfmt::skip]
    let r: i8x32 = simd_shuffle(BitVec::to_i8x32(a), BitVec::to_i8x32(b), [
        0, 32, 1, 33, 2, 34, 3, 35,
        4, 36, 5, 37, 6, 38, 7, 39,
        16, 48, 17, 49, 18, 50, 19, 51,
        20, 52, 21, 53, 22, 54, 23, 55,
    ]);
    r.into()
}

/// Unpacks and interleave 16-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi16)

pub fn _mm256_unpackhi_epi16(a: __m256i, b: __m256i) -> __m256i {
    let r: i16x16 = simd_shuffle(
        BitVec::to_i16x16(a),
        BitVec::to_i16x16(b),
        [4, 20, 5, 21, 6, 22, 7, 23, 12, 28, 13, 29, 14, 30, 15, 31],
    );
    r.into()
}

/// Unpacks and interleave 16-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi16)

pub fn _mm256_unpacklo_epi16(a: __m256i, b: __m256i) -> __m256i {
    let r: i16x16 = simd_shuffle(
        BitVec::to_i16x16(a),
        BitVec::to_i16x16(b),
        [0, 16, 1, 17, 2, 18, 3, 19, 8, 24, 9, 25, 10, 26, 11, 27],
    );
    r.into()
}

/// Unpacks and interleave 32-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi32)

pub fn _mm256_unpackhi_epi32(a: __m256i, b: __m256i) -> __m256i {
    let r: i32x8 = simd_shuffle(
        BitVec::to_i32x8(a),
        BitVec::to_i32x8(b),
        [2, 10, 3, 11, 6, 14, 7, 15],
    );
    r.into()
}

/// Unpacks and interleave 32-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi32)

pub fn _mm256_unpacklo_epi32(a: __m256i, b: __m256i) -> __m256i {
    let r: i32x8 = simd_shuffle(
        BitVec::to_i32x8(a),
        BitVec::to_i32x8(b),
        [0, 8, 1, 9, 4, 12, 5, 13],
    );
    r.into()
}

/// Unpacks and interleave 64-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi64)

pub fn _mm256_unpackhi_epi64(a: __m256i, b: __m256i) -> __m256i {
    let r: i64x4 = simd_shuffle(BitVec::to_i64x4(a), BitVec::to_i64x4(b), [1, 5, 3, 7]);
    r.into()
}

/// Unpacks and interleave 64-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi64)

pub fn _mm256_unpacklo_epi64(a: __m256i, b: __m256i) -> __m256i {
    let r: i64x4 = simd_shuffle(BitVec::to_i64x4(a), BitVec::to_i64x4(b), [0, 4, 2, 6]);
    r.into()
}

/// Computes the bitwise XOR of 256 bits (representing integer data)
/// in `a` and `b`
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_xor_si256)

pub fn _mm256_xor_si256(a: __m256i, b: __m256i) -> __m256i {
    simd_xor(BitVec::to_i64x4(a), BitVec::to_i64x4(b)).into()
}

/// Extracts an 8-bit integer from `a`, selected with `INDEX`. Returns a 32-bit
/// integer containing the zero-extended integer data.
///
/// See [LLVM commit D20468](https://reviews.llvm.org/D20468).
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extract_epi8)

// This intrinsic has no corresponding instruction.

pub fn _mm256_extract_epi8<const INDEX: i32>(a: __m256i) -> i32 {
    simd_extract(BitVec::to_u8x32(a), INDEX as u64) as u32 as i32
}

/// Extracts a 16-bit integer from `a`, selected with `INDEX`. Returns a 32-bit
/// integer containing the zero-extended integer data.
///
/// See [LLVM commit D20468](https://reviews.llvm.org/D20468).
///
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extract_epi16)

// This intrinsic has no corresponding instruction.

pub fn _mm256_extract_epi16<const INDEX: i32>(a: __m256i) -> i32 {
    simd_extract(BitVec::to_u16x16(a), INDEX as u64) as u32 as i32
}
