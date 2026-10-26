#![feature(staged_api, cfg_target_has_reliable_f16_f128, ergonomic_clones, float_masks, f16)]
#![allow(internal_features, unexpected_cfgs, dead_code)]
#![unstable(feature = "flt2dec_runtime_test", issue = "none")]

pub use std::{clone, cmp, f64, fmt, iter, mem, ops, option, primitive, ptr, result};

#[path = "../../library/core/src/num/imp/bignum.rs"]
pub mod actual_bignum;
#[path = "../../library/core/src/num/imp/flt2dec/decoder.rs"]
pub mod actual_decoder;
#[path = "../../library/core/src/num/imp/diy_float.rs"]
pub mod actual_diy_float;
#[path = "../../library/core/src/num/imp/flt2dec/strategy/dragon.rs"]
pub mod actual_dragon;
#[path = "../../library/core/src/num/imp/flt2dec/estimator.rs"]
pub mod actual_estimator;
#[path = "../../library/core/src/num/imp/flt2dec/strategy/grisu.rs"]
pub mod actual_grisu;
#[path = "../../library/core/src/num/imp/traits.rs"]
pub mod actual_traits;
#[path = "runtime-baseline-dragon.rs"]
pub mod baseline_dragon;
#[path = "runtime-baseline-grisu.rs"]
pub mod baseline_grisu;
#[path = "runtime-common.rs"]
pub mod runtime_common;

pub mod num {
    pub use std::num::*;
    pub mod imp {
        pub use crate::actual_bignum as bignum;
        pub use crate::actual_diy_float as diy_float;
        pub use crate::actual_traits::FloatExt;
        pub mod flt2dec {
            pub use crate::actual_decoder::Decoded;
            pub use crate::actual_estimator as estimator;
            pub use crate::runtime_common::{MAX_SIG_DIGITS, round_up};
            pub mod strategy {
                pub use crate::actual_dragon as dragon;
            }
        }
    }
}

fn check_case(decoded: actual_decoder::Decoded, check_roundtrip: impl Fn(&str)) {
    [17, 32].into_iter().for_each(|len| {
        let mut expected_buf = [std::mem::MaybeUninit::uninit(); 32];
        let mut actual_buf = [std::mem::MaybeUninit::uninit(); 32];
        let expected = baseline_grisu::format_shortest_opt(&decoded, &mut expected_buf[..len])
            .map(|(digits, exponent)| (digits.to_vec(), exponent));
        let actual = actual_grisu::format_shortest_opt(&decoded, &mut actual_buf[..len])
            .map(|(digits, exponent)| (digits.to_vec(), exponent));
        assert_eq!(actual, expected, "decoded input: {decoded:?}, buffer: {len}");
        actual.iter().for_each(|(digits, exponent)| {
            assert!(!digits.is_empty() && digits.len() <= 17);
            assert!(digits.iter().all(u8::is_ascii_digit));
            let significand: String = digits.iter().map(|digit| char::from(*digit)).collect();
            check_roundtrip(&format!(
                "{significand}e{}",
                i32::from(*exponent) - digits.len() as i32
            ));
        });
    });
}

fn sample_bits(index: u64) -> u64 {
    let value = index.wrapping_add(0x9e3779b97f4a7c15);
    let value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    let value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
    value ^ (value >> 31)
}

fn check_exact(decoded: actual_decoder::FullDecoded) {
    match decoded {
        actual_decoder::FullDecoded::Finite(decoded) => {
            [0, 1, 2, 17, 32].into_iter().for_each(|len| {
                [i16::MIN, -309, -1, 0, 1, 309, i16::MAX].into_iter().for_each(|limit| {
                    let mut expected_buf = [std::mem::MaybeUninit::uninit(); 32];
                    let mut actual_buf = [std::mem::MaybeUninit::uninit(); 32];
                    let (expected, expected_exp) =
                        baseline_dragon::format_exact(&decoded, &mut expected_buf[..len], limit);
                    let (actual, actual_exp) =
                        actual_dragon::format_exact(&decoded, &mut actual_buf[..len], limit);
                    assert_eq!(
                        (actual, actual_exp),
                        (expected, expected_exp),
                        "decoded input: {decoded:?}, buffer: {len}, limit: {limit}",
                    );
                    assert!(actual.iter().all(u8::is_ascii_digit));
                });
            });
        }
        actual_decoder::FullDecoded::Nan
        | actual_decoder::FullDecoded::Infinite
        | actual_decoder::FullDecoded::Zero => (),
    }
}

#[test]
fn dragon_exact_f64_matches_base() {
    (0..2047u64)
        .flat_map(|exponent| [0, (1 << 52) - 1].map(move |mantissa| (exponent << 52) | mantissa))
        .chain((0..2000).map(sample_bits))
        .for_each(|bits| check_exact(actual_decoder::decode(f64::from_bits(bits)).1));
}

#[test]
fn dragon_exact_f32_matches_base() {
    (0..255u32)
        .flat_map(|exponent| [0, (1 << 23) - 1].map(move |mantissa| (exponent << 23) | mantissa))
        .chain((0..2000).map(sample_bits).map(|bits| bits as u32))
        .for_each(|bits| check_exact(actual_decoder::decode(f32::from_bits(bits)).1));
}

#[test]
fn shortest_f64_matches_base_and_roundtrips() {
    let boundaries = (0..2047u64).flat_map(|exponent| {
        [0, 1, 1 << 51, (1 << 52) - 1].map(move |mantissa| (exponent << 52) | mantissa)
    });
    boundaries.chain((0..20000).map(sample_bits).map(|bits| bits & i64::MAX as u64)).for_each(
        |bits| {
            let (_, decoded) = actual_decoder::decode(f64::from_bits(bits));
            match decoded {
                actual_decoder::FullDecoded::Finite(decoded) => check_case(decoded, |rendered| {
                    assert_eq!(rendered.parse::<f64>().ok().map(f64::to_bits), Some(bits));
                }),
                actual_decoder::FullDecoded::Nan
                | actual_decoder::FullDecoded::Infinite
                | actual_decoder::FullDecoded::Zero => (),
            }
        },
    );
}

#[test]
fn shortest_f32_matches_base_and_roundtrips() {
    let boundaries = (0..255u32).flat_map(|exponent| {
        [0, 1, 1 << 22, (1 << 23) - 1].map(move |mantissa| (exponent << 23) | mantissa)
    });
    boundaries
        .chain((0..20000).map(sample_bits).map(|bits| bits as u32 & i32::MAX as u32))
        .for_each(|bits| {
            let (_, decoded) = actual_decoder::decode(f32::from_bits(bits));
            match decoded {
                actual_decoder::FullDecoded::Finite(decoded) => check_case(decoded, |rendered| {
                    assert_eq!(rendered.parse::<f32>().ok().map(f32::to_bits), Some(bits));
                }),
                actual_decoder::FullDecoded::Nan
                | actual_decoder::FullDecoded::Infinite
                | actual_decoder::FullDecoded::Zero => (),
            }
        });
}
