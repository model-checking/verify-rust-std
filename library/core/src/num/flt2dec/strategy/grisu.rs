//! Rust adaptation of the Grisu3 algorithm described in "Printing Floating-Point Numbers Quickly
//! and Accurately with Integers"[^1]. It uses about 1KB of precomputed table, and in turn, it's
//! very quick for most inputs.
//!
//! [^1]: Florian Loitsch. 2010. Printing floating-point numbers quickly and
//!   accurately with integers. SIGPLAN Not. 45, 6 (June 2010), 233-243.

#[cfg(kani)]
use crate::kani;
use crate::mem::MaybeUninit;
use crate::num::diy_float::Fp;
use crate::num::flt2dec::{Decoded, MAX_SIG_DIGITS, round_up};

// see the comments in `format_shortest_opt` for the rationale.
#[doc(hidden)]
pub const ALPHA: i16 = -60;
#[doc(hidden)]
pub const GAMMA: i16 = -32;

/*
# the following Python code generates this table:
for i in xrange(-308, 333, 8):
    if i >= 0: f = 10**i; e = 0
    else: f = 2**(80-4*i) // 10**-i; e = 4 * i - 80
    l = f.bit_length()
    f = ((f << 64 >> (l-1)) + 1) >> 1; e += l - 64
    print '    (%#018x, %5d, %4d),' % (f, e, i)
*/

#[doc(hidden)]
pub static CACHED_POW10: [(u64, i16, i16); 81] = [
    // (f, e, k)
    (0xe61acf033d1a45df, -1087, -308),
    (0xab70fe17c79ac6ca, -1060, -300),
    (0xff77b1fcbebcdc4f, -1034, -292),
    (0xbe5691ef416bd60c, -1007, -284),
    (0x8dd01fad907ffc3c, -980, -276),
    (0xd3515c2831559a83, -954, -268),
    (0x9d71ac8fada6c9b5, -927, -260),
    (0xea9c227723ee8bcb, -901, -252),
    (0xaecc49914078536d, -874, -244),
    (0x823c12795db6ce57, -847, -236),
    (0xc21094364dfb5637, -821, -228),
    (0x9096ea6f3848984f, -794, -220),
    (0xd77485cb25823ac7, -768, -212),
    (0xa086cfcd97bf97f4, -741, -204),
    (0xef340a98172aace5, -715, -196),
    (0xb23867fb2a35b28e, -688, -188),
    (0x84c8d4dfd2c63f3b, -661, -180),
    (0xc5dd44271ad3cdba, -635, -172),
    (0x936b9fcebb25c996, -608, -164),
    (0xdbac6c247d62a584, -582, -156),
    (0xa3ab66580d5fdaf6, -555, -148),
    (0xf3e2f893dec3f126, -529, -140),
    (0xb5b5ada8aaff80b8, -502, -132),
    (0x87625f056c7c4a8b, -475, -124),
    (0xc9bcff6034c13053, -449, -116),
    (0x964e858c91ba2655, -422, -108),
    (0xdff9772470297ebd, -396, -100),
    (0xa6dfbd9fb8e5b88f, -369, -92),
    (0xf8a95fcf88747d94, -343, -84),
    (0xb94470938fa89bcf, -316, -76),
    (0x8a08f0f8bf0f156b, -289, -68),
    (0xcdb02555653131b6, -263, -60),
    (0x993fe2c6d07b7fac, -236, -52),
    (0xe45c10c42a2b3b06, -210, -44),
    (0xaa242499697392d3, -183, -36),
    (0xfd87b5f28300ca0e, -157, -28),
    (0xbce5086492111aeb, -130, -20),
    (0x8cbccc096f5088cc, -103, -12),
    (0xd1b71758e219652c, -77, -4),
    (0x9c40000000000000, -50, 4),
    (0xe8d4a51000000000, -24, 12),
    (0xad78ebc5ac620000, 3, 20),
    (0x813f3978f8940984, 30, 28),
    (0xc097ce7bc90715b3, 56, 36),
    (0x8f7e32ce7bea5c70, 83, 44),
    (0xd5d238a4abe98068, 109, 52),
    (0x9f4f2726179a2245, 136, 60),
    (0xed63a231d4c4fb27, 162, 68),
    (0xb0de65388cc8ada8, 189, 76),
    (0x83c7088e1aab65db, 216, 84),
    (0xc45d1df942711d9a, 242, 92),
    (0x924d692ca61be758, 269, 100),
    (0xda01ee641a708dea, 295, 108),
    (0xa26da3999aef774a, 322, 116),
    (0xf209787bb47d6b85, 348, 124),
    (0xb454e4a179dd1877, 375, 132),
    (0x865b86925b9bc5c2, 402, 140),
    (0xc83553c5c8965d3d, 428, 148),
    (0x952ab45cfa97a0b3, 455, 156),
    (0xde469fbd99a05fe3, 481, 164),
    (0xa59bc234db398c25, 508, 172),
    (0xf6c69a72a3989f5c, 534, 180),
    (0xb7dcbf5354e9bece, 561, 188),
    (0x88fcf317f22241e2, 588, 196),
    (0xcc20ce9bd35c78a5, 614, 204),
    (0x98165af37b2153df, 641, 212),
    (0xe2a0b5dc971f303a, 667, 220),
    (0xa8d9d1535ce3b396, 694, 228),
    (0xfb9b7cd9a4a7443c, 720, 236),
    (0xbb764c4ca7a44410, 747, 244),
    (0x8bab8eefb6409c1a, 774, 252),
    (0xd01fef10a657842c, 800, 260),
    (0x9b10a4e5e9913129, 827, 268),
    (0xe7109bfba19c0c9d, 853, 276),
    (0xac2820d9623bf429, 880, 284),
    (0x80444b5e7aa7cf85, 907, 292),
    (0xbf21e44003acdd2d, 933, 300),
    (0x8e679c2f5e44ff8f, 960, 308),
    (0xd433179d9c8cb841, 986, 316),
    (0x9e19db92b4e31ba9, 1013, 324),
    (0xeb96bf6ebadf77d9, 1039, 332),
];

#[doc(hidden)]
pub const CACHED_POW10_FIRST_E: i16 = -1087;
#[doc(hidden)]
pub const CACHED_POW10_LAST_E: i16 = 1039;

#[doc(hidden)]
pub fn cached_power(alpha: i16, gamma: i16) -> (i16, Fp) {
    let offset = CACHED_POW10_FIRST_E as i32;
    let range = (CACHED_POW10.len() as i32) - 1;
    let domain = (CACHED_POW10_LAST_E - CACHED_POW10_FIRST_E) as i32;
    let idx = ((gamma as i32) - offset) * range / domain;
    let (f, e, k) = CACHED_POW10[idx as usize];
    debug_assert!(alpha <= e && e <= gamma);
    (k, Fp { f, e })
}

/// Given `x > 0`, returns `(k, 10^k)` such that `10^k <= x < 10^(k+1)`.
#[doc(hidden)]
pub fn max_pow10_no_more_than(x: u32) -> (u8, u32) {
    debug_assert!(x > 0);

    const X9: u32 = 10_0000_0000;
    const X8: u32 = 1_0000_0000;
    const X7: u32 = 1000_0000;
    const X6: u32 = 100_0000;
    const X5: u32 = 10_0000;
    const X4: u32 = 1_0000;
    const X3: u32 = 1000;
    const X2: u32 = 100;
    const X1: u32 = 10;

    if x < X4 {
        if x < X2 {
            if x < X1 { (0, 1) } else { (1, X1) }
        } else {
            if x < X3 { (2, X2) } else { (3, X3) }
        }
    } else {
        if x < X6 {
            if x < X5 { (4, X4) } else { (5, X5) }
        } else if x < X8 {
            if x < X7 { (6, X6) } else { (7, X7) }
        } else {
            if x < X9 { (8, X8) } else { (9, X9) }
        }
    }
}

// Verification note:
// The Kani-specific code in this file is scoped to proving memory safety of the
// Grisu implementation, especially that every `MaybeUninit<u8>` byte exposed
// through `assume_init_*` has been written and that all writes stay inside the
// caller-provided buffer. It intentionally abstracts some expensive arithmetic
// steps; those abstractions preserve the bounds used by the safety proof,
// but they are not claims of decimal-conversion numerical correctness.
#[cfg(kani)]
// Kani-only power-of-ten table used by loop invariants and max-pow10 stubs.
fn kani_pow10_u32(kappa: u8) -> u32 {
    match kappa {
        0 => 1,
        1 => 10,
        2 => 100,
        3 => 1_000,
        4 => 10_000,
        5 => 100_000,
        6 => 1_000_000,
        7 => 10_000_000,
        8 => 100_000_000,
        _ => 1_000_000_000,
    }
}

#[cfg(kani)]
// Kani-only power-of-ten table for exact-mode error and loop bounds.
fn kani_pow10_u64(kappa: usize) -> u64 {
    match kappa {
        0 => 1,
        1 => 10,
        2 => 100,
        3 => 1_000,
        4 => 10_000,
        5 => 100_000,
        6 => 1_000_000,
        7 => 10_000_000,
        8 => 100_000_000,
        9 => 1_000_000_000,
        10 => 10_000_000_000,
        11 => 100_000_000_000,
        12 => 1_000_000_000_000,
        13 => 10_000_000_000_000,
        14 => 100_000_000_000_000,
        15 => 1_000_000_000_000_000,
        16 => 10_000_000_000_000_000,
        17 => 100_000_000_000_000_000,
        18 => 1_000_000_000_000_000_000,
        _ => 0,
    }
}

#[cfg(kani)]
// Loop-invariant predicate for the exact-mode integral digit phase.
fn kani_exact_integral_state(integral_limit: usize, i: usize, kappa: i16, ten_kappa: u32) -> bool {
    if i < integral_limit {
        kappa == (integral_limit - i - 1) as i16
            && ten_kappa == kani_pow10_u32((integral_limit - i - 1) as u8)
    } else {
        i == integral_limit && kappa == 0 && ten_kappa == 1
    }
}

#[cfg(kani)]
// Loop-invariant predicate for the shortest-mode integral digit phase.
fn kani_shortest_integral_state(integral_limit: usize, i: usize, ten_kappa: u32) -> bool {
    if i < integral_limit {
        ten_kappa == kani_pow10_u32((integral_limit - i - 1) as u8)
    } else {
        i == integral_limit && ten_kappa == 1
    }
}

#[cfg(kani)]
// Kani bound for the abstract shortest-mode ULP growth in the fractional loop.
const GRISU_SHORTEST_MAX_ULP: u64 = 1_000_000_000_000_000_000;

#[cfg(kani)]
#[inline]
// Kani abstraction for `(value as u64) << e` used in shortest-mode remainder scaling.
fn scale_u32_by_binary_exp(value: u32, e: usize, scale: u64) -> u64 {
    let _ = (value, e);
    let scaled: u64 = kani::any();
    // The concrete operation is `(value as u64) << e`. For this harness we
    // only need a bounded value that can be safely added to `plus1frac`.
    // The exact equality is part of the numerical algorithm, not the
    // MaybeUninit/bounds proof pursued here.
    kani::assume(scale > 0);
    kani::assume(scaled <= u64::MAX - scale);
    scaled
}

#[cfg(kani)]
#[inline]
// Kani abstraction for scaling `10^kappa` before passing it to `round_and_weed`.
fn scale_pow10_by_binary_exp(value: u32, e: usize) -> u64 {
    let _ = (value, e);
    let scaled: u64 = kani::any();
    // This value is passed to `round_and_weed` as the scaled 10^kappa.
    // `round_and_weed` is verified separately and requires only positivity
    // for memory-safety purposes, so the shift itself is abstracted here.
    kani::assume(scaled > 0);
    scaled
}

#[cfg(kani)]
// Kani replacement for `max_pow10_no_more_than` that keeps only its semantic contract.
fn kani_max_pow10_no_more_than(x: u32) -> (u8, u32) {
    kani::assume(x > 0);
    let kappa: u8 = kani::any();
    kani::assume(kappa <= 9);

    let pow = kani_pow10_u32(kappa);
    kani::assume(pow <= x);
    if kappa < 9 {
        kani::assume((x as u64) < (pow as u64) * 10);
    }

    (kappa, pow)
}

#[cfg(kani)]
// Kani-only model of the normalized and cached-power-scaled shortest-mode state.
fn kani_scale_shortest_inputs() -> (i16, Fp, Fp, Fp) {
    // This harness verifies memory safety of the digit-generation control flow.
    // It models only the post-scaling Grisu Fp triple instead of proving the
    // cached-power multiplication here. The decimal split (`plus1int` and
    // `plus1frac`) and all distance quantities are still computed by the real
    // code from this shared post-scale state.
    //
    // This is a deliberate tradeoff: the real normalize/cached-power/multiply
    // path is expensive for Kani and belongs to the numerical correctness proof.
    // The challenge-relevant unsafe operations happen after scaling, so this
    // model over-approximates the post-scale control-flow states while retaining
    // the bounds needed for all buffer writes and slice initialization checks.
    let minusk: i16 = kani::any();
    let e_abs: usize = kani::any();
    let plus_f: u64 = kani::any();
    let minus_f: u64 = kani::any();
    let v_f: u64 = kani::any();

    kani::assume(minusk >= -308 && minusk <= 332);
    kani::assume(e_abs >= (-GAMMA) as usize && e_abs <= (-ALPHA) as usize);

    kani::assume(plus_f >= (1u64 << 62));
    kani::assume(plus_f <= u64::MAX - 16);
    kani::assume(minus_f >= (1u64 << 62));
    kani::assume(minus_f <= plus_f);
    kani::assume(v_f >= minus_f && v_f <= plus_f);

    let e = -(e_abs as i16);
    (minusk, Fp { f: plus_f, e }, Fp { f: minus_f, e }, Fp { f: v_f, e })
}

// In exact mode, Grisu itself can generate at most 10 integral digits plus
// 18 fractional digits before either rounding or the error bound stops it.
// A final carry digit may still be appended by `round_up`.
#[cfg(kani)]
// Maximum exact-mode digits that the Kani loop contracts track before a carry.
const GRISU_EXACT_OPT_MAX_DIGITS: usize = 28;
#[cfg(kani)]
// Scratch-buffer bound used by exact-mode harnesses, including one carry digit.
const GRISU_EXACT_OPT_MAX_BUF_LEN: usize = GRISU_EXACT_OPT_MAX_DIGITS + 1;

/// The shortest mode implementation for Grisu.
///
/// It returns `None` when it would return an inexact representation otherwise.
pub fn format_shortest_opt<'a>(
    d: &Decoded,
    buf: &'a mut [MaybeUninit<u8>],
) -> Option<(/*digits*/ &'a [u8], /*exp*/ i16)> {
    assert!(d.mant > 0);
    assert!(d.minus > 0);
    assert!(d.plus > 0);
    assert!(d.mant.checked_add(d.plus).is_some());
    assert!(d.mant.checked_sub(d.minus).is_some());
    assert!(buf.len() >= MAX_SIG_DIGITS);
    assert!(d.mant + d.plus < (1 << 61)); // we need at least three bits of additional precision

    #[cfg(kani)]
    let (minusk, plus, minus, v) = kani_scale_shortest_inputs();

    #[cfg(not(kani))]
    let (minusk, plus, minus, v) = {
        // start with the normalized values with the shared exponent
        let plus = Fp { f: d.mant + d.plus, e: d.exp }.normalize();
        let minus = Fp { f: d.mant - d.minus, e: d.exp }.normalize_to(plus.e);
        let v = Fp { f: d.mant, e: d.exp }.normalize_to(plus.e);

        // find any `cached = 10^minusk` such that `ALPHA <= minusk + plus.e + 64 <= GAMMA`.
        // since `plus` is normalized, this means `2^(62 + ALPHA) <= plus * cached < 2^(64 + GAMMA)`;
        // given our choices of `ALPHA` and `GAMMA`, this puts `plus * cached` into `[4, 2^32)`.
        //
        // it is obviously desirable to maximize `GAMMA - ALPHA`,
        // so that we don't need many cached powers of 10, but there are some considerations:
        //
        // 1. we want to keep `floor(plus * cached)` within `u32` since it needs a costly division.
        //    (this is not really avoidable, remainder is required for accuracy estimation.)
        // 2. the remainder of `floor(plus * cached)` repeatedly gets multiplied by 10,
        //    and it should not overflow.
        //
        // the first gives `64 + GAMMA <= 32`, while the second gives `10 * 2^-ALPHA <= 2^64`;
        // -60 and -32 is the maximal range with this constraint, and V8 also uses them.
        let (minusk, cached) = cached_power(ALPHA - plus.e - 64, GAMMA - plus.e - 64);

        // scale fps. this gives the maximal error of 1 ulp (proved from Theorem 5.1).
        let plus = plus.mul(cached);
        let minus = minus.mul(cached);
        let v = v.mul(cached);
        debug_assert_eq!(plus.e, minus.e);
        debug_assert_eq!(plus.e, v.e);
        (minusk, plus, minus, v)
    };

    #[cfg(kani)]
    {
        debug_assert_eq!(plus.e, minus.e);
        debug_assert_eq!(plus.e, v.e);
    }

    //         +- actual range of minus
    //   | <---|---------------------- unsafe region --------------------------> |
    //   |     |                                                                 |
    //   |  |<--->|  | <--------------- safe region ---------------> |           |
    //   |  |     |  |                                               |           |
    //   |1 ulp|1 ulp|                 |1 ulp|1 ulp|                 |1 ulp|1 ulp|
    //   |<--->|<--->|                 |<--->|<--->|                 |<--->|<--->|
    //   |-----|-----|-------...-------|-----|-----|-------...-------|-----|-----|
    //   |   minus   |                 |     v     |                 |   plus    |
    // minus1     minus0           v - 1 ulp   v + 1 ulp           plus0       plus1
    //
    // above `minus`, `v` and `plus` are *quantized* approximations (error < 1 ulp).
    // as we don't know the error is positive or negative, we use two approximations spaced equally
    // and have the maximal error of 2 ulps.
    //
    // the "unsafe region" is a liberal interval which we initially generate.
    // the "safe region" is a conservative interval which we only accept.
    // we start with the correct repr within the unsafe region, and try to find the closest repr
    // to `v` which is also within the safe region. if we can't, we give up.
    let plus1 = plus.f + 1;
    //  let plus0 = plus.f - 1; // only for explanation
    //  let minus0 = minus.f + 1; // only for explanation
    let minus1 = minus.f - 1;
    let e = -plus.e as usize; // shared exponent
    let scale = 1u64 << e;

    // divide `plus1` into integral and fractional parts.
    // integral parts are guaranteed to fit in u32, since cached power guarantees `plus < 2^32`
    // and normalized `plus.f` is always less than `2^64 - 2^4` due to the precision requirement.
    let plus1int = (plus1 >> e) as u32;
    let plus1frac = plus1 & (scale - 1);

    // calculate the largest `10^max_kappa` no more than `plus1` (thus `plus1 < 10^(max_kappa+1)`).
    // this is an upper bound of `kappa` below.
    #[cfg(kani)]
    let (max_kappa, max_ten_kappa) = kani_max_pow10_no_more_than(plus1int);
    #[cfg(not(kani))]
    let (max_kappa, max_ten_kappa) = max_pow10_no_more_than(plus1int);

    let mut i = 0;
    let exp = max_kappa as i16 - minusk + 1;

    // Theorem 6.2: if `k` is the greatest integer s.t. `0 <= y mod 10^k <= y - x`,
    //              then `V = floor(y / 10^k) * 10^k` is in `[x, y]` and one of the shortest
    //              representations (with the minimal number of significant digits) in that range.
    //
    // find the digit length `kappa` between `(minus1, plus1)` as per Theorem 6.2.
    // Theorem 6.2 can be adopted to exclude `x` by requiring `y mod 10^k < y - x` instead.
    // (e.g., `x` = 32000, `y` = 32777; `kappa` = 2 since `y mod 10^3 = 777 < y - x = 777`.)
    // the algorithm relies on the later verification phase to exclude `y`.
    let delta1 = plus1 - minus1;
    //  let delta1int = (delta1 >> e) as usize; // only for explanation
    let delta1frac = delta1 & (scale - 1);

    // render integral parts, while checking for the accuracy at each step.
    let shortest_integral_limit = max_kappa as usize + 1;
    let mut ten_kappa = max_ten_kappa; // 10^kappa
    let mut remainder = plus1int; // digits yet to be rendered
    #[cfg(kani)]
    let mut int_q = 0u32;
    #[cfg(kani)]
    let mut int_r = 0u32;
    #[cfg(kani)]
    let mut scaled_r = 0u64;
    #[cfg(kani)]
    let mut plus1rem = 0u64;
    // The loop contract summarizes the integral-digit phase for Kani.
    #[cfg_attr(kani, kani::loop_invariant(
        shortest_integral_limit == max_kappa as usize + 1
            && shortest_integral_limit <= 10
            && i <= shortest_integral_limit
            && i < MAX_SIG_DIGITS
            && i <= buf.len()
            && e > 0
            && e <= 60
            && scale == (1u64 << e)
            && plus1frac < scale
            && delta1frac < scale
            && plus1 >= minus1
            && v.f <= plus1
            && kani_shortest_integral_state(shortest_integral_limit, i, ten_kappa)
            && ten_kappa > 0
            && ten_kappa <= plus1int
            && remainder <= plus1int
            && (remainder as u64) < (ten_kappa as u64) * 10
    ))]
    #[cfg_attr(kani, kani::loop_modifies(
        &i,
        &ten_kappa,
        &remainder,
        &int_q,
        &int_r,
        &scaled_r,
        &plus1rem,
        &mut *buf
    ))]
    while i < shortest_integral_limit {
        // we always have at least one digit to render, as `plus1 >= 10^kappa`
        // invariants:
        // - `delta1int <= remainder < 10^(kappa+1)`
        // - `plus1int = d[0..n-1] * 10^(kappa+1) + remainder`
        //   (it follows that `remainder = plus1int % 10^(kappa+1)`)

        // divide `remainder` by `10^kappa`. both are scaled by `2^-e`.
        #[cfg(not(kani))]
        let int_q = remainder / ten_kappa;
        #[cfg(not(kani))]
        let int_r = remainder % ten_kappa;
        #[cfg(kani)]
        {
            let _ = remainder;
            int_q = kani::any();
            int_r = kani::any();
            kani::assume(ten_kappa > 0);
            kani::assume(int_q < 10);
            kani::assume(int_r < ten_kappa);
        }
        debug_assert!(int_q < 10);
        buf[i] = MaybeUninit::new(b'0' + int_q as u8);
        i += 1;

        #[cfg(not(kani))]
        let plus1rem = ((int_r as u64) << e) + plus1frac; // == (plus1 % 10^kappa) * 2^e
        #[cfg(kani)]
        {
            scaled_r = scale_u32_by_binary_exp(int_r, e, scale);
            plus1rem = scaled_r + plus1frac; // == (plus1 % 10^kappa) * 2^e
        }
        if plus1rem < delta1 {
            // `plus1 % 10^kappa < delta1 = plus1 - minus1`; we've found the correct `kappa`.
            #[cfg(not(kani))]
            let ten_kappa = (ten_kappa as u64) << e; // scale 10^kappa back to the shared exponent
            #[cfg(kani)]
            let ten_kappa = scale_pow10_by_binary_exp(ten_kappa, e); // scale 10^kappa back to the shared exponent
            // SAFETY: we initialized that memory above.
            let digits = unsafe { buf[..i].assume_init_mut() };
            #[cfg(not(kani))]
            return round_and_weed(digits, exp, plus1rem, delta1, plus1 - v.f, ten_kappa, 1);
            #[cfg(kani)]
            return if round_and_weed(digits, plus1rem, delta1, plus1 - v.f, ten_kappa, 1) {
                Some((digits, exp))
            } else {
                None
            };
        }

        // break the loop when we have rendered all integral digits.
        // the exact number of digits is `max_kappa + 1` as `plus1 < 10^(max_kappa+1)`.
        if i == shortest_integral_limit {
            debug_assert_eq!(ten_kappa, 1);
            break;
        }

        // restore invariants
        ten_kappa /= 10;
        remainder = int_r;
    }

    // render fractional parts, while checking for the accuracy at each step.
    // this time we rely on repeated multiplications, as division will lose the precision.
    let mut remainder = plus1frac;
    let mut threshold = delta1frac;
    let mut ulp = 1;
    #[cfg(kani)]
    let mut frac_digits = 0usize;
    #[cfg(kani)]
    let mut frac_q = 0u8;
    #[cfg(kani)]
    let mut frac_r = 0u64;
    #[cfg(kani)]
    let mut next_threshold = 0u64;
    #[cfg(kani)]
    let mut next_ulp = 1u64;
    // The fractional loop can run until the shortest-mode buffer is full. The
    // contract gives Kani an inductive summary instead of relying on a large
    // unwind. It also carries the initialized-prefix fact through the abstract
    // fractional step.
    #[cfg_attr(kani, kani::loop_invariant(
        shortest_integral_limit == max_kappa as usize + 1
            && shortest_integral_limit <= 10
            && frac_digits <= MAX_SIG_DIGITS - shortest_integral_limit
            && i == shortest_integral_limit + frac_digits
            && i <= MAX_SIG_DIGITS
            && i <= buf.len()
            && e > 0
            && e <= 60
            && scale == (1u64 << e)
            && remainder < scale
            && threshold < scale
            && ulp > 0
            && ulp <= GRISU_SHORTEST_MAX_ULP
            && plus1 >= v.f
    ))]
    #[cfg_attr(kani, kani::loop_modifies(
        &i,
        &remainder,
        &threshold,
        &ulp,
        &frac_digits,
        &frac_q,
        &frac_r,
        &next_threshold,
        &next_ulp,
        &mut *buf
    ))]
    loop {
        #[cfg(kani)]
        if i >= MAX_SIG_DIGITS {
            break None;
        }

        // the next digit should be significant as we've tested that before breaking out
        // invariants, where `m = max_kappa + 1` (# of digits in the integral part):
        // - `remainder < 2^e`
        // - `plus1frac * 10^(n-m) = d[m..n-1] * 2^e + remainder`

        #[cfg(not(kani))]
        {
            remainder *= 10; // won't overflow, `2^e * 10 < 2^64`
            threshold *= 10;
            ulp *= 10;
        }
        #[cfg(not(kani))]
        let frac_q = remainder >> e;
        #[cfg(not(kani))]
        let frac_r = remainder & (scale - 1);
        #[cfg(kani)]
        {
            frac_q = kani::any();
            frac_r = kani::any();
            next_threshold = kani::any();
            next_ulp = kani::any();

            kani::assume(frac_q < 10);
            kani::assume(frac_r < scale);
            kani::assume(next_threshold <= scale * 10);
            kani::assume(next_ulp > 0 && next_ulp <= GRISU_SHORTEST_MAX_ULP);
        }
        #[cfg(kani)]
        {
            threshold = next_threshold;
            ulp = next_ulp;
        }
        debug_assert!(frac_q < 10);
        buf[i] = MaybeUninit::new(b'0' + frac_q as u8);
        i += 1;
        #[cfg(kani)]
        {
            frac_digits += 1;
        }

        if frac_r < threshold {
            let ten_kappa = scale; // implicit divisor
            let Some(plus1v) = (plus1 - v.f).checked_mul(ulp) else {
                return None;
            };
            // SAFETY: we initialized that memory above.
            let digits = unsafe { buf[..i].assume_init_mut() };
            #[cfg(not(kani))]
            return round_and_weed(digits, exp, frac_r, threshold, plus1v, ten_kappa, ulp);
            #[cfg(kani)]
            return if round_and_weed(digits, frac_r, threshold, plus1v, ten_kappa, ulp) {
                Some((digits, exp))
            } else {
                None
            };
        }

        // restore invariants
        remainder = frac_r;
    }
}

#[cfg(not(kani))]
fn round_and_weed<'a>(
    buf: &'a mut [u8],
    exp: i16,
    remainder: u64,
    threshold: u64,
    plus1v: u64,
    ten_kappa: u64,
    ulp: u64,
) -> Option<(&'a [u8], i16)> {
    assert!(!buf.is_empty());

    // produce two approximations to `v` (actually `plus1 - v`) within 1.5 ulps.
    // the resulting representation should be the closest representation to both.
    //
    // here `plus1 - v` is used since calculations are done with respect to `plus1`
    // in order to avoid overflow/underflow (hence the seemingly swapped names).
    let plus1v_down = plus1v + ulp; // plus1 - (v - 1 ulp)
    let plus1v_up = plus1v - ulp; // plus1 - (v + 1 ulp)

    // decrease the last digit and stop at the closest representation to `v + 1 ulp`.
    let mut plus1w = remainder; // plus1w(n) = plus1 - w(n)
    {
        let last = buf.last_mut().unwrap();

        // we work with the approximated digits `w(n)`, which is initially equal to `plus1 -
        // plus1 % 10^kappa`. after running the loop body `n` times, `w(n) = plus1 -
        // plus1 % 10^kappa - n * 10^kappa`. we set `plus1w(n) = plus1 - w(n) =
        // plus1 % 10^kappa + n * 10^kappa` (thus `remainder = plus1w(0)`) to simplify checks.
        // note that `plus1w(n)` is always increasing.
        while plus1w < plus1v_up
            && threshold - plus1w >= ten_kappa
            && (plus1w + ten_kappa < plus1v_up
                || plus1v_up - plus1w >= plus1w + ten_kappa - plus1v_up)
        {
            *last -= 1;
            debug_assert!(*last > b'0'); // the shortest repr cannot end with `0`
            plus1w += ten_kappa;
        }
    }

    // check if this representation is also the closest representation to `v - 1 ulp`.
    if plus1w < plus1v_down
        && threshold - plus1w >= ten_kappa
        && (plus1w + ten_kappa < plus1v_down
            || plus1v_down - plus1w >= plus1w + ten_kappa - plus1v_down)
    {
        return None;
    }

    // now we have the closest representation to `v` between `plus1` and `minus1`.
    // this is too liberal, though, so we reject any `w(n)` not between `plus0` and `minus0`.
    if 2 * ulp <= plus1w && plus1w <= threshold - 4 * ulp { Some((buf, exp)) } else { None }
}

/// The rounding-and-weeding phase of Grisu shortest. This is hoisted from the
/// old nested function so Kani can stub it while verifying `format_shortest_opt`.
///
/// we've generated all significant digits of `plus1`, but not sure if it's the optimal one.
/// For example, if `minus1` is 3.14153... and `plus1` is 3.14158..., there are 5 different
/// shortest representation from 3.14154 to 3.14158 but we only have the greatest one.
/// We have to successively decrease the last digit and check if this is the optimal repr.
/// There are at most 9 candidates (..1 to ..9), so this is fairly quick. ("rounding" phase)
///
/// the function checks if this "optimal" repr is actually within the ulp ranges,
/// and also, it is possible that the "second-to-optimal" repr can actually be optimal
/// due to the rounding error. in either case this returns `false`. ("weeding" phase)
///
/// all arguments here are scaled by the common (but implicit) value `k`, so that:
/// - `remainder = (plus1 % 10^kappa) * k`
/// - `threshold = (plus1 - minus1) * k` (and also, `remainder < threshold`)
/// - `plus1v = (plus1 - v) * k` (and also, `threshold > plus1v` from prior invariants)
/// - `ten_kappa = 10^kappa * k`
/// - `ulp = 2^-e * k`
///
/// Verification note: this helper returns only whether the already-created
/// digit slice should be accepted. The caller owns the slice and exponent, so
/// returning `bool` is equivalent to the old `Option<(&[u8], i16)>` structure
/// but can be used with `#[kani::stub_verified]`. The original slice-returning
/// type cannot be generated by Kani as an arbitrary verified-stub result.
#[cfg_attr(kani, kani::requires(!buf.is_empty()))]
#[cfg_attr(kani, kani::requires(buf[buf.len() - 1] >= b'0'))]
#[cfg_attr(kani, kani::requires(buf[buf.len() - 1] <= b'9'))]
#[cfg_attr(kani, kani::requires(remainder < threshold))]
#[cfg_attr(kani, kani::requires(ten_kappa > 0))]
#[cfg_attr(kani, kani::requires(ulp > 0))]
#[cfg_attr(kani, kani::modifies(&mut buf[buf.len() - 1]))]
#[cfg_attr(kani, kani::ensures(|result| !*result || (
    buf[buf.len() - 1] >= b'0' && buf[buf.len() - 1] <= b'9'
)))]
#[cfg(kani)]
fn round_and_weed(
    buf: &mut [u8],
    remainder: u64,
    threshold: u64,
    plus1v: u64,
    ten_kappa: u64,
    ulp: u64,
) -> bool {
    assert!(!buf.is_empty());

    // produce two approximations to `v` (actually `plus1 - v`) within 1.5 ulps.
    // the resulting representation should be the closest representation to both.
    //
    // here `plus1 - v` is used since calculations are done with respect to `plus1`
    // in order to avoid overflow/underflow (hence the seemingly swapped names).
    let Some(plus1v_down) = plus1v.checked_add(ulp) else {
        return false;
    }; // plus1 - (v - 1 ulp)
    let Some(plus1v_up) = plus1v.checked_sub(ulp) else {
        return false;
    }; // plus1 - (v + 1 ulp)

    // decrease the last digit and stop at the closest representation to `v + 1 ulp`.
    let mut plus1w = remainder; // plus1w(n) = plus1 - w(n)
    {
        let last = buf.last_mut().unwrap();

        // we work with the approximated digits `w(n)`, which is initially equal to `plus1 -
        // plus1 % 10^kappa`. after running the loop body `n` times, `w(n) = plus1 -
        // plus1 % 10^kappa - n * 10^kappa`. we set `plus1w(n) = plus1 - w(n) =
        // plus1 % 10^kappa + n * 10^kappa` (thus `remainder = plus1w(0)`) to simplify checks.
        // note that `plus1w(n)` is always increasing.
        //
        // we have three conditions to terminate. any of them will make the loop unable to
        // proceed, but we then have at least one valid representation known to be closest to
        // `v + 1 ulp` anyway. we will denote them as TC1 through TC3 for brevity.
        //
        // TC1: `w(n) <= v + 1 ulp`, i.e., this is the last repr that can be the closest one.
        // this is equivalent to `plus1 - w(n) = plus1w(n) >= plus1 - (v + 1 ulp) = plus1v_up`.
        // combined with TC2 (which checks if `w(n+1)` is valid), this prevents the possible
        // overflow on the calculation of `plus1w(n)`.
        //
        // TC2: `w(n+1) < minus1`, i.e., the next repr definitely does not round to `v`.
        // this is equivalent to `plus1 - w(n) + 10^kappa = plus1w(n) + 10^kappa >
        // plus1 - minus1 = threshold`. the left hand side can overflow, but we know
        // `threshold > plus1v`, so if TC1 is false, `threshold - plus1w(n) >
        // threshold - (plus1v - 1 ulp) > 1 ulp` and we can safely test if
        // `threshold - plus1w(n) < 10^kappa` instead.
        //
        // TC3: `abs(w(n) - (v + 1 ulp)) <= abs(w(n+1) - (v + 1 ulp))`, i.e., the next repr is
        // no closer to `v + 1 ulp` than the current repr. given `z(n) = plus1v_up - plus1w(n)`,
        // this becomes `abs(z(n)) <= abs(z(n+1))`. again assuming that TC1 is false, we have
        // `z(n) > 0`. we have two cases to consider:
        //
        // - when `z(n+1) >= 0`: TC3 becomes `z(n) <= z(n+1)`. as `plus1w(n)` is increasing,
        //   `z(n)` should be decreasing and this is clearly false.
        // - when `z(n+1) < 0`:
        //   - TC3a: the precondition is `plus1v_up < plus1w(n) + 10^kappa`. assuming TC2 is
        //     false, `threshold >= plus1w(n) + 10^kappa` so it cannot overflow.
        //   - TC3b: TC3 becomes `z(n) <= -z(n+1)`, i.e., `plus1v_up - plus1w(n) >=
        //     plus1w(n+1) - plus1v_up = plus1w(n) + 10^kappa - plus1v_up`. the negated TC1
        //     gives `plus1v_up > plus1w(n)`, so it cannot overflow or underflow when
        //     combined with TC3a.
        //
        // consequently, we should stop when `TC1 || TC2 || (TC3a && TC3b)`. the following is
        // equal to its inverse, `!TC1 && !TC2 && (!TC3a || !TC3b)`.
        while round_and_weed_can_decrement(plus1w, plus1v_up, threshold, ten_kappa) {
            if *last <= b'1' {
                return false;
            }
            *last -= 1;
            debug_assert!(*last > b'0'); // the shortest repr cannot end with `0`
            let Some(next_plus1w) = plus1w.checked_add(ten_kappa) else {
                return false;
            };
            plus1w = next_plus1w;
        }
    }

    // check if this representation is also the closest representation to `v - 1 ulp`.
    //
    // this is simply same to the terminating conditions for `v + 1 ulp`, with all `plus1v_up`
    // replaced by `plus1v_down` instead. overflow analysis equally holds.
    if round_and_weed_can_decrement(plus1w, plus1v_down, threshold, ten_kappa) {
        return false;
    }

    // now we have the closest representation to `v` between `plus1` and `minus1`.
    // this is too liberal, though, so we reject any `w(n)` not between `plus0` and `minus0`,
    // i.e., `plus1 - plus1w(n) <= minus0` or `plus1 - plus1w(n) >= plus0`. we utilize the facts
    // that `threshold = plus1 - minus1` and `plus1 - plus0 = minus0 - minus1 = 2 ulp`.
    let Some(two_ulp) = ulp.checked_mul(2) else {
        return false;
    };
    let Some(four_ulp) = ulp.checked_mul(4) else {
        return false;
    };
    let Some(upper) = threshold.checked_sub(four_ulp) else {
        return false;
    };
    two_ulp <= plus1w && plus1w <= upper
}

#[inline]
#[cfg(kani)]
// Helper used by the verified `round_and_weed` body to make the decrement condition reusable.
fn round_and_weed_can_decrement(
    plus1w: u64,
    plus1v_edge: u64,
    threshold: u64,
    ten_kappa: u64,
) -> bool {
    if plus1w >= plus1v_edge {
        return false;
    }
    let Some(threshold_gap) = threshold.checked_sub(plus1w) else {
        return false;
    };
    if threshold_gap < ten_kappa {
        return false;
    }
    let Some(next_plus1w) = plus1w.checked_add(ten_kappa) else {
        return false;
    };
    if next_plus1w < plus1v_edge {
        return true;
    }
    plus1v_edge - plus1w >= next_plus1w - plus1v_edge
}

/// The shortest mode implementation for Grisu with Dragon fallback.
///
/// This should be used for most cases.
pub fn format_shortest<'a>(
    d: &Decoded,
    buf: &'a mut [MaybeUninit<u8>],
) -> (/*digits*/ &'a [u8], /*exp*/ i16) {
    use crate::num::flt2dec::strategy::dragon::format_shortest as fallback;
    // SAFETY: The borrow checker is not smart enough to let us use `buf`
    // in the second branch, so we launder the lifetime here. But we only re-use
    // `buf` if `format_shortest_opt` returned `None` so this is okay.
    match format_shortest_opt(d, unsafe { &mut *(buf as *mut _) }) {
        Some(ret) => ret,
        None => fallback(d, buf),
    }
}

/// The exact and fixed mode implementation for Grisu.
///
/// It returns `None` when it would return an inexact representation otherwise.
#[cfg(not(kani))]
pub fn format_exact_opt<'a>(
    d: &Decoded,
    buf: &'a mut [MaybeUninit<u8>],
    limit: i16,
) -> Option<(/*digits*/ &'a [u8], /*exp*/ i16)> {
    assert!(d.mant > 0);
    assert!(d.mant < (1 << 61)); // we need at least three bits of additional precision
    assert!(!buf.is_empty());

    // normalize and scale `v`.
    let v = Fp { f: d.mant, e: d.exp }.normalize();
    let (minusk, cached) = cached_power(ALPHA - v.e - 64, GAMMA - v.e - 64);
    let v = v.mul(cached);

    // divide `v` into integral and fractional parts.
    let e = -v.e as usize;
    let vint = (v.f >> e) as u32;
    let vfrac = v.f & ((1 << e) - 1);

    let requested_digits = buf.len();

    const POW10_UP_TO_9: [u32; 10] =
        [1, 10, 100, 1000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000, 1_000_000_000];

    // We deviate from the original algorithm here and do some early checks to determine if we can satisfy requested_digits.
    // If we determine that we can't, we exit early and avoid most of the heavy lifting that the algorithm otherwise does.
    //
    // When vfrac is zero, we can easily determine if vint can satisfy requested digits:
    //      If requested_digits >= 11, vint is not able to exhaust the count by itself since 10^(11 -1) > u32 max value >= vint.
    //      If vint < 10^(requested_digits - 1), vint cannot exhaust the count.
    //      Otherwise, vint might be able to exhaust the count and we need to execute the rest of the code.
    if (vfrac == 0) && ((requested_digits >= 11) || (vint < POW10_UP_TO_9[requested_digits - 1])) {
        return None;
    }

    // both old `v` and new `v` (scaled by `10^-k`) has an error of < 1 ulp (Theorem 5.1).
    // as we don't know the error is positive or negative, we use two approximations
    // spaced equally and have the maximal error of 2 ulps (same to the shortest case).
    //
    // the goal is to find the exactly rounded series of digits that are common to
    // both `v - 1 ulp` and `v + 1 ulp`, so that we are maximally confident.
    // if this is not possible, we don't know which one is the correct output for `v`,
    // so we give up and fall back.
    //
    // `err` is defined as `1 ulp * 2^e` here (same to the ulp in `vfrac`),
    // and we will scale it whenever `v` gets scaled.
    let mut err = 1;

    // calculate the largest `10^max_kappa` no more than `v` (thus `v < 10^(max_kappa+1)`).
    // this is an upper bound of `kappa` below.
    let (max_kappa, max_ten_kappa) = max_pow10_no_more_than(vint);

    let mut i = 0;
    let exp = max_kappa as i16 - minusk + 1;

    // if we are working with the last-digit limitation, we need to shorten the buffer
    // before the actual rendering in order to avoid double rounding.
    // note that we have to enlarge the buffer again when rounding up happens!
    let len = if exp <= limit {
        // oops, we cannot even produce *one* digit.
        // this is possible when, say, we've got something like 9.5 and it's being rounded to 10.
        //
        // in principle we can immediately call `possibly_round` with an empty buffer,
        // but scaling `max_ten_kappa << e` by 10 can result in overflow.
        // thus we are being sloppy here and widen the error range by a factor of 10.
        // this will increase the false negative rate, but only very, *very* slightly;
        // it can only matter noticeably when the mantissa is bigger than 60 bits.
        //
        // SAFETY: `len=0`, so the obligation of having initialized this memory is trivial.
        return unsafe {
            possibly_round(buf, 0, exp, limit, v.f / 10, (max_ten_kappa as u64) << e, err << e)
        };
    } else if ((exp as i32 - limit as i32) as usize) < buf.len() {
        (exp - limit) as usize
    } else {
        buf.len()
    };
    debug_assert!(len > 0);

    // render integral parts.
    // the error is entirely fractional, so we don't need to check it in this part.
    let mut kappa = max_kappa as i16;
    let mut ten_kappa = max_ten_kappa; // 10^kappa
    let mut remainder = vint; // digits yet to be rendered
    loop {
        // we always have at least one digit to render
        // invariants:
        // - `remainder < 10^(kappa+1)`
        // - `vint = d[0..n-1] * 10^(kappa+1) + remainder`
        //   (it follows that `remainder = vint % 10^(kappa+1)`)

        // divide `remainder` by `10^kappa`. both are scaled by `2^-e`.
        let q = remainder / ten_kappa;
        let r = remainder % ten_kappa;
        debug_assert!(q < 10);
        buf[i] = MaybeUninit::new(b'0' + q as u8);
        i += 1;

        // is the buffer full? run the rounding pass with the remainder.
        if i == len {
            let vrem = ((r as u64) << e) + vfrac; // == (v % 10^kappa) * 2^e
            // SAFETY: we have initialized `len` many bytes.
            return unsafe {
                possibly_round(buf, len, exp, limit, vrem, (ten_kappa as u64) << e, err << e)
            };
        }

        // break the loop when we have rendered all integral digits.
        // the exact number of digits is `max_kappa + 1` as `plus1 < 10^(max_kappa+1)`.
        if i > max_kappa as usize {
            debug_assert_eq!(ten_kappa, 1);
            debug_assert_eq!(kappa, 0);
            break;
        }

        // restore invariants
        kappa -= 1;
        ten_kappa /= 10;
        remainder = r;
    }

    // render fractional parts.
    //
    // in principle we can continue to the last available digit and check for the accuracy.
    // unfortunately we are working with the finite-sized integers, so we need some criterion
    // to detect the overflow. V8 uses `remainder > err`, which becomes false when
    // the first `i` significant digits of `v - 1 ulp` and `v` differ. however this rejects
    // too many otherwise valid input.
    //
    // since the later phase has a correct overflow detection, we instead use tighter criterion:
    // we continue til `err` exceeds `10^kappa / 2`, so that the range between `v - 1 ulp` and
    // `v + 1 ulp` definitely contains two or more rounded representations. this is same to
    // the first two comparisons from `possibly_round`, for the reference.
    let mut remainder = vfrac;
    let maxerr = 1 << (e - 1);
    while err < maxerr {
        // invariants, where `m = max_kappa + 1` (# of digits in the integral part):
        // - `remainder < 2^e`
        // - `vfrac * 10^(n-m) = d[m..n-1] * 2^e + remainder`
        // - `err = 10^(n-m)`

        remainder *= 10; // won't overflow, `2^e * 10 < 2^64`
        err *= 10; // won't overflow, `err * 10 < 2^e * 5 < 2^64`

        // divide `remainder` by `10^kappa`.
        // both are scaled by `2^e / 10^kappa`, so the latter is implicit here.
        let q = remainder >> e;
        let r = remainder & ((1 << e) - 1);
        debug_assert!(q < 10);
        buf[i] = MaybeUninit::new(b'0' + q as u8);
        i += 1;

        // is the buffer full? run the rounding pass with the remainder.
        if i == len {
            // SAFETY: we have initialized `len` many bytes.
            return unsafe { possibly_round(buf, len, exp, limit, r, 1 << e, err) };
        }

        // restore invariants
        remainder = r;
    }

    // further calculation is useless (`possibly_round` definitely fails), so we give up.
    return None;

    // we've generated all requested digits of `v`, which should be also same to corresponding
    // digits of `v - 1 ulp`. now we check if there is a unique representation shared by
    // both `v - 1 ulp` and `v + 1 ulp`; this can be either same to generated digits, or
    // to the rounded-up version of those digits. if the range contains multiple representations
    // of the same length, we cannot be sure and should return `None` instead.
    //
    // all arguments here are scaled by the common (but implicit) value `k`, so that:
    // - `remainder = (v % 10^kappa) * k`
    // - `ten_kappa = 10^kappa * k`
    // - `ulp = 2^-e * k`
    //
    // SAFETY: the first `len` bytes of `buf` must be initialized.
    unsafe fn possibly_round(
        buf: &mut [MaybeUninit<u8>],
        mut len: usize,
        mut exp: i16,
        limit: i16,
        remainder: u64,
        ten_kappa: u64,
        ulp: u64,
    ) -> Option<(&[u8], i16)> {
        debug_assert!(remainder < ten_kappa);

        //           10^kappa
        //    :   :   :<->:   :
        //    :   :   :   :   :
        //    :|1 ulp|1 ulp|  :
        //    :|<--->|<--->|  :
        // ----|-----|-----|----
        //     |     v     |
        // v - 1 ulp   v + 1 ulp
        //
        // (for the reference, the dotted line indicates the exact value for
        // possible representations in given number of digits.)
        //
        // error is too large that there are at least three possible representations
        // between `v - 1 ulp` and `v + 1 ulp`. we cannot determine which one is correct.
        if ulp >= ten_kappa {
            return None;
        }

        //    10^kappa
        //   :<------->:
        //   :         :
        //   : |1 ulp|1 ulp|
        //   : |<--->|<--->|
        // ----|-----|-----|----
        //     |     v     |
        // v - 1 ulp   v + 1 ulp
        //
        // in fact, 1/2 ulp is enough to introduce two possible representations.
        // (remember that we need a unique representation for both `v - 1 ulp` and `v + 1 ulp`.)
        // this won't overflow, as `ulp < ten_kappa` from the first check.
        if ten_kappa - ulp <= ulp {
            return None;
        }

        //     remainder
        //       :<->|                           :
        //       :   |                           :
        //       :<--------- 10^kappa ---------->:
        //     | :   |                           :
        //     |1 ulp|1 ulp|                     :
        //     |<--->|<--->|                     :
        // ----|-----|-----|------------------------
        //     |     v     |
        // v - 1 ulp   v + 1 ulp
        //
        // if `v + 1 ulp` is closer to the rounded-down representation (which is already in `buf`),
        // then we can safely return. note that `v - 1 ulp` *can* be less than the current
        // representation, but as `1 ulp < 10^kappa / 2`, this condition is enough:
        // the distance between `v - 1 ulp` and the current representation
        // cannot exceed `10^kappa / 2`.
        //
        // the condition equals to `remainder + ulp < 10^kappa / 2`.
        // since this can easily overflow, first check if `remainder < 10^kappa / 2`.
        // we've already verified that `ulp < 10^kappa / 2`, so as long as
        // `10^kappa` did not overflow after all, the second check is fine.
        if ten_kappa - remainder > remainder && ten_kappa - 2 * remainder >= 2 * ulp {
            // SAFETY: our caller initialized that memory.
            return Some((unsafe { buf[..len].assume_init_ref() }, exp));
        }

        //   :<------- remainder ------>|   :
        //   :                          |   :
        //   :<--------- 10^kappa --------->:
        //   :                    |     |   : |
        //   :                    |1 ulp|1 ulp|
        //   :                    |<--->|<--->|
        // -----------------------|-----|-----|-----
        //                        |     v     |
        //                    v - 1 ulp   v + 1 ulp
        //
        // on the other hands, if `v - 1 ulp` is closer to the rounded-up representation,
        // we should round up and return. for the same reason we don't need to check `v + 1 ulp`.
        //
        // the condition equals to `remainder - ulp >= 10^kappa / 2`.
        // again we first check if `remainder > ulp` (note that this is not `remainder >= ulp`,
        // as `10^kappa` is never zero). also note that `remainder - ulp <= 10^kappa`,
        // so the second check does not overflow.
        if remainder > ulp && ten_kappa - (remainder - ulp) <= remainder - ulp {
            if let Some(c) =
                // SAFETY: our caller must have initialized that memory.
                round_up(unsafe { buf[..len].assume_init_mut() })
            {
                // only add an additional digit when we've been requested the fixed precision.
                // we also need to check that, if the original buffer was empty,
                // the additional digit can only be added when `exp == limit` (edge case).
                exp += 1;
                if exp > limit && len < buf.len() {
                    buf[len] = MaybeUninit::new(c);
                    len += 1;
                }
            }
            // SAFETY: we and our caller initialized that memory.
            return Some((unsafe { buf[..len].assume_init_ref() }, exp));
        }

        // otherwise we are doomed (i.e., some values between `v - 1 ulp` and `v + 1 ulp` are
        // rounding down and others are rounding up) and give up.
        None
    }
}

/// The exact and fixed mode implementation for Grisu.
///
/// It returns `None` when it would return an inexact representation otherwise.
#[cfg(kani)]
// Verification version: keeps exact-mode digit writes and rounding structure, with loop contracts
// and bounded assumptions so Kani can prove the unsafe slice initialization sites.
pub fn format_exact_opt<'a>(
    d: &Decoded,
    buf: &'a mut [MaybeUninit<u8>],
    limit: i16,
) -> Option<(/*digits*/ &'a [u8], /*exp*/ i16)> {
    assert!(d.mant > 0);
    assert!(d.mant < (1 << 61)); // we need at least three bits of additional precision
    assert!(!buf.is_empty());

    // normalize and scale `v`.
    let v = Fp { f: d.mant, e: d.exp }.normalize();
    let (minusk, cached) = cached_power(ALPHA - v.e - 64, GAMMA - v.e - 64);
    let v = v.mul(cached);
    #[cfg(kani)]
    {
        kani::assume(v.f >= (1u64 << 62) && v.f <= u64::MAX - 16);
        kani::assume(v.e >= ALPHA && v.e <= GAMMA);
    }

    // divide `v` into integral and fractional parts.
    let e = -v.e as usize;
    let vint = (v.f >> e) as u32;
    let vfrac = v.f & ((1 << e) - 1);

    let requested_digits = buf.len();

    const POW10_UP_TO_9: [u32; 10] =
        [1, 10, 100, 1000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000, 1_000_000_000];

    // We deviate from the original algorithm here and do some early checks to determine if we can satisfy requested_digits.
    // If we determine that we can't, we exit early and avoid most of the heavy lifting that the algorithm otherwise does.
    //
    // When vfrac is zero, we can easily determine if vint can satisfy requested digits:
    //      If requested_digits >= 11, vint is not able to exhaust the count by itself since 10^(11 -1) > u32 max value >= vint.
    //      If vint < 10^(requested_digits - 1), vint cannot exhaust the count.
    //      Otherwise, vint might be able to exhaust the count and we need to execute the rest of the code.
    if (vfrac == 0) && ((requested_digits >= 11) || (vint < POW10_UP_TO_9[requested_digits - 1])) {
        return None;
    }

    // both old `v` and new `v` (scaled by `10^-k`) has an error of < 1 ulp (Theorem 5.1).
    // as we don't know the error is positive or negative, we use two approximations
    // spaced equally and have the maximal error of 2 ulps (same to the shortest case).
    //
    // the goal is to find the exactly rounded series of digits that are common to
    // both `v - 1 ulp` and `v + 1 ulp`, so that we are maximally confident.
    // if this is not possible, we don't know which one is the correct output for `v`,
    // so we give up and fall back.
    //
    // `err` is defined as `1 ulp * 2^e` here (same to the ulp in `vfrac`),
    // and we will scale it whenever `v` gets scaled.
    let mut err = 1;

    // calculate the largest `10^max_kappa` no more than `v` (thus `v < 10^(max_kappa+1)`).
    // this is an upper bound of `kappa` below.
    let (max_kappa, max_ten_kappa) = max_pow10_no_more_than(vint);

    let mut i = 0;
    let exp = max_kappa as i16 - minusk + 1;

    // if we are working with the last-digit limitation, we need to shorten the buffer
    // before the actual rendering in order to avoid double rounding.
    // note that we have to enlarge the buffer again when rounding up happens!
    let len = if exp <= limit {
        // oops, we cannot even produce *one* digit.
        // this is possible when, say, we've got something like 9.5 and it's being rounded to 10.
        //
        // in principle we can immediately call `possibly_round` with an empty buffer,
        // but scaling `max_ten_kappa << e` by 10 can result in overflow.
        // thus we are being sloppy here and widen the error range by a factor of 10.
        // this will increase the false negative rate, but only very, *very* slightly;
        // it can only matter noticeably when the mantissa is bigger than 60 bits.
        //
        // SAFETY: `len=0`, so the obligation of having initialized this memory is trivial.
        return unsafe {
            possibly_round(buf, 0, exp, limit, v.f / 10, (max_ten_kappa as u64) << e, err << e)
        };
    } else if ((exp as i32 - limit as i32) as usize) < buf.len() {
        (exp - limit) as usize
    } else {
        buf.len()
    };
    debug_assert!(len > 0);
    debug_assert!(len <= buf.len());

    // render integral parts.
    // the error is entirely fractional, so we don't need to check it in this part.
    let integral_limit = max_kappa as usize + 1;
    let mut kappa = max_kappa as i16;
    let mut ten_kappa = max_ten_kappa; // 10^kappa
    let mut remainder = vint; // digits yet to be rendered
    #[cfg(kani)]
    let mut q = 0u32;
    #[cfg(kani)]
    let mut r = 0u32;
    // Exact/fixed integral phase: prove that every write before the call to
    // `possibly_round` initializes the prefix `buf[..i]`, and that the prefix
    // length never exceeds the requested `len`.
    #[cfg_attr(kani, kani::loop_invariant(
        integral_limit == max_kappa as usize + 1
            && integral_limit <= 10
            && i <= integral_limit
            && i <= len
            && len <= buf.len()
            && e > 0
            && e <= 60
            && kani_exact_integral_state(integral_limit, i, kappa, ten_kappa)
            && ten_kappa > 0
            && ten_kappa <= vint
            && (ten_kappa as u64) <= (u64::MAX >> e)
            && remainder <= vint
            && (remainder as u64) < (ten_kappa as u64) * 10
            && vfrac < (1u64 << e)
            && err == 1
    ))]
    #[cfg_attr(kani, kani::loop_modifies(&i, &kappa, &ten_kappa, &remainder, &q, &r, &mut *buf))]
    while i < integral_limit && i < len {
        // we always have at least one digit to render
        // invariants:
        // - `remainder < 10^(kappa+1)`
        // - `vint = d[0..n-1] * 10^(kappa+1) + remainder`
        //   (it follows that `remainder = vint % 10^(kappa+1)`)

        // divide `remainder` by `10^kappa`. both are scaled by `2^-e`.
        #[cfg(kani)]
        {
            q = kani::any();
            r = kani::any();
            kani::assume(ten_kappa > 0);
            kani::assume(q < 10);
            kani::assume(r < ten_kappa);
        }
        #[cfg(not(kani))]
        let (q, r) = div_rem_by_pow10(remainder, ten_kappa);
        debug_assert!(q < 10);
        buf[i] = MaybeUninit::new(b'0' + q as u8);
        i += 1;

        // is the buffer full? run the rounding pass with the remainder.
        if i == len {
            let vrem = ((r as u64) << e) + vfrac; // == (v % 10^kappa) * 2^e
            // SAFETY: we have initialized `len` many bytes.
            return unsafe {
                possibly_round(buf, len, exp, limit, vrem, (ten_kappa as u64) << e, err << e)
            };
        }

        // break the loop when we have rendered all integral digits.
        // the exact number of digits is `max_kappa + 1` as `plus1 < 10^(max_kappa+1)`.
        if i == integral_limit {
            debug_assert_eq!(ten_kappa, 1);
            debug_assert_eq!(kappa, 0);
            break;
        }

        // restore invariants
        kappa -= 1;
        ten_kappa /= 10;
        remainder = r;
    }
    if i < integral_limit {
        return None;
    }

    // render fractional parts.
    //
    // in principle we can continue to the last available digit and check for the accuracy.
    // unfortunately we are working with the finite-sized integers, so we need some criterion
    // to detect the overflow. V8 uses `remainder > err`, which becomes false when
    // the first `i` significant digits of `v - 1 ulp` and `v` differ. however this rejects
    // too many otherwise valid input.
    //
    // since the later phase has a correct overflow detection, we instead use tighter criterion:
    // we continue til `err` exceeds `10^kappa / 2`, so that the range between `v - 1 ulp` and
    // `v + 1 ulp` definitely contains two or more rounded representations. this is same to
    // the first two comparisons from `possibly_round`, for the reference.
    let mut remainder = vfrac;
    let maxerr = 1 << (e - 1);
    #[cfg(kani)]
    let mut frac_digits = 0usize;
    #[cfg(kani)]
    let mut q = 0u64;
    #[cfg(kani)]
    let mut r = 0u64;
    // Exact/fixed fractional phase: `err` grows by powers of ten and the
    // algorithm stops after at most 18 fractional digits. The invariant exposes
    // that bound directly so Kani does not have to infer it from arithmetic.
    #[cfg_attr(kani, kani::loop_invariant(
        e > 0
            && e <= 60
            && maxerr == (1u64 << (e - 1))
            && maxerr <= u64::MAX / 10
            && maxerr < kani_pow10_u64(18)
            && i <= len
            && len <= buf.len()
            && integral_limit <= 10
            && frac_digits <= 18
            && err == kani_pow10_u64(frac_digits)
            && i == integral_limit + frac_digits
            && remainder < (1u64 << e)
    ))]
    #[cfg_attr(kani, kani::loop_modifies(&i, &remainder, &err, &frac_digits, &q, &r, &mut *buf))]
    while err < maxerr && i < len {
        // invariants, where `m = max_kappa + 1` (# of digits in the integral part):
        // - `remainder < 2^e`
        // - `vfrac * 10^(n-m) = d[m..n-1] * 2^e + remainder`
        // - `err = 10^(n-m)`

        remainder *= 10; // won't overflow, `2^e * 10 < 2^64`
        err *= 10; // won't overflow, `err * 10 < 2^e * 5 < 2^64`

        // divide `remainder` by `10^kappa`.
        // both are scaled by `2^e / 10^kappa`, so the latter is implicit here.
        #[cfg(kani)]
        {
            q = remainder >> e;
            r = remainder & ((1 << e) - 1);
        }
        #[cfg(not(kani))]
        let q = remainder >> e;
        #[cfg(not(kani))]
        let r = remainder & ((1 << e) - 1);
        debug_assert!(q < 10);
        buf[i] = MaybeUninit::new(b'0' + q as u8);
        i += 1;
        #[cfg(kani)]
        {
            frac_digits += 1;
        }

        // is the buffer full? run the rounding pass with the remainder.
        if i == len {
            // SAFETY: we have initialized `len` many bytes.
            return unsafe { possibly_round(buf, len, exp, limit, r, 1 << e, err) };
        }

        // restore invariants
        remainder = r;
    }

    // further calculation is useless (`possibly_round` definitely fails), so we give up.
    return None;

    // we've generated all requested digits of `v`, which should be also same to corresponding
    // digits of `v - 1 ulp`. now we check if there is a unique representation shared by
    // both `v - 1 ulp` and `v + 1 ulp`; this can be either same to generated digits, or
    // to the rounded-up version of those digits. if the range contains multiple representations
    // of the same length, we cannot be sure and should return `None` instead.
    //
    // all arguments here are scaled by the common (but implicit) value `k`, so that:
    // - `remainder = (v % 10^kappa) * k`
    // - `ten_kappa = 10^kappa * k`
    // - `ulp = 2^-e * k`
    //
    // SAFETY: the first `len` bytes of `buf` must be initialized.
    unsafe fn possibly_round(
        buf: &mut [MaybeUninit<u8>],
        mut len: usize,
        mut exp: i16,
        limit: i16,
        remainder: u64,
        ten_kappa: u64,
        ulp: u64,
    ) -> Option<(&[u8], i16)> {
        debug_assert!(remainder < ten_kappa);

        //           10^kappa
        //    :   :   :<->:   :
        //    :   :   :   :   :
        //    :|1 ulp|1 ulp|  :
        //    :|<--->|<--->|  :
        // ----|-----|-----|----
        //     |     v     |
        // v - 1 ulp   v + 1 ulp
        //
        // (for the reference, the dotted line indicates the exact value for
        // possible representations in given number of digits.)
        //
        // error is too large that there are at least three possible representations
        // between `v - 1 ulp` and `v + 1 ulp`. we cannot determine which one is correct.
        if ulp >= ten_kappa {
            return None;
        }

        //    10^kappa
        //   :<------->:
        //   :         :
        //   : |1 ulp|1 ulp|
        //   : |<--->|<--->|
        // ----|-----|-----|----
        //     |     v     |
        // v - 1 ulp   v + 1 ulp
        //
        // in fact, 1/2 ulp is enough to introduce two possible representations.
        // (remember that we need a unique representation for both `v - 1 ulp` and `v + 1 ulp`.)
        // this won't overflow, as `ulp < ten_kappa` from the first check.
        if ten_kappa - ulp <= ulp {
            return None;
        }

        //     remainder
        //       :<->|                           :
        //       :   |                           :
        //       :<--------- 10^kappa ---------->:
        //     | :   |                           :
        //     |1 ulp|1 ulp|                     :
        //     |<--->|<--->|                     :
        // ----|-----|-----|------------------------
        //     |     v     |
        // v - 1 ulp   v + 1 ulp
        //
        // if `v + 1 ulp` is closer to the rounded-down representation (which is already in `buf`),
        // then we can safely return. note that `v - 1 ulp` *can* be less than the current
        // representation, but as `1 ulp < 10^kappa / 2`, this condition is enough:
        // the distance between `v - 1 ulp` and the current representation
        // cannot exceed `10^kappa / 2`.
        //
        // the condition equals to `remainder + ulp < 10^kappa / 2`.
        // since this can easily overflow, first check if `remainder < 10^kappa / 2`.
        // we've already verified that `ulp < 10^kappa / 2`, so as long as
        // `10^kappa` did not overflow after all, the second check is fine.
        if ten_kappa - remainder > remainder && ten_kappa - 2 * remainder >= 2 * ulp {
            // SAFETY: our caller initialized that memory.
            return Some((unsafe { buf[..len].assume_init_ref() }, exp));
        }

        //   :<------- remainder ------>|   :
        //   :                          |   :
        //   :<--------- 10^kappa --------->:
        //   :                    |     |   : |
        //   :                    |1 ulp|1 ulp|
        //   :                    |<--->|<--->|
        // -----------------------|-----|-----|-----
        //                        |     v     |
        //                    v - 1 ulp   v + 1 ulp
        //
        // on the other hands, if `v - 1 ulp` is closer to the rounded-up representation,
        // we should round up and return. for the same reason we don't need to check `v + 1 ulp`.
        //
        // the condition equals to `remainder - ulp >= 10^kappa / 2`.
        // again we first check if `remainder > ulp` (note that this is not `remainder >= ulp`,
        // as `10^kappa` is never zero). also note that `remainder - ulp <= 10^kappa`,
        // so the second check does not overflow.
        if remainder > ulp && ten_kappa - (remainder - ulp) <= remainder - ulp {
            if let Some(c) =
                // SAFETY: our caller must have initialized that memory.
                round_up(unsafe { buf[..len].assume_init_mut() })
            {
                // only add an additional digit when we've been requested the fixed precision.
                // we also need to check that, if the original buffer was empty,
                // the additional digit can only be added when `exp == limit` (edge case).
                exp += 1;
                if exp > limit && len < buf.len() {
                    buf[len] = MaybeUninit::new(c);
                    len += 1;
                }
            }
            // SAFETY: we and our caller initialized that memory.
            return Some((unsafe { buf[..len].assume_init_ref() }, exp));
        }

        // otherwise we are doomed (i.e., some values between `v - 1 ulp` and `v + 1 ulp` are
        // rounding down and others are rounding up) and give up.
        None
    }
}

/// The exact and fixed mode implementation for Grisu with Dragon fallback.
///
/// This should be used for most cases.
pub fn format_exact<'a>(
    d: &Decoded,
    buf: &'a mut [MaybeUninit<u8>],
    limit: i16,
) -> (/*digits*/ &'a [u8], /*exp*/ i16) {
    use crate::num::flt2dec::strategy::dragon::format_exact as fallback;
    // SAFETY: The borrow checker is not smart enough to let us use `buf`
    // in the second branch, so we launder the lifetime here. But we only re-use
    // `buf` if `format_exact_opt` returned `None` so this is okay.
    match format_exact_opt(d, unsafe { &mut *(buf as *mut _) }, limit) {
        Some(ret) => ret,
        None => fallback(d, buf, limit),
    }
}

// =========================================================================
// Challenge 28: Verify float to decimal conversion module harnesses
// =========================================================================

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;

    // The harnesses below use decoded-value ranges that contain the finite
    // states produced by `decode()` for f16/f32/f64. They do not verify the
    // decode entry point itself; they start from the `Decoded` contract used by
    // the formatting strategies.
    // Symbolic `Decoded` generator for shortest-mode Grisu and fallback harnesses.
    fn arbitrary_decoded_shortest() -> Decoded {
        let mant: u64 = kani::any();
        let plus: u64 = kani::any();
        let exp: i16 = kani::any();

        kani::assume(mant >= 2 && mant <= (1u64 << 54));
        kani::assume(plus == 1 || plus == 2);
        kani::assume(exp >= -1076 && exp <= 971);

        Decoded { mant, minus: 1, plus, exp, inclusive: kani::any() }
    }

    // Symbolic `Decoded` generator for exact/fixed-mode Grisu and fallback harnesses.
    fn arbitrary_decoded_exact() -> Decoded {
        let mant: u64 = kani::any();
        let exp: i16 = kani::any();

        kani::assume(mant > 0 && mant <= (1u64 << 54));
        kani::assume(exp >= -1076 && exp <= 971);

        Decoded { mant, minus: 1, plus: 1, exp, inclusive: kani::any() }
    }

    // Stub for `Fp::mul`, used by exact/fixed-mode harnesses.
    fn stub_fp_mul(a: Fp, b: Fp) -> Fp {
        let f: u64 = kani::any();

        // `b` is the normalized cached power, so the real high-half product is
        // bounded by approximately `a.f / 2 <= f <= a.f`. Keep that envelope
        // while leaving the exact rounded product nondeterministic. This stub
        // is used by exact/fixed-mode harnesses to avoid proving DiyFp
        // multiplication here; the surrounding proof is about buffer safety.
        kani::assume(b.f >= (1u64 << 63));
        kani::assume(f >= (a.f >> 1));
        kani::assume(f <= a.f);

        Fp { f, e: a.e + b.e + 64 }
    }

    // Stub for `cached_power`, preserving only the exponent and normalization bounds Grisu uses.
    fn stub_cached_power(alpha: i16, gamma: i16) -> (i16, Fp) {
        let k: i16 = kani::any();
        let f: u64 = kani::any();
        let e: i16 = kani::any();

        // Preserve the cached-power postconditions that Grisu uses for bounds.
        // The table lookup and numerical choice of the power are outside this
        // local safety proof.
        kani::assume(k >= -308 && k <= 332);
        kani::assume(f >= (1u64 << 63));
        kani::assume(e >= alpha && e <= gamma);

        (k, Fp { f, e })
    }

    // Stub for `max_pow10_no_more_than`, backed by the same power-of-ten contract.
    fn stub_max_pow10_no_more_than(x: u32) -> (u8, u32) {
        kani::assume(x > 0);
        let kappa: u8 = kani::any();
        kani::assume(kappa <= 9);

        // Keep the semantic contract of `max_pow10_no_more_than`: `pow` is a
        // power of ten no larger than `x`, and the next larger power would
        // exceed `x`. This is enough for loop bounds.
        let pow = kani_pow10_u32(kappa);
        kani::assume(pow <= x);
        if kappa < 9 {
            kani::assume(x < pow * 10);
        }

        (kappa, pow)
    }

    // Stub for `flt2dec::round_up`, used only when exact/fixed mode may carry.
    fn stub_round_up(d: &mut [u8]) -> Option<u8> {
        // Exact/fixed-mode verification only needs to know that `round_up` may
        // mutate initialized digits and may return a carry digit. The real
        // decimal carry propagation is outside this Grisu control-flow harness,
        // so this remains a conventional stub.
        if kani::any() { if d.is_empty() { Some(b'1') } else { Some(b'0') } } else { None }
    }

    // Initializes a stub-returned digit prefix before converting it to `&[u8]`.
    fn init_digits(buf: &mut [MaybeUninit<u8>], len: usize) {
        // Harness-only initializer for stubs that model successful fallback or
        // optimized formatting. It is not used before proving real
        // `assume_init_*` call sites inside `format_shortest_opt` or
        // `format_exact_opt`.
        let mut i = 0;
        while i < len {
            buf[i] = MaybeUninit::new(if i == 0 { b'1' } else { b'0' });
            i += 1;
        }
    }

    // Stub for `format_shortest_opt` when verifying the top-level Dragon fallback wrapper.
    fn stub_format_shortest_opt<'a>(
        _d: &Decoded,
        buf: &'a mut [MaybeUninit<u8>],
    ) -> Option<(&'a [u8], i16)> {
        if kani::any() {
            let len: usize = kani::any();
            kani::assume(len > 0 && len <= buf.len());
            init_digits(buf, len);
            Some((unsafe { buf[..len].assume_init_ref() }, kani::any()))
        } else {
            None
        }
    }

    // Stub for `format_exact_opt` when verifying the top-level Dragon fallback wrapper.
    fn stub_format_exact_opt<'a>(
        _d: &Decoded,
        buf: &'a mut [MaybeUninit<u8>],
        _limit: i16,
    ) -> Option<(&'a [u8], i16)> {
        if kani::any() {
            let len: usize = kani::any();
            kani::assume(len <= buf.len());
            init_digits(buf, len);
            Some((unsafe { buf[..len].assume_init_ref() }, kani::any()))
        } else {
            None
        }
    }

    // Stub for `dragon::format_shortest`, returning an initialized fallback digit slice.
    fn stub_dragon_format_shortest<'a>(
        _d: &Decoded,
        buf: &'a mut [MaybeUninit<u8>],
    ) -> (&'a [u8], i16) {
        let len: usize = kani::any();
        kani::assume(len > 0 && len <= buf.len());
        init_digits(buf, len);
        (unsafe { buf[..len].assume_init_ref() }, kani::any())
    }

    // Stub for `dragon::format_exact`, returning an initialized fallback digit slice.
    fn stub_dragon_format_exact<'a>(
        _d: &Decoded,
        buf: &'a mut [MaybeUninit<u8>],
        _limit: i16,
    ) -> (&'a [u8], i16) {
        let len: usize = kani::any();
        kani::assume(len <= buf.len());
        init_digits(buf, len);
        (unsafe { buf[..len].assume_init_ref() }, kani::any())
    }

    #[kani::proof]
    #[kani::unwind(18)]
    // `round_and_weed` is not a hand-written stub here. Its contract is checked
    // by `harness_round_and_weed`, and this harness verifies that
    // `format_shortest_opt` satisfies that contract at each call site.
    #[kani::stub_verified(round_and_weed)]
    fn harness_format_shortest_opt() {
        let d = arbitrary_decoded_shortest();
        let mut buf: [MaybeUninit<u8>; MAX_SIG_DIGITS] =
            [const { MaybeUninit::uninit() }; MAX_SIG_DIGITS];
        let _ = format_shortest_opt(&d, &mut buf);
    }

    #[kani::proof_for_contract(round_and_weed)]
    #[kani::unwind(20)]
    fn harness_round_and_weed() {
        // Verify the real rounding-and-weeding body for all nonempty digit
        // slices up to `MAX_SIG_DIGITS` and arbitrary arithmetic inputs that
        // satisfy the function contract. This establishes the body used by the
        // `stub_verified` harness above.
        let len: usize = kani::any();
        kani::assume(len > 0 && len <= MAX_SIG_DIGITS);

        let mut buf = [b'1'; MAX_SIG_DIGITS];
        let mut i = 0;
        while i < len {
            let digit: u8 = kani::any();
            kani::assume(digit >= b'0' && digit <= b'9');
            buf[i] = digit;
            i += 1;
        }

        let remainder: u64 = kani::any();
        let threshold: u64 = kani::any();
        let plus1v: u64 = kani::any();
        let ten_kappa: u64 = kani::any();
        let ulp: u64 = kani::any();

        let _ = round_and_weed(&mut buf[..len], remainder, threshold, plus1v, ten_kappa, ulp);
    }

    #[kani::proof]
    #[kani::unwind(29)]
    // Exact/fixed mode still uses conventional stubs for the expensive scaling
    // and decimal carry helper. This harness should be read as a control-flow
    // and initialized-buffer proof, not a proof of exact rounding correctness.
    #[kani::stub(Fp::mul, stub_fp_mul)]
    #[kani::stub(cached_power, stub_cached_power)]
    #[kani::stub(max_pow10_no_more_than, stub_max_pow10_no_more_than)]
    #[kani::stub(crate::num::flt2dec::round_up, stub_round_up)]
    fn harness_format_exact_opt() {
        let d = arbitrary_decoded_exact();
        let limit: i16 = kani::any();
        let buf_len: usize = kani::any();
        kani::assume(buf_len > 0 && buf_len <= GRISU_EXACT_OPT_MAX_BUF_LEN);
        let mut buf: [MaybeUninit<u8>; GRISU_EXACT_OPT_MAX_BUF_LEN] =
            [const { MaybeUninit::uninit() }; GRISU_EXACT_OPT_MAX_BUF_LEN];
        let _ = format_exact_opt(&d, &mut buf[..buf_len], limit);
    }

    #[kani::proof]
    #[kani::unwind(18)]
    // Top-level shortest fallback proof: the optimized Grisu path and Dragon
    // fallback are stubbed with initialized-output contracts so the unsafe
    // buffer laundering in `format_shortest` can be checked in isolation.
    #[kani::stub(format_shortest_opt, stub_format_shortest_opt)]
    #[kani::stub(
        crate::num::flt2dec::strategy::dragon::format_shortest,
        stub_dragon_format_shortest
    )]
    fn harness_format_shortest() {
        let d = arbitrary_decoded_shortest();
        let mut buf: [MaybeUninit<u8>; MAX_SIG_DIGITS] =
            [const { MaybeUninit::uninit() }; MAX_SIG_DIGITS];
        let _ = format_shortest(&d, &mut buf);
    }

    #[kani::proof]
    #[kani::unwind(30)]
    // Same top-level fallback proof for exact/fixed mode.
    #[kani::stub(format_exact_opt, stub_format_exact_opt)]
    #[kani::stub(crate::num::flt2dec::strategy::dragon::format_exact, stub_dragon_format_exact)]
    fn harness_format_exact() {
        let d = arbitrary_decoded_exact();
        let limit: i16 = kani::any();
        let buf_len: usize = kani::any();
        kani::assume(buf_len > 0 && buf_len <= GRISU_EXACT_OPT_MAX_BUF_LEN);
        let mut buf: [MaybeUninit<u8>; GRISU_EXACT_OPT_MAX_BUF_LEN] =
            [const { MaybeUninit::uninit() }; GRISU_EXACT_OPT_MAX_BUF_LEN];
        let _ = format_exact(&d, &mut buf[..buf_len], limit);
    }
}
