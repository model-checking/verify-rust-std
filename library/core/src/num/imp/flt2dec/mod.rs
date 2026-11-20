/*!

Floating-point number to decimal conversion routines.

# Problem statement

We are given the floating-point number `v = f * 2^e` with an integer `f`,
and its bounds `minus` and `plus` such that any number between `v - minus` and
`v + plus` will be rounded to `v`. For the simplicity we assume that
this range is exclusive. Then we would like to get the unique decimal
representation `V = 0.d[0..n-1] * 10^k` such that:

- `d[0]` is non-zero.

- It's correctly rounded when parsed back: `v - minus < V < v + plus`.
  Furthermore it is shortest such one, i.e., there is no representation
  with less than `n` digits that is correctly rounded.

- It's closest to the original value: `abs(V - v) <= 10^(k-n) / 2`. Note that
  there might be two representations satisfying this uniqueness requirement,
  in which case some tie-breaking mechanism is used.

We will call this mode of operation as to the *shortest* mode. This mode is used
when there is no additional constraint, and can be thought as a "natural" mode
as it matches the ordinary intuition (it at least prints `0.1f32` as "0.1").

We have two more modes of operation closely related to each other. In these modes
we are given either the number of significant digits `n` or the last-digit
limitation `limit` (which determines the actual `n`), and we would like to get
the representation `V = 0.d[0..n-1] * 10^k` such that:

- `d[0]` is non-zero, unless `n` was zero in which case only `k` is returned.

- It's closest to the original value: `abs(V - v) <= 10^(k-n) / 2`. Again,
  there might be some tie-breaking mechanism.

When `limit` is given but not `n`, we set `n` such that `k - n = limit`
so that the last digit `d[n-1]` is scaled by `10^(k-n) = 10^limit`.
If such `n` is negative, we clip it to zero so that we will only get `k`.
We are also limited by the supplied buffer. This limitation is used to print
the number up to given number of fractional digits without knowing
the correct `k` beforehand.

We will call the mode of operation requiring `n` as to the *exact* mode,
and one requiring `limit` as to the *fixed* mode. The exact mode is a subset of
the fixed mode: the sufficiently large last-digit limitation will eventually fill
the supplied buffer and let the algorithm to return.

# Implementation overview

It is easy to get the floating point printing correct but slow (Russ Cox has
[demonstrated](https://research.swtch.com/ftoa) how it's easy), or incorrect but
fast (naïve division and modulo). But it is surprisingly hard to print
floating point numbers correctly *and* efficiently.

There are two classes of algorithms widely known to be correct.

- The "Dragon" family of algorithm is first described by Guy L. Steele Jr. and
  Jon L. White. They rely on the fixed-size big integer for their correctness.
  A slight improvement was found later, which is posthumously described by
  Robert G. Burger and R. Kent Dybvig. David Gay's `dtoa.c` routine is
  a popular implementation of this strategy.

- The "Grisu" family of algorithm is first described by Florian Loitsch.
  They use very cheap integer-only procedure to determine the close-to-correct
  representation which is at least guaranteed to be shortest. The variant,
  Grisu3, actively detects if the resulting representation is incorrect.

We implement both algorithms with necessary tweaks to suit our requirements.
In particular, published literatures are short of the actual implementation
difficulties like how to avoid arithmetic overflows. Each implementation,
available in `strategy::dragon` and `strategy::grisu` respectively,
extensively describes all necessary justifications and many proofs for them.
(It is still difficult to follow though. You have been warned.)

Both implementations expose two public functions:

- `format_shortest(decoded, buf)`, which always needs at least
  `MAX_SIG_DIGITS` digits of buffer. Implements the shortest mode.

- `format_exact(decoded, buf, limit)`, which accepts as small as
  one digit of buffer. Implements exact and fixed modes.

They try to fill the `u8` buffer with digits and returns the number of digits
written and the exponent `k`. They are total for all finite `f32` and `f64`
inputs (Grisu internally falls back to Dragon if necessary).

The rendered digits are formatted into the actual string form with
four functions:

- `to_shortest_str` prints the shortest representation, which can be padded by
  zeroes to make *at least* given number of fractional digits.

- `to_shortest_exp_str` prints the shortest representation, which can be
  padded by zeroes when its exponent is in the specified ranges,
  or can be printed in the exponential form such as `1.23e45`.

- `to_exact_exp_str` prints the exact representation with given number of
  digits in the exponential form.

- `to_exact_fixed_str` prints the fixed representation with *exactly*
  given number of fractional digits.

They all return a slice of preallocated `Part` array, which corresponds to
the individual part of strings: a fixed string, a part of rendered digits,
a number of zeroes or a small (`u16`) number. The caller is expected to
provide a large enough buffer and `Part` array, and to assemble the final
string from resulting `Part`s itself.

All algorithms and formatting functions are accompanied by extensive tests
in `coretests::num::flt2dec` module. It also shows how to use individual
functions.

*/

// while this is extensively documented, this is in principle private which is
// only made public for testing. do not expose us.
#![doc(hidden)]
#![unstable(
    feature = "flt2dec",
    reason = "internal routines only exposed for testing",
    issue = "none"
)]

pub use self::decoder::{DecodableFloat, Decoded, FullDecoded, decode};
use super::fmt::{Formatted, Part};
use crate::mem::MaybeUninit;

pub mod decoder;
pub mod estimator;

/// Digit-generation algorithms.
pub mod strategy {
    pub mod dragon;
    pub mod grisu;
}

/// Ghost state shared by the proof harnesses, loop invariants and safety checks of the
/// digit-generation strategies.
///
/// What those proofs must establish is that `buf[..n]` has been written by the time it is passed to
/// `assume_init_*`. Neither a loop invariant nor Kani's own initialization checks (which do not
/// support slices of `MaybeUninit`) can say "this memory is initialized" directly, so the proofs
/// track a property of the bytes instead: every byte the strategies store is at least `b'0'`,
/// while a byte that was never stored keeps the value the harness gave it, and the harnesses
/// start from buffers with arbitrary contents (`any_buf`). The index `w` is picked
/// nondeterministically by the harness before the call, which keeps the invariants free of
/// quantifiers. What Kani proves is thus: whatever the buffer contains initially,
/// `buf[w] >= b'0'` holds for every `w < n` at every `assume_init_*` call on `buf[..n]`.
///
/// This implies that a real run, on a buffer that is uninitialized, never reads a byte it has
/// not written. The strategies read the buffer only through those `assume_init_*` calls, so up
/// to the first such read the run does not depend on what the buffer contained initially, and
/// it is also a run of the harness for every choice of initial contents. If that read covered a
/// byte `w` that was never written, the choice with a zero at `w` would violate the property.
/// So the read covers only bytes the run has written, the run still does not depend on the
/// initial contents after it, and the same reasoning applies to the next read.
///
/// "A run of the harness" has two qualifications. The harnesses replace some safe arithmetic
/// helpers by models (see the `verify` modules); these allow everything the helpers can do, so
/// the real run is still among the runs of the harness. And Kani checks arithmetic overflow and
/// `debug_assert!`, so the argument does not cover a run that continues past either of them, as
/// a release build would.
#[cfg(kani)]
pub(crate) mod ghost {
    use crate::mem::MaybeUninit;

    /// The index whose initialization is being tracked. Set once per harness to `kani::any()`.
    static mut WITNESS: usize = 0;

    /// Starts tracking an arbitrary index.
    pub(crate) fn pick_witness() {
        // SAFETY: the harnesses are single-threaded.
        unsafe { WITNESS = crate::kani::any() };
    }

    /// The tracked index.
    pub(crate) fn witness() -> usize {
        // SAFETY: the harnesses are single-threaded.
        unsafe { WITNESS }
    }

    /// A digit buffer for a harness: `N` bytes with arbitrary contents.
    ///
    /// The bytes are deliberately not `MaybeUninit::uninit()`: the proofs then hold for every
    /// initial contents by construction, and do not depend on how Kani models memory that was
    /// never written.
    pub(crate) fn any_buf<const N: usize>() -> [MaybeUninit<u8>; N] {
        let bytes: [u8; N] = crate::kani::any();
        // SAFETY: `[u8; N]` and `[MaybeUninit<u8>; N]` have the same layout, and every `u8` is a
        // valid `MaybeUninit<u8>`.
        unsafe { (&raw const bytes).cast::<[MaybeUninit<u8>; N]>().read() }
    }

    /// `buf[..n]` has been written, as far as the witness index can tell.
    pub(crate) fn written(buf: &[MaybeUninit<u8>], n: usize) -> bool {
        let w = witness();
        // SAFETY: the harnesses make their buffers with `any_buf`, so every byte holds a value.
        w >= n || w >= buf.len() || unsafe { buf[w].assume_init() } >= b'0'
    }

    /// The proof obligation of an `assume_init_*` call on `buf[..n]`.
    ///
    /// A violation is reported through `assert_unchecked` rather than `assert!`, so that it is
    /// undefined behavior and not a panic: the strategy harnesses are `#[kani::should_panic]`,
    /// which accepts panics but nothing else.
    pub(crate) fn assert_written(buf: &[MaybeUninit<u8>], n: usize) {
        // SAFETY: none is claimed. This is the property the harnesses ask Kani to prove, and
        // Kani reports a violation as a failed check.
        unsafe { crate::hint::assert_unchecked(written(buf, n)) };
    }
}

/// The minimum size of buffer necessary for the shortest mode.
///
/// It is a bit non-trivial to derive, but this is one plus the maximal number of
/// significant decimal digits from formatting algorithms with the shortest result.
/// The exact formula is `ceil(# bits in mantissa * log_10 2 + 1)`.
pub const MAX_SIG_DIGITS: usize = 17;

/// When `d` contains decimal digits, increase the last digit and propagate carry.
/// Returns a next digit when it causes the length to change.
#[doc(hidden)]
pub fn round_up(d: &mut [u8]) -> Option<u8> {
    match d.iter().rposition(|&c| c != b'9') {
        Some(i) => {
            // d[i+1..n] is all nines
            d[i] += 1;
            d[i + 1..].fill(b'0');
            None
        }
        None if d.is_empty() => {
            // an empty buffer rounds up (a bit strange but reasonable)
            Some(b'1')
        }
        None => {
            // 999..999 rounds to 1000..000 with an increased exponent
            d[0] = b'1';
            d[1..].fill(b'0');
            Some(b'0')
        }
    }
}

/// Formats given decimal digits `0.<...buf...> * 10^exp` into the decimal form
/// with at least given number of fractional digits. The result is stored to
/// the supplied parts array and a slice of written parts is returned.
///
/// `frac_digits` can be less than the number of actual fractional digits in `buf`;
/// it will be ignored and full digits will be printed. It is only used to print
/// additional zeroes after rendered digits. Thus `frac_digits` of 0 means that
/// it will only print given digits and nothing else.
fn digits_to_dec_str<'a>(
    buf: &'a [u8],
    exp: i16,
    frac_digits: usize,
    parts: &'a mut [MaybeUninit<Part<'a>>],
) -> &'a [Part<'a>] {
    assert!(!buf.is_empty());
    assert!(buf[0] > b'0');
    assert!(parts.len() >= 4);

    // if there is the restriction on the last digit position, `buf` is assumed to be
    // left-padded with the virtual zeroes. the number of virtual zeroes, `nzeroes`,
    // equals to `max(0, exp + frac_digits - buf.len())`, so that the position of
    // the last digit `exp - buf.len() - nzeroes` is no more than `-frac_digits`:
    //
    //                       |<-virtual->|
    //       |<---- buf ---->|  zeroes   |     exp
    //    0. 1 2 3 4 5 6 7 8 9 _ _ _ _ _ _ x 10
    //    |                  |           |
    // 10^exp    10^(exp-buf.len())   10^(exp-buf.len()-nzeroes)
    //
    // `nzeroes` is individually calculated for each case in order to avoid overflow.

    if exp <= 0 {
        // the decimal point is before rendered digits: [0.][000...000][1234][____]
        let minus_exp = -(exp as i32) as usize;
        parts[0] = MaybeUninit::new(Part::Copy(b"0."));
        parts[1] = MaybeUninit::new(Part::Zero(minus_exp));
        parts[2] = MaybeUninit::new(Part::Copy(buf));
        if frac_digits > buf.len() && frac_digits - buf.len() > minus_exp {
            parts[3] = MaybeUninit::new(Part::Zero((frac_digits - buf.len()) - minus_exp));
            // SAFETY: we just initialized the elements `..4`.
            unsafe { parts[..4].assume_init_ref() }
        } else {
            // SAFETY: we just initialized the elements `..3`.
            unsafe { parts[..3].assume_init_ref() }
        }
    } else {
        let exp = exp as usize;
        if exp < buf.len() {
            // the decimal point is inside rendered digits: [12][.][34][____]
            parts[0] = MaybeUninit::new(Part::Copy(&buf[..exp]));
            parts[1] = MaybeUninit::new(Part::Copy(b"."));
            parts[2] = MaybeUninit::new(Part::Copy(&buf[exp..]));
            if frac_digits > buf.len() - exp {
                parts[3] = MaybeUninit::new(Part::Zero(frac_digits - (buf.len() - exp)));
                // SAFETY: we just initialized the elements `..4`.
                unsafe { parts[..4].assume_init_ref() }
            } else {
                // SAFETY: we just initialized the elements `..3`.
                unsafe { parts[..3].assume_init_ref() }
            }
        } else {
            // the decimal point is after rendered digits: [1234][____0000] or [1234][__][.][__].
            parts[0] = MaybeUninit::new(Part::Copy(buf));
            parts[1] = MaybeUninit::new(Part::Zero(exp - buf.len()));
            if frac_digits > 0 {
                parts[2] = MaybeUninit::new(Part::Copy(b"."));
                parts[3] = MaybeUninit::new(Part::Zero(frac_digits));
                // SAFETY: we just initialized the elements `..4`.
                unsafe { parts[..4].assume_init_ref() }
            } else {
                // SAFETY: we just initialized the elements `..2`.
                unsafe { parts[..2].assume_init_ref() }
            }
        }
    }
}

/// Formats the given decimal digits `0.<...buf...> * 10^exp` into the exponential
/// form with at least the given number of fractional digits. When `upper` is `true`,
/// the exponent will be prefixed by `E`; otherwise that's `e`. The result is
/// stored to the supplied parts array and a slice of written parts is returned.
///
/// `frac_digits` can be less than the number of actual fractional digits in `buf`;
/// it will be ignored and full digits will be printed. It is only used to print
/// additional zeroes after rendered digits. Thus, `frac_digits == 0` means that
/// it will only print the given digits and nothing else.
///
/// For example, `buf = b"123", exp = 3, frac_digits = 4` yields the parts for
/// `1.2300e2`.
fn digits_to_exp_str<'a>(
    buf: &'a [u8],
    exp: i16,
    frac_digits: usize,
    upper: bool,
    parts: &'a mut [MaybeUninit<Part<'a>>],
) -> &'a [Part<'a>] {
    assert!(!buf.is_empty());
    assert!(buf[0] > b'0');
    assert!(parts.len() >= 6);

    let mut n = 0;

    parts[n] = MaybeUninit::new(Part::Copy(&buf[..1]));
    n += 1;

    // The first generated digit becomes the integral digit, anything after that is already part of
    // the fractional portion we can emit verbatim.
    let actual_frac_digits = buf.len() - 1;
    if actual_frac_digits > 0 || frac_digits > 0 {
        // Emit a decimal point either when we already have fractional digits or when the requested
        // precision needs trailing zeroes after the radix point.
        parts[n] = MaybeUninit::new(Part::Copy(b"."));
        n += 1;
        if actual_frac_digits > 0 {
            parts[n] = MaybeUninit::new(Part::Copy(&buf[1..]));
            n += 1;
        }
        if frac_digits > actual_frac_digits {
            // format_exact exhausted the meaningful digits, so extend the fractional part with
            // zeroes up to the requested precision.
            parts[n] = MaybeUninit::new(Part::Zero(frac_digits - actual_frac_digits));
            n += 1;
        }
    }

    // 0.1234 x 10^exp = 1.234 x 10^(exp-1)
    let exp = exp as i32 - 1; // avoid underflow when exp is i16::MIN
    if exp < 0 {
        parts[n] = MaybeUninit::new(Part::Copy(if upper { b"E-" } else { b"e-" }));
        parts[n + 1] = MaybeUninit::new(Part::Num(-exp as u16));
    } else {
        parts[n] = MaybeUninit::new(Part::Copy(if upper { b"E" } else { b"e" }));
        parts[n + 1] = MaybeUninit::new(Part::Num(exp as u16));
    }
    // SAFETY: we just initialized the elements `..n + 2`.
    unsafe { parts[..n + 2].assume_init_ref() }
}

/// Sign formatting options.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Sign {
    /// Prints `-` for any negative value.
    Minus, // -inf -1 -0  0  1  inf nan
    /// Prints `-` for any negative value, or `+` otherwise.
    MinusPlus, // -inf -1 -0 +0 +1 +inf nan
}

/// Returns the static byte string corresponding to the sign to be formatted.
/// It can be either `""`, `"+"` or `"-"`.
fn determine_sign(sign: Sign, decoded: &FullDecoded, negative: bool) -> &'static str {
    match (*decoded, sign) {
        (FullDecoded::Nan, _) => "",
        (_, Sign::Minus) => {
            if negative {
                "-"
            } else {
                ""
            }
        }
        (_, Sign::MinusPlus) => {
            if negative {
                "-"
            } else {
                "+"
            }
        }
    }
}

/// Formats the given floating point number into the decimal form with at least
/// given number of fractional digits. The result is stored to the supplied parts
/// array while utilizing given byte buffer as a scratch. `upper` is currently
/// unused but left for the future decision to change the case of non-finite values,
/// i.e., `inf` and `nan`. The first part to be rendered is always a `Part::Sign`
/// (which can be an empty string if no sign is rendered).
///
/// `format_shortest` should be the underlying digit-generation function.
/// It should return the part of the buffer that it initialized.
/// You probably would want `strategy::grisu::format_shortest` for this.
///
/// `frac_digits` can be less than the number of actual fractional digits in `v`;
/// it will be ignored and full digits will be printed. It is only used to print
/// additional zeroes after rendered digits. Thus `frac_digits` of 0 means that
/// it will only print given digits and nothing else.
///
/// The byte buffer should be at least `MAX_SIG_DIGITS` bytes long.
/// There should be at least 4 parts available, due to the worst case like
/// `[+][0.][0000][2][0000]` with `frac_digits = 10`.
pub fn to_shortest_str<'a, T, F>(
    mut format_shortest: F,
    v: T,
    sign: Sign,
    frac_digits: usize,
    buf: &'a mut [MaybeUninit<u8>],
    parts: &'a mut [MaybeUninit<Part<'a>>],
) -> Formatted<'a>
where
    T: DecodableFloat,
    F: FnMut(&Decoded, &'a mut [MaybeUninit<u8>]) -> (&'a [u8], i16),
{
    assert!(parts.len() >= 4);
    assert!(buf.len() >= MAX_SIG_DIGITS);

    let (negative, full_decoded) = decode(v);
    let sign = determine_sign(sign, &full_decoded, negative);
    match full_decoded {
        FullDecoded::Nan => {
            parts[0] = MaybeUninit::new(Part::Copy(b"NaN"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Infinite => {
            parts[0] = MaybeUninit::new(Part::Copy(b"inf"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Zero => {
            if frac_digits > 0 {
                // [0.][0000]
                parts[0] = MaybeUninit::new(Part::Copy(b"0."));
                parts[1] = MaybeUninit::new(Part::Zero(frac_digits));
                Formatted {
                    sign,
                    // SAFETY: we just initialized the elements `..2`.
                    parts: unsafe { parts[..2].assume_init_ref() },
                }
            } else {
                parts[0] = MaybeUninit::new(Part::Copy(b"0"));
                Formatted {
                    sign,
                    // SAFETY: we just initialized the elements `..1`.
                    parts: unsafe { parts[..1].assume_init_ref() },
                }
            }
        }
        FullDecoded::Finite(ref decoded) => {
            let (buf, exp) = format_shortest(decoded, buf);
            Formatted { sign, parts: digits_to_dec_str(buf, exp, frac_digits, parts) }
        }
    }
}

/// Formats the given floating point number into the decimal form or
/// the exponential form, depending on the resulting exponent. The result is
/// stored to the supplied parts array while utilizing given byte buffer
/// as a scratch. `upper` is used to determine the case of non-finite values
/// (`inf` and `nan`) or the case of the exponent prefix (`e` or `E`).
/// The first part to be rendered is always a `Part::Sign` (which can be
/// an empty string if no sign is rendered).
///
/// `format_shortest` should be the underlying digit-generation function.
/// It should return the part of the buffer that it initialized.
/// You probably would want `strategy::grisu::format_shortest` for this.
///
/// The `dec_bounds` is a tuple `(lo, hi)` such that the number is formatted
/// as decimal only when `10^lo <= V < 10^hi`. Note that this is the *apparent* `V`
/// instead of the actual `v`! Thus any printed exponent in the exponential form
/// cannot be in this range, avoiding any confusion.
///
/// The byte buffer should be at least `MAX_SIG_DIGITS` bytes long.
/// There should be at least 6 parts available, due to the worst case like
/// `[+][1][.][2345][e][-][6]`.
pub fn to_shortest_exp_str<'a, T, F>(
    mut format_shortest: F,
    v: T,
    sign: Sign,
    dec_bounds: (i16, i16),
    upper: bool,
    buf: &'a mut [MaybeUninit<u8>],
    parts: &'a mut [MaybeUninit<Part<'a>>],
) -> Formatted<'a>
where
    T: DecodableFloat,
    F: FnMut(&Decoded, &'a mut [MaybeUninit<u8>]) -> (&'a [u8], i16),
{
    assert!(parts.len() >= 6);
    assert!(buf.len() >= MAX_SIG_DIGITS);
    assert!(dec_bounds.0 <= dec_bounds.1);

    let (negative, full_decoded) = decode(v);
    let sign = determine_sign(sign, &full_decoded, negative);
    match full_decoded {
        FullDecoded::Nan => {
            parts[0] = MaybeUninit::new(Part::Copy(b"NaN"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Infinite => {
            parts[0] = MaybeUninit::new(Part::Copy(b"inf"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Zero => {
            parts[0] = if dec_bounds.0 <= 0 && 0 < dec_bounds.1 {
                MaybeUninit::new(Part::Copy(b"0"))
            } else {
                MaybeUninit::new(Part::Copy(if upper { b"0E0" } else { b"0e0" }))
            };
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Finite(ref decoded) => {
            let (buf, exp) = format_shortest(decoded, buf);
            let vis_exp = exp as i32 - 1;
            let parts = if dec_bounds.0 as i32 <= vis_exp && vis_exp < dec_bounds.1 as i32 {
                digits_to_dec_str(buf, exp, 0, parts)
            } else {
                digits_to_exp_str(buf, exp, 0, upper, parts)
            };
            Formatted { sign, parts }
        }
    }
}

/// Returns a rather crude approximation (upper bound) for the maximum buffer size
/// calculated from the given decoded exponent.
///
/// The exact limit is:
///
/// - when `exp < 0`, the maximum length is `ceil(log_10 (5^-exp * (2^64 - 1)))`.
/// - when `exp >= 0`, the maximum length is `ceil(log_10 (2^exp * (2^64 - 1)))`.
///
/// `ceil(log_10 (x^exp * (2^64 - 1)))` is less than `ceil(log_10 (2^64 - 1)) +
/// ceil(exp * log_10 x)`, which is in turn less than `20 + (1 + exp * log_10 x)`.
/// We use the facts that `log_10 2 < 5/16` and `log_10 5 < 12/16`, which is
/// enough for our purposes.
///
/// Why do we need this? `format_exact` functions will fill the entire buffer
/// unless limited by the last digit restriction, but it is possible that
/// the number of digits requested is ridiculously large (say, 30,000 digits).
/// The vast majority of buffer will be filled with zeroes, so we don't want to
/// allocate all the buffer beforehand. Consequently, for any given arguments,
/// 826 bytes of buffer should be sufficient for `f64`. Compare this with
/// the actual number for the worst case: 770 bytes (when `exp = -1074`).
fn estimate_max_buf_len(exp: i16) -> usize {
    21 + ((if exp < 0 { -12 } else { 5 } * exp as i32) as usize >> 4)
}

/// Formats given floating point number into the exponential form with
/// exactly given number of fractional digits. The result is stored to
/// the supplied parts array while utilizing given byte buffer as a scratch.
/// `upper` is used to determine the case of the exponent prefix (`e` or `E`).
/// The first part to be rendered is always a `Part::Sign` (which can be
/// an empty string if no sign is rendered).
///
/// `format_exact` should be the underlying digit-generation function.
/// It should return the part of the buffer that it initialized.
/// You probably would want `strategy::grisu::format_exact` for this.
///
/// The returned format is `[sign][digit][.fraction?][zero padding?][e|E][exponent]`.
///
/// The byte buffer should be at least `frac_digits + 1` bytes long unless
/// `frac_digits` is so large that only the fixed number of digits will be ever written.
/// (The tipping point for `f64` is about 800, so 1000 bytes should be enough.)
/// There should be at least 6 parts available, due to the worst case like
/// `[+][1][.][2345][e][-][6]`.
pub fn to_exact_exp_str<'a, T, F>(
    mut format_exact: F,
    v: T,
    sign: Sign,
    frac_digits: usize,
    upper: bool,
    buf: &'a mut [MaybeUninit<u8>],
    parts: &'a mut [MaybeUninit<Part<'a>>],
) -> Formatted<'a>
where
    T: DecodableFloat,
    F: FnMut(&Decoded, &'a mut [MaybeUninit<u8>], i16) -> (&'a [u8], i16),
{
    assert!(parts.len() >= 6);

    let (negative, full_decoded) = decode(v);
    let sign = determine_sign(sign, &full_decoded, negative);
    match full_decoded {
        FullDecoded::Nan => {
            parts[0] = MaybeUninit::new(Part::Copy(b"NaN"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Infinite => {
            parts[0] = MaybeUninit::new(Part::Copy(b"inf"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Zero => {
            if frac_digits > 0 {
                // [0.][0000][e0]
                parts[0] = MaybeUninit::new(Part::Copy(b"0."));
                parts[1] = MaybeUninit::new(Part::Zero(frac_digits));
                parts[2] = MaybeUninit::new(Part::Copy(if upper { b"E0" } else { b"e0" }));
                Formatted {
                    sign,
                    // SAFETY: we just initialized the elements `..3`.
                    parts: unsafe { parts[..3].assume_init_ref() },
                }
            } else {
                parts[0] = MaybeUninit::new(Part::Copy(if upper { b"0E0" } else { b"0e0" }));
                Formatted {
                    sign,
                    // SAFETY: we just initialized the elements `..1`.
                    parts: unsafe { parts[..1].assume_init_ref() },
                }
            }
        }
        FullDecoded::Finite(ref decoded) => {
            let maxlen = estimate_max_buf_len(decoded.exp);
            // Scratch space is only needed for the significant digits that `format_exact` can
            // actually generate. Any remaining requested fractional precision becomes a trailing
            // `Part::Zero`.
            let sig_digits = if frac_digits < maxlen { frac_digits + 1 } else { maxlen };
            assert!(buf.len() >= sig_digits);

            let (buf, exp) = format_exact(decoded, &mut buf[..sig_digits], i16::MIN);
            Formatted { sign, parts: digits_to_exp_str(buf, exp, frac_digits, upper, parts) }
        }
    }
}

/// Formats given floating point number into the decimal form with exactly
/// given number of fractional digits. The result is stored to the supplied parts
/// array while utilizing given byte buffer as a scratch. `upper` is currently
/// unused but left for the future decision to change the case of non-finite values,
/// i.e., `inf` and `nan`. The first part to be rendered is always a `Part::Sign`
/// (which can be an empty string if no sign is rendered).
///
/// `format_exact` should be the underlying digit-generation function.
/// It should return the part of the buffer that it initialized.
/// You probably would want `strategy::grisu::format_exact` for this.
///
/// The byte buffer should be enough for the output unless `frac_digits` is
/// so large that only the fixed number of digits will be ever written.
/// (The tipping point for `f64` is about 800, and 1000 bytes should be enough.)
/// There should be at least 4 parts available, due to the worst case like
/// `[+][0.][0000][2][0000]` with `frac_digits = 10`.
pub fn to_exact_fixed_str<'a, T, F>(
    mut format_exact: F,
    v: T,
    sign: Sign,
    frac_digits: usize,
    buf: &'a mut [MaybeUninit<u8>],
    parts: &'a mut [MaybeUninit<Part<'a>>],
) -> Formatted<'a>
where
    T: DecodableFloat,
    F: FnMut(&Decoded, &'a mut [MaybeUninit<u8>], i16) -> (&'a [u8], i16),
{
    assert!(parts.len() >= 4);

    let (negative, full_decoded) = decode(v);
    let sign = determine_sign(sign, &full_decoded, negative);
    match full_decoded {
        FullDecoded::Nan => {
            parts[0] = MaybeUninit::new(Part::Copy(b"NaN"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Infinite => {
            parts[0] = MaybeUninit::new(Part::Copy(b"inf"));
            // SAFETY: we just initialized the elements `..1`.
            Formatted { sign, parts: unsafe { parts[..1].assume_init_ref() } }
        }
        FullDecoded::Zero => {
            if frac_digits > 0 {
                // [0.][0000]
                parts[0] = MaybeUninit::new(Part::Copy(b"0."));
                parts[1] = MaybeUninit::new(Part::Zero(frac_digits));
                Formatted {
                    sign,
                    // SAFETY: we just initialized the elements `..2`.
                    parts: unsafe { parts[..2].assume_init_ref() },
                }
            } else {
                parts[0] = MaybeUninit::new(Part::Copy(b"0"));
                Formatted {
                    sign,
                    // SAFETY: we just initialized the elements `..1`.
                    parts: unsafe { parts[..1].assume_init_ref() },
                }
            }
        }
        FullDecoded::Finite(ref decoded) => {
            let maxlen = estimate_max_buf_len(decoded.exp);
            assert!(buf.len() >= maxlen);

            // it *is* possible that `frac_digits` is ridiculously large.
            // `format_exact` will end rendering digits much earlier in this case,
            // because we are strictly limited by `maxlen`.
            let limit = if frac_digits < 0x8000 { -(frac_digits as i16) } else { i16::MIN };
            let (buf, exp) = format_exact(decoded, &mut buf[..maxlen], limit);
            if exp <= limit {
                // the restriction couldn't been met, so this should render like zero no matter
                // `exp` was. this does not include the case that the restriction has been met
                // only after the final rounding-up; it's a regular case with `exp = limit + 1`.
                debug_assert_eq!(buf.len(), 0);
                if frac_digits > 0 {
                    // [0.][0000]
                    parts[0] = MaybeUninit::new(Part::Copy(b"0."));
                    parts[1] = MaybeUninit::new(Part::Zero(frac_digits));
                    Formatted {
                        sign,
                        // SAFETY: we just initialized the elements `..2`.
                        parts: unsafe { parts[..2].assume_init_ref() },
                    }
                } else {
                    parts[0] = MaybeUninit::new(Part::Copy(b"0"));
                    Formatted {
                        sign,
                        // SAFETY: we just initialized the elements `..1`.
                        parts: unsafe { parts[..1].assume_init_ref() },
                    }
                }
            } else {
                Formatted { sign, parts: digits_to_dec_str(buf, exp, frac_digits, parts) }
            }
        }
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
pub(crate) mod verify {
    use super::*;
    use crate::kani;

    /// Any `Decoded` at all, including ones that `decode` never produces.
    pub(crate) fn any_decoded() -> Decoded {
        Decoded {
            mant: kani::any(),
            minus: kani::any(),
            plus: kani::any(),
            exp: kani::any(),
            inclusive: kani::any(),
        }
    }

    /// Stands in for `round_up` in the harnesses of the digit generation strategies. `round_up`
    /// is safe code working on bytes that are already initialized, but the iterator and `fill`
    /// machinery it pulls into the callers' loops makes instrumenting their loop contracts several
    /// times as expensive. This model lets every byte keep its value, be incremented (panicking on
    /// overflow, as the real addition does), or become `b'0'` or `b'1'`, independently of the
    /// others, and returns `None`, `Some(b'0')` or `Some(b'1')`. `check_round_up_model` proves
    /// that this covers everything `round_up` does.
    ///
    /// The loop has a contract so that its cost does not grow with the length of the buffer. The
    /// invariant keeps what the proofs need, the possible values of the byte at the witness index
    /// (see `ghost`); the other bytes become arbitrary, which only adds behaviors.
    pub(crate) fn any_round_up(d: &mut [u8]) -> Option<u8> {
        let w = ghost::witness();
        let old = if w < d.len() { d[w] } else { 0 };
        let mut i = 0;
        #[kani::loop_invariant(i <= d.len()
            && (w >= d.len()
                || if i <= w {
                    d[w] == old
                } else {
                    d[w] == old
                        || (old < u8::MAX && d[w] == old + 1)
                        || d[w] == b'0'
                        || d[w] == b'1'
                }))]
        #[kani::loop_modifies(&i, &mut d[..])]
        while i < d.len() {
            match kani::any::<u8>() {
                0 => {}
                1 => d[i] += 1,
                2 => d[i] = b'0',
                _ => d[i] = b'1',
            }
            i += 1;
        }
        match kani::any::<u8>() {
            0 => None,
            1 => Some(b'0'),
            _ => Some(b'1'),
        }
    }

    /// `any_round_up` over-approximates `round_up`: whatever the digits (or non-digits) are,
    /// each byte of the buffer ends up with one of the values the model allows for it, and so does
    /// the returned digit. The byte `w` is arbitrary, so this holds for all of them, and since the
    /// model chooses independently for each byte, it allows every combination. The real function
    /// panics when it increments a `0xff` byte, hence `should_panic`; the two properties are
    /// stated with `assert_unchecked` so that their violation would not count as a panic.
    ///
    /// This is checked for slices of up to 32 bytes, which covers the Dragon harnesses.
    /// `grisu::verify::check_format_exact_opt` passes the model longer slices; checking those
    /// here is too expensive, and for them the model rests on reading `round_up`: it looks for
    /// the last byte that is not `b'9'`, increments it and overwrites what follows with `b'0'`,
    /// or writes `b'1'` and `b'0'`s if there is none, whatever the length.
    #[kani::proof]
    #[kani::should_panic]
    #[kani::unwind(34)]
    fn check_round_up_model() {
        const CAP: usize = 32;
        let mut d: [u8; CAP] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= CAP);
        let w: usize = kani::any();
        kani::assume(w < CAP);
        let old = d[w];
        let ret = round_up(&mut d[..len]);
        let new = d[w];
        // SAFETY: none is claimed. These are the properties this harness asks Kani to prove.
        unsafe {
            crate::hint::assert_unchecked(
                new == old || (old < u8::MAX && new == old + 1) || new == b'0' || new == b'1',
            );
            crate::hint::assert_unchecked(matches!(ret, None | Some(b'0') | Some(b'1')));
        }
    }

    /// Capacity of the digit buffers used by the harnesses. The lengths actually passed to the
    /// functions under verification are symbolic, anywhere up to this capacity. It exceeds the
    /// largest scratch buffer `to_exact_fixed_str` can ask for with an `f64` (828 bytes).
    const BUF_CAP: usize = 1024;
    /// Capacity of the `parts` arrays; the functions need at most 6.
    const PARTS_CAP: usize = 8;

    /// What every element of a `parts` array points to before the call. The functions under
    /// verification cannot produce a part that points here, so a returned part that does was
    /// never written.
    static POISON: [u8; 1] = [0];

    /// A `parts` array for a harness. Its elements hold a value, so that the check in
    /// `inspect_parts` does not depend on how Kani models memory that was never written.
    fn poisoned_parts<'a>() -> [MaybeUninit<Part<'a>>; PARTS_CAP] {
        [MaybeUninit::new(Part::Copy(&POISON)); PARTS_CAP]
    }

    /// Checks that every returned part has been written (see `POISON`), and reads the two ends of
    /// the slices they refer to.
    ///
    /// The loop runs a fixed number of times instead of `parts.len()` times, so that no unwinding
    /// assertion depends on the symbolic length.
    fn inspect_parts(parts: &[Part<'_>]) {
        assert!(parts.len() <= 6);
        let mut i = 0;
        while i < 6 {
            if i < parts.len() {
                if let Part::Copy(bytes) = parts[i] {
                    assert!(!crate::ptr::eq(bytes.as_ptr(), POISON.as_ptr()));
                    if let (Some(&first), Some(&last)) = (bytes.first(), bytes.last()) {
                        let _ = (first, last);
                    }
                }
            }
            i += 1;
        }
    }

    /// Any digit string a caller may pass to `digits_to_dec_str` and `digits_to_exp_str` without
    /// tripping their leading `assert!`s: non-empty, with a non-zero first digit. The remaining
    /// bytes are unconstrained.
    fn any_digits(storage: &[u8; BUF_CAP]) -> &[u8] {
        let len: usize = kani::any();
        kani::assume(len >= 1 && len <= BUF_CAP);
        kani::assume(storage[0] > b'0');
        &storage[..len]
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_digits_to_dec_str() {
        let storage: [u8; BUF_CAP] = kani::any();
        let buf = any_digits(&storage);
        let mut parts = poisoned_parts();
        let nparts: usize = kani::any();
        kani::assume(nparts >= 4 && nparts <= PARTS_CAP);

        let out = digits_to_dec_str(buf, kani::any(), kani::any(), &mut parts[..nparts]);
        assert!(out.len() >= 2 && out.len() <= 4);
        inspect_parts(out);
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn check_digits_to_exp_str() {
        let storage: [u8; BUF_CAP] = kani::any();
        let buf = any_digits(&storage);
        let mut parts = poisoned_parts();
        let nparts: usize = kani::any();
        kani::assume(nparts >= 6 && nparts <= PARTS_CAP);

        let out =
            digits_to_exp_str(buf, kani::any(), kani::any(), kani::any(), &mut parts[..nparts]);
        assert!(out.len() >= 3 && out.len() <= 6);
        inspect_parts(out);
    }

    fn any_sign() -> Sign {
        if kani::any() { Sign::Minus } else { Sign::MinusPlus }
    }

    /// Models an arbitrary digit-generation callback that honors what the `to_*_str` functions
    /// document about it: it returns the part of `buf` it initialized, and that part is a digit
    /// string acceptable to `digits_to_dec_str`/`digits_to_exp_str` (see `any_digits`). How many
    /// digits are written (anywhere from 1 to `buf.len()`), which bytes they are, and the returned
    /// exponent are all nondeterministic.
    fn any_nonempty_digits<'a>(buf: &'a mut [MaybeUninit<u8>]) -> &'a [u8] {
        let len: usize = kani::any();
        kani::assume(len >= 1 && len <= buf.len());
        let digits: [u8; BUF_CAP] = kani::any();
        kani::assume(digits[0] > b'0');
        // SAFETY: the buffers of the harnesses hold at most `BUF_CAP` bytes, so `len` bytes can be
        // read from `digits` and written to `buf`, and the two do not overlap.
        unsafe {
            crate::ptr::copy_nonoverlapping(digits.as_ptr(), buf.as_mut_ptr().cast::<u8>(), len)
        };
        // SAFETY: `buf[..len]` was initialized just above.
        unsafe { buf[..len].assume_init_ref() }
    }

    fn any_shortest<'a>(_: &Decoded, buf: &'a mut [MaybeUninit<u8>]) -> (&'a [u8], i16) {
        (any_nonempty_digits(buf), kani::any())
    }

    /// Like `any_shortest`, for the exact mode as `to_exact_exp_str` uses it: it asks for digits
    /// without a limit on the last one (`limit == i16::MIN`), so there are always some.
    fn any_exact_unlimited<'a>(
        _: &Decoded,
        buf: &'a mut [MaybeUninit<u8>],
        _: i16,
    ) -> (&'a [u8], i16) {
        (any_nonempty_digits(buf), kani::any())
    }

    /// Like `any_shortest`, for the exact mode as `to_exact_fixed_str` uses it: when the
    /// requested last-digit `limit` cannot be met, the callback reports `exp <= limit` together
    /// with no digits at all.
    fn any_exact<'a>(_: &Decoded, buf: &'a mut [MaybeUninit<u8>], limit: i16) -> (&'a [u8], i16) {
        let exp: i16 = kani::any();
        if exp <= limit {
            // SAFETY: an empty prefix has nothing to initialize.
            (unsafe { buf[..0].assume_init_ref() }, exp)
        } else {
            (any_nonempty_digits(buf), exp)
        }
    }

    macro_rules! check_to_str {
        ($float:ty, $shortest:ident, $shortest_exp:ident, $exact_exp:ident, $exact_fixed:ident) => {
            #[kani::proof]
            #[kani::unwind(8)]
            fn $shortest() {
                let mut buf = [MaybeUninit::<u8>::uninit(); BUF_CAP];
                let mut parts = poisoned_parts();
                let (buf_len, nparts): (usize, usize) = kani::any();
                kani::assume(buf_len >= MAX_SIG_DIGITS && buf_len <= BUF_CAP);
                kani::assume(nparts >= 4 && nparts <= PARTS_CAP);

                let out = to_shortest_str(
                    any_shortest,
                    kani::any::<$float>(),
                    any_sign(),
                    kani::any(),
                    &mut buf[..buf_len],
                    &mut parts[..nparts],
                );
                assert!(out.parts.len() >= 1 && out.parts.len() <= 4);
                inspect_parts(out.parts);
            }

            #[kani::proof]
            #[kani::unwind(8)]
            fn $shortest_exp() {
                let mut buf = [MaybeUninit::<u8>::uninit(); BUF_CAP];
                let mut parts = poisoned_parts();
                let (buf_len, nparts): (usize, usize) = kani::any();
                kani::assume(buf_len >= MAX_SIG_DIGITS && buf_len <= BUF_CAP);
                kani::assume(nparts >= 6 && nparts <= PARTS_CAP);
                let dec_bounds: (i16, i16) = kani::any();
                kani::assume(dec_bounds.0 <= dec_bounds.1);

                let out = to_shortest_exp_str(
                    any_shortest,
                    kani::any::<$float>(),
                    any_sign(),
                    dec_bounds,
                    kani::any(),
                    &mut buf[..buf_len],
                    &mut parts[..nparts],
                );
                assert!(out.parts.len() >= 1 && out.parts.len() <= 6);
                inspect_parts(out.parts);
            }

            #[kani::proof]
            #[kani::unwind(8)]
            fn $exact_exp() {
                let mut buf = [MaybeUninit::<u8>::uninit(); BUF_CAP];
                let mut parts = poisoned_parts();
                let (buf_len, nparts): (usize, usize) = kani::any();
                kani::assume(buf_len <= BUF_CAP);
                kani::assume(nparts >= 6 && nparts <= PARTS_CAP);
                let v: $float = kani::any();
                let frac_digits: usize = kani::any();
                // The function asserts that the scratch buffer is large enough for the digits it
                // is going to request.
                if let (_, FullDecoded::Finite(decoded)) = decode(v) {
                    let maxlen = estimate_max_buf_len(decoded.exp);
                    kani::assume(
                        buf_len >= if frac_digits < maxlen { frac_digits + 1 } else { maxlen },
                    );
                }

                let out = to_exact_exp_str(
                    any_exact_unlimited,
                    v,
                    any_sign(),
                    frac_digits,
                    kani::any(),
                    &mut buf[..buf_len],
                    &mut parts[..nparts],
                );
                assert!(out.parts.len() >= 1 && out.parts.len() <= 6);
                inspect_parts(out.parts);
            }

            #[kani::proof]
            #[kani::unwind(8)]
            fn $exact_fixed() {
                let mut buf = [MaybeUninit::<u8>::uninit(); BUF_CAP];
                let mut parts = poisoned_parts();
                let (buf_len, nparts): (usize, usize) = kani::any();
                kani::assume(buf_len <= BUF_CAP);
                kani::assume(nparts >= 4 && nparts <= PARTS_CAP);
                let v: $float = kani::any();
                // The function asserts that the scratch buffer is large enough for the digits it
                // is going to request.
                if let (_, FullDecoded::Finite(decoded)) = decode(v) {
                    kani::assume(buf_len >= estimate_max_buf_len(decoded.exp));
                }

                let out = to_exact_fixed_str(
                    any_exact,
                    v,
                    any_sign(),
                    kani::any(),
                    &mut buf[..buf_len],
                    &mut parts[..nparts],
                );
                assert!(out.parts.len() >= 1 && out.parts.len() <= 4);
                inspect_parts(out.parts);
            }
        };
    }

    // `f16` only implements `DecodableFloat` on targets with reliable `f16` support, and `f128`
    // does not implement it at all.
    #[cfg(target_has_reliable_f16)]
    check_to_str!(
        f16,
        check_to_shortest_str_f16,
        check_to_shortest_exp_str_f16,
        check_to_exact_exp_str_f16,
        check_to_exact_fixed_str_f16
    );
    check_to_str!(
        f32,
        check_to_shortest_str_f32,
        check_to_shortest_exp_str_f32,
        check_to_exact_exp_str_f32,
        check_to_exact_fixed_str_f32
    );
    check_to_str!(
        f64,
        check_to_shortest_str_f64,
        check_to_shortest_exp_str_f64,
        check_to_exact_exp_str_f64,
        check_to_exact_fixed_str_f64
    );
}
