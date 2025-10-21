//! This file contains auxiliary definitions for Flux

/// List of properties tracked for the result of primitive bitwise operations.
/// See the following link for more information on how extensible properties for primitive operations work:
/// <https://flux-rs.github.io/flux/guide/specifications.html#extensible-properties-for-primitive-ops>
#[flux::defs {
    fn char_to_int(x:char) -> int {
        cast(x)
    }

    property ShiftRightByFour[>>](x, y) {
        16 * [>>](x, 4) == x
    }

    property MaskLess[&](x, y) {
        [&](x, y) <= x && [&](x, y) <= y
    }

    property ShiftLeft[<<](n, k) {
        0 < k => n <= [<<](n, k)
    }

    fn is_ascii_uppercase(n: int) -> bool {
        cast('A') <= n && n <= cast('Z')
    }

    fn is_ascii_lowercase(n: int) -> bool {
        cast('a') <= n && n <= cast('z')
    }

    fn to_ascii_uppercase(n: int) -> int {
        n - (cast(is_ascii_lowercase(n)) * 32)
    }

    fn to_ascii_lowercase(n: int) -> int {
        n + (cast(is_ascii_uppercase(n)) * 32)
    }

    property BitXor0[^](x, y) {
        (y == 0) => [^](x, y) == x
    }

    property BitXor32[^](x, y) {
        (is_ascii_lowercase(x) && y == 32) => [^](x, y) == x - 32
    }

    property BitOr0[|](x, y) {
        (y == 0) => [|](x, y) == x
    }

    property BitOr32[|](x, y) {
        (is_ascii_uppercase(x) && y == 32) => [|](x, y) == x + 32
    }

}]
#[flux::specs {
    mod hash {
        mod sip {
            struct Hasher {
              k0: u64,
              k1: u64,
              length: usize, // how many bytes we've processed
              state: State,  // hash State
              tail: u64,     // unprocessed bytes le
              ntail: usize{v: v <= 8}, // how many bytes in tail are valid
              _marker: PhantomData<S>,
            }
        }

        impl BuildHasherDefault {
            #[trusted(reason="https://github.com/flux-rs/flux/issues/1185")]
            fn new() -> Self;
        }
    }

    impl Hasher for hash::sip::Hasher {
        fn write(self: &mut Self, msg: &[u8]) ensures self: Self; // mut-ref-unfolding
    }

    impl Clone for hash::BuildHasherDefault {
        #[trusted(reason="https://github.com/flux-rs/flux/issues/1185")]
        fn clone(self: &Self) -> Self;
    }

    impl Debug for time::Duration {
        #[trusted(reason="modular arithmetic invariant inside nested fmt_decimal")]
        fn fmt(self: &Self, f: &mut fmt::Formatter) -> fmt::Result;
    }
}]
const _: () = {};
