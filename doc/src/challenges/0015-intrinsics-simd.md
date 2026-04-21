# Challenge 15: Contracts and Tests for SIMD Intrinsics

- **Status:** Open
- **Solution:** 
- **Tracking Issue:** [#173](https://github.com/model-checking/verify-rust-std/issues/173)
- **Start date:** 2025/02/01
- **End date:** 2025/08/01
- **Reward:** *20000 USD*

-------------------


## Goal

A number of Rust projects rely on the SIMD intrinsics provided by
[core::arch](https://doc.rust-lang.org/beta/core/arch/) for
performance. This includes libraries like [hashbrown]() that are used
in
[HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html),
as well as third-party cryptographic libraries like
[libcrux](https://github.com/cryspen/libcrux) and
[Dalek](https://github.com/dalek-cryptography/curve25519-dalek) that
are used in mainstream software projects. 

The goal of this project is to provide testable formal specifications
for the 100 most commonly used intrinsics for x86_64 and aarch64
platforms, chosen specifically to cover all the intrinsics used in
hashbrown and in popular cryptographic libraries.

For each intrinsic, the main goal is to provide contracts in the form
of pre- and post-conditions, and to verify whether these contracts
hold when the intrinsics are executed in Rust.  A secondary goal is to
use these contracts as formal specifications of the intrinsics API
when doing proofs of Rust programs.


## Motivation

Rust is the language of choice for new security-critical and
performance-sensitive projects, and consequently a number of new
cryptographic projects use Rust to build their infrastructure and
trusted computing base. However, the SIMD intrinsics in Rust lack
documentation and are easy to misuse, and so even the best Rust programmers
need to wade through Intel or Arm assembly documentation to understand
the functional behavior of these intrinsics.

Separately, when formally verifying cryptographic libraries, each
project needs to define its own semantics for SIMD instructions.
Indeed such SIMD specifications have currently been defined for
cryptographic verification projects in [F*](https://github.com/hacl-star/hacl-star), 
[EasyCrypt](https://github.com/jasmin-lang/jasmin), and [HOL Light](https://github.com/awslabs/s2n-bignum/tree/main).
This specification work is both time-consuming and error-prone,
there is also no guarantee of consistency between the instruction
semantics used in these different tools.

Consequently, we believe there is a strong need for a consistent,
formal, testable specification of the SIMD intrinsics that can aid
Rust developers. Furthermore, we believe that this
specification should written in a way that can be used to aid formal
verification of Rust programs using various proof assistants. 

## Description

Consider the function [`_mm_blend_epi16`](https://doc.rust-lang.org/beta/core/arch/x86_64/fn._mm_blend_epi16.html)
in [core::arch::x86_64](https://doc.rust-lang.org/beta/core/arch/x86_64/index.html):

```
pub unsafe fn _mm_blend_epi16(
    a: __m128i,
    b: __m128i,
    const IMM8: i32,
) -> __m128i
```

Its description says:
```
Blend packed 16-bit integers from a and b using the mask IMM8.

The mask bits determine the selection. A clear bit selects the corresponding element of a, and a set bit the corresponding element of b.
```

It then points to [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_blend_epi16) for the C intrinsic which provides the pseudocode:
```
FOR j := 0 to 7
i := j*16
IF imm8[j]
dst[i+15:i] := b[i+15:i]
ELSE
dst[i+15:i] := a[i+15:i]
FI
ENDFOR
```

We propose to reflect the behavior of the semantics as described in
Intel's documentation directly as pre- and post-conditions in Rust.

```
#[requires(IMM8 >= 0 && IMM8 <= 255)]
#[ensures(|result|
    forall (|j| implies(j >= 0 && j < 8,
        if get_bit(IMM8,j) then
            get_lane(result, j) == get_lane(b,j)
        else
            get_lane(result, j) == get_lane(a,j))))]
pub unsafe fn _mm_blend_epi16(
    a: __m128i,
    b: __m128i,
    const IMM8: i32,
) -> __m128i
```

This contract can then be used to automatically generate tests
for the intrinsic, which can be put in CI.

As a second layer of assurance, these contracts can be compiled
to some verification framework and proved to be sound against
a hand-written model of the intrinsics functions.

Finally, Rust verification toolchains can also rely on this contract
to model the intrinsics library within their analyses. This would
enable the verification of Rust applications that rely on SIMD intrinsics.


### Assumptions

The contracts we write for the SIMD intrinsics should be well tested
but, in the end, are hand-written based on the documentation
of the intrinsics provided by Intel and ARM. Consequently, the
user must trust that these semantics are correctly written.

When using the contracts within a formal verification project,
the user will, as usual, have to trust that the verification
tool correctly encodes the semantics of Rust and performs
a sound analysis within a clearly documented model.

### Success Criteria

The goal is to annotate >= 100 intrinsics in `core::arch::x86_64` and
`core::arch::aarch64` with contracts, and all these contracts will be
tested comprehensively in Rust. These functions should include all the
intrinsics currently used in standard libraries like
[hashbrown](https://github.com/rust-lang/hashbrown) (the basis
of the Rust [HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html) implementation).

An additional success criterion is to show that these contracts can be
used by verification tools to prove properties about example code that
uses them. Of particular interest is code used in cryptographic
libraries, but even other standalone examples using SIMD intrinsics
would be considered valuable. 
