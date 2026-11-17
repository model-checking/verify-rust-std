# Challenge 33: Safety of the SipHash implementation behind `DefaultHasher`

- **Status:** *Open*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** [#NNN](https://github.com/model-checking/verify-rust-std/issues/NNN)
- **Start date:** *YYYY/MM/DD*
- **Reward:** *TBD*

-------------------

## Goal

Verify the safety of the SipHash implementation in
[sip.rs](https://github.com/model-checking/verify-rust-std/blob/main/library/core/src/hash/sip.rs), which backs
`SipHasher`, `SipHasher13` and `std::hash::DefaultHasher`, for messages of arbitrary length and arbitrary
sequences of calls, and verify the correctness of its byte buffering.

## Motivation

`DefaultHasher` is the hasher of every `HashMap` and `HashSet` that does not name another one, so every key
inserted into or looked up in such a map passes through `Hasher::write` in this file. `write` reads the message
with unchecked loads: `ptr::copy_nonoverlapping` of 8, 4 and 2 bytes from `msg.as_ptr().add(i)`, and
`get_unchecked`. The offsets are computed from the message length and from a private counter of buffered bytes
(`ntail`). A mistake of one in that arithmetic reads up to seven bytes past the end of a slice supplied by safe
code.

The unsafe loads are deliberate. A simpler formulation of `u8to64_le` was reverted for speed in
[rust-lang/rust#69332](https://github.com/rust-lang/rust/pull/69332), and the comment above the function records
why. The safety comments in `write` rely on facts that are written nowhere as an invariant: that `ntail` is always
less than 8, and that the number of bytes left after the buffered prefix splits into whole 8-byte blocks plus a
remainder. A related fact is only true by construction: `reset` does not clear `tail`, and `finish` reads `tail`
unconditionally, which is correct only because the single caller of `reset` has just set `tail` to zero.

We know of no soundness bug reported against this file. The case for the challenge is exposure and the absence
of any machine-checked statement of the invariant, not a history of defects.

## Description

The private type `Hasher<S: Sip>` holds the keys, the four words of mixing state, the total length, and up to
seven buffered bytes (`tail`, with `ntail` of them valid). `Sip` is a private trait with exactly two
implementations, `Sip13Rounds` and `Sip24Rounds`. `write` first completes a buffered partial block from the start
of the message, then consumes whole 8-byte blocks in a `while` loop, then buffers the remaining 0 to 7 bytes with
`u8to64_le`. The macro `load_int_le!` is expanded three times (for `u32` and `u16` in `u8to64_le`, for `u64` in the
loop of `write`).

The following are out of scope:

- `Hash::hash_slice` for integer slices in `core::hash` (`hash/mod.rs`). Its unsafe block reinterprets a slice
  of integers as bytes for any `Hasher` supplied by the caller and does not depend on this file.
- The provided methods of the `Hasher` trait (`write_u8`, `write_usize`, `write_length_prefix` and the others).
  They are safe functions that call `write` with a byte array; a proof of `write` for every message covers what
  they do to a SipHash state.
- `RandomState` and the generation of its keys in `std`.
- Cryptographic properties of SipHash, and resistance to collision attacks.

No existing challenge lists a function of `core::hash`. The primitives used here, `ptr::copy_nonoverlapping` and
`<*const T>::add`, are targets of [Challenge 2](0002-intrinsics-memory.md) and
[Challenge 3](0003-pointer-arithmentic.md); their verification is not repeated here.

### Assumptions

- `core::ptr`, `core::slice`, `core::cmp` and the integer methods of `core::num` may be assumed correct. Existing
  verified contracts for them may be reused, and deductive tools may rely on their own specifications of these
  modules.
- The proofs must cover both implementations of `Sip`. Because the trait is private and has no other
  implementation, this is all instantiations of `Hasher<S>`.
- `write` adds the message length to a `usize` counter (`self.length += length`). Overflow of this counter is not
  undefined behavior: it panics when overflow checks are enabled and wraps otherwise, and only the low 8 bits of
  the counter are used. Solutions may assume that `self.length + msg.len()` does not overflow. An overflow panic
  is acceptable.
- No user code is called from this file, so unwinding need not be modeled beyond that panic.
- The repository's CI runs 64-bit little-endian targets, and proofs need only run there. Specifications should
  be written in terms of bytes and positions, not of the host byte order, so that they also describe big-endian
  targets (the code calls `to_le`).

### Success Criteria

The verification must be unbounded: it must hold for messages of arbitrary length, and for a hasher in any state
that an arbitrary sequence of earlier calls can produce. A proof that starts only from a newly created hasher, or
that fixes or bounds the message length, does not meet this criterion. In particular the proof must cover a
message shorter than the gap in the buffered block (the early return in `write`), a message that completes the
buffered block exactly, and any number of whole blocks after it.

Write and prove a contract for the following unsafe function. The contract must state the safety precondition
(the bytes `start..start + len` are in bounds of `buf`) and, for `len < 8`, the postcondition that the result is
the little-endian value of those bytes: byte `start + k` of `buf` is bits `8k` to `8k + 7` of the result, and all
higher bits are zero.

| Function | Location |
|---------|---------|
| `u8to64_le` (including both expansions of `load_int_le!` inside it) | `core::hash::sip` |

State the invariant of `Hasher<S>` that the unsafe code relies on. It must imply `ntail < 8` and say which bits
of `tail` are meaningful. Prove that every way of creating a hasher establishes it:

| Function | Location |
|---------|---------|
| `Hasher::<S>::new_with_keys` together with `Hasher::<S>::reset` | `core::hash::sip` |
| `Default for Hasher<S>`, `Clone for Hasher<S>` | `core::hash::sip` |
| `SipHasher::new`, `SipHasher::new_with_keys` | `core::hash::sip` |
| `SipHasher13::new`, `SipHasher13::new_with_keys` | `core::hash::sip` |
| `DefaultHasher::new`, `Default for DefaultHasher` | `std::hash::random` |

Prove the absence of undefined behavior for the following safe abstractions, from any state that satisfies the
invariant, and prove that `write` and `write_str` preserve the invariant:

| Function | Location |
|---------|---------|
| `<Hasher<S> as Hasher>::write` (including the expansion of `load_int_le!` in its loop) | `core::hash::sip` |
| `<Hasher<S> as Hasher>::write_str` | `core::hash::sip` |
| `<Hasher<S> as Hasher>::finish` | `core::hash::sip` |
| `Sip13Rounds::c_rounds`, `Sip13Rounds::d_rounds`, `Sip24Rounds::c_rounds`, `Sip24Rounds::d_rounds` | `core::hash::sip` |
| `<SipHasher as Hasher>::{write, write_str, finish}` | `core::hash::sip` |
| `<SipHasher13 as Hasher>::{write, write_str, finish}` | `core::hash::sip` |
| `<DefaultHasher as Hasher>::{write, write_str, finish}` | `std::hash::random` |

Prove the following about the buffering done by `write`, for a message `msg` and a state with `p` buffered bytes:

- The total length increases by `msg.len()`.
- Afterwards `(p + msg.len()) % 8` bytes are buffered.
- The buffered bytes are, in order, the last `(p + msg.len()) % 8` bytes of the previously buffered bytes
  followed by `msg`, and `tail` holds them in little-endian position with all higher bits zero.

The value of the digest (the mixing state and the result of `finish`) need not be specified. Solutions are
encouraged to also prove agreement with the SipHash-2-4 reference test vectors and the SipHash-1-3 vectors of
the library's own tests, and should say which parts of the mixing code those proofs exercise.

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Invoking undefined behavior via compiler intrinsics.

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
