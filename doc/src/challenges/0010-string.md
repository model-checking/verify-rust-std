# Challenge 10: Memory safety of String

- **Status:** Open
- **Tracking Issue:** [#61](https://github.com/model-checking/verify-rust-std/issues/61)
- **Start date:** *2024-08-19*
- **End date:** *2024-12-10*

-------------------

## Goal

In this challenge, the goal is to verify the memory safety of `std::string::String`.
Even though the majority of `String` methods are safe, many of them are safe abstractions over unsafe code.

For instance, the `insert` method is implemented as follows in v1.80.1:
```rust
pub fn insert(&mut self, idx: usize, ch: char) {
    assert!(self.is_char_boundary(idx));
    let mut bits = [0; 4];
    let bits = ch.encode_utf8(&mut bits).as_bytes();

    unsafe {
        self.insert_bytes(idx, bits);
    }
}
```
where `insert_bytes` has the following implementation:
```rust
unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
    let len = self.len();
    let amt = bytes.len();
    self.vec.reserve(amt);

    unsafe {
        ptr::copy(self.vec.as_ptr().add(idx), self.vec.as_mut_ptr().add(idx + amt), len - idx);
        ptr::copy_nonoverlapping(bytes.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
        self.vec.set_len(len + amt);
    }
}
```
The call to the unsafe `insert_bytes` method (which itself contains unsafe code) makes `insert` susceptible to undefined behavior.

### Success Criteria

Verify the memory safety of all public functions that are safe abstractions over unsafe code:

1. `from_utf16le` (unbounded)
1. `from_utf16le_lossy`(unbounded)
1. `from_utf16be` (unbounded)
1. `from_utf16be_lossy` (unbounded)
1. `pop`
1. `remove`
1. `remove_matches` (unbounded)
1. `retain` (unbounded)
1. `insert`
1. `insert_str` (unbounded)
1. `split_off` (unbounded)
1. `drain`
1. `replace_range` (unbounded)
1. `into_boxed_str`
1. `leak`

Ones marked as unbounded must be verified for any string/slice length.

### List of UBs

All proofs must automatically ensure the absence of the following [undefined behaviors](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

* Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
* Reading from uninitialized memory.
* Mutating immutable bytes.
* Producing an invalid value

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](../general-rules.md)
in addition to the ones listed above.
