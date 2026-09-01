# RAPx

[RAPx](https://github.com/safer-rust/RAPx) is a lightweight tool for checking
safety requirements around `unsafe` Rust APIs. The main user effort is adding
contracts to unsafe APIs with attributes such as `#[rapx::requires(...)]` and,
when needed, marking targets with `#[rapx::verify]`. RAPx then collects the
unsafe call sites, resolves the contracts for their callees, and runs the
verification automatically. It does not require a proof harness or a separate
test driver for each target.

The current verifier works with RAPx's built-in safety tags, such as
`ValidPtr`, `InBound`, `Align`, `Init`, `Typed`, `NonNull`, `NonOverlap`, and
`ValidNum`. Properties outside this tag set need to be expressed with the
supported tags or added to RAPx before the verifier can check them.

RAPx runs on MIR. For each unsafe checkpoint, it extracts paths, keeps the
statements needed for the property being checked, executes those statements
symbolically, and asks an SMT solver to prove the obligation. The report marks
each property as `Proved` or `Unproved`, and each target as `SOUND` or
`UNSOUND`. The RAPx Book has more detail on
[verification modes](https://safer-rust.github.io/RAPx-Book/8.1-overview.html),
[target collection](https://safer-rust.github.io/RAPx-Book/8.2-collection.html),
[safety contracts](https://safer-rust.github.io/RAPx-Book/8.3-contracts.html),
and the [verification pipeline](https://safer-rust.github.io/RAPx-Book/8.4-pipeline.html).

## Installation

The RAPx workflow in this repository pins both the Rust nightly toolchain and
the RAPx revision used by CI. See `.github/workflows/rapx.yml` for the exact
versions.

To install RAPx locally, clone the RAPx repository and run its installer:

```bash
git clone --branch verify-std https://github.com/safer-rust/RAPx.git
cd RAPx
./install.sh
```

RAPx currently requires a nightly Rust toolchain. The workflow for this
repository installs `nightly-2025-11-25` and the `rust-src` component:

```bash
rustup toolchain install nightly-2025-11-25
rustup component add rust-src --toolchain nightly-2025-11-25
```

## Usage

RAPx has two verification modes.

In `scan` mode, RAPx scans the crate and selects functions whose bodies contain
unsafe blocks, plus methods on structs with `#[rapx::invariant(...)]`
annotations:

```bash
cargo rapx verify --mode scan
```

In `targeted` mode, RAPx verifies only functions marked with `#[rapx::verify]`:

```bash
cargo rapx verify --mode targeted
```

The annotations can be hidden from normal Rust builds with `cfg_attr`. Challenge
17 annotates slice functions this way:

```rust
#[cfg_attr(rapx, rapx::verify)]
#[cfg_attr(rapx, rapx::requires(InBound(index_access(self, index))))]
pub const unsafe fn get_unchecked<I>(&self, index: I) -> &I::Output
where
    I: [const] SliceIndex<Self>,
{
    unsafe { &*index.get_unchecked(self) }
}
```

Unsafe callees can carry the contracts that callers must satisfy. For example,
`slice::from_raw_parts` records pointer, initialization, lifetime, aliasing,
alignment, and size requirements:

```rust
#[cfg_attr(rapx, rapx::requires(NonNull(data)))]
#[cfg_attr(rapx, rapx::requires(ValidPtr(data, T, len)))]
#[cfg_attr(rapx, rapx::requires(Init(data, T, len)))]
#[cfg_attr(rapx, rapx::requires(Alive(data)))]
#[cfg_attr(rapx, rapx::requires(Alias(data)))]
#[cfg_attr(rapx, rapx::requires(Align(data, T)))]
#[cfg_attr(rapx, rapx::requires(ValidNum(size_of(T) * len <= isize::MAX)))]
pub const unsafe fn from_raw_parts<'a, T>(data: *const T, len: usize) -> &'a [T] {
    // ...
}
```

RAPx reads contracts from direct annotations, trait method annotations, and a
JSON table for standard-library functions. If a callee has no contract attached,
RAPx can also follow a short unsafe call chain and use contracts from a deeper
callee.

## Using RAPx to verify the Rust Standard Library

The current CI job verifies the slice module for challenge 17. From the root of
a local `verify-rust-std` checkout, set up the environment in the same way as
the workflow:

```bash
export RUSTUP_TOOLCHAIN=nightly-2025-11-25
export RAPX_SYSROOT="$(rustc +$RUSTUP_TOOLCHAIN --print sysroot)"
export LD_LIBRARY_PATH="$RAPX_SYSROOT/lib"
export RUSTFLAGS="--cfg=rapx -Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(rapx)"
export __CARGO_TESTS_ONLY_SRC_ROOT="$(pwd)/library"

cd library/core
cargo +$RUSTUP_TOOLCHAIN rapx verify --module slice --mode targeted
```

`--module slice` restricts the run to `core::slice`. `--mode targeted` tells
RAPx to check only functions carrying `#[cfg_attr(rapx, rapx::verify)]`.
Without `--cfg=rapx`, the `cfg_attr` annotations do not expand and RAPx will
not see those targets.

To inspect what RAPx will verify without running the full verifier, use:

```bash
cargo rapx verify --prepare-targets
```

To inspect how contracts are resolved and expanded into concrete obligations,
use:

```bash
cargo rapx verify --debug-contracts
```
