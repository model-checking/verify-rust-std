# Flux

[Flux](https://flux-rs.github.io/flux) is a refinement type checker
that can be used to prove user-defined safety properties for Rust.
Users can write their own properties via refinement type contracts
(a generalization of pre- and post-conditions). Additionally, out of the
box, Flux checks for various issues such as

- arithmetic overflows
- division by zero
- array bounds violations

Currently, Flux does not distinguish between logic errors (e.g., those that may cause a panic)
and errors that can lead to undefined behavior. They both manifest
as contract violations.

## Installation

See the [installation section of the Flux book](https://flux-rs.github.io/flux/install.html)
to learn how to install and run Flux.


## Usage

(Adapted from the Kani documentation; see [the Flux book](https://flux-rs.github.io/flux)
for many more examples.)

Consider a Rust file `demo.rs` with a function that returns
the absolute value of the difference between two integers.
To *prove* that the function always returns a *non-negative* result, you write
a Flux specification—above the function definition—that says the output
is a refinement type `i32{v: 0 <= v}` denoting non-negative `i32` values.


``` rust
// demo.rs
#[allow(dead_code)]
#[cfg_attr(flux, flux::spec(fn(a: i32, b: i32) -> i32{v:0 <= v}))]
fn test_abs(a:i32, b:i32) -> i32 {
    if a > b {
        a - b
    } else {
        b - a
    }
}
```

Now, if you run

```
$ flux --crate-type=lib demo.rs
```

Flux will return immediately with **no output** indicating the code is safe.

This may be baffling for those with a keen understanding of arithmetic overflows:
what if `a` is `INT_MAX` and `b` is `INT_MIN`? Indeed, Flux has overflow checking
off by default but you can optionally switch it on for a function, module, or entire crate.

``` rust
// demo.rs
#[allow(dead_code)]
#[cfg_attr(flux, flux::opts(check_overflow = true))]
#[cfg_attr(flux, flux::spec(fn(a: i32, b: i32) -> i32{v:0 <= v}))]
fn test_abs(a:i32, b:i32) -> i32 {
    if a > b {
        a - b
    } else {
        b - a
    }
}
```

Now, when you run `flux` you see that

```
$ flux --crate-type=lib demo.rs
error[E0999]: arithmetic operation may overflow
 --> demo.rs:9:9
  |
9 |         b - a
  |         ^^^^^

error[E0999]: arithmetic operation may overflow
 --> demo.rs:7:9
  |
7 |         a - b
  |         ^^^^^

error: aborting due to 2 previous errors
```

You might *fix* the errors, i.e., prove the function have no overflows,
by requiring the *inputs* also be non-negative:

```rust
#[allow(dead_code)]
#[cfg_attr(flux, flux::opts(check_overflow = true))]
#[cfg_attr(flux, flux::spec(fn(a: i32{0 <= a}, b: i32{0 <= b}) -> i32{v: 0 <= v}))]
fn test_abs(a:u32, b:u32) -> u32 {
    if a > b {
        a - b
    } else {
        b - a
    }
}
```

This time `flux --crate-type=lib demo.rs` finishes swiftly without reporting any errors.

For a more detailed online interactive tutorial, with many more examples, see [the Flux book](https://flux-rs.github.io/flux).

## Using Flux to verify the (model-checking fork of) the Rust Standard Library

Currrently, we have configured Flux to run on the
[model-checking fork](https://github.com/model-checking/verify-rust-std)
of the Rust Standard Library. You can run Flux on

1. a single function,
2. a single file,
3. a set of files matching a glob-pattern, or
4. the entire crate.

### Running on a Single Function

Suppose the function is in a file inside `library/core/src/`, e.g.,
`library/core/src/ascii/ascii_char.rs`.
For example, let's suppose `test_abs` was added to the end of that file,
*with* the `check_overflow = true`  and *without* the `flux::spec` contract.
Then if you did

```bash
$ cd library/core
$ FLUXFLAGS="-Fcheck-def=test_abs" cargo flux
```

you should get some output like

```
    Checking core v0.0.0 (/verify-rust-std/library/core)

error[E0999]: arithmetic operation may overflow
   --> core/src/ascii/ascii_char.rs:635:9
    |
635 |         b - a
    |         ^^^^^

error[E0999]: arithmetic operation may overflow
   --> core/src/ascii/ascii_char.rs:633:9
    |
633 |         a - b
    |         ^^^^^

error: could not compile `core` (lib) due to 2 previous errors

Checking core v0.0.0 (/verify-rust-std/library/core)
Finished `flux` profile [unoptimized + debuginfo] target(s) in 5.54s
```


You can now fix the error by adding the non-negative input specification above the definition
of `test_abs`

```rust
#[cfg_attr(flux, flux::spec(fn(a: i32{0 <= a}, b: i32{0 <= b}) -> i32{v: 0 <= v})]
```

and when you re-run, it should finish with no warnings

**NOTE** When checking inside `core`, we wrap the `flux` specification attributes
in `#[cfg_attr(flux,...)]` so they are only read by flux.

### Running on a Single File

To run on a single _file_ you can just pass the name of that file to flux (relative from the
crate root) as

```bash
$ cd library/core
$ FLUXFLAGS="-Finclude=src/ascii/ascii_char.rs" cargo flux
```

### Running on a Globset of Files

To run on a comma-separated _globset of files_, e.g., an entire module, you can just pass
the appropriate globset as

```bash
$ cd library/core
$ FLUXFLAGS="-Finclude=src/ascii/*" cargo flux
```

### Configuring Flux via `Cargo.toml`

Flux can also be configured in the `Cargo.toml` under the
`[package.metadata.flux]` section.

You can add or remove things from the `include` declaration there
to check other files. Currently, it is configured to only run on a
tiny subset of the modules; you should comment out that line if you
want to run on _all_ of `core`.

You can run flux on all the parts of the `core` crate specified in `include`
directive in the `Cargo.toml` by doing

```bash
$ cd library/core
$ cargo flux
```

### Running on the Entire Crate

Currently the `core/Cargo.toml` is configured (see the `[package.metadata.flux]`) to
only run on a tiny subset of the modules, you should comment out that line if you
really want to run on _all_ of `core`, and then run

```bash
$ cd library/core
$ cargo flux
```

Sadly, various Rust features exercised by the crate are not currently supported by
Flux making it crash ignominously.

You can tell it to do a "best-effort" analysis by ignoring those crashes
(as much as possible) by

```bash
$ FLUXFLAGS="-Fcatch-bugs" cargo flux
```

in which case Flux will grind over the whole crate and point out nearly 300+ *possible*
warnings about overflows, array bounds accesses etc.,
and also about 200+ ICE (places where it crashes!) To do this, you may also have
to tell Flux to not check certain modules, e.g. by adding
various `flux::trusted` annotations [as shown here](https://github.com/flux-rs/verify-rust-std/blob/fluxable/library/core/src/lib.rs)


## More details

You can find more information on using Flux—especially on how to write different
kinds of specifications and configuration options—in [the Flux book](https://flux-rs.github.io/flux).
Happy proving!

## Caveats and Current Limitations

Flux is aimed to be a lightweight verifier that is predictable and fully automated. To achieve this,
it restricts refinement predicates to decidable fragments of first-order logic
(i.e., without quantifiers). As a result, some properties (such as sortedness of arrays) may be
hard to specify.

Flux also has limited and conservative support for unsafe code. It can track properties of
pointers (e.g., alignment and provenance) but not the values of data written through
them.

Lastly, Flux is under active development, and many Rust features are not yet supported.
