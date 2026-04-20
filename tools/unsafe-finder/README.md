# Unsafe finder

This tool parses a Rust file and identifies three types of functions:
1. those that belong to impls and are `pub unsafe`;
2. those that belong to impls and are *not* `unsafe` but contain `unsafe` code; and,
3. those that are default functions belonging to traits and contain `unsafe` code.

The clippy `missing_safety_doc` lint nags developers to add
(plain-text) safety comments to functions in category (1), with a
configuration option that will make clippy also complain about private
unsafe functions (default false). For the purpose of verifying the
Rust standard library, such functions should have contracts and be
verified against them.

For categories (2) and (3), the unsafety is encapsulated in the
function; there must be some reason that the unsafe code in the
function is actually OK. (See
https://github.com/rust-lang/rust-clippy/issues/9330 for more
discussion on this issue). To verify the Rust standard library, one
must verify that there is no undefined behaviour triggered by the
unsafe code, probably by verifying the stated reason that the code is
OK.

There are some related metrics which are automatically generated in the
`verify-rust-std` project. Those metrics live in `scritps/kani-std-analysis/metrics-data-core.json`.

# Command-line arguments

This tool takes a directory or a list of .rs files as input and prints
out a list of impls and traits that have functions in categories (1)
through (3), as well as the involved functions.

```
$ target/debug/unsafe-finder rc.rs
impl<T: ?Sized, A: Allocator> Rc<T, A> {}
--- unsafe-containing fn inner
--- unsafe-containing fn into_inner_with_allocator

impl<T> Rc<T> {}
--- unsafe-containing fn new
--- unsafe-containing fn new_uninit
--- unsafe-containing fn new_zeroed
--- unsafe-containing fn try_new
--- unsafe-containing fn try_new_uninit
--- unsafe-containing fn try_new_zeroed
--- unsafe-containing fn pin

etc
```
