Invoke with:
```
cargo run metadata/ scanner_results/
```

The metadata/ folder contains the kani-metadata.json files produced by running:

```
kani autoharness --std ./library -Z function-contracts -Z mem-predicates -Z float-lib -Z c-ffi -Z loop-contracts --only-codegen --no-assert-contracts -j --output-format=terse -Z unstable-options -Z autoharness --cbmc-args --object-bits 12
```

on the standard library. The scanner_results/ directory contains the CSV files that the [scanner tool in Kani](https://github.com/model-checking/kani/tree/main/tools/scanner) produces.

The output is `autoharness_data.md`, which contains Markdown tables summarizing the autoharness application across all the crates in the standard library.

One of the tables has a column for "Skipped Type Categories." Generally speaking, "precise types" are what we think of as actual Rust types, and "type categories" are my subjective sense of how to group those types further. For example, `&mut i32` and `&mut u32` are two precise types, but they're in the same type category `&mut`. See the code for exact details on how we create type categories; the TL;DR is that we have a few hardcoded ones for raw pointers and references, and the rest we create using a fully-qualified path splitting heuristic.
