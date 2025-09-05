# Partial verification of RawVec with VeriFast

With certain [caveats](#caveats), this proof proves functional correctness as well as [soundness](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) of RawVec associated functions `new_in`, `with_capacity_in`, `try_reserve`, `try_reserve_exact`, and `drop`, as well as functional correctness of RawVec associated functions `into_box`, `from_raw_parts_in`, `from_nonnull_in`, `ptr`, and `capacity`, RawVecInner associated functions `new_in`, `with_capacity_in`, `try_allocate_in`, `from_raw_parts_in`, `from_nonnull_in`, `ptr`, `non_null`, `capacity`, `current_memory`, `try_reserve`, `try_reserve_exact`, `needs_to_grow`, `set_ptr_and_cap`, `grow_amortized`, `grow_exact`, `shrink`, `shrink_unchecked`, and `deallocate`, and functions `capacity_overflow`, `new_cap`, `finish_grow`, `handle_error`, `alloc_guard`, and `layout_array`.

## Caveats

First of all, this proof was performed with the following VeriFast command-line flags:
- `-skip_specless_fns`: VeriFast ignores the functions that do not have a `req` or `ens` clause.
- `-ignore_unwind_paths`: This proof ignores code that is reachable only when unwinding.
- `-allow_assume`: This proof uses a number of `assume` ghost statements and `assume_correct` clauses. These must be carefully audited.

Secondly, since VeriFast uses the `rustc` frontend, which assumes a particular target architecture, VeriFast's results hold only for the used Rust toolchain's target architecture. When VeriFast reports "0 errors found" for a Rust program, it always reports the targeted architecture as well (e.g. `0 errors found (2149 statements verified) (target: x86_64-unknown-linux-gnu (LP64))`).

Thirdly, VeriFast has a number of [known unsoundnesses](https://github.com/verifast/verifast/issues?q=is%3Aissue+is%3Aopen+label%3Aunsoundness) (reasons why VeriFast might in some cases incorrectly accept a program), including the following:
- VeriFast does not yet fully verify compliance with Rust's [pointer aliasing rules](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).
- VeriFast does not yet properly verify compliance of custom type interpretations with Rust's [variance](https://doc.rust-lang.org/reference/subtyping.html#variance) rules.

Fourthly, unlike foundational tools such as [RefinedRust](https://plv.mpi-sws.org/refinedrust/), VeriFast has not itself been verified, so there are undoubtedly also unknown unsoundnesses. Such unsoundnesses might exist in VeriFast's [symbolic execution engine](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2531006855) [itself](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2534922580) or in its [prelude](https://github.com/verifast/verifast/tree/master/bin/rust) (definitions and axioms automatically imported at the start of every verification run) or in the [specifications](https://github.com/verifast/verifast/blob/master/bin/rust/std/lib.rsspec) it uses for the Rust standard library functions called by the program being verified.
