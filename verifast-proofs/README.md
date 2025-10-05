# VeriFast proofs

This directory contains [VeriFast](../doc/src/tools/verifast.md) proofs for (currently a very, very small) part of the standard library.

Specifically, it currently contains the following proofs:

- Partial proof of [LinkedList](alloc/collections/linked_list.rs/)
- Partial proof of [RawVec](alloc/raw_vec/mod.rs/)

See each proof's accompanying README for a tour of the proof and applicable caveats.

## Maintaining the proofs

 If the VeriFast CI action fails because of a failing diff, please run `cd verifast-proofs; ./patch-verifast-proofs.sh` to fix the problem.

## `-skip_specless_fns`

VeriFast supports selecting the code to verify on a function-by-function basis. By default, when given a `.rs` file VeriFast will try to verify [semantic well-typedness](https://verifast.github.io/verifast/rust-reference/non-unsafe-funcs.html) of all non-`unsafe` functions in that file (and in any submodules), and will require that the user provide specifications for all `unsafe` functions, which it will then verify against those specifications. However, when given the `-skip_specless_fns` command-line flag, VeriFast will skip all functions for which the user did not provide a specification.

## Applying VeriFast

To verify a function in a file <code>library/<i>crate</i>/src/<i>mod</i>/<i>file</i>.rs</code>, proceed as follows:
1. Copy that file to <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/original/<i>file</i>.rs</code> as well as to <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/verified/<i>file</i>.rs</code>.
2. Create a file <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/original/lib.rs</code> to serve as crate root for verification, and include <code><b>mod</b> <i>file</i>;</code>. (See the existing proofs for examples.) Copy it to <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/verified/lib.rs</code>.
2. Add a VeriFast specification to the function(s) you want to verify, and any other VeriFast annotations to make the proof go through, in <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/verified/<i>file</i>.rs</code>. While doing so, you will need to change the code slightly so as to be able to insert ghost commands in the correct places. 
3. Add commands for checking your proof to `verifast-proofs/check-verifast-proofs.mysh`. This includes the following:
    1. A `verifast` invocation for checking the VeriFast proof.
    2. A `refinement-checker` invocation for checking that the code changes you made in the verified version do not change the meaning of the program. Specifically, this tool checks that the original code *refines* the verified code, i.e. that each behavior of a function in the original version is also a behavior of the corresponding function in the verified version. As a result, if the verified version has been verified to have no bad behaviors, the original version also has no bad behaviors.
    3. A `diff` invocation for checking that the version in `original` is identical to the original version in `library`.

### Example

Take the VeriFast proof of `linked_list.rs` as an example. The file structure is:

```
linked_list.rs
  original
    lib.rs
    linked_list.rs
    linked_list
      tests.rs
  verified
    lib.rs
    linked_list.rs
    linked_list
      tests.rs
```
- The `lib.rs` files are the crate roots we created for verification.
- The `linked_list.rs` files contain the `LinkedList` implementation code. `verified/linked_list.rs` adds VeriFast annotations and includes minor code changes with respect to the implementation in `original/linked_list.rs` when necessary to make it possible for annotations to be inserted in the right places and to make the proof go through.
- Since the original `linked_list.rs` contains a `tests` module, we create empty `tests.rs` files.

We then:
1. Run VeriFast to ensure the proof in `verified/linked_list.rs` goes through.
2. Run the refinement checker to make sure that `verified/linked_list.rs` refines `original/linked_list.rs`. Since we made changes to `verified/linked_list.rs` to make the proof go through, we want to be sure that those changes did not affect the implementation behavior--i.e., we want to be sure that our proof of the verified version of the file actually allows us to make claims about the original version.
3. Run the diff tool to ensure that `original/linked_list.rs` matches the file in `library/`, i.e., check that we're verifying the most recent version of the `LinkedList` implementation available in this repository.

Separating steps 2) and 3) lets us distinguish between CI failures caused by incorrect modifications to the verified files (failure in step 2) versus a proof that was once correct, but is just out of date (failure in step 3). Without the copy of the original file, when the `library/` files change, there would be no easy way to tell whether the VeriFast proofs are wrong or just stale.

The [VeriFast](../.github/workflows/verifast.yml) GitHub action will run `verifast-proofs/check-verifast-proofs.mysh`. Check that file to see which version of VeriFast is used.
