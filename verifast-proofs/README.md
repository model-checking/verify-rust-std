# VeriFast proofs

This directory contains [VeriFast](../doc/src/tools/verifast.md) proofs for (currently a very, very small) part of the standard library.

VeriFast supports selecting the code to verify on a function-by-function basis. By default, when given a `.rs` file VeriFast will try to verify [semantic well-typedness](https://verifast.github.io/verifast/rust-reference/non-unsafe-funcs.html) of all non-`unsafe` functions in that file (and in any submodules), and will require that the user provide specifications for all `unsafe` functions, which it will then verify against those specifications. However, when given the `-skip_specless_fns` command-line flag, VeriFast will skip all functions for which the user did not provide a specification.

To verify a function in a file <code>library/<i>crate</i>/src/<i>mod</i>/<i>file</i>.rs</code>, proceed as follows:
1. Copy that file to <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/original/<i>file</i>.rs</code> as well as to <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/verified/<i>file</i>.rs</code>.
2. Create a file <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/original/lib.rs</code> to serve as crate root for verification, and include <code><b>mod</b> <i>file</i>;</code>. (See the existing proofs for examples.) Copy it to <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/verified/lib.rs</code>.
2. Add a VeriFast specification to the function(s) you want to verify, and any other VeriFast annotations to make the proof go through, in <code>verifast-proofs/<i>crate</i>/<i>mod</i>/<i>file</i>.rs/verified/<i>file</i>.rs</code>. While doing so, you will need to change the code slightly so as to be able to insert ghost commands in the correct places. 
3. Add commands for checking your proof to `verifast-proofs/check-verifast-proofs.mysh`. This includes the following:
    1. A `verifast` invocation for checking the VeriFast proof.
    2. A `refinement-checker` invocation for checking that the code changes you made in the verified version do not change the meaning of the program. Specifically, this tool checks that the original code *refines* the verified code, i.e. that each behavior of a function in the original version is also a behavior of the corresponding function in the verified version. As a result, if the verified version has been verified to have no bad behaviors, the original version also has no bad behaviors.
    3. A `diff` invocation for checking that the version in `original` is identical to the original version in `library`.

The [VeriFast](../.github/workflows/verifast.yml) GitHub action will run `verifast-proofs/check-verifast-proofs.mysh`. Check that file to see which version of VeriFast is used.
