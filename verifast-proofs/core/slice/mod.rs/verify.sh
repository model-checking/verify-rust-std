set -e -x

export VFVERSION=25.11-slice-support

# Step 1: VeriFast verification
verifast -rustc_args "--edition 2024" -skip_specless_fns -ignore_unwind_paths -allow_assume -allow_dead_code verified/lib.rs

# Step 2: Refinement check (with-directives is the verified code minus VeriFast annotations)
refinement-checker --rustc-args "--edition 2024" with-directives/lib.rs verified/lib.rs > /dev/null

# Step 3: Verify with-directives refines original (using --ignore-directives)
refinement-checker --rustc-args "--edition 2024" --ignore-directives original/lib.rs with-directives/lib.rs > /dev/null
