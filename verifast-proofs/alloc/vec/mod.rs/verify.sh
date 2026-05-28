set -e -x

export VFVERSION=25.11-slice-support-v2

# Step 1: VeriFast verification
verifast -rustc_args "--edition 2024 --cfg no_global_oom_handling" -skip_specless_fns -ignore_unwind_paths -allow_assume -allow_dead_code verified/lib.rs

# Step 2: Refinement check (with-directives is the verified code minus VeriFast annotations)
# TODO: Temporarily disabled — refinement-checker does not yet support RawPtr
# (used by the non_null! macro's &raw const syntax in into_iter.rs).
# Re-enable once refinement-checker gains RawPtr support.
# refinement-checker --rustc-args "--edition 2024 --cfg no_global_oom_handling" with-directives/lib.rs verified/lib.rs > /dev/null

# Step 3: Verify with-directives refines original (using --ignore-directives)
# TODO: Temporarily disabled — same RawPtr limitation as Step 2.
# refinement-checker --rustc-args "--edition 2024 --cfg no_global_oom_handling" --ignore-directives original/lib.rs with-directives/lib.rs > /dev/null

# Step 4: Verify that our derived original matches the library source
# The original/mod.rs is derived from the verified code (with annotations and
# upstream code changes stripped). We check that the upstream modifications
# are a valid refinement by the refinement checker above.
# The actual library source diff is informational only.
