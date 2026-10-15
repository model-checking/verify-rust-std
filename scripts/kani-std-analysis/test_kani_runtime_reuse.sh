#!/usr/bin/env bash
set -eo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"
source scripts/run-kani.sh --run list

test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT
build_dir="$test_dir/kani"
stub_commit=expected
get_current_commit() { printf '%s\n' "$stub_commit"; }

reject_reuse() {
    if check_binary_exists "$build_dir" expected >/dev/null; then
        echo "Incomplete or stale Kani runtime was accepted" >&2
        exit 1
    fi
}

reject_reuse
mkdir -p "$build_dir/scripts" "$build_dir/target/kani/bin" "$build_dir/target/kani/lib"
touch "$build_dir/scripts/kani" "$build_dir/target/kani/bin/kani-driver" \
    "$build_dir/target/kani/bin/kani-compiler" "$build_dir/target/kani/lib/libkani.rlib"
chmod +x "$build_dir/scripts/kani" "$build_dir/target/kani/bin/kani-driver" \
    "$build_dir/target/kani/bin/kani-compiler"
reject_reuse
kani_patch_hash > "$build_dir/target/kani/std-proof-patch.sha256"
check_binary_exists "$build_dir" expected

printf '%s\n' stale-patch > "$build_dir/target/kani/std-proof-patch.sha256"
reject_reuse
kani_patch_hash > "$build_dir/target/kani/std-proof-patch.sha256"

stub_commit=stale
reject_reuse
stub_commit=expected
chmod -x "$build_dir/target/kani/bin/kani-compiler"
reject_reuse
chmod +x "$build_dir/target/kani/bin/kani-compiler"
rm "$build_dir/target/kani/lib/libkani.rlib"
reject_reuse
touch "$build_dir/target/kani/lib/libkani.rlib"
rm -rf -- "$build_dir/target"
reject_reuse
echo "Kani runtime reuse tests passed."

probe_property=num::imp::flt2dec::strategy::grisu::generate_shortest.loop_invariant_step.1
if (export GITHUB_EVENT_NAME=pull_request KANI_MANUAL_PROBE=false KANI_PROBE_PROPERTY="$probe_property";
    source scripts/run-kani.sh --run list) >/dev/null 2>&1; then
    echo "Automatic property filtering was accepted" >&2
    exit 1
fi
(
    export GITHUB_EVENT_NAME=workflow_dispatch KANI_MANUAL_PROBE=true KANI_PROBE_PROPERTY="$probe_property"
    source scripts/run-kani.sh --run list
    [[ " ${kani_cbmc_args[*]} " == *" --property $probe_property "* ]]
)
if (export GITHUB_EVENT_NAME=workflow_dispatch KANI_MANUAL_PROBE=true KANI_PROBE_PROPERTY=unknown;
    source scripts/run-kani.sh --run list) >/dev/null 2>&1; then
    echo "Unknown diagnostic property was accepted" >&2
    exit 1
fi
echo "Manual property probe guards passed."
