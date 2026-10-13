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
check_binary_exists "$build_dir" expected

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
