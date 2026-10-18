#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
tool_dir=$(cd -- "${1:?path to patched CBMC bin directory}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

c++ -std=c++17 -O1 "$script_dir/test_cbmc_loop_assigns.cpp" -o "$scratch/loop-assigns-tests"
"$scratch/loop-assigns-tests" "$tool_dir" "$scratch" "$tool_dir/goto-cc"
