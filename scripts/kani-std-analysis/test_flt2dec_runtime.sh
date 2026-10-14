#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_dir=$(cd -- "$script_dir/../.." && pwd)
common="$script_dir/runtime-common.rs"
baseline="$script_dir/runtime-baseline-grisu.rs"
dragon_baseline="$script_dir/runtime-baseline-dragon.rs"
[[ ! -e "$common" && ! -e "$baseline" && ! -e "$dragon_baseline" ]]
scratch=$(mktemp -d)
trap 'rm -f "$common" "$baseline" "$dragon_baseline"; rm -rf "$scratch"' EXIT

curl --fail --location --retry 3 --output "$baseline" \
    https://raw.githubusercontent.com/model-checking/verify-rust-std/f9a85eb1e74426b0200e2e14c8ba02bccbc2e7de/library/core/src/num/imp/flt2dec/strategy/grisu.rs
curl --fail --location --retry 3 --output "$dragon_baseline" \
    https://raw.githubusercontent.com/model-checking/verify-rust-std/f9a85eb1e74426b0200e2e14c8ba02bccbc2e7de/library/core/src/num/imp/flt2dec/strategy/dragon.rs
python3 -I - "$repo_dir" "$common" <<'PY'
from pathlib import Path
import sys

source = (Path(sys.argv[1]) / "library/core/src/num/imp/flt2dec/mod.rs").read_text()
constant = next(line for line in source.splitlines() if line.startswith("pub const MAX_SIG_DIGITS:"))
start = source.index("pub fn round_up(")
end = source.index("\n}\n", start) + 3
Path(sys.argv[2]).write_text(constant + "\n" + source[start:end])
PY

rustc +nightly-2026-09-25 --edition 2024 --test \
    -C opt-level=2 -C debug-assertions=yes -C overflow-checks=yes \
    "$script_dir/test_flt2dec_runtime.rs" -o "$scratch/runtime-tests"
"$scratch/runtime-tests"
