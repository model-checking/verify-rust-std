#!/usr/bin/env bash
set -euo pipefail

if [[ "$(uname -s)" != Linux || "${1:-}" != --remote ]]; then
  echo 'The frontend build is restricted to the remote Linux verification job.' >&2
  exit 2
fi

backend_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
source_commit=809de4596839b739dd999f9e462242c835e3af46
source_hash=0238aec44351c877b3c859c7252340540923c1b620f9981be176d7cea4e67a1e
build_dir="$(mktemp -d "${TMPDIR:-/tmp}/verifast-iter-backend.XXXXXXXX")"
trap 'rm -rf -- "$build_dir"' EXIT

command -v capnp >/dev/null
curl --fail --location --retry 2 --max-time 120 --max-filesize 67108864 \
  --output "$build_dir/source.tar.gz" \
  "https://codeload.github.com/verifast/verifast/tar.gz/$source_commit"
printf '%s  %s\n' "$source_hash" "$build_dir/source.tar.gz" | sha256sum --check
tar -xzf "$build_dir/source.tar.gz" --strip-components=1 -C "$build_dir" \
  "verifast-$source_commit/src/rust_frontend"
patch --batch --fuzz=0 --directory="$build_dir" -p1 < "$backend_dir/add-unchecked.patch"

rustup component add --toolchain nightly-2026-02-05 rustc-dev llvm-tools
CARGO_BUILD_JOBS=1 CARGO_PROFILE_DEV_DEBUG=0 RUSTFLAGS='-C rpath=yes' \
  cargo +nightly-2026-02-05 build --locked --jobs 1 \
  --manifest-path "$build_dir/src/rust_frontend/vf_mir_exporter/Cargo.toml"
install -m 755 "$build_dir/src/rust_frontend/vf_mir_exporter/target/debug/vf_mir_exporter" \
  "${VERIFAST_HOME:?}/bin/vf-rust-mir-exporter"
echo 'Prepared VeriFast 26.09 with the checked AddUnchecked frontend mapping'
