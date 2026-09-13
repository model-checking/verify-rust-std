#!/usr/bin/env bash
set -euo pipefail

if [[ "$(uname -s)" != Linux || "${1:-}" != --remote ]]; then
  echo 'The frontend build is restricted to the remote Linux verification job.' >&2
  exit 2
fi

backend_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# The cached exporter still needs the pinned toolchain's shared libraries.
rustup component add --toolchain nightly-2026-02-05 rustc-dev llvm-tools
cache_key="$(sha256sum "$backend_dir/prepare.sh" "$backend_dir/add-unchecked.patch" \
  "$backend_dir/const-generics.patch" "$backend_dir/nonzero-usize.patch" \
  "$backend_dir/maybeuninit-ownership.patch" | sha256sum | cut -d ' ' -f 1)"
cache_dir="$HOME/.cache/verifast-iter-adapters/$cache_key"
if [[ -f "$cache_dir/checksums" ]]; then
  (cd "$cache_dir" && sha256sum --check checksums)
  install -m 755 "$cache_dir/verifast" "${VERIFAST_HOME:?}/bin/verifast"
  install -m 755 "$cache_dir/vf-rust-mir-exporter" "$VERIFAST_HOME/bin/vf-rust-mir-exporter"
  install -m 755 "$cache_dir/refinement-checker" "$VERIFAST_HOME/bin/refinement-checker"
  install -m 644 "$cache_dir/std-lib.rsspec" "$VERIFAST_HOME/bin/rust/std/lib.rsspec"
  echo 'Restored the patched frontend; all proof and regression checks will run'
  exit 0
fi
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
  "verifast-$source_commit/src" "verifast-$source_commit/bin"
patch --batch --fuzz=0 --directory="$build_dir" -p1 < "$backend_dir/add-unchecked.patch"
patch --batch --fuzz=0 --directory="$build_dir" -p1 < "$backend_dir/const-generics.patch"
patch --batch --fuzz=0 --directory="$build_dir" -p1 < "$backend_dir/nonzero-usize.patch"
patch --batch --fuzz=0 --directory="$build_dir" -p1 < "$backend_dir/maybeuninit-ownership.patch"

# Use the dependency bundle pinned by upstream's setup-build.sh. Its compiler
# and package paths are built for /tmp/vfdeps-adf88dc on Linux.
curl --fail --location --retry 2 --max-time 180 --max-filesize 536870912 \
  --output "$build_dir/deps.txz" \
  https://github.com/verifast/vfdeps/releases/download/25.01/vfdeps-adf88dc-linux.txz
printf '%s  %s\n' \
  8d022c93d51a1d13ec1e782d767c60462405f6865d5ee416f82d6234e93ee580 \
  "$build_dir/deps.txz" | sha256sum --check
tar -xjf "$build_dir/deps.txz" --directory=/tmp
export PATH="/tmp/vfdeps-adf88dc/bin:$PATH"
export CAPNP_INCLUDE=/tmp/vfdeps-adf88dc/include
export CAPNP_INC_DIR="$CAPNP_INCLUDE"
# The dynamic linker expands this token after the executable is installed.
# shellcheck disable=SC2016
export OCAMLOPT_CCLIB_FLAGS='-Wl,-rpath=$ORIGIN'
export Z3_DLL_DIR=/tmp/vfdeps-adf88dc/lib

CARGO_BUILD_JOBS=1 cargo +nightly-2026-02-05 install --locked --jobs 1 \
  --git https://github.com/btj/capnpc-ocaml-decoder \
  --rev 2d6606d9b59cd0c88a66729f3f076c10c0c8e0b2 --root "$build_dir/decoder"
export PATH="$build_dir/decoder/bin:$PATH"
CARGO_BUILD_JOBS=1 CARGO_PROFILE_DEV_DEBUG=0 RUSTFLAGS='-C rpath=yes' \
  cargo +nightly-2026-02-05 build --locked --jobs 1 \
  --manifest-path "$build_dir/src/rust_frontend/vf_mir_exporter/Cargo.toml"
install -m 755 "$build_dir/src/rust_frontend/vf_mir_exporter/target/debug/vf_mir_exporter" \
  "${VERIFAST_HOME:?}/bin/vf-rust-mir-exporter"
(
  cd "$build_dir/src"
  dune build -j 1 vfconsole/vfconsole.exe refinement_checker/main.exe
)
install -m 755 "$build_dir/src/_build/default/vfconsole/vfconsole.exe" "$VERIFAST_HOME/bin/verifast"
install -m 755 "$build_dir/src/_build/default/refinement_checker/main.exe" \
  "$VERIFAST_HOME/bin/refinement-checker"
install -m 644 "$build_dir/bin/rust/std/lib.rsspec" "$VERIFAST_HOME/bin/rust/std/lib.rsspec"
mkdir -p "$cache_dir"
install -m 755 "$VERIFAST_HOME/bin/verifast" "$cache_dir/verifast"
install -m 755 "$VERIFAST_HOME/bin/vf-rust-mir-exporter" "$cache_dir/vf-rust-mir-exporter"
install -m 755 "$VERIFAST_HOME/bin/refinement-checker" "$cache_dir/refinement-checker"
install -m 644 "$VERIFAST_HOME/bin/rust/std/lib.rsspec" "$cache_dir/std-lib.rsspec"
(cd "$cache_dir" && sha256sum verifast vf-rust-mir-exporter refinement-checker std-lib.rsspec > checksums)
echo 'Prepared VeriFast 26.09 with checked addition and symbolic usize const parameters'
