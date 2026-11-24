#!/bin/bash

set -euo pipefail

patch_dir=$(cd "$(dirname "$0")" && pwd)
destination=$(cd "${1:?Pass an empty tool installation directory}" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf -- "$build_dir"' EXIT

git clone --quiet --depth 1 --branch 26.10 https://github.com/verifast/verifast.git "$build_dir/verifast"
cd "$build_dir/verifast"
test "$(git rev-parse HEAD)" = f76012fb518703b1d98e243ac4f487f16877cfcb
for patch in "$patch_dir"/*.patch; do
    git apply "$patch"
done

# Use the dependency archive pinned by VeriFast 26.10's setup-build.sh.
. ./config.sh
deps="/tmp/$VFDEPS_NAME"
if [[ ! -x "$deps/bin/dune" ]]; then
    archive="$build_dir/$VFDEPS_NAME-linux.txz"
    curl -fLsS --retry 3 "https://github.com/verifast/vfdeps/releases/download/25.01/$VFDEPS_NAME-linux.txz" -o "$archive"
    printf '8d022c93d51a1d13ec1e782d767c60462405f6865d5ee416f82d6234e93ee580  %s\n' "$archive" | sha256sum --check
    tar -xf "$archive" -C /tmp
fi

cargo +stable install --locked --root "$build_dir/decoder" \
    --git https://github.com/btj/capnpc-ocaml-decoder --rev 2d6606d9b59cd0c88a66729f3f076c10c0c8e0b2
export PATH="$build_dir/decoder/bin:$deps/bin:$PATH"
export CAPNP_INC_DIR="$deps/include" CAPNP_INCLUDE="$deps/include"
export LIBRARY_PATH="$deps/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export LD_LIBRARY_PATH="$deps/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

(
    cd src
    dune build -j 2 vfconsole/vfconsole.exe refinement_checker/main.exe
)
cargo build --locked --release --jobs 2 --target-dir "$build_dir/target" \
    --manifest-path src/rust_frontend/vf_mir_exporter/Cargo.toml

mkdir "$destination/bin"
cp -a bin/. "$destination/bin/"
install -m 755 src/_build/default/vfconsole/vfconsole.exe "$destination/bin/verifast"
install -m 755 src/_build/default/refinement_checker/main.exe "$destination/bin/refinement-checker"
install -m 755 "$build_dir/target/release/vf_mir_exporter" "$destination/bin/vf-rust-mir-exporter"
cp "$deps/lib/libz3.so" "$destination/bin/"
