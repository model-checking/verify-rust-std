#!/bin/bash
set -e -o pipefail

tool_dir="$(cd "$(dirname "$0")" && pwd)"
toolchain=nightly-2026-09-25
tool_bin_ready() {
  local bin=$1
  [[ -x "$bin/verifast" && -x "$bin/refinement-checker" &&
     -x "$bin/vf-rust-mir-exporter" && -f "$bin/rust/prelude_core.rsspec" ]]
}

if [[ -n "${VF_PATCHED_VERIFAST_BIN:-}" ]]; then
  bin=$VF_PATCHED_VERIFAST_BIN
  if [[ -f "$bin" ]]; then bin=$(dirname "$bin"); fi
  if ! tool_bin_ready "$bin"; then
    echo 'VF_PATCHED_VERIFAST_BIN must identify a matching VeriFast, refinement checker, exporter, and prelude.' >&2
    exit 1
  fi
  cd "$bin" && pwd
  exit
fi

cd "$tool_dir"
proof_patches=(patches/verifast-26.10/[0-9][0-9]-*.patch)
cache="$(cd ../../library && pwd)/target/vf_verifast_patched"
key="$(shasum -a 256 build-patched-verifast.sh "${proof_patches[@]}" | shasum -a 256 | cut -d ' ' -f 1)"
installation="$cache/$key"
if tool_bin_ready "$installation/bin"; then
  printf '%s\n' "$installation/bin"
  exit 0
fi

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'Building the patched VeriFast requires x86-64 Linux. Set VF_PATCHED_VERIFAST_BIN to a matching prebuilt toolchain on other hosts.' >&2
  exit 1
fi

mkdir -p "$cache"
build_dir="$(mktemp -d "$cache/.build.XXXXXX")"
publish_dir="$(mktemp -d "$cache/.install.XXXXXX")"
deps_stage=""
trap 'rm -rf "$build_dir" "$publish_dir" "$deps_stage"' EXIT
export TMPDIR="$build_dir" DUNE_CACHE=disabled

source_archive="${VF_STRING_SOURCE_ARCHIVE:-$build_dir/verifast-26.10.tar.gz}"
if [[ -z "${VF_STRING_SOURCE_ARCHIVE:-}" ]]; then
  curl -fLsS --retry 3 -o "$source_archive" https://codeload.github.com/verifast/verifast/tar.gz/refs/tags/26.10
fi
printf '%s  %s\n' d8ac9f2f744216460c440560e2b23de81d57fcdf5384689e4983adca0fadc37a "$source_archive" | shasum -a 256 -c >&2
tar -xf "$source_archive" -C "$build_dir"
source_dir="$build_dir/verifast-26.10"

# The upstream archive uses CRLF for these sources. Store the patch with LF.
sed -i 's/\r$//' "$source_dir/src/"{frontend/ast,frontend/verifast0,verifast,verifast1,verify_expr}.ml
for proof_patch in "${proof_patches[@]}"; do
  patch --fuzz=0 -p1 -d "$source_dir" < "$proof_patch" >&2
done

# Keep the extracted exporter out of the enclosing Rust library workspace.
# Its local Cap'n Proto dependencies inherit their own workspace metadata.
cat >> "$source_dir/src/rust_frontend/vf_mir_exporter/Cargo.toml" <<'TOML'

[workspace]
exclude = ["capnproto-rust/capnp", "capnproto-rust/capnpc"]
TOML

# The prebuilt vfdeps OCaml toolchain expects its installation prefix at /tmp/vfdeps-adf88dc.
deps="/tmp/vfdeps-adf88dc"
if [[ -n "${VF_STRING_VFDEPS:-}" && ! -e "$deps" ]]; then
  ln -s "$(realpath "$VF_STRING_VFDEPS")" "$deps"
fi
if [[ ! -x "$deps/bin/dune" ]]; then
  deps_archive="$build_dir/vfdeps-adf88dc-linux.txz"
  curl -fLsS --retry 3 -o "$deps_archive" https://github.com/verifast/vfdeps/releases/download/25.01/vfdeps-adf88dc-linux.txz
  printf '%s  %s\n' 8d022c93d51a1d13ec1e782d767c60462405f6865d5ee416f82d6234e93ee580 "$deps_archive" | shasum -a 256 -c >&2
  deps_stage="$(mktemp -d /tmp/.vfdeps.XXXXXX)"
  tar -xf "$deps_archive" -C "$deps_stage"
  mv -nT "$deps_stage/vfdeps-adf88dc" "$deps" || true
  rm -rf "$deps_stage"
fi

export PATH="$deps/bin:$PATH"
export CAPNP_INC_DIR="$deps/include" CAPNP_INCLUDE="$deps/include"
export LIBRARY_PATH="$deps/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export LD_LIBRARY_PATH="$deps/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

decoder_path="${VF_STRING_DECODER:-}"
if [[ -z "$decoder_path" ]]; then
  cargo +stable install --locked --git https://github.com/btj/capnpc-ocaml-decoder \
    --rev 2d6606d9b59cd0c88a66729f3f076c10c0c8e0b2 --root "$build_dir/decoder" >&2
  decoder_path="$build_dir/decoder/bin/capnpc-ocaml-decoder"
fi
if [[ ! -x "$decoder_path" ]]; then
  echo "Cannot execute $decoder_path" >&2
  exit 1
fi
mkdir -p "$build_dir/tools"
ln -s "$(realpath "$decoder_path")" "$build_dir/tools/capnpc-ocaml-decoder"
export PATH="$build_dir/tools:$PATH"

rustc_dev="$(rustup run "$toolchain" rustc --print sysroot)/lib/rustlib/rustc-src/rust/compiler"
if [[ ! -d "$rustc_dev" ]]; then
  rustup component add --toolchain "$toolchain" rustc-dev llvm-tools-preview >&2
fi

jobs=${VF_STRING_BUILD_JOBS:-4}
(cd "$source_dir/src" && dune build -j "$jobs" vfconsole/vfconsole.exe refinement_checker/main.exe) >&2
(cd "$source_dir/src/rust_frontend/vf_mir_exporter" &&
  cargo +"$toolchain" build --locked --release --jobs "$jobs" --target-dir "$build_dir/exporter") >&2

mkdir -p "$publish_dir/bin/rust"
install -m755 "$source_dir/src/_build/default/vfconsole/vfconsole.exe" "$publish_dir/bin/verifast"
install -m755 "$source_dir/src/_build/default/refinement_checker/main.exe" "$publish_dir/bin/refinement-checker"
install -m755 "$build_dir/exporter/release/vf_mir_exporter" "$publish_dir/bin/vf-rust-mir-exporter"
install -m644 "$source_dir/bin/rust/prelude_core.rsspec" "$publish_dir/bin/rust/prelude_core.rsspec"
mv -nT "$publish_dir" "$installation"
tool_bin_ready "$installation/bin"
printf '%s\n' "$installation/bin"
