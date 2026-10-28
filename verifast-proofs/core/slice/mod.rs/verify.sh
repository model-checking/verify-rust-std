#!/bin/bash
set -e -x

export VFVERSION=26.10
if [ -f ../../../setup-verifast-home ]; then
  . ../../../setup-verifast-home
fi
if ! command -v verifast >/dev/null 2>&1 && [ -d "$VERIFAST_HOME/bin" ]; then
  export PATH="$VERIFAST_HOME/bin:$PATH"
fi

# VeriFast 26.10 is built against rustc nightly-2026-09-25 (see setup-verifast-home).
# The `core` sysroot below must be compiled by that exact rustc, so it is built from the
# `rust-src` component of that toolchain rather than from the repository's `library/core`
# subtree, which tracks a newer nightly whose intrinsics and feature gates that rustc
# does not know.
VF_RUST_TOOLCHAIN=nightly-2026-09-25
RUSTC="$(rustup which --toolchain $VF_RUST_TOOLCHAIN rustc 2>/dev/null || rustup which rustc 2>/dev/null || which rustc)"
CARGO="$(rustup which --toolchain $VF_RUST_TOOLCHAIN cargo 2>/dev/null || rustup which cargo 2>/dev/null || which cargo)"
HOST_TRIPLE="$("$RUSTC" -vV | sed -n 's/^host: //p')"
if [[ "$HOST_TRIPLE" == *"apple-darwin"* ]]; then
  DYLIB_EXT="dylib"
else
  DYLIB_EXT="so"
fi

SYSROOT_REL="../../../../library/target/vf_sysroot"
SYSROOT_LIB_REL="$SYSROOT_REL/lib/rustlib/$HOST_TRIPLE/lib"

if [ ! -f "$SYSROOT_LIB_REL/libcore_noslice.rlib" ] || [ ! -f "$SYSROOT_LIB_REL/libsafety.$DYLIB_EXT" ]; then
  mkdir -p "$SYSROOT_LIB_REL"
  RUSTC_SYSROOT="$("$RUSTC" --print sysroot)"
  cp -n "$RUSTC_SYSROOT/lib/rustlib/$HOST_TRIPLE/lib/"* "$SYSROOT_LIB_REL/" || true
  if [ -d ../../../../library/contracts/safety ]; then
    (cd ../../../../library/contracts/safety && RUSTC="$RUSTC" "$CARGO" build --release)
    cp "../../../../library/target/release/libsafety.$DYLIB_EXT" "$SYSROOT_LIB_REL/"
  elif [ -d ../../../../deps/safety ]; then
    (cd ../../../../deps/safety && RUSTC="$RUSTC" "$CARGO" build --release)
    cp "../../../../deps/safety/target/release/libsafety.$DYLIB_EXT" "$SYSROOT_LIB_REL/"
  fi
  RUST_SRC="$RUSTC_SYSROOT/lib/rustlib/src/rust/library"
  if [ ! -d "$RUST_SRC/core/src" ]; then
    rustup component add rust-src --toolchain "$VF_RUST_TOOLCHAIN"
  fi
  CORE_SRC_TMP="$SYSROOT_REL/core_src/core"
  rm -rf "$SYSROOT_REL/core_src"
  mkdir -p "$CORE_SRC_TMP"
  ln -s "$RUST_SRC/stdarch" "$SYSROOT_REL/core_src/stdarch"
  ln -s "$RUST_SRC/portable-simd" "$SYSROOT_REL/core_src/portable-simd"
  cp -R "$RUST_SRC/core/src" "$CORE_SRC_TMP/src"
  # The four visibility/attribute edits that let the slice sources compile as a separate
  # crate against this `core` (listed in README.md, "Sysroot").
  patch -p1 -d "$CORE_SRC_TMP/src" < core-sysroot.patch
  "$RUSTC" --crate-name core --edition=2024 "$CORE_SRC_TMP/src/lib.rs" --crate-type lib \
    -C embed-bitcode=no -Z force-unstable-if-unmarked -A warnings \
    -L dependency="$SYSROOT_LIB_REL" \
    --extern "safety=$SYSROOT_LIB_REL/libsafety.$DYLIB_EXT" \
    -o "$SYSROOT_LIB_REL/libcore_noslice.rlib"
  rm -rf "$SYSROOT_REL/core_src"
fi

SYSROOT="$(cd "$SYSROOT_REL" && pwd)"
SYSROOT_LIB="$SYSROOT/lib/rustlib/$HOST_TRIPLE/lib"
RUSTC_ARGS="--crate-type lib --edition=2024 --extern core=$SYSROOT_LIB/libcore_noslice.rlib --extern safety=$SYSROOT_LIB/libsafety.$DYLIB_EXT -L dependency=$SYSROOT_LIB -Z force-unstable-if-unmarked -A warnings"

verifast -rustc_args "$RUSTC_ARGS" -extern_spec std=core.rsspec -skip_specless_fns -ignore_unwind_paths -allow_assume -allow_ignore_ref_creation verified/lib.rs
refinement-checker --rustc-args "$RUSTC_ARGS" original/lib.rs verified/lib.rs > /dev/null
if ! diff original/slice.rs ../../../../library/core/src/slice/mod.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi
if ! diff original/slice/raw.rs ../../../../library/core/src/slice/raw.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi
if ! diff original/slice/rotate.rs ../../../../library/core/src/slice/rotate.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi

