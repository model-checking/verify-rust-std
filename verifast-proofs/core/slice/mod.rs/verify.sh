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
  python3 - "$CORE_SRC_TMP/src" << 'PYEOF'
import sys, os

src_dir = sys.argv[1]

# 1. Make RangeInclusive fields pub in ops/range.rs
p = os.path.join(src_dir, "ops/range.rs")
s = open(p).read()
s = s.replace("pub(crate) start: Idx,", '#[stable(feature = "rust1", since = "1.0.0")] pub start: Idx,')
s = s.replace("pub(crate) end: Idx,", '#[stable(feature = "rust1", since = "1.0.0")] pub end: Idx,')
s = s.replace("pub(crate) exhausted: bool,", '#[stable(feature = "rust1", since = "1.0.0")] pub exhausted: bool,')
open(p, "w").write(s)

# 2. Make new() pub in slice/iter.rs and slice/iter/macros.rs
for rel in ["slice/iter.rs", "slice/iter/macros.rs"]:
    p = os.path.join(src_dir, rel)
    s = open(p).read()
    s = s.replace("pub(super) const fn new(", '#[stable(feature = "rust1", since = "1.0.0")] #[rustc_const_stable(feature = "rust1", since = "1.0.0")] pub const fn new(')
    s = s.replace("pub(crate) const fn new(", '#[stable(feature = "rust1", since = "1.0.0")] #[rustc_const_stable(feature = "rust1", since = "1.0.0")] pub const fn new(')
    s = s.replace("pub(super) fn new(", '#[stable(feature = "rust1", since = "1.0.0")] pub fn new(')
    s = s.replace("pub(crate) fn new(", '#[stable(feature = "rust1", since = "1.0.0")] pub fn new(')
    open(p, "w").write(s)

# 3. In slice/mod.rs and slice/raw.rs, comment out #[lang = "slice_len_fn"] and #[rustc_diagnostic_item
for rel in ["slice/mod.rs", "slice/raw.rs"]:
    p = os.path.join(src_dir, rel)
    s = open(p).read()
    s = s.replace('#[lang = "slice_len_fn"]', '// #[lang = "slice_len_fn"]')
    s = s.replace('#[rustc_diagnostic_item =', '// #[rustc_diagnostic_item =')
    open(p, "w").write(s)

# 4. In slice/mod.rs, make inherent methods on [T], [u8], [[T; N]] pub(crate)
p = os.path.join(src_dir, "slice/mod.rs")
lines = open(p).readlines()
in_slice_impl = False
brace_depth = 0
out = []
for line in lines:
    stripped = line.strip()
    if stripped.startswith("impl") and ("[T]" in stripped or "[u8]" in stripped or "[[T; N]]" in stripped) and " for " not in stripped:
        in_slice_impl = True
    if in_slice_impl:
        brace_depth += line.count("{") - line.count("}")
        if line.startswith("    pub const fn ") or line.startswith("    pub fn ") or line.startswith("    pub const unsafe fn ") or line.startswith("    pub unsafe fn "):
            line = line.replace("    pub ", "    pub(crate) ", 1)
        if brace_depth <= 0 and "{" not in line and "}" in line:
            in_slice_impl = False
            brace_depth = 0
    out.append(line)
open(p, "w").write("".join(out))
PYEOF
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

verifast -rustc_args "$RUSTC_ARGS" -extern_spec std=core.rsspec -skip_specless_fns -ignore_unwind_paths -allow_assume -allow_ignore_ref_creation -allow_dead_code verified/lib.rs
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

