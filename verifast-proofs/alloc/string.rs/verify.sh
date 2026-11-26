#!/bin/bash
set -e -o pipefail

cd "$(dirname "$0")"
mode=${1:-}
if [[ $# -gt 1 || ( -n "$mode" && "$mode" != --negative ) ]]; then
  echo "Usage: bash verify.sh [--negative]" >&2
  exit 2
fi

export VFVERSION=26.10
. ../../setup-verifast-home
set +x
VF_PATCHED_BIN="$(bash ../../tools/build-patched-verifast.sh)"

# VeriFast 26.10 is built against rustc nightly-2026-09-25 (see setup-verifast-home).
# Build a temporary sysroot from the pinned rust-src. The copied dependency
# sources stay available while VeriFast reads the locations in imported MIR.
VF_RUST_TOOLCHAIN=nightly-2026-09-25
RUSTC="$(rustup which --toolchain "$VF_RUST_TOOLCHAIN" rustc)"
RUSTC_VERSION="$("$RUSTC" -vV)"
HOST_TRIPLE="$(sed -n 's/^host: //p' <<< "$RUSTC_VERSION")"
VF_WORK_ROOT="$(cd ../../../library && pwd)/target"
mkdir -p "$VF_WORK_ROOT"

verify_target() (
  TARGET_TRIPLE=$1
  variant=${2:-}
  WORK_DIR="$(mktemp -d "$VF_WORK_ROOT/vf_string_sysroot.XXXXXX")"
  trap 'rm -rf "$WORK_DIR"' EXIT
  export TMPDIR="$WORK_DIR"

  SYSROOT="$WORK_DIR/sysroot"
  SYSROOT_LIB="$SYSROOT/lib/rustlib/$TARGET_TRIPLE/lib"
  mkdir -p "$SYSROOT_LIB" "$WORK_DIR/core" "$WORK_DIR/alloc"
  RUSTC_SYSROOT="$("$RUSTC" --print sysroot)"
  RUST_SRC="$RUSTC_SYSROOT/lib/rustlib/src/rust/library"
  if [ ! -d "$RUST_SRC/core/src" ] || [ ! -d "$RUST_SRC/alloc/src" ]; then
    rustup component add rust-src --toolchain "$VF_RUST_TOOLCHAIN"
  fi

  echo "Building the String proof sysroot for $TARGET_TRIPLE with $VF_RUST_TOOLCHAIN"
  cp -R "$RUST_SRC/core/src" "$WORK_DIR/core/src"
  ln -s "$RUST_SRC/stdarch" "$WORK_DIR/stdarch"
  ln -s "$RUST_SRC/portable-simd" "$WORK_DIR/portable-simd"
  patch --fuzz=0 -p1 -d "$WORK_DIR/core/src" < core-sysroot.patch
  if [[ -n "$variant" ]]; then
    patch --fuzz=0 -p1 -d "$WORK_DIR/core/src" < "../string.rs-negative/$variant.patch"
  fi
  "$RUSTC" --target "$TARGET_TRIPLE" --crate-name core --edition=2024 "$WORK_DIR/core/src/lib.rs" --crate-type lib \
    -C embed-bitcode=no -Z force-unstable-if-unmarked -A warnings \
    -o "$SYSROOT_LIB/libcore_string.rlib"

  cat > "$WORK_DIR/cb.rs" <<'RS'
#![no_std]
#![feature(compiler_builtins, staged_api)]
#![compiler_builtins]
#![stable(feature = "rust1", since = "1.0.0")]
const _: () = assert!(!core::mem::needs_drop::<core::str::Chars<'static>>());
RS
  "$RUSTC" --target "$TARGET_TRIPLE" --sysroot "$SYSROOT" --crate-name compiler_builtins --edition=2024 "$WORK_DIR/cb.rs" --crate-type lib \
    -C embed-bitcode=no -Z force-unstable-if-unmarked -A warnings \
    --extern core="$SYSROOT_LIB/libcore_string.rlib" \
    -L dependency="$SYSROOT_LIB" \
    -o "$SYSROOT_LIB/libcompiler_builtins.rlib"

  cp -R "$RUST_SRC/alloc/src" "$WORK_DIR/alloc/src"
  patch --fuzz=0 -p1 -d "$WORK_DIR/alloc/src" < alloc-sysroot.patch
  "$RUSTC" --target "$TARGET_TRIPLE" --sysroot "$SYSROOT" --crate-name alloc --edition=2024 "$WORK_DIR/alloc/src/lib.rs" --crate-type lib \
    -C embed-bitcode=no -Z force-unstable-if-unmarked -A warnings \
    --extern core="$SYSROOT_LIB/libcore_string.rlib" \
    --extern compiler_builtins="$SYSROOT_LIB/libcompiler_builtins.rlib" \
    -L dependency="$SYSROOT_LIB" \
    -o "$SYSROOT_LIB/liballoc_nostring.rlib"

  # Extend the release's bundled specs and use a matching local verifier,
  # exporter and refinement checker. The stock installation remains read-only.
  VF_BINDIR="$WORK_DIR/bin"
  mkdir -p "$VF_BINDIR/rust/std"
  for item in "$VERIFAST_HOME/bin/"*; do
    base="$(basename "$item")"
    if [ "$base" = "verifast" ]; then
      cp "$VF_PATCHED_BIN/verifast" "$VF_BINDIR/verifast"
    elif [ "$base" = "vf-rust-mir-exporter" ]; then
      ln -s "$VF_PATCHED_BIN/vf-rust-mir-exporter" "$VF_BINDIR/$base"
    elif [ "$base" != "rust" ]; then
      ln -s "$item" "$VF_BINDIR/$base"
    fi
  done
  for item in "$VERIFAST_HOME/bin/rust/"*; do
    base="$(basename "$item")"
    if [ "$base" = "prelude_core.rsspec" ]; then
      cp "$VF_PATCHED_BIN/rust/$base" "$VF_BINDIR/rust/$base"
    elif [ "$base" != "std" ]; then
      ln -s "$item" "$VF_BINDIR/rust/$base"
    fi
  done
  python3 - "$VERIFAST_HOME/bin/rust/std/lib.rsspec" string_deps.rsspec "$VF_BINDIR/rust/std/lib.rsspec" "$WORK_DIR/string_local.rsspec" <<'PY'
import sys
from pathlib import Path

merged = Path(sys.argv[1]).read_text()
marker = "\n// String crate-local specifications\n"
spec = Path(sys.argv[2]).read_text()
assert spec.count(marker) == 1, "Expected one String crate-local specification marker"
extra, _, local = spec.partition(marker)
# Refine `Chars::next` in the temporary rsspec copy so `None` preserves `chars1.as_str() == chars0.as_str()`
# (needed for `FusedIterator` / repeated `Drain::next` after exhaustion; matches `core::str::Chars::next`).
old_chars_none = "                Option::None => bs == [],"
new_chars_none = "                Option::None => bs == [] &*& chars1.as_str() == chars0.as_str(),"
assert merged.count(old_chars_none) == 1, "Expected one Chars::next Option::None line in bundled std/lib.rsspec"
merged = merged.replace(old_chars_none, new_chars_none, 1)
# Dropping a value ends its initialization, while its storage remains allocated.
drop_start = merged.index("unsafe fn drop_in_place<T: ?Sized>(to_drop: *mut T);")
drop_end = merged.index("\n\n", drop_start)
drop_contract = merged[drop_start:drop_end]
assert drop_contract.count("*to_drop |-> _;") == 2
merged = merged[:drop_start] + drop_contract.replace("*to_drop |-> _;", "*to_drop |-?-> _;") + merged[drop_end:]
# A local binding can be frozen again after Drop ends its initialization.
freeze_start = merged.index("fn freeze<T>(ptr: *T);")
freeze_end = merged.index("//@ on_unwind_ens false;", freeze_start)
freeze_contract = merged[freeze_start:freeze_end]
assert freeze_contract.count("*ptr |-> _") == 2
merged = merged[:freeze_start] + freeze_contract.replace("*ptr |-> _", "*ptr |-?-> _") + merged[freeze_end:]
# Each overlap case supplies the return state of the copy intrinsic.
# Its nested outcome also excludes unwinding once the precondition holds.
copy_start = merged.index("unsafe fn copy<T>(")
copy_end = merged.index("unsafe fn copy_nonoverlapping<T>(", copy_start)
copy_contract = merged[copy_start:copy_end]
old = "|-?-> bs"
updated = []
for line in copy_contract.splitlines(keepends=True):
    if line.rstrip(",\n").endswith(old):
        prefix, end, separator = line.rpartition(old)
        line = prefix + end + " on_unwind_ens false" + separator
    updated.append(line)
copy_fixed = "".join(updated)
assert copy_fixed.count("on_unwind_ens false") == 5
merged = merged[:copy_start] + copy_fixed + merged[copy_end:]
Path(sys.argv[3]).write_text(merged + "\n" + extra)
Path(sys.argv[4]).write_text(local)
PY

  RUSTC_ARGS="--target $TARGET_TRIPLE --crate-type lib --edition=2024 --extern core=$SYSROOT_LIB/libcore_string.rlib --extern alloc=$SYSROOT_LIB/liballoc_nostring.rlib --extern compiler_builtins=$SYSROOT_LIB/libcompiler_builtins.rlib -L dependency=$SYSROOT_LIB -Z force-unstable-if-unmarked -A warnings"

  verifast=(env "LD_LIBRARY_PATH=$VF_BINDIR${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    "$VF_BINDIR/verifast" -rustc_args "$RUSTC_ARGS" -skip_specless_fns)
  verifier=(env "VF_VEC_COLLECT_PROOF=$PWD/remove_matches.vfproof" "${verifast[@]}"
    -extern_spec "self=$WORK_DIR/string_local.rsspec" -allow_ignore_ref_creation -allow_dead_code)
  refinement=("$VF_PATCHED_BIN/refinement-checker" --rustc-args "$RUSTC_ARGS" original/lib.rs)

  check_verifast() {
    local log=$1
    shift
    if ! "$@" > "$log" 2>&1 ||
       grep -Fq 'Detected an inconsistency after axiom instantiations' "$log" ||
       ! grep -Eq '0 errors found \([1-9][0-9]* statements verified\)' "$log"; then
      cat "$log" >&2
      return 1
    fi
    grep -F "0 errors found" "$log"
  }

  if [ "$mode" = --negative ]; then
    expect_rejection() {
      local log=$1 diagnostic=$2
      shift 2
      if "$@" > "$log" 2>&1 ||
         grep -Fq 'Detected an inconsistency after axiom instantiations' "$log" ||
         ! grep -Fq "$diagnostic" "$log"; then
        cat "$log" >&2
        echo "Expected rejection containing '$diagnostic'" >&2
        return 1
      fi
      grep -F "$diagnostic" "$log"
    }

    if [[ -n "$variant" ]]; then
      case "$variant" in
        collect-guard) diagnostic='Unrecognized Iterator::collect forwarding body' ;;
        collect-cleanup) diagnostic='Unrecognized Iterator::collect cleanup' ;;
      esac
      echo "Checking Iterator::collect mutation $variant"
      expect_rejection "$WORK_DIR/$variant.log" "$diagnostic" "${verifier[@]}" verified/lib.rs
      return
    fi

    check_mutation() {
      local name=$1 diagnostic=$2 refinement_diagnostic=${3:-}
      local mutant="$WORK_DIR/$name"
      echo "Checking negative proof $name"
      cp -R verified "$mutant"
      patch --fuzz=0 "$mutant/string.rs" < "../string.rs-negative/$name.patch"
      expect_rejection "$mutant/verifast.log" "$diagnostic" "${verifier[@]}" "$mutant/lib.rs"
      if [ -n "$refinement_diagnostic" ]; then
        expect_rejection "$mutant/refinement.log" "$refinement_diagnostic" "${refinement[@]}" "$mutant/lib.rs"
      fi
    }

    check_mutation replace-range-wrong-boundary 'Cannot prove is_char_boundary' 'are not equal: FieldTerm'
    vec_storage_missing='No matching heap chunks: points_to<std::vec::Vec<u8, std::alloc::Global>>'
    check_mutation replace-range-forget-splice "$vec_storage_missing"
    check_mutation drain-drop-forget-drain "$vec_storage_missing"

    echo 'Checking function-item eligibility'
    expect_rejection "$WORK_DIR/function-item.log" 'Local function item has no verified body: unchecked_by_verifast' \
      "${verifast[@]}" ../string.rs-negative/unverified-function-item.rs
    echo 'Checking that a marked Vec collection requires its proof file'
    expect_rejection "$WORK_DIR/missing-vec-proof.log" 'The annotated Vec collect requires a MIR proof file' \
      env -u VF_VEC_COLLECT_PROOF "${verifast[@]}" ../string.rs-negative/specialized-vec-collect.rs
    echo 'Checking that the default Vec proof rejects the IntoIter specialization'
    expect_rejection "$WORK_DIR/vec-specialization.log" 'Expected one compiler-resolved MIR body for <std::vec::Vec<T> as std::vec::spec_from_iter::SpecFromIter<T, I>>::from_iter' \
      env "VF_VEC_COLLECT_PROOF=$PWD/remove_matches.vfproof" "${verifast[@]}" \
        ../string.rs-negative/specialized-vec-collect.rs
    echo 'Checking layout for a zero-sized MaybeUninit'
    check_verifast "$WORK_DIR/zero-sized-maybe-uninit.log" "${verifast[@]}" ../string.rs-negative/zero-sized-maybe-uninit.rs
    echo 'Checking lifetime inference across branches'
    check_verifast "$WORK_DIR/lifetime-branches.log" "${verifast[@]}" ../string.rs-negative/lifetime-branches.rs
  else
    check_verifast "$WORK_DIR/verifast.log" "${verifier[@]}" verified/lib.rs

    if ! "${refinement[@]}" verified/lib.rs > "$WORK_DIR/refinement.log" 2>&1; then
      cat "$WORK_DIR/refinement.log" >&2
      exit 1
    fi
    grep -F "No refinement errors found" "$WORK_DIR/refinement.log"
  fi
)

verify_target "$HOST_TRIPLE"
if [[ "$mode" == --negative ]]; then
  verify_target "$HOST_TRIPLE" collect-guard
  verify_target "$HOST_TRIPLE" collect-cleanup
else
  verify_target s390x-unknown-linux-gnu
fi

if ! diff original/string.rs ../../../library/alloc/src/string.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi
