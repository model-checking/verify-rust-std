#!/bin/bash
# VeriFast proof of Challenge 8 (smallsort), see README.md. Checks the target crates under targets/. For each crate:
#   1. its executable code refines rewritten/ (= original/ + the reviewed rewrites/NNN-*.patch, rebuilt and
#      compared here): only annotations, calls to the trusted std wrappers in place of the calls they wrap
#      (refinement-checker inlines the wrappers), and `for` loops written as their own desugaring were added,
#   2. its trusted blocks in smallsort.rs are exactly trusted/comparator_model.rs, trusted/model_axioms.rs,
#      trusted/std_wrappers.rs and trusted/comparator_call_wrapper.rs (and, in targets/unstable_small_sort/specialized only,
#      trusted/freeze_small_sort_wrapper.rs; no other crate may contain that block), its std_extra.rsspec
#      is exactly trusted/std_extra.rsspec, and `assume` (ghost statement or `assume_correct`) appears
#      nowhere outside the trusted blocks,
#   3. VeriFast accepts it, with -ignore_unwind_paths and -ignore_ref_creation (see README.md, "Verification").
# Also checks once that original/smallsort.rs is still identical to the library source,
# and that the spec of the trusted wrapper in trusted/freeze_small_sort_wrapper.rs is exactly the spec of
# `UnstableSmallSortFreezeTypeImpl::small_sort` in targets/unstable_freeze_small_sort/{default,copy}.
# Both tools compile with `--edition 2024`, the edition core is built with.
#
# Usage: ./verify.sh [DIR...]       (DIR is a crate directory, e.g. targets/swap_if_less or
#                                    targets/stable_small_sort/default; defaults to every crate under targets/)
# Environment: VFVERSION (default 26.10), VERIFAST_HOME (default ~/.verifast/toolchains/verifast-$VFVERSION).
# If VERIFAST_HOME does not exist, the wrappers verifast-proofs/{verifast,refinement-checker} download and
# install that VeriFast release first (verifast-proofs/setup-verifast-home), as for the other proofs.

cd "$(dirname "$0")"

export VFVERSION="${VFVERSION:-26.10}"
export VERIFAST_HOME="${VERIFAST_HOME:-$HOME/.verifast/toolchains/verifast-$VFVERSION}"
VERIFAST_PROOFS_DIR="$(cd ../../../../.. && pwd)"
export PATH="$VERIFAST_HOME/bin:$VERIFAST_PROOFS_DIR:$PATH"

# Cap the memory of VeriFast and refinement-checker (default 8G, override with VF_MEM). VeriFast 26.10 can
# exhaust memory within seconds (e.g. on a 20-element array literal). Each run gets its own systemd scope
# with a hard MemoryMax, so an out-of-memory kill stays inside that scope; an OOM kill inside the caller's
# scope could otherwise stop the caller's whole terminal session. Without a systemd user session (e.g. on
# CI) only the timeout applies.
: "${VF_MEM:=8G}"
# Each run is also stopped after VF_TIMEOUT seconds (default 5400); the timeout runs inside the scope.
: "${VF_TIMEOUT:=5400}"
if systemd-run --user --scope --quiet -p MemoryMax=64M true > /dev/null 2>&1; then
  vf_capped() { systemd-run --user --scope --quiet -p MemoryMax="$VF_MEM" -p MemorySwapMax=0 "$(type -P timeout)" "$VF_TIMEOUT" "$(type -P "$1")" "${@:2}"; }
else
  vf_capped() { timeout "$VF_TIMEOUT" "$(type -P "$1")" "${@:2}"; }
fi
# VeriFast 26.10 can derive false from its own axioms (e.g. for a by-value struct of two structs holding
# NonNull<K>) and then report "0 errors found" for anything. Its solver then prints "Detected an
# inconsistency". That line also appears in sound runs (the accepted RawVec proof prints it), so it is not
# an error by itself: it is reported on the terminal (fd 3), next to the crate's result, and a PASS printed
# with it must be audited: check the crate with `//@ assert false;` placed where its proof's assertions are.
exec 3>&2
verifast() {
  local out rc
  out=$(vf_capped verifast "$@" 2>&1); rc=$?
  if grep -q "Detected an inconsistency" <<< "$out"; then
    echo "warning: VeriFast reported an inconsistency in its axioms for ${*: -1}; audit before trusting a PASS" >&3
  fi
  printf '%s\n' "$out"
  return $rc
}
refinement-checker() { vf_capped refinement-checker "$@"; }

LIBRARY_FILE=../../../../../../library/core/src/slice/sort/shared/smallsort.rs
if ! diff original/smallsort.rs "$LIBRARY_FILE"; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  exit 1
fi

RUSTC_ARGS="--edition 2024"

# The trusted master files and the gate tools are pinned: sha256 over, for each file in this order, its
# name, a newline and its content. Changing any of them needs a new review and a new hash here.
TRUSTED_FILES=(trusted/comparator_model.rs trusted/comparator_call_wrapper.rs trusted/std_wrappers.rs
               trusted/freeze_small_sort_wrapper.rs trusted/std_extra.rsspec trusted/model_axioms.rs
               tools/entry_spec_pin.py tools/ghost_gate.py tools/copy_gate.py spec/entry_spec_pins.json
               rewrites/apply.sh rewrites/001-insert-tail-explicit-guard-drop.patch)
TRUSTED_SHA256=0850f4af2b19bfb838073598192e6bfe80ad8b02daa5da348fd9935ef319201a
trusted_hash() {
  for f in "${TRUSTED_FILES[@]}"; do echo "$f"; cat "$f"; done | sha256sum | cut -d' ' -f1
}
if [[ $(trusted_hash) != "$TRUSTED_SHA256" ]] || [[ $(ls trusted | wc -l) != 6 ]] || [[ $(ls rewrites/*.patch | wc -l) != 1 ]]; then
  echo "error: the trusted files differ from the reviewed ones (sha256 mismatch or extra/missing file in trusted/)"
  exit 1
fi

# Trusted blocks of smallsort.rs, and their master copies. Every crate contains BLOCKS; FREEZE_BLOCK is
# required in FREEZE_BLOCK_CRATE and forbidden elsewhere.
BLOCKS=("COMPARATOR MODEL" "MODEL AXIOMS" "STD WRAPPERS" "COMPARATOR CALL WRAPPER")
MASTERS=(trusted/comparator_model.rs trusted/model_axioms.rs trusted/std_wrappers.rs trusted/comparator_call_wrapper.rs)
FREEZE_BLOCK="FREEZE SMALL SORT WRAPPER"
FREEZE_MASTER=trusted/freeze_small_sort_wrapper.rs
FREEZE_BLOCK_CRATE=targets/unstable_small_sort/specialized
FREEZE_SPEC_CRATES=(targets/unstable_freeze_small_sort/default targets/unstable_freeze_small_sort/copy)
STD_EXTRA=trusted/std_extra.rsspec
# A ghost `assume(...)` statement or an `assume_correct` clause (but not `intrinsics::assume(...)`).
ASSUME_RE='(^|[^:_A-Za-z0-9])assume(\(|_correct)'

begin_marker() { echo "// ===== BEGIN TRUSTED $1 ====="; }
end_marker() { echo "// ===== END TRUSTED $1 ====="; }

# Prints the trusted block $2 of file $1, markers included.
trusted_block() {
  sed -n "\|^$(begin_marker "$2")\$|,\|^$(end_marker "$2")\$|p" "$1"
}

# Prints file $1 without its trusted blocks.
outside_trusted_blocks() {
  local script=()
  for b in "${BLOCKS[@]}" "$FREEZE_BLOCK"; do
    script+=(-e "\|^$(begin_marker "$b")\$|,\|^$(end_marker "$b")\$|d")
  done
  sed "${script[@]}" "$1"
}

# Prints the spec (the `/*@ ... @*/` blocks before the body) of `fn small_sort<F>` in the impls of
# `UnstableSmallSortFreezeTypeImpl` in file $1 (each line stripped of leading whitespace), or, with $2 =
# wrapper, of the wrapper in $1. Fails unless exactly one such function has a spec.
freeze_spec() {
  python3 - "$1" "$2" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
if sys.argv[2] == 'wrapper':
    pat = r'fn unstable_small_sort_freeze_type_impl_small_sort__VeriFast_wrapper<[^\n]*\n((?:/\*@.*?@\*/\s*)+)//@ assume_correct'
else:
    s = s[s.index('pub(crate) trait UnstableSmallSortFreezeTypeImpl'):s.index('const SMALL_SORT_FALLBACK_THRESHOLD')]
    pat = r'fn small_sort<F>\(v: &mut \[T\], is_less: &mut F\)\s*where\s*F: FnMut\(&T, &T\) -> bool,\s*((?:/\*@.*?@\*/\s*)+)\{'
specs = re.findall(pat, s, flags=re.S)
if len(specs) != 1:
    sys.exit(1)
print('\n'.join(l.strip() for l in specs[0].strip().split('\n')))
PY
}

wrapper_spec=$(freeze_spec "$FREEZE_MASTER" wrapper) || { echo "error: no spec found in $FREEZE_MASTER"; exit 1; }
for c in "${FREEZE_SPEC_CRATES[@]}"; do
  if [[ "$(freeze_spec "$c/smallsort.rs" impl)" != "$wrapper_spec" ]]; then
    echo "error: the spec in $FREEZE_MASTER differs from the spec of UnstableSmallSortFreezeTypeImpl::small_sort in $c"
    exit 1
  fi
done

# rewritten/ must be original/ + the pinned patches (rewrites/apply.sh), byte for byte.
rw_tmp=$(mktemp -d)
cp original/smallsort.rs original/lib.rs "$rw_tmp/"
for p in rewrites/[0-9][0-9][0-9]-*.patch; do (cd "$rw_tmp" && patch -s -p1 < "$OLDPWD/$p") || { echo "error: $p does not apply"; exit 1; }; done
if ! diff -q "$rw_tmp/smallsort.rs" rewritten/smallsort.rs > /dev/null || ! diff -q "$rw_tmp/lib.rs" rewritten/lib.rs > /dev/null; then
  echo "error: rewritten/ is not original/ + rewrites/*.patch (run rewrites/apply.sh)"
  exit 1
fi
rm -rf "$rw_tmp"

if [[ $# -eq 0 ]]; then
  set -- $(find targets -name lib.rs -printf '%h\n' | sort)
fi

failed=0
for dir in "$@"; do
  dir="${dir%/}"
  if ! refinement-checker --rustc-args "$RUSTC_ARGS" rewritten/lib.rs "$dir/lib.rs" > /dev/null 2>&1; then
    echo "FAIL $dir: code differs from rewritten/ (refinement-checker)"
    failed=1
    continue
  fi
  trusted_ok=1
  for i in "${!BLOCKS[@]}"; do
    if [[ $(grep -c "^$(begin_marker "${BLOCKS[$i]}")\$" "$dir/smallsort.rs") != 1 ]] ||
       ! diff -q <(trusted_block "$dir/smallsort.rs" "${BLOCKS[$i]}") "${MASTERS[$i]}" > /dev/null; then
      echo "FAIL $dir: trusted block ${BLOCKS[$i]} in smallsort.rs differs from ${MASTERS[$i]}"
      trusted_ok=0
    fi
  done
  n=$(grep -c "^$(begin_marker "$FREEZE_BLOCK")\$" "$dir/smallsort.rs")
  if [[ "$dir" == "$FREEZE_BLOCK_CRATE" ]]; then
    if [[ $n != 1 ]] || ! diff -q <(trusted_block "$dir/smallsort.rs" "$FREEZE_BLOCK") "$FREEZE_MASTER" > /dev/null; then
      echo "FAIL $dir: trusted block $FREEZE_BLOCK in smallsort.rs differs from $FREEZE_MASTER"
      trusted_ok=0
    fi
  elif [[ $n != 0 ]] || grep -q "unstable_small_sort_freeze_type_impl_small_sort__VeriFast_wrapper" "$dir/smallsort.rs"; then
    echo "FAIL $dir: trusted block $FREEZE_BLOCK is only allowed in $FREEZE_BLOCK_CRATE"
    trusted_ok=0
  fi
  if ! diff -q "$dir/std_extra.rsspec" "$STD_EXTRA" > /dev/null 2>&1; then
    echo "FAIL $dir: std_extra.rsspec differs from $STD_EXTRA"
    trusted_ok=0
  fi
  if outside_trusted_blocks "$dir/smallsort.rs" | grep -qE "$ASSUME_RE" || grep -qE "$ASSUME_RE" "$dir/lib.rs"; then
    echo "FAIL $dir: assume used outside the trusted blocks"
    trusted_ok=0
  fi
  if [[ $trusted_ok == 0 ]]; then
    failed=1
    continue
  fi
  # -allow_dead_code: unwind cleanup code after calls that cannot unwind is unreachable.
  # Pinned entry specifications (spec/entry_spec_pins.json, tools/entry_spec_pin.py): not changed,
  # strengthened, weakened or removed (a removed spec would make -skip_specless_fns skip the entry).
  if ! pin_out=$(python3 tools/entry_spec_pin.py check "$dir" 2>&1); then
    echo "FAIL $dir: $pin_out"; failed=1; continue
  fi
  # Ghost constructs that let VeriFast 26.10 derive false without any axiom (tools/ghost_gate.py).
  if ! gate_out=$(python3 tools/ghost_gate.py "$dir" 2>&1); then
    echo "FAIL $dir: $gate_out"; failed=1; continue
  fi
  # Direct `ptr::copy`-family calls (unbounded prelude spec, see tools/copy_gate.py): only the trusted
  # wrapper ptr_copy_1__VeriFast_wrapper may call ptr::copy.
  if ! copy_out=$(python3 tools/copy_gate.py "$dir" 2>&1); then
    echo "FAIL $dir: $copy_out"; failed=1; continue
  fi
  output=$(verifast -rustc_args "$RUSTC_ARGS" -skip_specless_fns -allow_assume -allow_dead_code -ignore_unwind_paths -ignore_ref_creation -extern_spec "std=$dir/std_extra.rsspec" "$dir/lib.rs" 2>&1)
  if grep -q "^0 errors found" <<< "$output"; then
    echo "PASS $dir"
  else
    echo "FAIL $dir: $(grep -E "error" <<< "$output" | grep -v '^ *|' | head -1)"
    failed=1
  fi
done
exit $failed
