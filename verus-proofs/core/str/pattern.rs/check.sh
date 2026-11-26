#!/usr/bin/env bash
# Checks the Verus proof of `StrSearcher` in `library/core/src/str/pattern.rs`.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
proofs=$(cd "$here/../../.." && pwd)
root=$(cd "$proofs/.." && pwd)
# Verified on Verus 28029ac (0.2026.11.11); see `../../../README.md`.
verus=${VERUS:-verus}
toolchain=$("$verus" --version | awk '/^[[:space:]]*Toolchain:/ { print $2; exit }')
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

echo "Checking that original/pattern.rs and original/char_boundary.rs match library/"
diff -u "$root/library/core/src/str/pattern.rs" "$here/original/pattern.rs" \
    || { echo "original/pattern.rs is stale; copy it from library/"; exit 1; }

# Prints the function in $1 whose first line starts with $2, up to its closing
# `    }`.
function_in() {
    awk -v start="$2" 'index($0, start) == 1 { p = 1 } p { print } p && $0 == "    }" { exit }' "$1"
}

# `char_boundary.rs` holds `str::floor_char_boundary`, `str::ceil_char_boundary`
# and `u8::is_utf8_char_boundary` as trait impls for `str` and `u8`, so their
# `pub const fn` is written `fn` (trait methods cannot be `pub` or `const`).
# Nothing else differs.
{
    echo "impl StrCharBoundary for str {"
    function_in "$root/library/core/src/str/mod.rs" '    pub const fn floor_char_boundary' \
        | sed '1s/pub const fn/fn/'
    echo
    function_in "$root/library/core/src/str/mod.rs" '    pub const fn ceil_char_boundary' \
        | sed '1s/pub const fn/fn/'
    echo "}"
    echo
    echo "impl U8CharBoundary for u8 {"
    function_in "$root/library/core/src/num/mod.rs" '    pub(crate) const fn is_utf8_char_boundary' \
        | sed '1s/pub(crate) const fn/fn/'
    echo "}"
} | diff -u "$here/original/char_boundary.rs" - \
    || { echo "original/char_boundary.rs is stale; re-extract it from library/"; exit 1; }

# The original compiles on its own, with `standalone.patch` applied: outside
# `core`, `Chars` and `CharIndices` have no visible fields.
echo "Checking that the original compiles (with standalone.patch applied)"
rustc "+$toolchain" --edition 2021 --crate-type=proc-macro --crate-name safety \
    -o "$tmp/libsafety.so" "$proofs/safety_stub.rs"
mkdir "$tmp/original"
cp "$here/original/lib.rs" "$here/original/char_boundary.rs" "$tmp/original/"
patch -s -o "$tmp/original/pattern.rs" "$here/original/pattern.rs" "$here/standalone.patch"
RUSTC_BOOTSTRAP=1 rustc "+$toolchain" --edition 2024 --crate-type=lib \
    --extern safety="$tmp/libsafety.so" --out-dir "$tmp" "$tmp/original/lib.rs"

# With the Verus annotations erased, `verified/` is that original. The only
# Verus attributes left in the code are these.
echo "Checking that the Verus-annotated program, with annotations erased, is the original"
python3 "$proofs/compare_erased.py" --verus "$verus" \
    --original "$tmp/original/lib.rs" --verified "$here/verified/lib.rs" \
    --allow 'exec_allows_no_decreases_clause=6' --allow 'loop_isolation(false)=2' \
    -- --extern safety="$tmp/libsafety.so"

# Erasure removes ghost code, so the HIR comparison does not see assumptions in proofs.
echo "Checking that only verified/pattern/trusted.rs has trusted items"
python3 "$proofs/check_trusted.py" "$here/verified"

echo "Verifying the Verus-annotated program"
(cd "$here/verified" && "$verus" --crate-type=lib --extern safety="$tmp/libsafety.so" lib.rs)
echo "All checks passed."
