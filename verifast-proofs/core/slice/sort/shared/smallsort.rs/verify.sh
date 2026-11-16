set -e -x

export VFVERSION=26.10

# Usage: bash verify.sh [CRATE...]   (CRATE is a directory under verified/, e.g. swap_if_less; default: all)
CRATES=(
  swap_if_less
  insertion_sort_shift_left
  sort4_stable
  has_efficient_in_place_swap
  stable_small_sort/default
  stable_small_sort/specialized
  unstable_small_sort/default
  unstable_small_sort/specialized
  unstable_freeze_small_sort/default
  unstable_freeze_small_sort/copy
)
if [[ $# -gt 0 ]]; then CRATES=("$@"); fi

# The trusted blocks (`// ===== BEGIN TRUSTED ... =====` .. `// ===== END TRUSTED ... =====`) are the same in
# every crate, `assume` occurs nowhere else, the freeze small-sort wrapper (trusted, see README.md) occurs only
# in unstable_small_sort/specialized, and its spec is exactly the spec that the two impls of
# `UnstableSmallSortFreezeTypeImpl::small_sort` are verified against.
python3 - <<'PY'
import re, sys
crates = ['swap_if_less', 'insertion_sort_shift_left', 'sort4_stable', 'has_efficient_in_place_swap',
          'stable_small_sort/default', 'stable_small_sort/specialized', 'unstable_small_sort/default',
          'unstable_small_sort/specialized', 'unstable_freeze_small_sort/default', 'unstable_freeze_small_sort/copy']
FREEZE, FREEZE_CRATE = 'FREEZE SMALL SORT WRAPPER', 'unstable_small_sort/specialized'
block_re = re.compile(r'^// ===== BEGIN TRUSTED (.*?) =====\n.*?^// ===== END TRUSTED \1 =====\n', re.M | re.S)
assume_re = re.compile(r'(^|[^:_A-Za-z0-9])assume(\(|_correct)')
def fail(msg): sys.exit('error: ' + msg)
src = {c: open(f'verified/{c}/smallsort.rs').read() for c in crates}
ref = None
for c in crates:
    blocks = {m.group(1): m.group(0) for m in block_re.finditer(src[c])}
    if len(blocks) != len(block_re.findall(src[c])): fail(f'{c}: duplicate trusted block')
    if (FREEZE in blocks) != (c == FREEZE_CRATE): fail(f'{c}: the {FREEZE} block belongs only in {FREEZE_CRATE}')
    blocks.pop(FREEZE, None)
    if ref is None: ref = blocks
    elif blocks != ref: fail(f'{c}: trusted blocks differ from those of {crates[0]}')
    if assume_re.search(block_re.sub('', src[c])): fail(f'{c}: assume outside the trusted blocks')
def spec(s, pat):
    found = re.findall(pat, s, flags=re.S)
    if len(found) != 1: fail('freeze small-sort spec not found')
    return [l.strip() for l in found[0].strip().split('\n')]
wrapper = spec(src[FREEZE_CRATE], r'fn unstable_small_sort_freeze_type_impl_small_sort__VeriFast_wrapper<[^\n]*\n((?:/\*@.*?@\*/\s*)+)//@ assume_correct')
for c in ['unstable_freeze_small_sort/default', 'unstable_freeze_small_sort/copy']:
    s = src[c][src[c].index('pub(crate) trait UnstableSmallSortFreezeTypeImpl'):src[c].index('const SMALL_SORT_FALLBACK_THRESHOLD')]
    if spec(s, r'fn small_sort<F>\(v: &mut \[T\], is_less: &mut F\)\s*where\s*F: FnMut\(&T, &T\) -> bool,\s*((?:/\*@.*?@\*/\s*)+)\{') != wrapper:
        fail(f'the freeze small-sort wrapper spec differs from the spec of UnstableSmallSortFreezeTypeImpl::small_sort in {c}')
PY

# `--edition 2024` is the edition core is built with. See README.md for the flags.
for c in "${CRATES[@]}"; do
  verifast -rustc_args "--edition 2024" -skip_specless_fns -allow_assume -allow_dead_code -ignore_unwind_paths -ignore_ref_creation -extern_spec std=std_extra.rsspec verified/$c/lib.rs
  refinement-checker --rustc-args "--edition 2024" rewritten/lib.rs verified/$c/lib.rs > /dev/null
done
if ! diff original/smallsort.rs ../../../../../../library/core/src/slice/sort/shared/smallsort.rs; then
  echo "::error title=Please run verifast-proofs/patch-verifast-proofs.sh::Some VeriFast proofs are out of date; please chdir to verifast-proofs and run patch-verifast-proofs.sh to update them."
  false
fi
