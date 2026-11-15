#!/bin/bash
# Tamper tests for the 2026-10-31 soundness fixes (comparator call wrapper, ptr::copy wrapper, gates, sha256
# pin): each mutation, applied to a fresh copy of the benchmark, must make verify.sh FAIL. Log: tamper.log.
B="$(cd "$(dirname "$0")/.." && pwd)"
S=$(mktemp -d); trap 'rm -rf "$S"' EXIT
C=swap_if_less
run() { # name, python mutation over files in copy dir
  rm -rf $S/tc8; cp -a $B $S/tc8; cd $S/tc8
  python3 -c "$2" || { echo "MUTATION-ERROR $1"; return; }
  out=$(VF_MEM=5G VF_TIMEOUT=600 ./verify.sh targets/$C 2>&1 | tail -2)
  if grep -q "^PASS" <<< "$out" && ! grep -q "FAIL\|error" <<< "$out"; then echo "NOT CAUGHT $1: $out"; else echo "caught $1: $(echo "$out" | head -c 300)"; fi
}
R='import re,glob
def sub(p,a,b,cnt=1):
    s=open(p).read(); assert a in s,(p,a); open(p,"w").write(s.replace(a,b,cnt))
F="targets/'$C'/smallsort.rs"
'
run T1-wrapper-guard-dropped-in-crate "$R
sub(F,'if is_less_models::<T, F>(f0) {\n        f1 == f0','if true {\n        f1 == f0')"
run T2-wrapper-guard-dropped-crate+master "$R
sub(F,'if is_less_models::<T, F>(f0) {\n        f1 == f0','if true {\n        f1 == f0')
sub('trusted/comparator_call_wrapper.rs','if is_less_models::<T, F>(f0) {\n        f1 == f0','if true {\n        f1 == f0')"
run T3-wrapper-block-removed "$R
s=open(F).read(); i=s.index('// ===== BEGIN TRUSTED COMPARATOR CALL WRAPPER'); j=s.index('// ===== END TRUSTED COMPARATOR CALL WRAPPER =====')+len('// ===== END TRUSTED COMPARATOR CALL WRAPPER =====')
open(F,'w').write(s[:i]+s[j:])"
run T4-wrapper-body-swapped-args "$R
sub(F,'    f(a, b)\n','    f(b, a)\n')"
run T5-call-site-swapped-args "$R
sub(F,'is_less__VeriFast_wrapper(is_less, &*v_b, &*v_a)','is_less__VeriFast_wrapper(is_less, &*v_a, &*v_b)')"
run T6-is_less_call-readded-outside-block "$R
sub(F,'// ===== BEGIN TRUSTED COMPARATOR MODEL','lem is_less_call<T, F>(f0: F, r: bool)\n    req true;\n    ens r == apply_lt(is_less_model_of::<T, F>(f0), r, r);\n{\n    assume(false);\n}\n// ===== BEGIN TRUSTED COMPARATOR MODEL')"
run T7-is_less_call-readded-in-block-crate+master "$R
for p in (F,'trusted/comparator_model.rs'):
    sub(p,'// ===== END TRUSTED COMPARATOR MODEL','lem is_less_call<T, F>(f0: F, a0: T, b0: T, r: bool)\n    req is_less_models::<T, F>(f0) == true;\n    ens r == apply_lt(is_less_model_of::<T, F>(f0), a0, b0);\n{\n    assume(false);\n}\n// ===== END TRUSTED COMPARATOR MODEL')"
run T8-copy-call-reverted "$R
sub(F,'ptr_copy_1__VeriFast_wrapper(v_a_swap, v_a);','ptr::copy(v_a_swap, v_a, 1);')"
run T9-copy-bound-dropped-in-crate "$R
sub(F,' &*& -1 <= offset &*& offset <= 1','')"
run T10-copy-bound-dropped-crate+master "$R
sub(F,' &*& -1 <= offset &*& offset <= 1','')
sub('trusted/std_wrappers.rs',' &*& -1 <= offset &*& offset <= 1','')"
run T11-copy-wrapper-body-count-2 "$R
sub(F,'    ptr::copy(src, dst, 1)\n','    ptr::copy(src, dst, 2)\n')"
run T12-copy-gate-tool-weakened "$R
sub('tools/copy_gate.py','if bad:','if False:')"
run T13-extra-trusted-file "$R
open('trusted/extra.rs','w').write('x')"
