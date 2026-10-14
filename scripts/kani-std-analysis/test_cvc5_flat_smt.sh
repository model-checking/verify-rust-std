#!/bin/bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cat > "$scratch/solver" <<'SH'
#!/bin/bash
printf '%s\n' "$@"
exit "${SOLVER_EXIT:-0}"
SH
chmod +x "$scratch/solver"
actual=$(KANI_CVC5_BINARY="$scratch/solver" bash "$script_dir/cvc5-flat-smt.sh" 'query with spaces.smt2')
expected=$(printf '%s\n' --lang=smt2 --solve-bv-as-int=sum 'query with spaces.smt2')
[[ "$actual" == "$expected" ]]
status=0
KANI_CVC5_BINARY="$scratch/solver" SOLVER_EXIT=71 \
    bash "$script_dir/cvc5-flat-smt.sh" >/dev/null || status=$?
[[ "$status" == 71 ]]

if [[ -n "${KANI_CVC5_BINARY:-}" ]]; then
    cat > "$scratch/query.smt2" <<'SMT'
(set-logic QF_BV)
(declare-fun x () (_ BitVec 64))
(assert (= x #xffffffffffffffff))
(assert (= (bvmul x x) #x0000000000000001))
(check-sat)
(assert (= (bvmul x x) #x0000000000000002))
(check-sat)
SMT
    actual=$(bash "$script_dir/cvc5-flat-smt.sh" --incremental "$scratch/query.smt2")
    [[ "$actual" == "$(printf 'sat\nunsat')" ]]
fi
echo 'CVC5 adapter checks passed'
