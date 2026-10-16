#!/usr/bin/env bash
set -euo pipefail

test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT
solver_adapter="$(dirname "${BASH_SOURCE[0]}")/z3-flat-smt.sh"

cat > "$test_dir/quantified.smt2" <<'SMT'
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (forall ((i (_ BitVec 8))) (= (select a i) (_ bv0 8))))
SMT
cat "$test_dir/quantified.smt2" > "$test_dir/unsat.smt2"
cat >> "$test_dir/unsat.smt2" <<'SMT'
(assert (not (= (select a (_ bv0 8)) (_ bv0 8))))
(check-sat)
SMT
actual_result=$("$solver_adapter" "$test_dir/unsat.smt2")
[[ "$actual_result" == unsat ]]

cat "$test_dir/quantified.smt2" > "$test_dir/sat.smt2"
echo '(check-sat)' >> "$test_dir/sat.smt2"
actual_result=$("$solver_adapter" "$test_dir/sat.smt2")
[[ "$actual_result" == sat ]]

echo '(assert missing_symbol)' > "$test_dir/invalid.smt2"
if "$solver_adapter" "$test_dir/invalid.smt2" > "$test_dir/stdout" 2> "$test_dir/stderr"; then
    echo "Invalid solver input was accepted" >&2
    exit 1
fi

echo "Quantified SMT adapter checks passed"
