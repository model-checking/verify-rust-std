#!/usr/bin/env bash
set -euo pipefail

if (( $# != 1 )); then
    echo "Usage: $0 SMT2_FILE" >&2
    exit 2
fi

quantified_input=$(mktemp)
trap 'rm -f -- "$quantified_input"' EXIT

# Kani contracts can contain quantifiers even when CBMC's flat encoding
# declares QF_AUFBV. Keep every assertion and permit quantified formulas.
awk '
    $0 == "(set-logic QF_AUFBV)" { print "(set-logic AUFBV)"; next }
    { print }
' "$1" > "$quantified_input"

z3 -smt2 "$quantified_input"
