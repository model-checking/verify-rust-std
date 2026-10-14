#!/bin/bash
set -euo pipefail

# Preserve the bit-vector query while solving multiplication through integers.
# Allow the integer arithmetic introduced by the bit-vector translation.
exec "${KANI_CVC5_BINARY:-cvc5}" --lang=smt2 --force-logic=ALL --solve-bv-as-int=sum "$@"
