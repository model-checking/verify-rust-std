#!/bin/bash
set -euo pipefail

# Preserve the bit-vector query while solving multiplication through integers.
exec "${KANI_CVC5_BINARY:-cvc5}" --lang=smt2 --solve-bv-as-int=sum "$@"
