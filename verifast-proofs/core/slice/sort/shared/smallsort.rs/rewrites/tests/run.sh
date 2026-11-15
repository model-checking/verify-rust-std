#!/bin/bash
# Differential test of rewrites/001 (see difftest/main.rs), in four build configurations.
cd "$(dirname "$0")"
TC=${TOOLCHAIN:-nightly-2026-10-12}
ok=1
for oc in on off; do for da in on off; do
  bin=/tmp/difftest_$$_${oc}_${da}
  rustc +$TC --edition 2024 -C overflow-checks=$oc -C debug-assertions=$da -O difftest/main.rs -o $bin 2> build_${oc}_${da}.log || { echo "BUILD FAIL $oc $da"; ok=0; continue; }
  $bin > trace_${oc}_${da}.txt 2> result_${oc}_${da}.txt; rc=$?
  echo "overflow-checks=$oc debug-assertions=$da: exit=$rc $(cat result_${oc}_${da}.txt)"
  [[ $rc == 0 ]] || ok=0
  rm -f $bin
done; done
[[ $ok == 1 ]] && echo "ALL IDENTICAL" || { echo "DIFFERENCES OR FAILURES"; exit 1; }
