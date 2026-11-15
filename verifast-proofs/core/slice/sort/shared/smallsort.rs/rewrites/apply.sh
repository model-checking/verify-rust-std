#!/bin/bash
# Builds rewritten/ from original/ by applying rewrites/NNN-*.patch in order.
set -e
cd "$(dirname "$0")/.."
rm -rf rewritten.tmp && mkdir rewritten.tmp
cp original/smallsort.rs original/lib.rs rewritten.tmp/
for p in rewrites/[0-9][0-9][0-9]-*.patch; do (cd rewritten.tmp && patch -s -p1 < "../$p"); done
rm -rf rewritten && mv rewritten.tmp rewritten
