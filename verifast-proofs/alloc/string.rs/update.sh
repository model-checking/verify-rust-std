#!/bin/bash
set -e -x

cd "$(dirname "$0")"

if ! git diff --quiet HEAD -- .; then
  echo "Working directory not clean. Please stash your changes and try again."
  exit 1
fi

upstream=../../../library/alloc/src/string.rs
git merge-file --diff3 verified/string.rs original/string.rs "$upstream"
cp "$upstream" original/string.rs
