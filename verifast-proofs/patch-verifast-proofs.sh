#!/bin/bash

set -e -x

cd "$(dirname "$0")"
export PATH=`pwd`:$PATH

patch_proof() {
  local negative_dir=${1:-}
  if ! git diff --quiet -- . "$@"; then
    echo "Directory not clean. Please stash changes and try again"
  else
    bash update.sh && bash verify.sh &&
      { [ -z "$negative_dir" ] || bash "$negative_dir/verify.sh"; } || git restore .
  fi
}

pushd alloc/collections/linked_list.rs
  patch_proof
popd
pushd alloc/collections/linked_list.rs-negative
  patch_proof
popd
pushd alloc/raw_vec/mod.rs
  patch_proof
popd
pushd alloc/string.rs
  patch_proof ../string.rs-negative
popd
