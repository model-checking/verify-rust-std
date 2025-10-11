#!/bin/bash

set -e -x

cd "$(dirname "$0")"
export PATH=`pwd`:$PATH

patch_proof() {
  if ! git diff --quiet .; then
    echo "Directory not clean. Please stash changes and try again"
  else
    bash update.sh && bash verify.sh || git restore .
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
