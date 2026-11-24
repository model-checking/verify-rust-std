#!/bin/bash

set -e -x

cd "$(dirname "$0")"

export PATH=`pwd`:$PATH

# The B-tree build uses the Linux x86_64 VeriFast dependency archive.
if [[ $(uname -sm) == 'Linux x86_64' ]]; then
  bash alloc/collections/btree/node.rs/verify.sh --ci
fi

cd alloc
  cd collections
    cd linked_list.rs
      bash verify.sh
    cd ..
  cd ..
  cd raw_vec
    cd mod.rs
      bash verify.sh
    cd ..
  cd ..
cd ..
