#!/bin/bash

set -e -x

cd "$(dirname "$0")"

export PATH=`pwd`:$PATH

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
