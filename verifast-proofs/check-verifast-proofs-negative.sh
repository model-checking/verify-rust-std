#!/bin/bash

set -e -x

cd "$(dirname "$0")"
export PATH=`pwd`:$PATH

cd alloc
  cd collections
    cd linked_list.rs-negative
      bash verify.sh
    cd ..
  cd ..
cd ..
