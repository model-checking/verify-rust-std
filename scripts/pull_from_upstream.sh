#!/bin/bash

set -eux

cd $1

TOOLCHAIN_DATE=$2
COMMIT_HASH=$3

# The checkout and pull itself needs to happen in sync with features/verify-rust-std
# Often times rust is going to be ahead of kani in terms of the toolchain, and both need to point to
# the same commit
SYNC_BRANCH="sync-$TOOLCHAIN_DATE" && echo "--- Fork branch: ${SYNC_BRANCH} ---"
# # 1. Update the upstream/master branch with the latest changes
git fetch upstream
git checkout $COMMIT_HASH

# # 2. Update the subtree branch
git subtree split --prefix=library --onto subtree/library -b subtree/library
# 3. Update main
git fetch origin
git checkout -b ${SYNC_BRANCH} origin/main
git subtree merge --prefix=library subtree/library --squash

# 4. Pull library's submodules
# The subtree command does not recursively pull submodules, so we do this manually.
cd library
git clone https://github.com/rust-lang/backtrace-rs.git
git clone https://github.com/rust-lang/stdarch.git

# TODO: Update origin/subtree/library as well after the process by pushing to it
