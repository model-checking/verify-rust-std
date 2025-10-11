set -x -e

if ! git diff --quiet .; then
  echo "Working directory not clean. Please stash your changes and try again"
  false
else
  UPSTREAM=../../../../library/alloc/src/raw_vec/mod.rs
  git merge-file --diff3 with-directives/raw_vec.rs original/raw_vec.rs $UPSTREAM
  git merge-file --diff3 verified/raw_vec.rs original/raw_vec.rs $UPSTREAM
  cp $UPSTREAM original/raw_vec.rs
fi
