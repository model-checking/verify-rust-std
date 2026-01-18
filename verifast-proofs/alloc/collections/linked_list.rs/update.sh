set -x -e

if ! git diff --quiet .; then
  echo "Working directory not clean. Please stash your changes and try again"
  false
else
  UPSTREAM=../../../../library/alloc/src/collections/linked_list.rs
  git merge-file --diff3 verified/linked_list.rs original/linked_list.rs $UPSTREAM
  cp $UPSTREAM original/linked_list.rs
fi
