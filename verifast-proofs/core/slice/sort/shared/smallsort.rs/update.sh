set -x -e

if ! git diff --quiet .; then
  echo "Working directory not clean. Please stash your changes and try again"
  false
else
  UPSTREAM=../../../../../../library/core/src/slice/sort/shared/smallsort.rs
  for f in rewritten/smallsort.rs $(find verified -name smallsort.rs | sort); do
    git merge-file --diff3 "$f" original/smallsort.rs $UPSTREAM
  done
  cp $UPSTREAM original/smallsort.rs
fi
