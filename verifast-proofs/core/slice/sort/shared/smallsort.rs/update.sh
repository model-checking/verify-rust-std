set -x -e

# Merges upstream changes of library/core/src/slice/sort/shared/smallsort.rs into the proof (called by
# verifast-proofs/patch-verifast-proofs.sh). Each target crate's smallsort.rs is merged three-way against
# original/smallsort.rs; rewritten/ is then rebuilt from the new original/ (rewrites/apply.sh).
if ! git diff --quiet .; then
  echo "Working directory not clean. Please stash your changes and try again"
  false
else
  UPSTREAM=../../../../../../library/core/src/slice/sort/shared/smallsort.rs
  for f in $(find targets -name smallsort.rs | sort); do
    git merge-file --diff3 "$f" original/smallsort.rs $UPSTREAM
  done
  cp $UPSTREAM original/smallsort.rs
  bash rewrites/apply.sh
fi
