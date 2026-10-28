set -x -e

if ! git diff --quiet .; then
  echo "Working directory not clean. Please stash your changes and try again"
  false
else
  UPSTREAM_MOD=../../../../library/core/src/slice/mod.rs
  UPSTREAM_RAW=../../../../library/core/src/slice/raw.rs
  UPSTREAM_ROTATE=../../../../library/core/src/slice/rotate.rs
  git merge-file --diff3 verified/slice.rs original/slice.rs $UPSTREAM_MOD
  cp $UPSTREAM_MOD original/slice.rs
  git merge-file --diff3 verified/slice/raw.rs original/slice/raw.rs $UPSTREAM_RAW
  cp $UPSTREAM_RAW original/slice/raw.rs
  git merge-file --diff3 verified/slice/rotate.rs original/slice/rotate.rs $UPSTREAM_ROTATE
  cp $UPSTREAM_ROTATE original/slice/rotate.rs
fi
