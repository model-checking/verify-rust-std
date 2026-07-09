set -e -x

git merge-file --diff3 verified/mod.rs original/mod.rs ../../../../library/alloc/src/vec/mod.rs
git merge-file --diff3 with-directives/mod.rs original/mod.rs ../../../../library/alloc/src/vec/mod.rs
cp ../../../../library/alloc/src/vec/mod.rs original/mod.rs
