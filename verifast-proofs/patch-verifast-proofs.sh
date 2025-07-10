set -e -x

pushd alloc/collections/linked_list.rs
  diff original/linked_list.rs ../../../../library/alloc/src/collections/linked_list.rs > /tmp/linked_list.diff || [ "$?" = 1 ]
  patch -p0 verified/linked_list.rs < /tmp/linked_list.diff
  patch -p0 original/linked_list.rs < /tmp/linked_list.diff
  rm /tmp/linked_list.diff
popd
pushd alloc/collections/linked_list.rs-negative
  diff original/linked_list.rs ../../../../library/alloc/src/collections/linked_list.rs > /tmp/linked_list.diff || [ "$?" = 1 ]
  patch -p0 verified/linked_list.rs < /tmp/linked_list.diff
  patch -p0 original/linked_list.rs < /tmp/linked_list.diff
  rm /tmp/linked_list.diff
popd
