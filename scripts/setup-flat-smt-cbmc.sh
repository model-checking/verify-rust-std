#!/usr/bin/env bash
set -euo pipefail

# CBMC 6.11's flat SMT encoding reverses arithmetic result and overflow fields.
# Backport the approved fix from https://github.com/diffblue/cbmc/pull/9145.
release=cbmc-6.11.0
fix=e36c27dd2e57ef6ce39c02a382d1c60ff6f4593f
revision="$release-$fix"
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
build_root=${1:-"$repository_root/cbmc_build"}
mkdir -p "$build_root/bin"
build_root=$(cd "$build_root" && pwd)

if [[ -x "$build_root/bin/cbmc" && -f "$build_root/bin/revision" ]] &&
    [[ $(cat "$build_root/bin/revision") == "$revision" ]]; then
    echo "CBMC with the flat SMT fix is up to date."
    exit 0
fi

download() {
    local url=$1 destination=$2 expected=$3 actual
    curl --fail --location --retry 3 --silent --show-error "$url" -o "$destination"
    actual=$(shasum -a 256 "$destination" | awk '{print $1}')
    if [[ "$actual" != "$expected" ]]; then
        echo "Checksum mismatch for $destination" >&2
        exit 1
    fi
}

work_root=$(mktemp -d "$build_root/work.XXXXXX")
download "https://api.github.com/repos/diffblue/cbmc/tarball/$release" \
    "$work_root/source.tar.gz" \
    e1e338604c77e040c5a142dd12c6fbb41c43d079588a07d5b0f89b3c57409d0a
download "https://github.com/diffblue/cbmc/commit/$fix.patch" \
    "$work_root/overflow.patch" \
    24824fb1ae03d82d5ae81002e60c933d4d516caa9620759c95da3bf43ee4fbe2
mkdir "$work_root/source"
tar -xzf "$work_root/source.tar.gz" -C "$work_root/source" --strip-components 1
patch --batch -p1 -d "$work_root/source" < "$work_root/overflow.patch"

# Keep CBMC's pinned MiniSAT checksum, using Debian's HTTPS endpoint.
python3 -I - "$work_root/source/src/solvers/CMakeLists.txt" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_text()
old = 'http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz'
new = 'https://deb.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz'
assert source.count(old) == 1
path.write_text(source.replace(old, new))
PY

cmake -S "$work_root/source" -B "$work_root/build" \
    -DCMAKE_BUILD_TYPE=Release -DWITH_JBMC=OFF -DWITH_MEMORY_ANALYZER=OFF \
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5
cmake --build "$work_root/build" --target cbmc --parallel 2
install -m 755 "$work_root/build/bin/cbmc" "$build_root/bin/cbmc"
printf '%s\n' "$revision" > "$build_root/bin/revision"
rm -rf "$work_root"
