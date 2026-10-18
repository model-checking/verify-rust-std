#!/usr/bin/env bash
set -euo pipefail

# CBMC 6.11's flat SMT encoding reverses arithmetic result and overflow fields.
# Backport the approved fix from https://github.com/diffblue/cbmc/pull/9145.
# Keep diagnostic traces opt-in with https://github.com/diffblue/cbmc/pull/9150.
# Kani explicitly requests --trace when generating concrete playback tests.
# Skip unused loop write-set inference when every loop has an explicit frame.
# Link CaDiCaL next to MiniSAT. Kani requests --sat-solver cadical by default,
# and a CBMC without CaDiCaL uses MiniSAT instead.
release=cbmc-6.11.0
fix=e36c27dd2e57ef6ce39c02a382d1c60ff6f4593f
trace_fix=d7caa9d6ff314348a99cb31778e569239ff6dd27
sat_impl="minisat2;cadical"
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
dfcc_patch="$repository_root/scripts/cbmc-skip-unused-loop-assigns.patch"
dfcc_fix=$(shasum -a 256 "$dfcc_patch" | awk '{print $1}')
revision="$release-$fix-$trace_fix-$dfcc_fix-$sat_impl"
build_root=${1:-"$repository_root/cbmc_build"}
mkdir -p "$build_root/bin"
build_root=$(cd "$build_root" && pwd)

if [[ -x "$build_root/bin/cbmc" && -x "$build_root/bin/goto-instrument" &&
      -x "$build_root/bin/goto-cc" &&
      -f "$build_root/bin/revision" ]] &&
    [[ $(cat "$build_root/bin/revision") == "$revision" ]]; then
    echo "Patched CBMC tools are up to date."
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
download "https://github.com/diffblue/cbmc/commit/$trace_fix.patch" \
    "$work_root/traces.patch" \
    3446691194b090e199b2e5d9ccbad1687154656530666f1a3526d0b3ae82618e
mkdir "$work_root/source"
tar -xzf "$work_root/source.tar.gz" -C "$work_root/source" --strip-components 1
patch --batch -p1 -d "$work_root/source" < "$work_root/overflow.patch"
patch --batch -p1 -d "$work_root/source" < "$work_root/traces.patch"
patch --batch -p1 -d "$work_root/source" < "$dfcc_patch"

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
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5 -Dsat_impl="$sat_impl"
cmake --build "$work_root/build" --target cbmc goto-instrument goto-cc --parallel 2
install -m 755 "$work_root/build/bin/cbmc" "$build_root/bin/cbmc"
install -m 755 "$work_root/build/bin/goto-instrument" "$build_root/bin/goto-instrument"
install -m 755 "$work_root/build/bin/goto-cc" "$build_root/bin/goto-cc"
printf '%s\n' "$revision" > "$build_root/bin/revision"
rm -rf "$work_root"
