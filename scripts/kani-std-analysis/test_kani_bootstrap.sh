#!/usr/bin/env bash
set -eo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"
source scripts/run-kani.sh --run list

test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT
export GIT_CONFIG_COUNT=3
export GIT_CONFIG_KEY_0=protocol.file.allow
export GIT_CONFIG_VALUE_0=always
export GIT_CONFIG_KEY_1=core.hooksPath
export GIT_CONFIG_VALUE_1=/dev/null
export GIT_CONFIG_KEY_2=commit.gpgsign
export GIT_CONFIG_VALUE_2=false

git init --quiet "$test_dir/charon"
printf '%s\n' 'required compiler dependency' > "$test_dir/charon/required"
git -C "$test_dir/charon" add required
git -C "$test_dir/charon" -c user.name=Test -c user.email=test@example.invalid commit --quiet -m fixture
charon_commit=$(git -C "$test_dir/charon" rev-parse HEAD)

git init --quiet "$test_dir/origin"
cat > "$test_dir/origin/.gitmodules" <<EOF
[submodule "charon"]
    path = charon
    url = file://$test_dir/charon
[submodule "firecracker"]
    path = firecracker
    url = file://$test_dir/unavailable-firecracker
[submodule "tests/perf/s2n-quic"]
    path = tests/perf/s2n-quic
    url = file://$test_dir/unavailable-s2n-quic
EOF
git -C "$test_dir/origin" add .gitmodules
git -C "$test_dir/origin" update-index --add --cacheinfo "160000,$charon_commit,charon"
git -C "$test_dir/origin" update-index --add --cacheinfo "160000,$charon_commit,firecracker"
git -C "$test_dir/origin" update-index --add --cacheinfo "160000,$charon_commit,tests/perf/s2n-quic"
git -C "$test_dir/origin" -c user.name=Test -c user.email=test@example.invalid commit --quiet -m fixture
commit=$(git -C "$test_dir/origin" rev-parse HEAD)

printf '0\n' > "$test_dir/attempts"
git() {
    if [[ "$1" == fetch ]]; then
        local attempts
        attempts=$(<"$test_dir/attempts")
        attempts=$((attempts + 1))
        printf '%s\n' "$attempts" > "$test_dir/attempts"
        if [[ "$attempts" -lt 3 ]]; then
            return 128
        fi
    fi
    command git "$@"
}
sleep() { :; }

# A partial build directory must be initialized, and unavailable benchmark
# repositories must not prevent fetching the required compiler dependency.
mkdir "$test_dir/build"
setup_kani_repo "file://$test_dir/origin" "$test_dir/build" unused "$commit"
[[ $(<"$test_dir/attempts") == 3 ]]
[[ $(git -C "$test_dir/build" rev-parse HEAD) == "$commit" ]]
[[ $(git -C "$test_dir/build/charon" rev-parse HEAD) == "$charon_commit" ]]
[[ -f "$test_dir/build/charon/required" ]]
[[ ! -e "$test_dir/build/firecracker/.git" ]]
[[ ! -e "$test_dir/build/tests/perf/s2n-quic/.git" ]]
[[ "$PWD" == "$repo_root" ]]

setup_kani_repo "file://$test_dir/origin" "$test_dir/build" unused "$commit"
[[ $(<"$test_dir/attempts") == 4 ]]

attempts=0
git() { attempts=$((attempts + 1)); return 42; }
if retry_kani_git fetch; then
    echo 'Failed Git downloads were accepted' >&2
    exit 1
else
    status=$?
fi
[[ "$status" == 42 && "$attempts" == 3 ]]
echo 'Kani bootstrap tests passed'
