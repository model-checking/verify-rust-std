#!/usr/bin/env bash
set -eo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

check_retry() (
    local failures="$1" expected_attempts="$2" expected_status="$3"
    local calls=0 waits=0 status=0
    source scripts/run-kani.sh --run list
    brew() {
        [[ "$#" == 2 && "$1" == tap && "$2" == diffblue/cbmc ]] || return 2
        calls=$((calls + 1))
        [[ "$calls" -gt "$failures" ]]
    }
    sleep() {
        [[ "$1" == 10 ]] || return 2
        waits=$((waits + 1))
    }
    prepare_cbmc_tap >/dev/null 2>&1 || status=$?
    [[ "$status" == "$expected_status" ]]
    [[ "$calls" == "$expected_attempts" ]]
    [[ "$waits" == "$((expected_attempts - 1))" ]]
)

check_retry 0 1 0
check_retry 1 2 0
check_retry 3 3 1

check_installer_retry() (
    local failures="$1" expected_attempts="$2" expected_status="$3"
    local calls=0 status=0 scratch
    scratch=$(mktemp -d)
    trap 'rm -rf "$scratch"' EXIT
    source scripts/run-kani.sh --run list
    installer() {
        [[ "$#" == 1 && "$1" == 'argument with spaces' ]] || return 2
        [[ -f "$CURL_HOME/.curlrc" ]] || return 3
        calls=$((calls + 1))
        printf '%s\n' "$CURL_HOME" >> "$scratch/calls"
        [[ "$calls" -gt "$failures" ]] || return 73
    }
    sleep() {
        [[ "$1" == 10 ]] || return 2
        printf 'wait\n' >> "$scratch/waits"
    }
    : > "$scratch/waits"
    GITHUB_ACTIONS=true install_kani_dependencies installer 'argument with spaces' \
        >/dev/null 2>&1 || status=$?
    [[ "$status" == "$expected_status" ]]
    [[ "$(wc -l < "$scratch/calls")" -eq "$expected_attempts" ]]
    [[ "$(wc -l < "$scratch/waits")" -eq "$((expected_attempts - 1))" ]]
    [[ ! -e "$(head -n 1 "$scratch/calls")" ]]
)

check_installer_retry 0 1 0
check_installer_retry 1 2 0
check_installer_retry 3 3 73
echo "CBMC tap and dependency retry tests passed."
