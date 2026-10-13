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
echo "CBMC tap retry tests passed."
