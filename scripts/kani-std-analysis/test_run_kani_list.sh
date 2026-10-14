#!/usr/bin/env bash
set -eo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

# Exercise the real argument parser and list dispatch without building Kani.
check_list() (
    local expected_command="$1"
    local expected_format="$2"
    shift 2
    source scripts/run-kani.sh --run list "$@"

    check_binary_exists() { return 0; }
    get_kani_path() { echo test_kani; }
    test_kani() {
        [[ "$1" != --version ]] || return 0
        [[ "$1" == "$expected_command" ]]
        local format_count=0
        local actual_format=""
        while (( $# > 0 )); do
            case "$1" in
                --format)
                    format_count=$((format_count + 1))
                    actual_format="$2"
                    shift
                    ;;
                --format=*)
                    format_count=$((format_count + 1))
                    actual_format="${1#--format=}"
                    ;;
            esac
            shift
        done
        [[ "$format_count" == 1 && "$actual_format" == "$expected_format" ]]
    }
    main >/dev/null
)

check_list list markdown
check_list list json --kani-args --format json
check_list list json --kani-args --format=json
check_list autoharness markdown --with-autoharness
check_list autoharness json --with-autoharness --kani-args --format json

check_cvc5_encoding() (
    export KANI_FLAT_SMT_CVC5=true KANI_FLAT_SMT_Z3=false KANI_ARITHMETIC_REFINEMENT=false
    source scripts/run-kani.sh --run list
    # The Yices dialect quantifies constant-array initialization, which the
    # integer arithmetic backend cannot reliably solve for coverage checks.
    [[ " ${kani_cbmc_args[*]} " == *" --bitwuzla "* ]]
    [[ " ${kani_cbmc_args[*]} " == *" --external-smt2-solver "* ]]
    [[ " ${kani_cbmc_args[*]} " != *" --yices "* ]]
)
check_cvc5_encoding
echo "Kani list argument tests passed."
