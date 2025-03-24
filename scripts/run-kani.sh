#!/bin/bash

set -e

usage() {
    echo "Usage: $0 [options] [-p <path>] [--run <verify-std|list>] [--kani-args <command arguments>]"
    echo "Options:"
    echo "  -h, --help         Show this help message"
    echo "  -p, --path <path>  Optional: Specify a path to a copy of the std library. For example, if you want to run the script from an outside directory."
    echo "  --run <verify-std|list|metrics>  Optional: Specify whether to run the 'kani verify-std' command, 'kani list' command, or collect Kani-specific metrics. Defaults to 'verify-std' if not specified."
    echo "  --kani-args  <command arguments to kani>  Optional: Arguments to pass to the command. Simply pass them in the same way you would to the Kani binary. This should be the last argument."
    exit 1
}

# Initialize variables
command_args=""
path=""
run_command="verify-std"

# Parse command line arguments
# TODO: Improve parsing with getopts
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            usage
            ;;
        -p|--path)
            if [[ -n $2 ]]; then
                path=$2
                shift 2
            else
                echo "Error: Path argument is missing"
                usage
            fi
            ;;
        --run)
            if [[ -n $2 && ($2 == "verify-std" || $2 == "list" || $2 == "metrics") ]]; then
                run_command=$2
                shift 2
            else
                echo "Error: Invalid run command. Must be 'verify-std', 'list', or 'metrics'."
                usage
            fi
            ;;
        --kani-args)
            shift
            command_args="$@"
            break
            ;;
        *)
            echo "Error: Unknown option $1"
            usage
            ;;
    esac
done

# Set working directory
if [[ -n "$path" ]]; then
    if [[ ! -d "$path" ]]; then
        echo "Error: Specified directory does not exist."
        usage
    fi
    WORK_DIR=$(realpath "$path")
else
    WORK_DIR=$(pwd)
fi

cd "$WORK_DIR"

# Default values
DEFAULT_TOML_FILE="tool_config/kani-version.toml"
DEFAULT_REPO_URL="https://github.com/model-checking/kani.git"
DEFAULT_BRANCH_NAME="features/verify-rust-std"

# Use environment variables if set, otherwise use defaults
TOML_FILE=${KANI_TOML_FILE:-$DEFAULT_TOML_FILE}
REPO_URL=${KANI_REPO_URL:-$DEFAULT_REPO_URL}
BRANCH_NAME=${KANI_BRANCH_NAME:-$DEFAULT_BRANCH_NAME}

# Unstable arguments to pass to Kani
unstable_args="-Z function-contracts -Z mem-predicates -Z float-lib -Z c-ffi -Z loop-contracts"

# Variables used for parallel harness verification
# When we say "parallel," we mean two dimensions of parallelization:
#   1. Sharding verification across multiple workers. The Kani workflow that calls this script defines WORKER_INDEX and WORKER_TOTAL for this purpose: 
#   we shard verification across WORKER_TOTAL workers, where each worker has a unique WORKER_INDEX that it uses to derive its share of ALL_HARNESSES to verify.
#   2. Within a single worker, we parallelize verification between multiple cores by invoking kani with -j.

# Array of all of the harnesses in the repository, set in get_harnesses()
declare -a ALL_HARNESSES
# Length of ALL_HARNESSES, set in get_harnesses()
declare -i HARNESS_COUNT
# `kani list` JSON FILE_VERSION that the parallel verification command expects
EXPECTED_JSON_FILE_VERSION="0.1"

# Function to read commit ID from TOML file
read_commit_from_toml() {
    local file="$1"
    if [[ ! -f "$file" ]]; then
        echo "Error: TOML file not found: $file" >&2
        exit 1
    fi
    local commit=$(grep '^commit *=' "$file" | sed 's/^commit *= *"\(.*\)"/\1/')
    if [[ -z "$commit" ]]; then
        echo "Error: 'commit' field not found in TOML file" >&2
        exit 1
    fi
    echo "$commit"
}

setup_kani_repo() {
    local repo_url="$1"
    local directory="$2"
    local branch="$3"
    local commit="$4"

    if [[ ! -d "${directory}" ]]; then
        mkdir -p "${directory}"
        pushd "${directory}" > /dev/null

        git init . >& /dev/null
        git remote add origin "${repo_url}" >& /dev/null
    else
        pushd "${directory}" > /dev/null
    fi

    git fetch --depth 1 origin "$commit" --quiet
    git checkout "$commit" --quiet
    git submodule update --init --recursive --depth 1 --quiet
    popd > /dev/null
}

get_current_commit() {
    local directory="$1"
    if [ -d "$directory/.git" ]; then
        git -C "$directory" rev-parse HEAD
    else
        echo ""
    fi
}

build_kani() {
    local directory="$1"
    pushd "$directory"
    source "kani-dependencies"
    # Check if installed versions are correct.
    if ./scripts/check-cbmc-version.py \
            --major ${CBMC_MAJOR} --minor ${CBMC_MINOR} --patch ${CBMC_PATCH} \
            && ./scripts/check_kissat_version.sh; then
        echo "Dependencies are up-to-date"
    else
        os_name=$(uname -s)

        if [[ "$os_name" == "Linux" ]]; then
            ./scripts/setup/ubuntu/install_deps.sh
        elif [[ "$os_name" == "Darwin" ]]; then
            ./scripts/setup/macos/install_deps.sh
        else
            echo "Unknown operating system"
        fi
    fi

    cargo build-dev --release
    popd
}

get_kani_path() {
    local build_dir="$1"
    echo "$(realpath "$build_dir/scripts/kani")"
}

# Run kani list with JSON format and process with jq to extract harness names and total number of harnesses.
# Note: The code to extract ALL_HARNESSES is dependent on `kani list --format json` FILE_VERSION 0.1.
# (The FILE_VERSION variable is defined in Kani in the list module's output code, current path kani-driver/src/list/output.rs)
# If FILE_VERSION changes, first update the ALL_HARNESSES extraction logic to work with the new format, if necessary,
# then update EXPECTED_JSON_FILE_VERSION.
get_harnesses() {
    local kani_path="$1"
    "$kani_path" list -Z list $unstable_args ./library --std --format json
    local json_file_version=$(jq -r '.["file-version"]' "$WORK_DIR/kani-list.json")
    if [[ $json_file_version != $EXPECTED_JSON_FILE_VERSION ]]; then
        echo "Error: The JSON file-version in kani-list.json does not equal $EXPECTED_JSON_FILE_VERSION"
        exit 1
    fi
    # Extract the harnesses inside "standard-harnesses" and "contract-harnesses" 
    # into an array called ALL_HARNESSES and the length of that array into HARNESS_COUNT
    ALL_HARNESSES=($(jq -r '
        ([.["standard-harnesses"] | to_entries | .[] | .value[]] + 
            [.["contract-harnesses"] | to_entries | .[] | .value[]]) | 
        .[]
    ' $WORK_DIR/kani-list.json))
    HARNESS_COUNT=${#ALL_HARNESSES[@]}
}

# Given an array of harness names, run verification for those harnesses
run_verification_subset() {
    local kani_path="$1"
    local harnesses=("${@:2}")  # All arguments after kani_path are harness names
    
    # Build the --harness arguments
    local harness_args=""
    for harness in "${harnesses[@]}"; do
        harness_args="$harness_args --harness $harness"
    done

    echo "Running verification for harnesses:"
    printf '%s\n' "${harnesses[@]}"
    "$kani_path" verify-std -Z unstable-options ./library \
        $unstable_args \
        --no-assert-contracts \
        $harness_args --exact \
        -j \
        --output-format=terse \
        $command_args \
        --enable-unstable \
        --cbmc-args --object-bits 12
}

# Check if binary exists and is up to date
check_binary_exists() {
    local build_dir="$1"
    local expected_commit="$2"
    local kani_path=$(get_kani_path "$build_dir")

    if [[ -d "${build_dir}" ]]; then
        local current_commit=$(get_current_commit "$build_dir")
        if [[ "$current_commit" = "$expected_commit" ]]; then
            return 0
        else
            echo "Kani repository is out of date. Rebuilding..."
        fi
    else
        echo "Kani repository not found. Creating..."
    fi
    return 1
}

main() {
    local build_dir="$WORK_DIR/kani_build"

    echo "Using TOML file: $TOML_FILE"
    echo "Using repository URL: $REPO_URL"

    # Read commit ID from TOML file
    commit=$(read_commit_from_toml "$TOML_FILE")

    # Check if binary already exists and is up to date
    if check_binary_exists "$build_dir" "$commit"; then
        echo "Kani binary is up to date. Skipping build."
    else
        echo "Building Kani from commit: $commit"

        # Clone repository and checkout specific commit
        setup_kani_repo "$REPO_URL" "$build_dir" "$BRANCH_NAME" "$commit"

        # Build project
        build_kani "$build_dir"

        echo "Kani build completed successfully!"
    fi

    # Get the path to the Kani executable
    kani_path=$(get_kani_path "$build_dir")
    echo "Kani executable path: $kani_path"

    echo "Running Kani command..."
    "$kani_path" --version

    if [[ "$run_command" == "verify-std" ]]; then
        if [[ -n "$WORKER_INDEX" && -n "$WORKER_TOTAL" ]]; then
            echo "Running as parallel worker $WORKER_INDEX of $WORKER_TOTAL"
            get_harnesses "$kani_path"

            echo "All harnesses:"
            printf '%s\n' "${ALL_HARNESSES[@]}"
            echo "Total number of harnesses: $HARNESS_COUNT"
            
            # Calculate this worker's portion (add WORKER_TOTAL - 1 to force ceiling division)
            chunk_size=$(( (HARNESS_COUNT + WORKER_TOTAL - 1) / WORKER_TOTAL ))
            echo "Number of harnesses this worker will run: $chunk_size"
            
            start_idx=$(( (WORKER_INDEX - 1) * chunk_size ))
            echo "Start index into ALL_HARNESSES is $start_idx"
            
            # Extract this worker's harnesses
            worker_harnesses=("${ALL_HARNESSES[@]:$start_idx:$chunk_size}")
            
            # Run verification for this subset
            run_verification_subset "$kani_path" "${worker_harnesses[@]}"
        else
            # Run verification for all harnesses (not in parallel)
            echo "Running Kani verify-std command..."
            "$kani_path" verify-std -Z unstable-options ./library \
                $unstable_args \
                --no-assert-contracts \
                $command_args \
                --enable-unstable \
                --cbmc-args --object-bits 12
        fi
    elif [[ "$run_command" == "list" ]]; then
        echo "Running Kani list command..."
        "$kani_path" list -Z list $unstable_args ./library --std --format markdown
    elif [[ "$run_command" == "metrics" ]]; then
        local current_dir=$(pwd)
        echo "Running Kani list command..."
        "$kani_path" list -Z list $unstable_args ./library --std --format json
        pushd scripts/kani-std-analysis
        echo "Running Kani's std-analysis command..."
        ./std-analysis.sh $build_dir
        pip install -r requirements.txt
        echo "Computing Kani-specific metrics..."
        ./kani_std_analysis.py --crate core \
          --kani-list-file $current_dir/kani-list.json \
          --metrics-file metrics-data-core.json
        ./kani_std_analysis.py --crate std \
          --kani-list-file $current_dir/kani-list.json \
          --metrics-file metrics-data-std.json
        popd
        rm kani-list.json
    fi
}

main
