#!/bin/bash

set -e

usage() {
    echo "Usage: $0 [options] [-p <path>] [--kani-args <command arguments>]"
    echo "Options:"
    echo "  -h, --help         Show this help message"
    echo "  -p, --path <path>  Optional: Specify a path to a copy of the std library. For example, if you want to run the script from an outside directory."
    echo "  --kani-args  <command arguments to kani>  Optional: Arguments to pass to the command. Simply pass them in the same way you would to the Kani binary. This should be the last argument."
    exit 1
}

# Initialize variables
command_args=""
path=""

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
        --kani-args)
            shift
            command_args="$@"
            break
            ;;
        *)
            break
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

clone_kani_repo() {
    local repo_url="$1"
    local directory="$2"
    local branch="$3"
    local commit="$4"
    git clone "$repo_url" "$directory"
    pushd "$directory"
    git checkout "$commit"
    popd
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
    os_name=$(uname -s)

    if [[ "$os_name" == "Linux" ]]; then
        ./scripts/setup/ubuntu/install_deps.sh
    elif [[ "$os_name" == "Darwin" ]]; then
        ./scripts/setup/macos/install_deps.sh
    else
        echo "Unknown operating system"
    fi

    git submodule update --init --recursive
    cargo build-dev --release
    popd
}

get_kani_path() {
    local build_dir="$1"
    echo "$(realpath "$build_dir/scripts/kani")"
}

run_kani_command() {
    local kani_path="$1"
    shift
    "$kani_path" "$@"
}

# Check if binary exists and is up to date
check_binary_exists() {
    local build_dir="$1"
    local expected_commit="$2"
    local kani_path=$(get_kani_path "$build_dir")

    if [[ -f "$kani_path" ]]; then
        local current_commit=$(get_current_commit "$build_dir")
        if [[ "$current_commit" = "$expected_commit" ]]; then
            return 0
        fi
    fi
    return 1
}


main() {
    local build_dir="$WORK_DIR/kani_build"
    local temp_dir_target=$(mktemp -d)

    echo "Using TOML file: $TOML_FILE"
    echo "Using repository URL: $REPO_URL"

    # Read commit ID from TOML file
    commit=$(read_commit_from_toml "$TOML_FILE")

    # Check if binary already exists and is up to date
    if check_binary_exists "$build_dir" "$commit"; then
        echo "Kani binary is up to date. Skipping build."
    else
        echo "Building Kani from commit: $commit"

        # Remove old build directory if it exists
        rm -rf "$build_dir"
        mkdir -p "$build_dir"

        # Clone repository and checkout specific commit
        clone_kani_repo "$REPO_URL" "$build_dir" "$BRANCH_NAME" "$commit"

        # Build project
        build_kani "$build_dir"

        echo "Kani build completed successfully!"
    fi

    # Get the path to the Kani executable
    kani_path=$(get_kani_path "$build_dir")
    echo "Kani executable path: $kani_path"

    echo "Running Kani command..."
    "$kani_path" --version

    echo "Running Kani verify-std command..."

    "$kani_path" verify-std -Z unstable-options ./library --target-dir "$temp_dir_target" -Z function-contracts -Z mem-predicates -Z loop-contracts --output-format=terse $command_args --enable-unstable --cbmc-args --object-bits 12
}

main

cleanup()
{
  rm -rf "$temp_dir_target"
}

trap cleanup EXIT
