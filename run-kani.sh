#!/bin/bash

set -e

usage() {
    echo "Usage: $0 [options] [-p <path>] [--k-args <command arguments>]"
    echo "Options:"
    echo "  -h, --help         Show this help message"
    echo "  -p, --path <path>  Specify a path (optional)"
    echo "  --kani-args           Optional: Arguments to pass to the command"
    exit 1
}

# Initialize variables
command_args=""
path=""

# Parse command line arguments
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
            shift  # Remove --k-args from the argument list
            command_args="$@"  # Capture all remaining arguments
            break  # Stop processing further arguments
            ;;
        *)
            # If --k-args is not used, treat all remaining arguments as command arguments
            command_args="$@"
            break
            ;;
    esac
done

# Set working directory
if [[ -n "$path" ]]; then
    if [[ ! -d "$path" ]]; then
        echo "Error: Specified directory does not exist."
        usage
        exit 1
    fi
    WORK_DIR=$(realpath "$path")
else
    WORK_DIR=$(pwd)
fi

cd "$WORK_DIR" || exit 1

# Default values
DEFAULT_TOML_FILE="kani-version.toml"
DEFAULT_REPO_URL="https://github.com/model-checking/kani.git"
DEFAULT_TARGET_DIR="kani_repo"
DEFAULT_BRANCH_NAME="features/verify-rust-std"

# Use environment variables if set, otherwise use defaults
TOML_FILE=${KANI_TOML_FILE:-$DEFAULT_TOML_FILE}
REPO_URL=${KANI_REPO_URL:-$DEFAULT_REPO_URL}
TARGET_DIR=${KANI_TARGET_DIR:-$DEFAULT_TARGET_DIR}
BRANCH_NAME=${KANI_BRANCH_NAME:-$DEFAULT_BRANCH_NAME}

os_name=$(uname -s)

# Function to read commit ID from TOML file
read_commit_from_toml() {
    local file="$1"
    if [ ! -f "$file" ]; then
        echo "Error: TOML file not found: $file" >&2
        exit 1
    fi
    local commit=$(grep '^commit *=' "$file" | sed 's/^commit *= *"\(.*\)"/\1/')
    if [ -z "$commit" ]; then
        echo "Error: 'commit' field not found in TOML file" >&2
        exit 1
    fi
    echo "$commit"
}

clone_repo() {
    local repo_url="$1"
    local directory="$2"
    local branch="$3"
    local commit="$4"
    git clone --depth 1 -b "$branch" "$repo_url" "$directory"
    cd "$directory"
    git checkout "$commit"
    cd - > /dev/null
}

checkout_commit() {
    local directory="$1"
    local commit="$2"
    cd "$directory"
    git checkout "$commit"
    cd ..
}

get_current_commit() {
    local directory="$1"
    if [ -d "$directory/.git" ]; then
        git -C "$directory" rev-parse HEAD
    else
        echo ""
    fi
}

build_project() {
    local directory="$1"
    cd "$directory"

    if [ "$os_name" == "Linux" ]; then
        ./scripts/setup/ubuntu/install_deps.sh
    elif [ "$os_name" == "Darwin" ]; then
        ./scripts/setup/macos/install_deps.sh
    else
        echo "Unknown operating system"
    fi

    cargo build-dev --release
    cd ..
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
    local kani_path="$build_dir/scripts/kani"

    if [ -f "$kani_path" ]; then
        local current_commit=$(get_current_commit "$build_dir")
        if [ "$current_commit" = "$expected_commit" ]; then
            return 0
        fi
    fi
    return 1
}


main() {
    local current_dir=$(pwd)
    local build_dir="$WORK_DIR/kani_build"
    local temp_dir_target=$(mktemp -d)

    echo "Using TOML file: $TOML_FILE"
    echo "Using repository URL: $REPO_URL"

    # Read commit ID from TOML file
    commit=$(read_commit_from_toml "$TOML_FILE")
    echo "Kani commit: $commit"

    # Check if binary already exists and is up to date
    if check_binary_exists "$build_dir" "$commit"; then
        echo "Kani binary is up to date. Skipping build."
    else
        echo "Building Kani from commit: $commit"

        # Remove old build directory if it exists
        rm -rf "$build_dir"
        mkdir -p "$build_dir"

        # Clone repository and checkout specific commit
        clone_repo "$REPO_URL" "$build_dir" "$BRANCH_NAME" "$commit"

        # Build project
        build_project "$build_dir"

        echo "Kani build completed successfully!"
    fi

    # Get the path to the Kani executable
    kani_path=$(get_kani_path "$build_dir")
    echo "Kani executable path: $kani_path"

    echo "Running Kani command..."
    "$kani_path" --version

    echo "Running Kani verify-std command..."
    cd $current_dir

    # Run the command with the provided arguments (if any)
    if [ -n "$command_args" ]; then
        "$kani_path" verify-std -Z unstable-options ./library --target-dir "$temp_dir_target" -Z function-contracts -Z mem-predicates --output-format=terse $command_args
    else
        "$kani_path" verify-std -Z unstable-options ./library --target-dir "$temp_dir_target" -Z function-contracts -Z mem-predicates --output-format=terse
    fi
}

main
