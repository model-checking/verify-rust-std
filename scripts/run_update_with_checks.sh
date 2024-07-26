#!/bin/bash

set -eux

BASE_HOME_DIR="$(pwd)"

# TODO: Remove all relative paths, with that blob that gets the scripts dir

# Set variables
REPO_OWNER="jaisnan"
REPO_NAME="rust-dev"
BRANCH_NAME="features/verifuy-07-21"
TOOLCHAIN_FILE="rust-toolchain.toml"

# Set base
BASE_REPO="https://github.com/model-checking/verify-rust-std.git"

# Create a temporary directory
TEMP_HOME_DIR=$(mktemp -d)

# Clone the repository into the temporary directory
git clone "$BASE_REPO" "$TEMP_HOME_DIR"
cd $TEMP_HOME_DIR

# Function to extract commit hash and date from rustc version
get_rustc_info() {
    local rustc_output=$(rustc --version --verbose)
    local commit_hash=$(echo "$rustc_output" | grep 'commit-hash' | awk '{print $2}')
    local commit_date=$(echo "$rustc_output" | grep 'commit-date' | awk '{print $2}')

    if [ -z "$commit_hash" ] || [ -z "$commit_date" ]; then
        echo "Error: Could not extract commit hash or date from rustc output."
        exit 1
    fi

    echo "$commit_hash:$commit_date"
}

# Read the toolchain date from the rust-toolchain.toml file
read_toolchain_date() {
    local toolchain_file=$TOOLCHAIN_FILE

    if [ ! -f "$toolchain_file" ]; then
        echo "Error: $toolchain_file not found in the working directory." >&2
        return 1
    fi

    local toolchain_date
    toolchain_date=$(grep -oP 'channel = "nightly-\K\d{4}-\d{2}-\d{2}' ./rust-toolchain.toml)

    if [ -z "$toolchain_date" ]; then
        echo "Error: Could not extract date from $toolchain_file" >&2
        return 1
    fi

    echo "$toolchain_date"
}

# Check if a path is provided as an argument
# This is useful for local processing and debugging
if [ $# -eq 1 ]; then
    REPO_PATH="$1"
    echo "Using provided repository path: $REPO_PATH"

    # Ensure the provided path exists and is a git repository
    if [ ! -d "$REPO_PATH/.git" ]; then
        echo "Error: Provided path is not a git repository."
        exit 1
    fi

    pushd $REPO_PATH
    git switch $BRANCH_NAME

    # Get rustc info
    RUSTC_INFO=$(get_rustc_info)
    TOOLCHAIN_DATE=$(read_toolchain_date)

    if [ $? -ne 0 ]; then
    exit 1
    fi
    COMMIT_HASH=$(echo $RUSTC_INFO | cut -d':' -f1)
    RUST_DATE=$(echo $RUSTC_INFO | cut -d':' -f2)
    popd
else
    # Create a temporary directory
    TEMP_KANI_DIR=$(mktemp -d)
    echo "Created temporary directory: $TEMP_KANI_DIR"

    # Clone the repository into the temporary directory
    echo "Cloning repository..."
    git clone --branch "$BRANCH_NAME" --depth 1 "https://github.com/$REPO_OWNER/$REPO_NAME.git" "$TEMP_KANI_DIR"

    # Move into this temp dir to read the toolchain
    cd $TEMP_KANI_DIR

    if [ $? -ne 0 ]; then
        echo "Error: Failed to clone the repository."
        rm -rf "$TEMP_KANI_DIR"
        exit 1
    fi

    # Get rustc info
    RUSTC_INFO=$(get_rustc_info)
    TOOLCHAIN_DATE=$(read_toolchain_date)

    COMMIT_HASH=$(echo $RUSTC_INFO | cut -d':' -f1)
    RUST_DATE=$(echo $RUSTC_INFO | cut -d':' -f2)

    # Clean up the temporary directory
    rm -rf "$TEMP_KANI_DIR"
fi

if [ -z "$COMMIT_HASH" ]; then
    echo "Could not find commit hash in rust-toolchain.toml"
    exit 1
fi

if [ -z "$RUST_DATE" ]; then
    echo "Could not find date in rust-toolchain.toml"
    exit 1
fi

# Go to temp dir
cd $TEMP_HOME_DIR

echo "Rust commit hash found: $COMMIT_HASH"
echo "Rust date found: $TOOLCHAIN_DATE"

# Ensure we have the rust-lang/rust repository as a remote named "upstream"
if ! git remote | grep -q '^upstream$'; then
    echo "Adding rust-lang/rust as upstream remote"
    git remote add upstream https://github.com/rust-lang/rust.git
fi


echo "------------------------------------"
# Call the first script to update the subtree
echo "Update subtree in Main"
source $BASE_HOME_DIR/scripts/pull_from_upstream.sh "$TEMP_HOME_DIR" $TOOLCHAIN_DATE $COMMIT_HASH
OUTPUT_SCRIPT1=("$?")
if [ "${#OUTPUT_SCRIPT1[@]}" -eq 0 ]; then
    echo "script1.sh failed to run."
    exit 1
else
    echo "script1.sh completed successfully."
fi

# Call the second script
echo "Running script2.sh..."
source $BASE_HOME_DIR/scripts/update_toolchain_date.sh "$TEMP_HOME_DIR" "$TOOLCHAIN_DATE"
OUTPUT_SCRIPT2=("$?")
if [ "${#OUTPUT_SCRIPT2[@]}" -eq 0 ]; then
    echo "script2.sh failed to run."
    exit 1
else
    echo "Update toolchain ran successfully."
fi

# Call the third script
echo "Running script3.sh..."
source $BASE_HOME_DIR/scripts/check_rustc.sh "$TEMP_HOME_DIR"
OUTPUT_SCRIPT3=("$?")
if [ "${#OUTPUT_SCRIPT3[@]}" -eq 0 ]; then
    echo "script3.sh failed to run."
    exit 1
else
    echo "script3.sh completed successfully."
fi

# Call the fourth script
echo "Running script4.sh..."
source $BASE_HOME_DIR/scripts/check_kani.sh "$TEMP_HOME_DIR"
OUTPUT_SCRIPT4=("$?")
if [ "${#OUTPUT_SCRIPT4[@]}" -eq 0 ]; then
    echo "script4.sh failed to run."
    exit 1
else
    echo "script4.sh completed successfully."
fi

# Remove the temporary directory
# rm -rf "$TEMP_DIR"
