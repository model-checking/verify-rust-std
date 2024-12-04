#!/bin/bash
# Runs the Rust bootstrap script in order to ensure the changes to this repo
# are compliant with the Rust repository tests.
#
# TODO: Need to enable full tidy run.

set -eu

usage() {
    echo "Usage: $0 [--help] [--bless]"
    echo "Options:"
    echo "  -h, --help      Show this help message"
    echo "  --bless         Update library files using tidy"
}

TIDY_MODE=""
# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            usage
            exit 0
            ;;
        --bless)
            TIDY_MODE="--bless"
            shift 1
            ;;
        *)
            echo "Error: Unknown option `$1`"
            usage
            exit 1
            ;;
    esac
done

# Set the working directory for your local repository
HEAD_DIR=$(git rev-parse --show-toplevel)

# Temporary directory for upstream repository
RUST_DIR=$(mktemp -d --suffix ".rust")

# Checkout your local repository
echo "Checking out local repository..."
cd "$HEAD_DIR"

# Get the commit ID from rustc --version
echo "Retrieving commit ID..."
COMMIT_ID=$(rustc --version | sed -e "s/.*(\(.*\) .*/\1/")
echo "$COMMIT_ID for rustc is"

# Get the full commit ID for shallow clone
curl -H "Connection: close" -o "${RUST_DIR}/output.json" -s --show-error \
    "https://api.github.com/repos/rust-lang/rust/commits?sha=${COMMIT_ID}&per_page=1"
COMMIT_ID=$(jq -r '.[0].sha' "${RUST_DIR}/output.json")

# Clone the rust-lang/rust repository
echo "Cloning rust-lang/rust repository into ${RUST_DIR}..."
pushd "$RUST_DIR" > /dev/null
git init
git remote add origin https://github.com/rust-lang/rust.git
git fetch --depth 1 origin $COMMIT_ID

echo "Checking out commit $COMMIT_ID..."
git checkout "$COMMIT_ID"
git submodule update --init --depth 1
popd

# Copy your library to the upstream directory
echo "Copying library to upstream directory..."
rm -rf "${RUST_DIR}/library"
cp -r "${HEAD_DIR}/library" "${RUST_DIR}"

# Configure repository
pushd "${RUST_DIR}"
./configure --set=llvm.download-ci-llvm=true
export RUSTFLAGS="--check-cfg cfg(kani) --check-cfg cfg(feature,values(any()))"

# Run tidy
if [ "${TIDY_MODE}" == "--bless" ];
then
    echo "Run rustfmt"
    # TODO: This should be:
    # ./x test tidy --bless
    ./x fmt
    cp -r "${RUST_DIR}/library" "${HEAD_DIR}"
else
    # TODO: This should be:
    # ./x test tidy
    echo "Check format"
    ./x fmt --check
fi

# Run tests
cd "$RUST_DIR/upstream"
echo "Running tests..."
./x test --stage 0 library/std

echo "Tests completed."

# Clean up the temporary directory
rm -rf "$RUST_DIR"
