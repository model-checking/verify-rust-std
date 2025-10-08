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
REPO_DIR=$(git rev-parse --show-toplevel)

# Temporary directory for upstream repository
TMP_RUST_DIR=$(mktemp -d -t "check_rustc_XXXXXX")

# Checkout your local repository
echo "Checking out local repository..."
cd "$REPO_DIR"

# Get the (short hash) commit ID from rustc --version
echo "Retrieving commit ID..."
COMMIT_ID=$(rustc --version | sed -e "s/.*(\(.*\) .*/\1/")

# Get the full commit ID for shallow clone
echo "Full commit id for $COMMIT_ID for is:"

if [ -z "${GH_TOKEN:-}" ]; then
  curl -o "${TMP_RUST_DIR}/output.json" -s --show-error \
      "https://api.github.com/repos/rust-lang/rust/commits?sha=${COMMIT_ID}&per_page=1"
else
  # Use token if possible to avoid being throttled
  curl -o "${TMP_RUST_DIR}/output.json" -s --show-error \
       --request GET \
       --url "https://api.github.com/repos/rust-lang/rust/commits?sha=${COMMIT_ID}&per_page=1" \
       --header "Accept: application/vnd.github+json" \
       --header "Authorization: Bearer $GH_TOKEN"
fi
cat "${TMP_RUST_DIR}/output.json"  # Dump the file in case `curl` fails.

COMMIT_ID=$(cat "${TMP_RUST_DIR}/output.json" | jq -r '.[0].sha')
echo "- $COMMIT_ID"

# Clone the rust-lang/rust repository
echo "Cloning rust-lang/rust repository into ${TMP_RUST_DIR}..."
pushd "$TMP_RUST_DIR" > /dev/null
git init
git remote add origin https://github.com/rust-lang/rust.git
git fetch --depth 1 origin $COMMIT_ID

echo "Checking out commit $COMMIT_ID..."
git checkout "$COMMIT_ID"
git submodule update --init --depth 1
popd

# Copy your library to the upstream directory
echo "Copying library to upstream directory..."
rm -rf "${TMP_RUST_DIR}/library"
cp -r "${REPO_DIR}/library" "${TMP_RUST_DIR}"

# Configure repository
pushd "${TMP_RUST_DIR}"
# Download LLVM binaries from Rust's CI instead of building them
./configure --set=llvm.download-ci-llvm=true
export RUSTFLAGS="--check-cfg cfg(kani) --check-cfg cfg(feature,values(any()))"
export RUST_BACKTRACE=1
unset GITHUB_ACTIONS # Bootstrap script requires specific repo layout when run from an action. Disable that.

# Run tidy
if [ "${TIDY_MODE}" == "--bless" ];
then
    echo "Run rustfmt"
    # TODO: This should be:
    # ./x test tidy --bless
    ./x fmt
    cp -r "${TMP_RUST_DIR}/library" "${REPO_DIR}"
else
    # TODO: This should be:
    # ./x test tidy
    echo "Check format"
    if ! ./x fmt --check; then
        echo "Format check failed. Run $0 --bless to fix the failures."
        # Clean up the temporary directory
        popd
        rm -rf "$TMP_RUST_DIR"
        exit 1
    fi
fi

# TODO: this logic is broken because the stage 0 bootstrap sequence was redesigned, c.f. https://blog.rust-lang.org/inside-rust/2025/05/29/redesigning-the-initial-bootstrap-sequence/
# However, changing the command to --stage 1 as suggested does not work; the compiler complains that there is an old version of the `safety` crate
# compiled by the beta compiler. For now, comment it out and see if continued work on this feature (e.g. https://github.com/rust-lang/rust/pull/142002) fixes it.
# Run tests
# cd "$TMP_RUST_DIR"
# echo "Running tests..."
# ./x test --stage 0 library/std

# echo "Tests completed."

# Clean up the temporary directory
rm -rf "$TMP_RUST_DIR"
