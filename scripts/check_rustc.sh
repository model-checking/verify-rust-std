#!/bin/bash

# Set the working directory for your local repository
HEAD_DIR=$1

# Temporary directory for upstream repository
TEMP_DIR=$(mktemp -d)

# Checkout your local repository
echo "Checking out local repository..."
cd "$HEAD_DIR"

# Get the commit ID from rustc --version
echo "Retrieving commit ID..."
COMMIT_ID=$(rustc --version | sed -e "s/.*(\(.*\) .*/\1/")
echo "$COMMIT_ID for rustc is"

# Clone the rust-lang/rust repository
echo "Cloning rust-lang/rust repository..."
git clone https://github.com/rust-lang/rust.git "$TEMP_DIR/upstream"

# Checkout the specific commit
echo "Checking out commit $COMMIT_ID..."
cd "$TEMP_DIR/upstream"
git checkout "$COMMIT_ID"

# Copy your library to the upstream directory
echo "Copying library to upstream directory..."
rm -rf "$TEMP_DIR/upstream/library"
cp -r "$HEAD_DIR/library" "$TEMP_DIR/upstream"

# Run the tests
cd "$TEMP_DIR/upstream"
export RUSTFLAGS="--check-cfg cfg(kani) --check-cfg cfg(feature,values(any()))"
echo "Running tests..."
./configure --set=llvm.download-ci-llvm=true
./x test --stage 0 library/std

echo "Tests completed."

# Clean up the temporary directory
rm -rf "$TEMP_DIR"
