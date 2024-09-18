#!/bin/bash

# Check if the correct number of args
if [[ $# -ne 2 ]]; then
    echo "Usage: $0 <toolchain_file_path> <new_date>"
    echo "$#"
    exit 1
fi

toolchain_file="$1/rust-toolchain.toml"
new_date="$2"

# Check if the toolchain file exists
if [[ ! -f "$toolchain_file" ]]; then
    echo "Error: Toolchain file does not exist."
    exit 1
fi

# Use sed to replace the date
sed -i.bak -E 's/^channel = "nightly-[0-9]{4}-[0-9]{2}-[0-9]{2}"$/channel = "nightly-'"$new_date"'"/' "$toolchain_file"

# Check if the replacement was succesful
if [[ $? -eq 0 ]]; then
    echo "Date succesfully updated in $toolchain_file"
    rm "${toolchain_file}.bak"

    git commit -am "Update toolchain to $new_date"
else
    echo "Error: Failed to update the file in $toolchain_file"
    exit 1
fi
