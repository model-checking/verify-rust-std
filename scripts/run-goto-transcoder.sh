#!/bin/bash

set -e

##############
# PARAMETERS #
##############
target=$1/kani_verify_std/target/x86_64-unknown-linux-gnu/debug
supported_regex=$2
unsupported_regex=neg

# ESBMC reads CBMC goto binaries directly since v8.4, so Kani's output needs no conversion.
esbmc_url=https://github.com/esbmc/esbmc/releases/download/v8.5/esbmc-linux.zip
esbmc=esbmc/release/bin/esbmc

contract_folder=$target/deps
# Cargo 1.99+ gives each package its own debug/build/PKG/HASH/out/ and no longer creates debug/deps.
if [ ! -d "$contract_folder" ]; then
    contract_folder=$(find "$target/build" -path '*/out/*.out' | grep "$supported_regex" | head -n 1 | xargs -r dirname)
fi
if [ -z "$contract_folder" ]; then
    echo "No contract programs matching '$supported_regex' under $target"
    exit 1
fi

##########
# SCRIPT #
##########

echo "Checking contracts with ESBMC"

if [ ! -x "$esbmc" ]; then
    echo "ESBMC not found. Downloading..."
    mkdir -p esbmc
    wget -q -O esbmc/esbmc-linux.zip $esbmc_url
    unzip -q -o esbmc/esbmc-linux.zip -d esbmc
    chmod +x $esbmc
fi

checked=0
ls $contract_folder | grep "$supported_regex" | grep -v .symtab.out > _contracts.txt

while IFS= read -r line; do
    # I expect each line to be similar to 'core-58cefd8dce4133f9__RNvNtNtCs9uKEoH8KKW4_4core3num6verify24checked_unchecked_add_i8.out'
    # The entrypoint of the contract would be _RNvNtNtCs9uKEoH8KKW4_4core3num6verify24checked_unchecked_add_i8
    [[ $line =~ (_RNv.*)\.out$ ]] || continue
    contract=${BASH_REMATCH[1]}
    if echo "$contract" | grep -q "$unsupported_regex"; then
        continue
    fi
    echo "Processing: $contract"
    $esbmc --binary $contract_folder/$line --function $contract < /dev/null
    checked=$((checked + 1))
done < "_contracts.txt"

rm "_contracts.txt"

if [ "$checked" -eq 0 ]; then
    echo "No contract matching '$supported_regex' was checked"
    exit 1
fi
