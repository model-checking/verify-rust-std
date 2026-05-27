#!/bin/bash

# Script to find files with specific annotations and print contracts
# containing those annotations up to a line with "fn"
PATTERN_STRING='^\s*#\[((safety::)?(requires|ensures)\(|cfg_attr\((kani|not\(kani\)))'

# Find all files in the git repository that contain any of the patterns
FILES=$(git grep -l -P "$PATTERN_STRING" library/)

if [ -z "$FILES" ]; then
  echo "No files found with the specified patterns."
  exit 1
fi

# Process each file
for FILE in $FILES; do
  echo "=== $FILE ==="

  # Use perl to find contracts starting with any pattern and ending at "fn"
  cat $FILE | perl -e "
    \$in_contract = 0;
    \$ws = 0;
    while(<>) {
      \$line = \$_;
      if (!\$in_contract && /$PATTERN_STRING/ && !/^\s*#\[cfg_attr\(kani, derive\(/) {
        \$in_contract = 1;
        /^(\s*)/;
        \$ws = length(\$1);
      }
      if (\$in_contract) {
        \$line =~ s/^ {\$ws}//;
        print \$line; 
        if (\$line =~ /(^| )fn /) {
          \$in_contract = 0;
          print \"\n\";
        }
      }
    }
  "

  echo
done
