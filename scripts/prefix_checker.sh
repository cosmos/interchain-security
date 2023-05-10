#!/bin/bash

# Check if file name is provided
if [[ -z $1 ]]; then
    echo "Error: No file name provided"
    exit 1
fi

# Extract keys from a given file
# this awk command extracts the first word from each line between a line containing
# "const (" and a line containing ")" in the Go file, but only if that word starts
# with a letter. This should correspond to the constant names in the const block.
extract_prefixes() {
    awk '/const \(/,/\)/ { if ($1 ~ /^[A-Za-z]/ && $1 != "const") print $1 }' $1
}

# Get the previous commit hash
prev_commit=$(git rev-parse HEAD~1)

# Extract keys from the current and previous versions of the file
current_prefixes=$(extract_prefixes $1)
prev_prefixes=$(extract_prefixes <(git show $prev_commit:$1))

echo $current_prefixes
echo $prev_prefixes

# Compare the keys
if ! [[ $current_prefixes == $prev_prefixes* ]]; then
    echo "Error: prefixes order changed or a prefix was deleted"
    exit 1
fi
