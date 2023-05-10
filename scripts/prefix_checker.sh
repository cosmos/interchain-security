#!/bin/bash

# Check if file name is provided
if [[ -z $1 ]]; then
    echo "Error: No file name provided"
    exit 1
fi

# Extract keys from a given file
extract_keys() {
    grep -oP '\b[A-Za-z_][A-Za-z0-9_]*\b' $1
}

# Get the previous commit hash
prev_commit=$(git rev-parse HEAD~1)

# Extract keys from the current and previous versions of the file
current_keys=$(extract_keys $1)
prev_keys=$(extract_keys <(git show $prev_commit:$1))

# Compare the keys
if ! [[ $current_keys == $prev_keys* ]]; then
    echo "Error: keys order changed or a key was deleted"
    exit 1
fi