#!/bin/bash

# Check if file name is provided
if [[ -z $1 ]]; then
    echo "Error: No file name provided"
    exit 1
fi

# Extract keys from a given file
extract_keys() {
    awk '/const \(/,/\)/ { if ($1 ~ /^[A-Za-z]/ && $1 != "const") print $1 }' $1
}


# Get the previous commit hash
prev_commit=$(git rev-parse HEAD~1)

# Extract keys from the current and previous versions of the file
current_keys=$(extract_keys $1)
prev_keys=$(extract_keys <(git show $prev_commit:$1))

echo $current_keys
echo $prev_keys

# Compare the keys
if ! [[ $current_keys == $prev_keys* ]]; then
    echo "Error: keys order changed or a key was deleted"
    exit 1
fi
