#!/bin/bash

# Assign the command line arguments to variables
filename=$1
start_index=$2
end_index=$3

# Loop from start_index to end_index
for ((index=$start_index; index<=$end_index; index++))
do
  # Use jq to extract the state with the current index and save it to a file named "<index>.json"
  jq --argjson idx $index '.states[] | select(."#meta".index == $idx)' $filename > "${index}.json"
done
