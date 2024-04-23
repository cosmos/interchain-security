#!/bin/bash

# Assign the command line arguments to variables
filename=$1
start_index=$2
end_index=$3

# Loop from start_index to end_index
for ((index=$start_index; index<=$end_index; index++))
do
  # Use jq to extract the index and the consumersWithPowerChangesInThisEpoch value and print them
  jq --argjson idx $index '.states[] | select(."#meta".index == $idx) | .currentState.providerState.consumersWithAddrAssignmentChangesInThisEpoch | "Index: \($idx) Value: \(.)"' $filename
done
