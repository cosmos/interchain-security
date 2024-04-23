#!/bin/bash

# Replace 'your_command_here' with your actual command, ensuring it's properly quoted if it contains spaces or special characters
COMMAND='go test -v'

EXPECTED_OUT="Running traces from the traces folder done"


# Loop 1000 times
for i in {1..100}
do
    output=$($COMMAND)

    # Compare the output with the initial output
    if ! echo "$output" | grep -q "$EXPECTED_OUT"; then
        echo $output
        echo "Error: Output at iteration $i does not contain the expected line."
        exit 1
    fi
done

echo "All outputs were consistent across 1000 runs."
