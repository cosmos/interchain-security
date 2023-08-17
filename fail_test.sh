#!/bin/bash
while true; do
    # Run your command here
    go run ./tests/e2e/... --tc happy-path-short --use-cometmock --use-gorelayer --verbose

    # Check the exit code of the command
    if [ $? -ne 0 ]; then
        # If the command failed, exit the loop
        break
    fi

    # Wait for a few seconds before running the command again
    sleep 5
done