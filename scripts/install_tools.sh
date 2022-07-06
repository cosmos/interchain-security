#!/bin/bash

set -e -o pipefail

if ! command -v gocyclo &> /dev/null ; then
    echo "gocyclo not installed or available in the PATH, installing" >&2
    go install github.com/fzipp/gocyclo/cmd/gocyclo@latest;
fi

if ! command -v gocritic &> /dev/null ; then
    echo "gocritic not installed or available in the PATH, installing" >&2
    go install github.com/go-critic/go-critic/cmd/gocritic@latest;
fi

if ! command -v goimports &> /dev/null ; then
    echo "goimports not installed or available in the PATH, installing" >&2
    go install golang.org/x/tools/cmd/goimports@latest;
fi

exit 0
