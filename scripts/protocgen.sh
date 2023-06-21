#!/usr/bin/env bash

set -eo pipefail

echo "Generating gogo proto code"
cd proto
ls ../ -alh
proto_dirs=$(find ./interchain_security -path -prune -o -name '*.proto' -print0 | xargs -0 -n1 dirname | sort | uniq)
generated_files=""
for dir in $proto_dirs; do
  for file in $(find "${dir}" -maxdepth 1 -name '*.proto'); do
    if grep "option go_package" "$file" &> /dev/null ; then
      echo "Generating protobuf files for: $file"
      buf generate --template buf.gen.gogo.yaml "$file"

    fi
  done
done
ls -alh
cd ..
ls -alh

files=$(find . -type f -name '*.pb.go')
if [ -n "$files" ]; then
  generated_files=$(printf "%s\n%s" "$generated_files" "$files")
else
  echo "No protobuf files generated for: $file"
fi

echo ".pb files:"
if [ -n "$generated_files" ]; then
  printf "%s\n" $generated_files
else
  echo "No protobuf files generated."
fi

# move proto files to the right places
cp -r github.com/cosmos/interchain-security/v3/* ./
rm -rf github.com
