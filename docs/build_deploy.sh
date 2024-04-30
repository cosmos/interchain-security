#!/bin/sh

# build versioned docs prepared by sync_versions.sh
echo "building docusaurus main docs"
npm ci && npm run build

# copy "legacy" docs directory into the final build directory
# the directory is in "docs/legacy" of the source branch (legacy-docs-page)
# the build environment must be in "./docs" for this to work as expected
git checkout origin/legacy-docs-page -- legacy
cp -r ./legacy ./build/
mv build ~/output
echo "done building docusaurus main docs"
