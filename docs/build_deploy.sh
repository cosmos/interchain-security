#!/bin/sh

# build versioned docs prepared by sync_versions.sh
echo "building docusaurus main docs"
cp supported_versions.json versions.json
npm ci && npm run build

mv build ~/output
echo "done building docusaurus main docs"
