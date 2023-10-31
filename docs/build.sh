#!/bin/sh

COMMIT=$(git rev-parse HEAD)
for version in $(jq -r .[] versions.json); do
    echo "Building docusaurus $version docs ..."
    git checkout $version
    npm cache clean --force && npm install && npm run docusaurus docs:version $version

    # versions.json / package-lock.json, get mangled by Docusarus causing problems
    rm versions.json package-lock.json
done

# Rebuild main/commit level docs
echo "Building docusaurus main docs ..."

rm package-lock.json
git checkout $COMMIT 

# Move figures over
cp -R figures ./versioned_docs/

# Actual build
npm install && npm run build

echo "Finished building docs ... "