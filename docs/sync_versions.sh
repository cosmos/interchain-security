#!/bin/sh

# this script builds the docs for all versions in versions.json
# all the versions are included in the docs webpage

# exit if there are uncommitted changes
if git diff-index --quiet HEAD --; then
    # initial branch
    COMMIT=$(git rev-parse HEAD)
    for version in $(jq -r .[] versions.json); do
        echo "Building docusaurus $version docs ..."
        git checkout $version
        npm cache clean --force && npm install && npm run docusaurus docs:version $version

        # versions.json / package-lock.json, get mangled by Docusarus causing problems
        rm versions.json package-lock.json
    done

    # return to initial branch but keep the files created by Docusarus in the loop above
    (git reset --hard && git checkout $COMMIT)

    # copy figures so they are available to all versioned docs
    cp -R figures ./versioned_docs/
else

    echo "Please commit all changes before running this script"
    exit 1
fi


