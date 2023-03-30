#!/bin/bash

# If -e is not set then if the build fails, it will use the old container, resulting in a very confusing debugging situation
# Setting -e makes it error out if the build fails
set -eux 

CONTAINER_NAME=$1
INSTANCE_NAME=$2
LOCAL_SDK_PATH=${3:-"default"} # Sets this var to default if null or unset
USE_GAIA_PROVIDER=${4:-"false"} # if true, use gaia as provider; if false, use ICS app
USE_GAIA_TAG=${5:-""} # gaia tag to use if using gaia as provider; by default the latest tag is used

# Remove existing container instance
set +e
docker rm -f "$INSTANCE_NAME"
set -e

# Delete old sdk directory if it exists 
if [ -d "./cosmos-sdk" ]; then
    rm -rf ./cosmos-sdk/
fi 

# Copy sdk directory to working dir if path was specified
if [[ "$LOCAL_SDK_PATH" != "default" ]]
then
    cp -n -r "$LOCAL_SDK_PATH" ./cosmos-sdk
    printf "\n\nUsing local sdk version from %s\n\n\n" "$LOCAL_SDK_PATH"
else
    printf "\n\nUsing default sdk version\n\n\n"
fi

# Build the Docker container
if [[ "$USE_GAIA_PROVIDER" = "true" ]]
then
    printf "\n\nUsing gaia as provider\n\n"
    printf "\n\nUsing gaia tag %s\n\n" "$USE_GAIA_TAG"
    docker build  -f Dockerfile.gaia -t "$CONTAINER_NAME" --build-arg USE_GAIA_TAG="$USE_GAIA_TAG" .
else
    printf "\n\nUsing ICS provider app as provider\n\n\n"
    docker build -f Dockerfile -t "$CONTAINER_NAME"  .
fi

# Remove copied sdk directory
rm -rf ./cosmos-sdk/

# Run new test container instance with extended privileges.
# Extended privileges are granted to the container here to allow for network namespace manipulation (bringing a node up/down) 
# See: https://docs.docker.com/engine/reference/run/#runtime-privilege-and-linux-capabilities
docker run --name "$INSTANCE_NAME" --cap-add=NET_ADMIN --privileged "$CONTAINER_NAME" /bin/bash /testnet-scripts/beacon.sh &
