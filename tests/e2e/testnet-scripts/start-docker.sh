#!/bin/bash

# If -e is not set then if the build fails, it will use the old container, resulting in a very confusing debugging situation
# Setting -e makes it error out if the build fails
set -eux 

CONTAINER_NAME=$1
INSTANCE_NAME=$2
LOCAL_SDK_PATH=${3:-"default"} # Sets this var to default if null or unset

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
docker build -t "$CONTAINER_NAME" .

# Remove copied sdk directory
rm -rf ./cosmos-sdk/

# Run new test container instance with extended privileges.
# Extended privileges are granted to the container here to allow for network namespace manipulation (bringing a node up/down) 
# See: https://docs.docker.com/engine/reference/run/#runtime-privilege-and-linux-capabilities
docker run --name "$INSTANCE_NAME" --cap-add=NET_ADMIN --privileged "$CONTAINER_NAME" /bin/bash /testnet-scripts/beacon.sh &
