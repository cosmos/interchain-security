#!/bin/bash

# If -e is not set then if the build fails, it will use the old container, resulting in a very confusing debugging situation
# Setting -e makes it error out if the build fails
set -eux

usage() {
    echo """
Usage: $0 [-c <string>] [-g <string>] [-s <string>] [-h] container-name instance-name
   [-c consumer-version] : the consumer version to be used in the container.
                           Mutial exclusive to -p
   [-p provider-version] : the provider version to be used in the container.
                           Mutial exclusive to -c
   [-g gaia-tag]         : use gaia as provider with specified version
   [-s SDK-path]         : use custom SDK
   [-h]                  : print this help
"""
}

## Process the optional arguments if any
while getopts ":c:p:g:s:h" flag
    do
             case "${flag}" in
                    c) CONSUMER_VERSION=${OPTARG};;
                    p) PROVIDER_VERSION=${OPTARG};;
                    g) USE_GAIA_TAG=${OPTARG};;
                    s) LOCAL_SDK_PATH=${OPTARG};;
                    h) SHOW_HELP=1;;
                    *) usage;;
             esac
    done

if [ ${SHOW_HELP+x} ]; then
    usage
    exit 0
fi

shift $((OPTIND - 1))

# Set positional arguments
CONTAINER_NAME=$1
INSTANCE_NAME=$2

# Remove existing container instance
set +e
docker rm -f "$INSTANCE_NAME"
set -e

# Delete old sdk directory if it exists
if [ -d "./cosmos-sdk" ]; then
    rm -rf ./cosmos-sdk/
fi

# Copy sdk directory to working dir if path was specified
if [[ ${LOCAL_SDK_PATH+x} ]]
then
    cp -n -r "$LOCAL_SDK_PATH" ./cosmos-sdk
    printf "\n\nUsing local sdk version from %s\n\n\n" "$LOCAL_SDK_PATH"
else
    printf "\n\nUsing default sdk version\n\n\n"
fi

# Build the Docker container
if [[ ${USE_GAIA_TAG+x} ]]
then
    printf "\n\nUsing gaia as provider\n\n"
    printf "\n\nUsing gaia tag %s\n\n" "$USE_GAIA_TAG"
    docker build  -f Dockerfile.gaia -t "$CONTAINER_NAME" --build-arg USE_GAIA_TAG="$USE_GAIA_TAG" .
elif [ ${CONSUMER_VERSION+x} ] && [ ${PROVIDER_VERSION+x} ]; then
    printf "\n\nUsing ICS consumer app from image version ${CONSUMER_VERSION} and provider from image version ${PROVIDER_VERSION}"
    docker build -f Dockerfile-Combined --build-arg PROVIDER_VERSION="${PROVIDER_VERSION}" --build-arg CONSUMER_VERSION="${CONSUMER_VERSION}" -t "$CONTAINER_NAME" .

elif [ ${CONSUMER_VERSION+x} ]; then
    printf "\n\nUsing ICS consumer app from image version ${CONSUMER_VERSION}"
    docker build -f Dockerfile-Consumer --build-arg CONSUMER_VERSION="${CONSUMER_VERSION}" -t "$CONTAINER_NAME" .
elif [ ${PROVIDER_VERSION+x} ]; then
    printf "\n\nUsing ICS provider app from image version ${PROVIDER_VERSION}"
    docker build -f Dockerfile-Provider --build-arg PROVIDER_VERSION="${PROVIDER_VERSION}" -t "$CONTAINER_NAME" .
else
    printf "\n\nUsing ICS provider app as provider\n\n\n"
    docker build -f Dockerfile -t "$CONTAINER_NAME" .
fi

# Remove copied sdk directory
rm -rf ./cosmos-sdk/

# Run new test container instance with extended privileges.
# Extended privileges are granted to the container here to allow for network namespace manipulation (bringing a node up/down)
# See: https://docs.docker.com/engine/reference/run/#runtime-privilege-and-linux-capabilities
docker run --name "$INSTANCE_NAME" --cap-add=NET_ADMIN --privileged "$CONTAINER_NAME" /bin/bash /testnet-scripts/beacon.sh &
