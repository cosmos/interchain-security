# syntax=docker/dockerfile:1

FROM golang:1.18-alpine AS is-builder

ENV PACKAGES curl make git libc-dev bash gcc linux-headers
RUN apk add --no-cache $PACKAGES

ENV CGO_ENABLED=0
ENV GOOS=linux
ENV GOFLAGS="-buildvcs=false"

WORKDIR /downloads

ARG PROVIDER_DIR_NAME
ARG CONSUMER_DIR_NAME

# TODO: At this point you have the directory names of consumer and provider,
# Their directories have been copied into the workdir. Lastly, you need to 
# change directories into each of the consumer and provider and call "make install"
# to install each binary within the container. Note that this puts constraints on
# consumers and providers in that they have to implement a make install target
# within their makefile, AND they must have a makefile inside each source code directory.
#
# Once you make install each binary, it looks like there might be some more setup below
# to replicate for the custom directories.  

## PSUEDOCDE
# IF directory strings are empty
# do the shit below as before

# ELSE 
# Do that same shit, but do it for the custom directories using the info above. 

# Copy in the repo under test
ADD . /interchain-security

WORKDIR /interchain-security

# Do not specify version here. It leads to odd replacement behavior 
RUN if [ -d "./cosmos-sdk" ]; then go mod edit -replace github.com/cosmos/cosmos-sdk=./cosmos-sdk; fi
RUN go mod tidy

# Install interchain security binary
RUN make install

# Get Hermes build
FROM informalsystems/hermes:1.0.0 AS hermes-builder

FROM --platform=linux/amd64 fedora:36
RUN dnf update -y
RUN dnf install -y which iproute iputils procps-ng vim-minimal tmux net-tools htop jq 
USER root

# Copy Hermes and IS binaries to final image
COPY --chown=0:0 --from=hermes-builder /usr/lib/x86_64-linux-gnu/libssl.so.1.1 /usr/lib/x86_64-linux-gnu/libssl.so.1.1
COPY --chown=0:0 --from=hermes-builder /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1 /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1

COPY --from=hermes-builder /usr/bin/hermes /usr/local/bin/

COPY --from=is-builder /go/bin/interchain-security-pd /usr/local/bin/interchain-security-pd
COPY --from=is-builder /go/bin/interchain-security-cd /usr/local/bin/interchain-security-cd
COPY --from=is-builder /go/bin/interchain-security-cdd /usr/local/bin/interchain-security-cdd


# Copy in the shell scripts that run the testnet
ADD ./tests/integration/testnet-scripts /testnet-scripts

# Copy in the hermes config
ADD ./tests/integration/testnet-scripts/hermes-config.toml /root/.hermes/config.toml
