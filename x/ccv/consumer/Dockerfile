# syntax=docker/dockerfile:1

FROM golang:1.20-alpine AS is-builder

ENV PACKAGES curl wget unzip make git libc-dev bash gcc linux-headers
RUN apk add --no-cache $PACKAGES

ENV CGO_ENABLED=0
ENV GOOS=linux
ENV GOFLAGS="-buildvcs=false"

# build the interchain-security provider from v1.1 tag
WORKDIR /provider
RUN wget https://github.com/cosmos/interchain-security/archive/refs/tags/v1.1.0.zip
RUN unzip v1.1.0.zip
WORKDIR /provider/interchain-security-1.1.0
RUN make install
# delete consumerd binary to see if the local one is being used 
RUN rm /go/bin/interchain-security-cd

# Copy in the repo under test
WORKDIR /
ADD . /interchain-security

WORKDIR /interchain-security

# # Do not specify version here. It leads to odd replacement behavior 
# RUN if [ -d "./cosmos-sdk" ]; then go mod edit -replace github.com/cosmos/cosmos-sdk=./cosmos-sdk; fi
# RUN go mod tidy

# Install interchain security binary
RUN make install

# Get Hermes build
FROM informalsystems/hermes:1.2.0 AS hermes-builder

FROM --platform=linux/amd64 fedora:36
RUN dnf update -y
RUN dnf install -y which iproute iputils procps-ng vim-minimal tmux net-tools htop jq
USER root

COPY --from=hermes-builder /usr/bin/hermes /usr/local/bin/

COPY --from=is-builder /go/bin/interchain-security-pd /usr/local/bin/interchain-security-pd
COPY --from=is-builder /go/bin/interchain-security-cd /usr/local/bin/interchain-security-cd
COPY --from=is-builder /go/bin/interchain-security-cdd /usr/local/bin/interchain-security-cdd


# Copy in the shell scripts that run the testnet
ADD ./tests/integration/testnet-scripts /testnet-scripts

# Copy in the hermes config
ADD ./tests/integration/testnet-scripts/hermes-config.toml /root/.hermes/config.toml
