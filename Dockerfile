# syntax=docker/dockerfile:1

FROM golang:1.18-alpine AS is-builder

ENV PACKAGES curl make git libc-dev bash gcc linux-headers
RUN apk add --no-cache $PACKAGES

ENV CGO_ENABLED=0
ENV GOOS=linux

WORKDIR /downloads

# Copy in the repo under test
ADD . /interchain-security

WORKDIR /interchain-security

RUN go mod edit -replace github.com/cosmos/cosmos-sdk@v0.45.2-0.20220613134718-c783aea68fbd=../cosmos-sdk
RUN go mod tidy

# Install interchain security binary
RUN make install

# Get Hermes build
FROM informalsystems/hermes:1.0.0-rc.1 AS hermes-builder

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


# Copy in the shell scripts that run the testnet
ADD ./integration-tests/testnet-scripts /testnet-scripts

# Copy in the hermes config
ADD ./integration-tests/testnet-scripts/hermes-config.toml /root/.hermes/config.toml