# syntax=docker/dockerfile:1

FROM golang:1.18-alpine AS is-builder

ENV PACKAGES curl make git libc-dev bash gcc linux-headers
RUN apk add --no-cache $PACKAGES

ENV CGO_ENABLED=0
ENV GOOS=linux
ENV GOFLAGS="-buildvcs=false"

# WORKDIR /downloads

# # Copy in the repo under test
# ADD . /interchain-security

# WORKDIR /interchain-security

# # Do not specify version here. It leads to odd replacement behavior 
# RUN if [ -d "./cosmos-sdk" ]; then go mod edit -replace github.com/cosmos/cosmos-sdk=./cosmos-sdk; fi
# RUN go mod tidy

# # Install interchain security binary
# RUN make install

# Get Hermes build
# FROM informalsystems/hermes:1.0.0 AS hermes-builder

# Get patched version of Hermes that supports relaying double signs
# modelled after official hermes image https://github.com/informalsystems/hermes/blob/master/ci/release/hermes.Dockerfile
FROM rust:1.64.0-buster AS patched-hermes

ENV PACKAGES curl make git libc-dev bash gcc linux-headers libssl-dev

WORKDIR /root
RUN rustup target add x86_64-unknown-linux-gnu
RUN git clone https://github.com/informalsystems/hermes
RUN cd hermes && git checkout master && cargo build --release --target x86_64-unknown-linux-gnu

FROM debian:buster-slim AS hermes-builder
LABEL maintainer="hello@informal.systems"

RUN useradd -m hermes -s /bin/bash
WORKDIR /home/hermes
USER hermes:hermes
ENTRYPOINT ["/usr/bin/hermes"]

COPY --chown=0:0 --from=patched-hermes /usr/lib/x86_64-linux-gnu/libssl.so.1.1 /usr/lib/x86_64-linux-gnu/libssl.so.1.1
COPY --chown=0:0 --from=patched-hermes /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1 /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1
COPY --chown=0:0 --from=patched-hermes /root/hermes/target/release/hermes /usr/bin/hermes
COPY --chown=0:0 --from=patched-hermes /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/ca-certificates.crt
# end patched hermes build

FROM --platform=linux/amd64 fedora:36
RUN dnf update -y
RUN dnf install -y which iproute iputils procps-ng vim-minimal tmux net-tools htop jq 
USER root

# Copy Hermes and IS binaries to final image
COPY --chown=0:0 --from=hermes-builder /usr/lib/x86_64-linux-gnu/libssl.so.1.1 /usr/lib/x86_64-linux-gnu/libssl.so.1.1
COPY --chown=0:0 --from=hermes-builder /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1 /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1

COPY --from=hermes-builder /usr/bin/hermes /usr/local/bin/

# COPY --from=is-builder /go/bin/interchain-security-pd /usr/local/bin/interchain-security-pd
# COPY --from=is-builder /go/bin/interchain-security-cd /usr/local/bin/interchain-security-cd
# COPY --from=is-builder /go/bin/interchain-security-cdd /usr/local/bin/interchain-security-cdd


# Copy in the shell scripts that run the testnet
ADD ./tests/integration/testnet-scripts /testnet-scripts

# Copy in the hermes config
ADD ./tests/integration/testnet-scripts/hermes-config.toml /root/.hermes/config.toml
