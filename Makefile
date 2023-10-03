#!/usr/bin/make -f

install: go.sum
		export GOFLAGS='-buildmode=pie'
		export CGO_CPPFLAGS="-D_FORTIFY_SOURCE=2"
		export CGO_LDFLAGS="-Wl,-z,relro,-z,now -fstack-protector"
		go install $(BUILD_FLAGS) ./cmd/interchain-security-pd
		go install $(BUILD_FLAGS) ./cmd/interchain-security-cd
		go install $(BUILD_FLAGS) ./cmd/interchain-security-cdd
		go install $(BUILD_FLAGS) ./cmd/interchain-security-sd

# run all tests: unit, integration, diff, and E2E
test:
	go test ./... && go run ./tests/e2e/...

# run all unit tests
test-unit:
	go test ./...

# run unit and integration tests
test-short:
	go test ./x/... ./app/... ./tests/integration/...

# run E2E tests
test-e2e:
	go run ./tests/e2e/...

# run difference tests
test-diff:
	go test ./tests/difference/...

# run only happy path E2E tests
test-e2e-short:
	go run ./tests/e2e/... --tc happy-path

# run only happy path E2E tests with cometmock
# this set of traces does not test equivocation but it does check downtime
test-e2e-short-cometmock:
	go run ./tests/e2e/... --tc happy-path-short --use-cometmock --use-gorelayer

# run full E2E tests in sequence (including multiconsumer)
test-e2e-multi-consumer:
	go run ./tests/e2e/... --include-multi-consumer

# run full E2E tests in parallel (including multiconsumer)
test-e2e-parallel:
	go run ./tests/e2e/... --include-multi-consumer --parallel

# run full E2E tests in sequence (including multiconsumer) using latest tagged gaia
test-gaia-e2e:
	go run ./tests/e2e/... --include-multi-consumer --use-gaia

# run only happy path E2E tests using latest tagged gaia
test-gaia-e2e-short:
	go run ./tests/e2e/... --tc happy-path --use-gaia

# run full E2E tests in parallel (including multiconsumer) using latest tagged gaia
test-gaia-e2e-parallel:
	go run ./tests/e2e/... --include-multi-consumer --parallel --use-gaia

# run full E2E tests in sequence (including multiconsumer) using specific tagged version of gaia
# usage: GAIA_TAG=v9.0.0 make test-gaia-e2e-tagged
test-gaia-e2e-tagged:
	go run ./tests/e2e/... --include-multi-consumer --use-gaia --gaia-tag $(GAIA_TAG)

# run only happy path E2E tests using latest tagged gaia
# usage: GAIA_TAG=v9.0.0 make test-gaia-e2e-short-tagged
test-gaia-e2e-short-tagged:
	go run ./tests/e2e/... --tc happy-path --use-gaia --gaia-tag $(GAIA_TAG)

# run full E2E tests in parallel (including multiconsumer) using specific tagged version of gaia
# usage: GAIA_TAG=v9.0.0 make test-gaia-e2e-parallel-tagged
test-gaia-e2e-parallel-tagged:
	go run ./tests/e2e/... --include-multi-consumer --parallel --use-gaia --gaia-tag $(GAIA_TAG)

# run all tests with caching disabled
test-no-cache:
	go test ./... -count=1 && go run ./tests/e2e/...

###############################################################################
###                                Linting                                  ###
###############################################################################

golangci_version=v1.52.2

lint:
	@echo "--> Running linter"
	@go install github.com/golangci/golangci-lint/cmd/golangci-lint@$(golangci_version)
	golangci-lint run  ./... --config .golangci.yml

format:
	find . -name '*.go' -type f -not -path "./vendor*" -not -path "*.git*" -not -path "./client/docs/statik/statik.go" -not -path "./tests/mocks/*" -not -name "*.pb.go" -not -name "*.pb.gw.go" -not -name "*.pulsar.go" -not -path "./crypto/keys/secp256k1/*" | xargs gofumpt -w -l
	golangci-lint run --fix --config .golangci.yml
.PHONY: format

mockgen_cmd=go run github.com/golang/mock/mockgen
mocks:
	$(mockgen_cmd) -package=keeper -destination=testutil/keeper/mocks.go -source=x/ccv/types/expected_keepers.go


BUILDDIR ?= $(CURDIR)/build
BUILD_TARGETS := build

build: BUILD_ARGS=-o $(BUILDDIR)/

$(BUILD_TARGETS): go.sum $(BUILDDIR)/
	go $@ -mod=readonly $(BUILD_FLAGS) $(BUILD_ARGS) ./...

$(BUILDDIR)/:
	mkdir -p $(BUILDDIR)/

###############################################################################
###                                Protobuf                                 ###
###############################################################################

DOCKER := $(shell which docker)
HTTPS_GIT := https://github.com/cosmos/interchain-security.git

containerProtoVer=0.13.0
containerProtoImage=ghcr.io/cosmos/proto-builder:$(containerProtoVer)

protoImage=$(DOCKER) run --rm -v $(CURDIR):/workspace --workdir /workspace $(containerProtoImage)


proto-all: proto-format proto-lint proto-gen

proto-gen:
	@echo "Generating Protobuf files"
	@$(protoImage) sh ./scripts/protocgen.sh;

proto-check:
	@if git diff --quiet --exit-code main...HEAD -- proto; then \
		echo "Pass! No committed changes found in /proto directory between the currently checked out branch and main."; \
	else \
		echo "Committed changes found in /proto directory between the currently checked out branch and main."; \
		modified_protos=$$(git diff --name-only main...HEAD proto); \
		modified_pb_files= ; \
        for proto_file in $${modified_protos}; do \
            proto_name=$$(basename "$${proto_file}" .proto); \
            pb_files=$$(find x/ccv -name "$${proto_name}.pb.go"); \
            for pb_file in $${pb_files}; do \
                if git diff --quiet --exit-code main...HEAD -- "$${pb_file}"; then \
                    echo "Missing committed changes in $${pb_file}"; \
					exit 1; \
                else \
                    modified_pb_files+="$${pb_file} "; \
                fi \
            done \
        done; \
		echo "Pass! Correctly modified pb files: "; \
		echo $${modified_pb_files}; \
    fi

proto-format:
	@echo "Formatting Protobuf files"
	@$(protoImage) find ./ -name "*.proto" -exec clang-format -i {} \;

proto-swagger-gen:
	@echo "Generating Protobuf Swagger"
	@$(protoImage) sh ./scripts/protocgen.sh

proto-lint:
	@$(protoImage) buf lint --error-format=json

proto-check-breaking:
	@$(protoImage) buf breaking --against $(HTTPS_GIT)#branch=main

proto-update-deps:
	@echo "Updating Protobuf dependencies"
	$(protoImage) buf mod update

.PHONY: proto-all proto-gen proto-format proto-lint proto-check proto-check-breaking proto-update-deps mocks

###############################################################################
###                              Documentation                              ###
###############################################################################

build-docs:
	@cd docs && ./build.sh

.PHONY: build-docs
