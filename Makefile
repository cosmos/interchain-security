#!/usr/bin/make -f

BRANCH := $(shell git rev-parse --abbrev-ref HEAD)
COMMIT := $(shell git log -1 --format='%H')
# Fetch tags and get the latest ICS version by filtering tags by vX.Y.Z and vX.Y.Z-lsm
# using lazy set to only execute commands when variable is used
# Note: v.5.0.0 is currently excluded from the list as it's a pre-release and will be added back once it's out of pre-release status
LATEST_RELEASE ?= $(shell git fetch; git tag -l --sort -v:refname 'v*.?' 'v*.?'-lsm 'v*.??' 'v*.??'-lsm --no-contains v5.0.0 | head -n 1)

# don't override user values
ifeq (,$(VERSION))
  VERSION := $(shell git describe --exact-match 2>/dev/null)
  # if VERSION is empty, then populate it with branch's name and raw commit hash
  ifeq (,$(VERSION))
    VERSION := $(BRANCH)-$(COMMIT)
  endif
endif

sharedFlags = -X github.com/cosmos/cosmos-sdk/version.Version=$(VERSION) \
		  -X github.com/cosmos/cosmos-sdk/version.Commit=$(COMMIT)

providerFlags := $(sharedFlags) -X github.com/cosmos/cosmos-sdk/version.AppName=interchain-security-pd -X github.com/cosmos/cosmos-sdk/version.Name=interchain-security-pd
consumerFlags := $(sharedFlags) -X github.com/cosmos/cosmos-sdk/version.AppName=interchain-security-cd -X github.com/cosmos/cosmos-sdk/version.Name=interchain-security-cd
democracyFlags := $(sharedFlags) -X github.com/cosmos/cosmos-sdk/version.AppName=interchain-security-cdd -X github.com/cosmos/cosmos-sdk/version.Name=interchain-security-cdd
standaloneFlags := $(sharedFlags) -X github.com/cosmos/cosmos-sdk/version.AppName=interchain-security-sd -X github.com/cosmos/cosmos-sdk/version.Name=interchain-security-sd

install: go.sum
		export GOFLAGS='-buildmode=pie'
		export CGO_CPPFLAGS="-D_FORTIFY_SOURCE=2"
		export CGO_LDFLAGS="-Wl,-z,relro,-z,now -fstack-protector"
		go install -ldflags "$(providerFlags)" ./cmd/interchain-security-pd
		go install -ldflags "$(consumerFlags)" ./cmd/interchain-security-cd
		go install -ldflags "$(democracyFlags)" ./cmd/interchain-security-cdd
		go install -ldflags "$(standaloneFlags)" ./cmd/interchain-security-sd

# run all tests: unit, integration, and E2E
test: test-unit test-integration test-e2e

# shortcut for local development
test-dev: test-unit test-integration test-mbt

# run unit tests
test-unit:
	go test ./x/... ./app/...

test-unit-cov:
	go test ./x/... ./app/... -coverpkg=./... -coverprofile=profile.out -covermode=atomic

# run unit and integration tests
test-integration:
	go test ./tests/integration/... -timeout 30m

test-integration-cov:
	go test ./tests/integration/... -timeout 30m -coverpkg=./... -coverprofile=integration-profile.out -covermode=atomic

# run mbt tests
test-mbt:
	cd tests/mbt/driver;\
	sh generate_traces.sh;\
	cd ../../..;\
	go test ./tests/mbt/... -timeout 30m

test-mbt-cov:
	cd tests/mbt/driver;\
	sh generate_traces.sh;\
	cd ../../..;\
	go test ./tests/mbt/... -timeout 30m -coverpkg=./... -coverprofile=mbt-profile.out -covermode=atomic

# runs mbt tests, but generates more traces
test-mbt-more-traces:
	cd tests/mbt/driver;\
	sh generate_more_traces.sh;\
	cd ../../..;\
	go test ./tests/mbt/... -timeout 30m

# run E2E tests
test-e2e:
	go run ./tests/e2e/...

# run only happy path E2E tests
test-e2e-short:
	go run ./tests/e2e/... --tc happy-path

# run only happy path E2E tests with cometmock
# this set of traces does not test equivocation but it does check downtime
test-e2e-short-cometmock:
	go run ./tests/e2e/... --tc happy-path-short --use-cometmock --use-gorelayer

# run minimal set of traces with cometmock and gaia
test-e2e-short-cometmock-gaia:
	go run ./tests/e2e/... --tc happy-path-short --use-cometmock --use-gorelayer --use-gaia

# run full E2E tests in sequence (including multiconsumer)
test-e2e-multi-consumer:
	go run ./tests/e2e/... --include-multi-consumer

# run full E2E tests in parallel (including multiconsumer)
test-e2e-parallel:
	go run ./tests/e2e/... --include-multi-consumer --parallel

# run E2E compatibility tests against latest release
test-e2e-compatibility-tests-latest:
	go run ./tests/e2e/... --tc compatibility -pv $(LATEST_RELEASE)

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

# test reading a trace from a file
test-trace:
	go run ./tests/e2e/... --test-file tests/e2e/tracehandler_testdata/happyPath.json::default

# tests and verifies the Quint models.
# Note: this is *not* using the Quint models to test the system,
# this tests/verifies the Quint models *themselves*.
verify-models:
	cd tests/mbt/model;\
	../run_invariants.sh


###############################################################################
###                         Simulation tests                                ###

# Run a full simulation test
sim-full:
	cd app/provider;\
	go test -mod=readonly . -run=^TestFullAppSimulation$  -Enabled=true -NumBlocks=500 -BlockSize=200 -Commit=true -timeout 24h -v

# Run full simulation without any inactive validators
sim-full-no-inactive-vals:
	cd app/provider;\
	go test -mod=readonly . -run=^TestFullAppSimulation$  -Enabled=true -NumBlocks=500 -BlockSize=200 -Commit=true -timeout 24h -Params=no_inactive_vals_params.json -v


###############################################################################
###                                Linting                                  ###
###############################################################################
golangci_lint_cmd=golangci-lint
golangci_version=v1.54.1

lint:
	@echo "--> Running linter"
	@go install github.com/golangci/golangci-lint/cmd/golangci-lint@$(golangci_version)
	@$(golangci_lint_cmd) run  ./... --config .golangci.yml

format:
	@go install mvdan.cc/gofumpt@latest
	@go install github.com/golangci/golangci-lint/cmd/golangci-lint@$(golangci_version)
	find . -name '*.go' -type f -not -path "./vendor*" -not -path "*.git*" -not -path "./client/docs/statik/statik.go" -not -path "./tests/mocks/*" -not -name "*.pb.go" -not -name "*.pb.gw.go" -not -name "*.pulsar.go" -not -path "./crypto/keys/secp256k1/*" | xargs gofumpt -w -l
	$(golangci_lint_cmd) run --fix --config .golangci.yml

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

containerProtoVer=0.14.0
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

build-docs-deploy:
	@cd docs && ./sync_versions.sh && ./build_deploy.sh

build-docs-local:
	@cd docs && ./build_local.sh

###############################################################################
### 							Test Traces									###
###############################################################################

e2e-traces:
	cd tests/e2e; go test -timeout 30s -run ^TestWriteExamples -v
