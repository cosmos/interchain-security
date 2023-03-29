#!/usr/bin/make -f

install: go.sum
		export GOFLAGS='-buildmode=pie'
		export CGO_CPPFLAGS="-D_FORTIFY_SOURCE=2"
		export CGO_LDFLAGS="-Wl,-z,relro,-z,now -fstack-protector"
		go install $(BUILD_FLAGS) ./cmd/interchain-security-pd
		go install $(BUILD_FLAGS) ./cmd/interchain-security-cd
		go install $(BUILD_FLAGS) ./cmd/interchain-security-cdd

# run all tests: unit, e2e, diff, and integration
test: 
	go test ./... && go run ./tests/integration/... 

# run e2e and unit tests
test-short:
	go test ./tests/e2e/... ./x/... ./app/...

# run difference tests
test-diff:
	go test ./tests/difference/...

# run only happy path integration tests
test-integration-short:
	go run ./tests/integration/... --happy-path-only

# run full integration tests in sequence (including multiconsumer)
test-integration:
	go run ./tests/integration/... --include-multi-consumer

# run full integration tests in parallel (including multiconsumer)
test-integration-parallel:
	go run ./tests/integration/... --include-multi-consumer --parallel

# run full integration tests in sequence (including multiconsumer) using latest tagged gaia
test-gaia-integration:
	go run ./tests/integration/... --include-multi-consumer --use-gaia

# run only happy path integration tests using latest tagged gaia
test-gaia-integration-short:
	go run ./tests/integration/... --happy-path-only --use-gaia

# run full integration tests in parallel (including multiconsumer) using latest tagged gaia
test-gaia-integration-parallel:
	go run ./tests/integration/... --include-multi-consumer --parallel --use-gaia

# run full integration tests in sequence (including multiconsumer) using specific tagged version of gaia
# usage: GAIA_TAG=v9.0.0 make test-gaia-integration-tagged
test-gaia-integration-tagged:
	go run ./tests/integration/... --include-multi-consumer --use-gaia --gaia-tag $(GAIA_TAG)

# run only happy path integration tests using latest tagged gaia
# usage: GAIA_TAG=v9.0.0 make test-gaia-integration-short-tagged
test-gaia-integration-short-tagged:
	go run ./tests/integration/... --happy-path-only --use-gaia --gaia-tag $(GAIA_TAG)

# run full integration tests in parallel (including multiconsumer) using specific tagged version of gaia
# usage: GAIA_TAG=v9.0.0 make test-gaia-integration-parallel-tagged
test-gaia-integration-parallel-tagged:
	go run ./tests/integration/... --include-multi-consumer --parallel --use-gaia --gaia-tag $(GAIA_TAG)

# run all tests with caching disabled
test-no-cache:
	go test ./... -count=1 && go run ./tests/integration/...

mockgen_cmd=go run github.com/golang/mock/mockgen
mocks:
	$(mockgen_cmd) -package=keeper -destination=testutil/keeper/mocks.go -source=x/ccv/types/expected_keepers.go

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
protoVer=0.11.6
protoImageName=ghcr.io/cosmos/proto-builder:$(protoVer)
protoImage=$(DOCKER) run --rm -v $(CURDIR):/workspace --workdir /workspace $(protoImageName)

proto-all: proto-format proto-lint proto-gen

proto-gen:
	@echo "Generating Protobuf files"
	@$(protoImage) sh ./scripts/protocgen.sh

proto-swagger-gen:
	@echo "Generating Protobuf Swagger"
	@$(protoImage) sh ./scripts/protoc-swagger-gen.sh
	$(MAKE) update-swagger-docs

proto-format:
	@$(protoImage) find ./ -name "*.proto" -exec clang-format -i {} \;

proto-lint:
	@$(protoImage) buf lint --error-format=json

proto-check-breaking:
	@$(protoImage) buf breaking --against $(HTTPS_GIT)#branch=main

CMT_URL              = https://raw.githubusercontent.com/cometbft/cometbft/v0.37.0/proto/tendermint

TM_CRYPTO_TYPES     = proto/tendermint/crypto
TM_ABCI_TYPES       = proto/tendermint/abci
TM_TYPES            = proto/tendermint/types
TM_VERSION          = proto/tendermint/version
TM_LIBS             = proto/tendermint/libs/bits
TM_P2P              = proto/tendermint/p2p

proto-update-deps:
	@echo "Updating Protobuf dependencies"

	@mkdir -p $(TM_ABCI_TYPES)
	@curl -sSL $(TM_URL)/abci/types.proto > $(TM_ABCI_TYPES)/types.proto

	@mkdir -p $(TM_VERSION)
	@curl -sSL $(TM_URL)/version/types.proto > $(TM_VERSION)/types.proto

	@mkdir -p $(TM_TYPES)
	@curl -sSL $(TM_URL)/types/types.proto > $(TM_TYPES)/types.proto
	@curl -sSL $(TM_URL)/types/evidence.proto > $(TM_TYPES)/evidence.proto
	@curl -sSL $(TM_URL)/types/params.proto > $(TM_TYPES)/params.proto
	@curl -sSL $(TM_URL)/types/validator.proto > $(TM_TYPES)/validator.proto
	@curl -sSL $(TM_URL)/types/block.proto > $(TM_TYPES)/block.proto

	@mkdir -p $(TM_CRYPTO_TYPES)
	@curl -sSL $(TM_URL)/crypto/proof.proto > $(TM_CRYPTO_TYPES)/proof.proto
	@curl -sSL $(TM_URL)/crypto/keys.proto > $(TM_CRYPTO_TYPES)/keys.proto

	@mkdir -p $(TM_LIBS)
	@curl -sSL $(TM_URL)/libs/bits/types.proto > $(TM_LIBS)/types.proto

	@mkdir -p $(TM_P2P)
	@curl -sSL $(TM_URL)/p2p/types.proto > $(TM_P2P)/types.proto

	$(DOCKER) run --rm -v $(CURDIR)/proto:/workspace --workdir /workspace $(protoImageName) buf mod update

.PHONY: proto-all proto-gen proto-swagger-gen proto-format proto-lint proto-check-breaking proto-update-deps

###############################################################################
###                              Documentation                              ###
###############################################################################

build-docs:
	@cd docs && ./build.sh

.PHONY: build-docs
