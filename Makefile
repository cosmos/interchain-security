#!/usr/bin/make -f

install: go.sum
		export GOFLAGS='-buildmode=pie'
		export CGO_CPPFLAGS="-D_FORTIFY_SOURCE=2"
		export CGO_LDFLAGS="-Wl,-z,relro,-z,now -fstack-protector"
		go install $(BUILD_FLAGS) ./cmd/interchain-security-pd
		go install $(BUILD_FLAGS) ./cmd/interchain-security-cd
		go install $(BUILD_FLAGS) ./cmd/interchain-security-cdd

# run all tests: unit, integration, diff, and E2E
test: 
	go test ./... && go run ./tests/e2e/... 

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
	go run ./tests/e2e/... --happy-path-only

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
	go run ./tests/e2e/... --happy-path-only --use-gaia

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
	go run ./tests/e2e/... --happy-path-only --use-gaia --gaia-tag $(GAIA_TAG)

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

golangci_version=latest

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

BUILD_TARGETS := build

build: BUILD_ARGS=-o $(BUILDDIR)/

$(BUILD_TARGETS): go.sum $(BUILDDIR)/
	go $@ -mod=readonly $(BUILD_FLAGS) $(BUILD_ARGS) ./...

$(BUILDDIR)/:
	mkdir -p $(BUILDDIR)/

###############################################################################
###                                Protobuf                                 ###
###############################################################################

containerProtoVer=0.12.1
containerProtoImage=ghcr.io/cosmos/proto-builder:$(containerProtoVer)
containerProtoGen=cosmos-sdk-proto-gen-$(containerProtoVer)
containerProtoGenSwagger=cosmos-sdk-proto-gen-swagger-$(containerProtoVer)
containerProtoFmt=cosmos-sdk-proto-fmt-$(containerProtoVer)

proto-all: proto-format proto-lint proto-gen

proto-gen:
	@echo "Generating Protobuf files"
	@if docker ps -a --format '{{.Names}}' | grep -Eq "^${containerProtoGen}$$"; then docker start -a $(containerProtoGen); else docker run --name $(containerProtoGen) -v $(CURDIR):/workspace --workdir /workspace $(containerProtoImage) \
		sh ./scripts/protocgen.sh; fi

proto-format:
	@echo "Formatting Protobuf files"
	@if docker ps -a --format '{{.Names}}' | grep -Eq "^${containerProtoFmt}$$"; then docker start -a $(containerProtoFmt); else docker run --name $(containerProtoFmt) -v $(CURDIR):/workspace --workdir /workspace tendermintdev/docker-build-proto \
		find ./ -not -path "./third_party/*" -name "*.proto" -exec clang-format -i {} \; ; fi

proto-swagger-gen:
	@echo "Generating Protobuf Swagger"
	@if docker ps -a --format '{{.Names}}' | grep -Eq "^${containerProtoGenSwagger}$$"; then docker start -a $(containerProtoGenSwagger); else docker run --name $(containerProtoGenSwagger) -v $(CURDIR):/workspace --workdir /workspace $(containerProtoImage) \
		sh ./scripts/protoc-swagger-gen.sh; fi

proto-lint:
	@$(DOCKER_BUF) lint --error-format=json

proto-check-breaking:
	@$(DOCKER_BUF) breaking --against $(HTTPS_GIT)#branch=main

TM_URL              = https://raw.githubusercontent.com/cometbft/cometbft/v0.37.0/proto/tendermint
GOGO_PROTO_URL      = https://raw.githubusercontent.com/regen-network/protobuf/cosmos
CONFIO_URL          = https://raw.githubusercontent.com/confio/ics23/v0.9.0
COSMOS_PROTO_URL    = https://raw.githubusercontent.com/regen-network/cosmos-proto/master
SDK_PROTO_URL		= https://raw.githubusercontent.com/notional-labs/cosmos-sdk/sdkv47-ics/proto/cosmos

TM_CRYPTO_TYPES     = third_party/proto/tendermint/crypto
TM_ABCI_TYPES       = third_party/proto/tendermint/abci
TM_TYPES            = third_party/proto/tendermint/types
TM_VERSION          = third_party/proto/tendermint/version
TM_LIBS             = third_party/proto/tendermint/libs/bits
TM_P2P              = third_party/proto/tendermint/p2p

SDK_QUERY 			= third_party/proto/cosmos/base/query/v1beta1
SDK_BASE 			= third_party/proto/cosmos/base/v1beta1
SDK_UPGRADE			= third_party/proto/cosmos/upgrade/v1beta1
SDK_STAKING			= third_party/proto/cosmos/staking/v1beta1
SDK_EVIDENCE		= third_party/proto/cosmos/evidence/v1beta1

GOGO_PROTO_TYPES    = third_party/proto/gogoproto
CONFIO_TYPES        = third_party/proto/confio
COSMOS_PROTO_TYPES  = third_party/proto/cosmos_proto

proto-update-deps:
	@mkdir -p $(COSMOS_PROTO_TYPES)
	@curl -sSL $(COSMOS_PROTO_URL)/cosmos.proto > $(COSMOS_PROTO_TYPES)/cosmos.proto

	@mkdir -p $(SDK_QUERY)
	@curl -sSL $(SDK_PROTO_URL)/base/query/v1beta1/pagination.proto > $(SDK_QUERY)/pagination.proto

	@mkdir -p $(SDK_BASE)
	@curl -sSL $(SDK_PROTO_URL)/base/v1beta1/coin.proto > $(SDK_BASE)/coin.proto

	@mkdir -p $(SDK_UPGRADE)
	@curl -sSL $(SDK_PROTO_URL)/upgrade/v1beta1/upgrade.proto > $(SDK_UPGRADE)/upgrade.proto

	@mkdir -p $(SDK_STAKING)
	@curl -sSL $(SDK_PROTO_URL)/staking/v1beta1/staking.proto > $(SDK_STAKING)/staking.proto

	@mkdir -p $(SDK_EVIDENCE)
	@curl -sSL $(SDK_PROTO_URL)/evidence/v1beta1/evidence.proto > $(SDK_EVIDENCE)/evidence.proto

## Importing of tendermint protobuf definitions currently requires the
## use of `sed` in order to build properly with cosmos-sdk's proto file layout
## (which is the standard Buf.build FILE_LAYOUT)
## Issue link: https://github.com/cometbft/cometbft/issues/5021
	@mkdir -p $(TM_TYPES)
	@curl -sSL $(TM_URL)/types/types.proto > $(TM_TYPES)/types.proto
	@curl -sSL $(TM_URL)/types/params.proto > $(TM_TYPES)/params.proto
	@curl -sSL $(TM_URL)/types/validator.proto > $(TM_TYPES)/validator.proto

	@mkdir -p $(TM_ABCI_TYPES)
	@curl -sSL $(TM_URL)/abci/types.proto > $(TM_ABCI_TYPES)/types.proto

	@mkdir -p $(TM_VERSION)
	@curl -sSL $(TM_URL)/version/types.proto > $(TM_VERSION)/types.proto

	@mkdir -p $(TM_LIBS)
	@curl -sSL $(TM_URL)/libs/bits/types.proto > $(TM_LIBS)/types.proto

	@mkdir -p $(TM_CRYPTO_TYPES)
	@curl -sSL $(TM_URL)/crypto/proof.proto > $(TM_CRYPTO_TYPES)/proof.proto
	@curl -sSL $(TM_URL)/crypto/keys.proto > $(TM_CRYPTO_TYPES)/keys.proto

	@mkdir -p $(CONFIO_TYPES)
	@curl -sSL $(CONFIO_URL)/proofs.proto > $(CONFIO_TYPES)/proofs.proto

## insert go package option into proofs.proto file
## Issue link: https://github.com/confio/ics23/issues/32
	@perl -i -l -p -e 'print "option go_package = \"github.com/confio/ics23/go\";" if $$. == 4' $(CONFIO_TYPES)/proofs.proto

.PHONY: proto-all proto-gen proto-gen-any proto-swagger-gen proto-format proto-lint proto-check-breaking proto-update-deps mocks

###############################################################################
###                              Documentation                              ###
###############################################################################

build-docs:
	@cd docs && ./build.sh

.PHONY: build-docs
