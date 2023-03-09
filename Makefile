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

BUILD_TARGETS := build

build: BUILD_ARGS=-o $(BUILDDIR)/

$(BUILD_TARGETS): go.sum $(BUILDDIR)/
	go $@ -mod=readonly $(BUILD_FLAGS) $(BUILD_ARGS) ./...

$(BUILDDIR)/:
	mkdir -p $(BUILDDIR)/

###############################################################################
###                                Protobuf                                 ###
###############################################################################

containerProtoVer=0.9.0
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

TM_URL              = https://raw.githubusercontent.com/tendermint/tendermint/v0.34.5/proto/tendermint
GOGO_PROTO_URL      = https://raw.githubusercontent.com/regen-network/protobuf/cosmos
CONFIO_URL          = https://raw.githubusercontent.com/confio/ics23/v0.7.1
COSMOS_PROTO_URL    = https://raw.githubusercontent.com/regen-network/cosmos-proto/master
SDK_PROTO_URL 		= https://raw.githubusercontent.com/cosmos/cosmos-sdk/interchain-security-rebase/proto/cosmos

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
## Issue link: https://github.com/tendermint/tendermint/issues/5021
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

.PHONY: proto-all proto-gen proto-gen-any proto-swagger-gen proto-format proto-lint proto-check-breaking proto-update-deps

