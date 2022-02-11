module github.com/cosmos/interchain-security

go 1.16

require (
	github.com/coinbase/rosetta-sdk-go v0.7.0 // indirect
	github.com/cosmos/cosmos-sdk v0.45.2-0.20220210215401-58c103ca4daf
	github.com/cosmos/iavl v0.17.3 // indirect
	github.com/cosmos/ibc-go v1.2.1-0.20211111105346-12a60b13a024
	github.com/gin-gonic/gin v1.7.0 // indirect
	github.com/gogo/protobuf v1.3.3
	github.com/golang/protobuf v1.5.2
	github.com/google/go-cmp v0.5.7 // indirect
	github.com/gorilla/mux v1.8.0
	github.com/grpc-ecosystem/grpc-gateway v1.16.0
	github.com/improbable-eng/grpc-web v0.14.1 // indirect
	github.com/jhump/protoreflect v1.9.0 // indirect
	github.com/lib/pq v1.10.2 // indirect
	github.com/onsi/ginkgo v1.16.4 // indirect
	github.com/onsi/gomega v1.13.0 // indirect
	github.com/opencontainers/image-spec v1.0.2 // indirect
	github.com/opencontainers/runc v1.0.3 // indirect
	github.com/prometheus/common v0.30.0 // indirect
	github.com/rs/zerolog v1.25.0 // indirect
	github.com/spf13/cast v1.4.1
	github.com/spf13/cobra v1.3.0
	github.com/spf13/viper v1.10.1 // indirect
	github.com/stretchr/testify v1.7.0
	// github.com/tendermint/spm v0.1.5
	github.com/tendermint/tendermint v0.34.14
	github.com/tendermint/tm-db v0.6.4
	google.golang.org/genproto v0.0.0-20220118154757-00ab72f36ad5
	google.golang.org/grpc v1.44.0
	google.golang.org/protobuf v1.27.1
)

replace (
	github.com/99designs/keyring => github.com/cosmos/keyring v1.1.7-0.20210622111912-ef00f8ac3d76
	// github.com/cosmos/cosmos-sdk => github.com/cosmos/cosmos-sdk v0.45.2-0.20220210215401-58c103ca4daf
	github.com/gogo/protobuf => github.com/regen-network/protobuf v1.3.3-alpha.regen.1
	google.golang.org/grpc => google.golang.org/grpc v1.33.2
)
