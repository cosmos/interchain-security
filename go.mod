module github.com/cosmos/interchain-security

go 1.16

require (
	github.com/cosmos/cosmos-sdk v0.45.2-0.20220421223926-3e3d83dec013
	github.com/cosmos/ibc-go v1.2.2
	github.com/cosmos/ibc-go/v3 v3.0.0-alpha1.0.20220210141024-fb2f0416254b
	github.com/gogo/protobuf v1.3.3
	github.com/golang/protobuf v1.5.2
	github.com/gorilla/mux v1.8.0
	github.com/gravity-devs/liquidity v1.4.5
	github.com/grpc-ecosystem/grpc-gateway v1.16.0
	github.com/grpc-ecosystem/grpc-gateway/v2 v2.10.0 // indirect
	github.com/kylelemons/godebug v1.1.0
	github.com/prometheus/common v0.30.0 // indirect
	github.com/rakyll/statik v0.1.7
	github.com/regen-network/cosmos-proto v0.3.1 // indirect
	github.com/rs/zerolog v1.25.0 // indirect
	github.com/spf13/cast v1.4.1
	github.com/spf13/cobra v1.3.0
	github.com/stretchr/testify v1.7.0
	github.com/tendermint/spm v0.1.9
	github.com/tendermint/tendermint v0.34.14
	github.com/tendermint/tm-db v0.6.4
	github.com/tidwall/gjson v1.6.7
	google.golang.org/genproto v0.0.0-20220317150908-0efb43f6373e
	google.golang.org/grpc v1.45.0
	google.golang.org/protobuf v1.27.1
	gopkg.in/yaml.v2 v2.4.0
)

replace (
	github.com/99designs/keyring => github.com/cosmos/keyring v1.1.7-0.20210622111912-ef00f8ac3d76
	// github.com/cosmos/ibc-go/v3 => github.com/informalsystems/ibc-go/v3 v3.0.0-alpha1.0.20220505161112-1f45da82fc75
	github.com/cosmos/ibc-go/v3 => /Users/danwt/Documents/work/ibc-go
	github.com/cosmos/cosmos-sdk => /Users/danwt/Documents/work/cosmos-sdk
	github.com/gogo/protobuf => github.com/regen-network/protobuf v1.3.3-alpha.regen.1
	google.golang.org/grpc => google.golang.org/grpc v1.33.2
)
