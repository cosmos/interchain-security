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
	github.com/rs/zerolog v1.25.0 // indirect
	github.com/spf13/cast v1.4.1
	github.com/spf13/cobra v1.3.0
	github.com/stretchr/testify v1.7.0
	github.com/tendermint/spm v0.1.9
	github.com/tendermint/tendermint v0.34.14
	github.com/tendermint/tm-db v0.6.4
	github.com/tidwall/gjson v1.6.7
	golang.org/x/crypto v0.0.0-20210921155107-089bfa567519 // indirect
	golang.org/x/net v0.0.0-20220225172249-27dd8689420f // indirect
	golang.org/x/sys v0.0.0-20220315194320-039c03cc5b86 // indirect
	google.golang.org/genproto v0.0.0-20220317150908-0efb43f6373e
	google.golang.org/grpc v1.45.0
	google.golang.org/protobuf v1.27.1
	gopkg.in/yaml.v2 v2.4.0
)

replace (
	github.com/99designs/keyring => github.com/cosmos/keyring v1.1.7-0.20210622111912-ef00f8ac3d76

	// TODO: update cosmos-sdk import once #11921 gets merged
	github.com/cosmos/cosmos-sdk => github.com/sainoe/cosmos-sdk v0.44.4-0.20220510144203-a0f64cfd6249
	github.com/cosmos/ibc-go/v3 => github.com/informalsystems/ibc-go/v3 v3.0.0-alpha1.0.20220405190259-988da4519455
	github.com/gogo/protobuf => github.com/regen-network/protobuf v1.3.3-alpha.regen.1
	google.golang.org/grpc => google.golang.org/grpc v1.33.2
)
