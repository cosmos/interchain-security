package types

import (
	"github.com/cosmos/ibc-go/v8/modules/core/exported"
	tendermint "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/msgservice"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
)

func RegisterLegacyAminoCodec(cdc *codec.LegacyAmino) {
}

// RegisterInterfaces registers the provider proposal structs to the interface registry
func RegisterInterfaces(registry codectypes.InterfaceRegistry) {
	registry.RegisterImplementations(
		(*govv1beta1.Content)(nil),
		&ConsumerAdditionProposal{},
	)
	registry.RegisterImplementations(
		(*govv1beta1.Content)(nil),
		&ConsumerRemovalProposal{},
	)
	registry.RegisterImplementations(
		(*govv1beta1.Content)(nil),
		&ConsumerModificationProposal{},
	)
	registry.RegisterImplementations(
		(*sdk.Msg)(nil),
		&MsgAssignConsumerKey{},
		&MsgConsumerAddition{},
		&MsgConsumerRemoval{},
		&MsgChangeRewardDenoms{},
		&MsgUpdateParams{},
	)
	// keep so existing proposals can be correctly deserialized
	registry.RegisterImplementations(
		(*govv1beta1.Content)(nil),
		&EquivocationProposal{},
	)
	registry.RegisterImplementations(
		(*govv1beta1.Content)(nil),
		&ChangeRewardDenomsProposal{},
	)
	registry.RegisterImplementations(
		(*sdk.Msg)(nil),
		&MsgSubmitConsumerMisbehaviour{},
	)
	registry.RegisterImplementations(
		(*sdk.Msg)(nil),
		&MsgSubmitConsumerDoubleVoting{},
	)
	registry.RegisterImplementations(
		(*sdk.Msg)(nil),
		&MsgOptIn{},
	)
	registry.RegisterImplementations(
		(*sdk.Msg)(nil),
		&MsgOptOut{},
	)
	registry.RegisterImplementations(
		(*exported.ClientMessage)(nil),
		&tendermint.Misbehaviour{},
	)
	registry.RegisterImplementations(
		(*sdk.Msg)(nil),
		&MsgSetConsumerCommissionRate{},
	)
	msgservice.RegisterMsgServiceDesc(registry, &_Msg_serviceDesc)
}

var (
	amino = codec.NewLegacyAmino()

	// ModuleCdc references the global x/ibc-transfer module codec. Note, the codec
	// should ONLY be used in certain instances of tests and for JSON encoding.
	//
	// The actual codec used for serialization should be provided to x/ibc transfer and
	// defined at the application level.
	ModuleCdc = codec.NewProtoCodec(codectypes.NewInterfaceRegistry())

	// AminoCdc is a amino codec created to support amino json compatible msgs.
	AminoCdc = codec.NewAminoCodec(amino)
)

func init() {
	RegisterLegacyAminoCodec(amino)
	amino.Seal()
}
