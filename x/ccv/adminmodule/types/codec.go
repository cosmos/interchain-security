package types

import (
	"github.com/cosmos/cosmos-sdk/codec"
	cdctypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/msgservice"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
)

func RegisterCodec(cdc *codec.LegacyAmino) {
	cdc.RegisterConcrete(&MsgDeleteAdmin{}, "adminmodule/DeleteAdmin", nil)

	cdc.RegisterConcrete(&MsgAddAdmin{}, "adminmodule/AddAdmin", nil)

	cdc.RegisterConcrete(&MsgSubmitProposal{}, "adminmodule/SubmitProposal", nil)
	// this line is used by starport scaffolding # 2
}

func RegisterInterfaces(registry cdctypes.InterfaceRegistry) {
	registry.RegisterImplementations((*sdk.Msg)(nil),
		&MsgDeleteAdmin{},
		&MsgAddAdmin{},
		&MsgSubmitProposal{},
	)

	registry.RegisterInterface(
		"cosmos.gov.v1beta1.Content",
		(*govtypes.Content)(nil),
		&govtypes.TextProposal{},
	)

	msgservice.RegisterMsgServiceDesc(registry, &_Msg_serviceDesc)
	// this line is used by starport scaffolding # 3
}

var (
	ModuleCdc = codec.NewProtoCodec(cdctypes.NewInterfaceRegistry())
)
