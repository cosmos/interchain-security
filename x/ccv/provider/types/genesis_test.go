package types_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"

	"github.com/stretchr/testify/require"
)

func TestValidateGenesisState(t *testing.T) {
	testCases := []struct {
		name     string
		genState *types.GenesisState
		expPass  bool
	}{
		{
			"valid initializing provider genesis with nil updates",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid"}},
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			true,
		},
		{
			"valid validating provider genesis with nil updates",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid"}},
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			true,
		},
		{
			"valid multiple provider genesis with multiple consumer chains",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{
					{ChainId: "chainid-1", ChannelId: "channelid1"},
					{ChainId: "chainid-2", ChannelId: "channelid2"},
					{ChainId: "chainid-3", ChannelId: "channelid3"},
					{ChainId: "chainid-4", ChannelId: "channelid4"},
				},
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			true,
		},
		{
			"valid provider genesis with custom params",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid"}},
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false)),
			),
			true,
		},
		{
			"invalid params",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid"}},
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					0, clienttypes.Height{}, nil, []string{"ibc", "upgradedIBCState"}, true, false)),
			),
			false,
		},
		{
			"invalid chain id",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "", ChannelId: "channelid"}},
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			false,
		},
		{
			"invalid channel id",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid", ChannelId: "ivnalidChannel{}"}},
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			false,
		},
	}

	for _, tc := range testCases {
		err := tc.genState.Validate()

		if tc.expPass {
			require.NoError(t, err, "test case: %s must pass", tc.name)
		} else {
			require.Error(t, err, "test case: %s must fail", tc.name)
		}
	}
}
