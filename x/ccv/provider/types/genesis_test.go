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

// Tests validation of consumer states and params within a provider genesis state
func TestValidateGenesisState(t *testing.T) {
	testCases := []struct {
		name     string
		genState *types.GenesisState
		expPass  bool
	}{
		{
			"valid initializing provider genesis with nil updates",
			types.NewGenesisState(
				[]types.ConsumerState{{"chainid-1", "channelid"}},
				types.DefaultParams(),
			),
			true,
		},
		{
			"valid validating provider genesis with nil updates",
			types.NewGenesisState(
				[]types.ConsumerState{{"chainid-1", "channelid"}},
				types.DefaultParams(),
			),
			true,
		},
		{
			"valid multiple provider genesis with multiple consumer chains",
			types.NewGenesisState(
				[]types.ConsumerState{
					{"chainid-1", "channelid"},
					{"chainid-2", "channelid2"},
					{"chainid-3", "channelid3"},
					{"chainid-4", "channelid4"},
				},
				types.DefaultParams(),
			),
			true,
		},
		{
			"valid provider genesis with custom params",
			types.NewGenesisState(
				[]types.ConsumerState{{"chainid-1", "channelid"}},
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false)),
			),
			true,
		},
		{
			"invalid params",
			types.NewGenesisState(
				[]types.ConsumerState{{"chainid-1", "channelid"}},
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					0, clienttypes.Height{}, nil, []string{"ibc", "upgradedIBCState"}, true, false)),
			),
			false,
		},
		{
			"invalid chain id",
			types.NewGenesisState(
				[]types.ConsumerState{{" ", "channelid"}},
				types.DefaultParams(),
			),
			false,
		},
		{
			"invalid channel id",
			types.NewGenesisState(
				[]types.ConsumerState{{"chainid", "invalidchannel{}"}},
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
