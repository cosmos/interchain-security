package types_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	testutil "github.com/cosmos/interchain-security/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"

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
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")}},
				nil,
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
					{ChainId: "chainid-1", ChannelId: "channelid1", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")},
					{ChainId: "chainid-2", ChannelId: "channelid2", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-2")},
					{ChainId: "chainid-3", ChannelId: "channelid3", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-3")},
					{ChainId: "chainid-4", ChannelId: "channelid4", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-4")},
				},
				nil,
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
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					3, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
			),
			true,
		},
		{
			"invalid params",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					0, clienttypes.Height{}, nil, []string{"ibc", "upgradedIBCState"}, true, false),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxPendingSlashPackets),
			),
			false,
		},
		{
			"invalid params, zero trusting period fraction",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					0, // 0 trusting period fraction here
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxPendingSlashPackets),
			),
			false,
		},
		{
			"invalid params, zero ccv timeout",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					types.DefaultTrustingPeriodFraction,
					0, // 0 ccv timeout here
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxPendingSlashPackets),
			),
			false,
		},
		{
			"invalid params, zero init timeout",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					0, // 0 init timeout here
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxPendingSlashPackets),
			),
			false,
		},
		{
			"invalid params, zero vsc timeout",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					0, // 0 vsc timeout here
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxPendingSlashPackets),
			),
			false,
		},
		{
			"invalid params, zero slash meter replenish period",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					0, // 0 slash meter replenish period here
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxPendingSlashPackets),
			),
			false,
		},
		{
			"invalid params, invalid slash meter replenish fraction",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					"1.15",
					types.DefaultMaxPendingSlashPackets),
			),
			false,
		},
		{
			"invalid params, invalid max pending slash packets",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					"1.15",
					-1),
			),
			false,
		},
		{
			"invalid chain id",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
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
				[]types.ConsumerState{{ChainId: "chainid", ChannelId: "ivnalidChannel{}", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			false,
		},
		{
			"empty client id",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid", ChannelId: "channel-0", ClientId: ""}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			false,
		},
		{
			"empty consumer genesis",
			types.NewGenesisState(
				0,
				nil,
				[]types.ConsumerState{{ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis: consumertypes.GenesisState{}}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
			),
			false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			err := tc.genState.Validate()

			if tc.expPass {
				require.NoError(t, err, "test case: %s must pass", tc.name)
			} else {
				require.Error(t, err, "test case: %s must fail", tc.name)
			}
		})
	}
}

func getInitialConsumerGenesis(t *testing.T, chainID string) consumertypes.GenesisState {
	// generate validator public key
	pubKey, err := testutil.GenPubKey()
	require.NoError(t, err)

	// create validator set with single validator
	validator := tmtypes.NewValidator(pubKey, 1)
	valSet := tmtypes.NewValidatorSet([]*tmtypes.Validator{validator})
	valHash := valSet.Hash()
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(valSet)

	cs := ibctmtypes.NewClientState(
		chainID,
		ibctmtypes.DefaultTrustLevel,
		time.Duration(1),
		time.Duration(2),
		time.Duration(1),
		clienttypes.Height{RevisionNumber: clienttypes.ParseChainID(chainID), RevisionHeight: 1},
		commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"},
		true,
		true,
	)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash[:])

	params := consumertypes.DefaultParams()
	params.Enabled = true
	return *consumertypes.NewInitialGenesisState(cs, consensusState, valUpdates, params)
}
