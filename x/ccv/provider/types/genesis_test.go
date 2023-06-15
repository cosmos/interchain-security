package types_test

import (
	"testing"
	"time"

	abci "github.com/cometbft/cometbft/abci/types"
	tmtypes "github.com/cometbft/cometbft/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v7/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/stretchr/testify/require"

	"github.com/octopus-network/interchain-security/testutil/crypto"
	consumertypes "github.com/octopus-network/interchain-security/x/ccv/consumer/types"
	"github.com/octopus-network/interchain-security/x/ccv/provider/types"
	ccv "github.com/octopus-network/interchain-security/x/ccv/types"
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
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			true,
		},
		{
			"valid multiple provider genesis with multiple consumer chains",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
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
				nil,
				nil,
				nil,
			),
			true,
		},
		{
			"valid provider genesis with custom params",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			true,
		},
		{
			"invalid zero valset update ID",
			types.NewGenesisState(
				0,
				nil,
				nil,
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid valset ID to block height mapping",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				[]types.ValsetUpdateIdToHeight{{ValsetUpdateId: 0}},
				nil,
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid unbonding op",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				nil,
				[]types.UnbondingOp{{UnbondingConsumerChains: nil}},
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					0, clienttypes.Height{}, nil, []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero trusting period fraction",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					"0.0", // 0 trusting period fraction here
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero ccv timeout",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction,
					0, // 0 ccv timeout here
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
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
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					0, // 0 init timeout here
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero vsc timeout",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					0, // 0 vsc timeout here
					types.DefaultSlashMeterReplenishPeriod,
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero slash meter replenish period",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					0, // 0 slash meter replenish period here
					types.DefaultSlashMeterReplenishFraction,
					types.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, invalid slash meter replenish fraction",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					"1.15",
					types.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, invalid max pending slash packets",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
					types.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					types.DefaultInitTimeoutPeriod,
					types.DefaultVscTimeoutPeriod,
					types.DefaultSlashMeterReplenishPeriod,
					"1.15",
					-1),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state chain id",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state channel id",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid", ChannelId: "ivnalidChannel{}", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"empty consumer state client id",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid", ChannelId: "channel-0", ClientId: ""}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state client id 2",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{ChainId: "chainid", ChannelId: "channel-0", ClientId: "abc", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid")}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"empty consumer state consumer genesis",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis: consumertypes.GenesisState{},
				}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state slash acks",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis:  getInitialConsumerGenesis(t, "chainid"),
					SlashDowntimeAck: []string{"cosmosvaloper1qlmk6r5w5taqrky4ycur4zq6jqxmuzr688htpp"},
				}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state pending VSC packets",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis:      getInitialConsumerGenesis(t, "chainid"),
					PendingValsetChanges: []ccv.ValidatorSetChangePacketData{{}},
				}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state pending VSC packets 2: invalid slash acks address",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis: getInitialConsumerGenesis(t, "chainid"),
					PendingValsetChanges: []ccv.ValidatorSetChangePacketData{{
						SlashAcks:        []string{"cosmosvaloper1qlmk6r5w5taqrky4ycur4zq6jqxmuzr688htpp"},
						ValsetUpdateId:   1,
						ValidatorUpdates: []abci.ValidatorUpdate{{}},
					}},
				}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOpsIndex - zero vscID",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{
					{
						ChainId:           "chainid",
						ChannelId:         "channel-0",
						ClientId:          "client-id",
						ConsumerGenesis:   getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []types.VscUnbondingOps{{}},
					},
				},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOpsIndex - no IDs",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{
					{
						ChainId:           "chainid",
						ChannelId:         "channel-0",
						ClientId:          "client-id",
						ConsumerGenesis:   getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []types.VscUnbondingOps{{VscId: 1}},
					},
				},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOp - no matching UnbondingOpsIndex",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{
					{
						ChainId:         "chainid",
						ChannelId:       "channel-0",
						ClientId:        "client-id",
						ConsumerGenesis: getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []types.VscUnbondingOps{
							{
								VscId: 1,
							},
						},
					},
				},
				[]types.UnbondingOp{
					{
						Id:                      13,
						UnbondingConsumerChains: []string{"chainid"},
					},
				},
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOp - no matching UnbondingOpsIndex 2",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{
					{
						ChainId:         "chainid",
						ChannelId:       "channel-0",
						ClientId:        "client-id",
						ConsumerGenesis: getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []types.VscUnbondingOps{
							{
								VscId:          1,
								UnbondingOpIds: []uint64{13},
							},
						},
					},
					{
						ChainId:         "chainid-2",
						ChannelId:       "channel-0",
						ClientId:        "client-id",
						ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-2"),
						UnbondingOpsIndex: []types.VscUnbondingOps{
							{
								VscId: 1,
							},
						},
					},
				},
				[]types.UnbondingOp{
					{
						Id:                      13,
						UnbondingConsumerChains: []string{"chainid", "chainid-2"},
					},
				},
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state unbonding operation operation 2",
			types.NewGenesisState(
				types.DefaultValsetUpdateID,
				nil,
				[]types.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					UnbondingOpsIndex: []types.VscUnbondingOps{{VscId: 1}},
				}},
				nil,
				nil,
				nil,
				nil,
				types.DefaultParams(),
				nil,
				nil,
				nil,
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
	t.Helper()
	// generate validator public key
	cId := crypto.NewCryptoIdentityFromIntSeed(239668)
	pubKey := cId.TMCryptoPubKey()

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
		[]string{"upgrade", "upgradedIBCState"})
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash)

	params := consumertypes.DefaultParams()
	params.Enabled = true
	return *consumertypes.NewInitialGenesisState(cs, consensusState, valUpdates, params)
}
