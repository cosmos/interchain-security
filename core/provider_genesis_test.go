package core_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v4/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	ccv "github.com/cosmos/interchain-security/core"
	"github.com/cosmos/interchain-security/testutil/crypto"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// Tests validation of consumer states and params within a provider genesis state
func TestValidateProviderGenesisState(t *testing.T) {
	testCases := []struct {
		name     string
		genState *ccv.ProviderGenesisState
		expPass  bool
	}{
		{
			"valid initializing provider genesis with nil updates",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			true,
		},
		{
			"valid multiple provider genesis with multiple consumer chains",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{
					{ChainId: "chainid-1", ChannelId: "channelid1", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")},
					{ChainId: "chainid-2", ChannelId: "channelid2", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-2")},
					{ChainId: "chainid-3", ChannelId: "channelid3", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-3")},
					{ChainId: "chainid-4", ChannelId: "channelid4", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-4")},
				},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			true,
		},
		{
			"valid provider genesis with custom params",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid-1")}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			true,
		},
		{
			"invalid zero valset update ID",
			ccv.NewProviderGenesisState(
				0,
				nil,
				nil,
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid valset ID to block height mapping",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				[]ccv.ValsetUpdateIdToHeight{{ValsetUpdateId: 0}},
				nil,
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid unbonding op",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				nil,
				[]ccv.UnbondingOp{{UnbondingConsumerChains: nil}},
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction, time.Hour, time.Hour, 30*time.Minute, time.Hour, "0.1", 400),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					0, clienttypes.Height{}, nil, []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					ccv.DefaultInitTimeoutPeriod,
					ccv.DefaultVscTimeoutPeriod,
					ccv.DefaultSlashMeterReplenishPeriod,
					ccv.DefaultSlashMeterReplenishFraction,
					ccv.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero trusting period fraction",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					"0.0", // 0 trusting period fraction here
					ccv.DefaultCCVTimeoutPeriod,
					ccv.DefaultInitTimeoutPeriod,
					ccv.DefaultVscTimeoutPeriod,
					ccv.DefaultSlashMeterReplenishPeriod,
					ccv.DefaultSlashMeterReplenishFraction,
					ccv.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero ccv timeout",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction,
					0, // 0 ccv timeout here
					ccv.DefaultInitTimeoutPeriod,
					ccv.DefaultVscTimeoutPeriod,
					ccv.DefaultSlashMeterReplenishPeriod,
					ccv.DefaultSlashMeterReplenishFraction,
					ccv.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero init timeout",
			ccv.NewProviderGenesisState(
				0,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					0, // 0 init timeout here
					ccv.DefaultVscTimeoutPeriod,
					ccv.DefaultSlashMeterReplenishPeriod,
					ccv.DefaultSlashMeterReplenishFraction,
					ccv.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero vsc timeout",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					ccv.DefaultInitTimeoutPeriod,
					0, // 0 vsc timeout here
					ccv.DefaultSlashMeterReplenishPeriod,
					ccv.DefaultSlashMeterReplenishFraction,
					ccv.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, zero slash meter replenish period",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					ccv.DefaultInitTimeoutPeriod,
					ccv.DefaultVscTimeoutPeriod,
					0, // 0 slash meter replenish period here
					ccv.DefaultSlashMeterReplenishFraction,
					ccv.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, invalid slash meter replenish fraction",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					ccv.DefaultInitTimeoutPeriod,
					ccv.DefaultVscTimeoutPeriod,
					ccv.DefaultSlashMeterReplenishPeriod,
					"1.15",
					ccv.DefaultMaxThrottledPackets),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid params, invalid max pending slash packets",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid-1", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.NewProviderParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
					time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
					ccv.DefaultTrustingPeriodFraction,
					ccv.DefaultCCVTimeoutPeriod,
					ccv.DefaultInitTimeoutPeriod,
					ccv.DefaultVscTimeoutPeriod,
					ccv.DefaultSlashMeterReplenishPeriod,
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
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "", ChannelId: "channelid", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state channel id",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid", ChannelId: "ivnalidChannel{}", ClientId: "client-id"}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"empty consumer state client id",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid", ChannelId: "channel-0", ClientId: ""}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state client id 2",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{ChainId: "chainid", ChannelId: "channel-0", ClientId: "abc", ConsumerGenesis: getInitialConsumerGenesis(t, "chainid")}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"empty consumer state consumer genesis",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis: ccv.ConsumerGenesisState{},
				}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state slash acks",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis:  getInitialConsumerGenesis(t, "chainid"),
					SlashDowntimeAck: []string{"cosmosvaloper1qlmk6r5w5taqrky4ycur4zq6jqxmuzr688htpp"},
				}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state pending VSC packets",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					ConsumerGenesis:      getInitialConsumerGenesis(t, "chainid"),
					PendingValsetChanges: []ccv.ValidatorSetChangePacketData{{}},
				}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state pending VSC packets 2: invalid slash acks address",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{
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
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOpsIndex - zero vscID",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{
					{
						ChainId:           "chainid",
						ChannelId:         "channel-0",
						ClientId:          "client-id",
						ConsumerGenesis:   getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []ccv.VscUnbondingOps{{}},
					},
				},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOpsIndex - no IDs",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{
					{
						ChainId:           "chainid",
						ChannelId:         "channel-0",
						ClientId:          "client-id",
						ConsumerGenesis:   getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []ccv.VscUnbondingOps{{VscId: 1}},
					},
				},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOp - no matching UnbondingOpsIndex",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{
					{
						ChainId:         "chainid",
						ChannelId:       "channel-0",
						ClientId:        "client-id",
						ConsumerGenesis: getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []ccv.VscUnbondingOps{
							{
								VscId: 1,
							},
						},
					},
				},
				[]ccv.UnbondingOp{
					{
						Id:                      13,
						UnbondingConsumerChains: []string{"chainid"},
					},
				},
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state UnbondingOp - no matching UnbondingOpsIndex 2",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{
					{
						ChainId:         "chainid",
						ChannelId:       "channel-0",
						ClientId:        "client-id",
						ConsumerGenesis: getInitialConsumerGenesis(t, "chainid"),
						UnbondingOpsIndex: []ccv.VscUnbondingOps{
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
						UnbondingOpsIndex: []ccv.VscUnbondingOps{
							{
								VscId: 1,
							},
						},
					},
				},
				[]ccv.UnbondingOp{
					{
						Id:                      13,
						UnbondingConsumerChains: []string{"chainid", "chainid-2"},
					},
				},
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
				nil,
				nil,
				nil,
			),
			false,
		},
		{
			"invalid consumer state unbonding operation operation 2",
			ccv.NewProviderGenesisState(
				ccv.DefaultValsetUpdateID,
				nil,
				[]ccv.ConsumerState{{
					ChainId: "chainid", ChannelId: "channel-0", ClientId: "client-id",
					UnbondingOpsIndex: []ccv.VscUnbondingOps{{VscId: 1}},
				}},
				nil,
				nil,
				nil,
				nil,
				ccv.DefaultProviderParams(),
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

func getInitialConsumerGenesis(t *testing.T, chainID string) ccv.ConsumerGenesisState {
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
		[]string{"upgrade", "upgradedIBCState"},
		true,
		true,
	)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash)

	params := ccv.DefaultConsumerParams()
	params.Enabled = true
	return *ccv.NewInitialConsumerGenesisState(cs, consensusState, valUpdates, params)
}
