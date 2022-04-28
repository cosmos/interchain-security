package types_test

import (
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/ibc-go/v3/testing/mock"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/require"
)

const (
	chainID                      = "gaia"
	trustingPeriod time.Duration = time.Hour * 24 * 7 * 2
	ubdPeriod      time.Duration = time.Hour * 24 * 7 * 3
	maxClockDrift  time.Duration = time.Second * 10
)

var (
	height      = clienttypes.NewHeight(0, 4)
	upgradePath = []string{"upgrade", "upgradedIBCState"}
)

func TestValidateInitialGenesisState(t *testing.T) {
	// generate validator private/public key
	privVal := mock.NewPV()
	pubKey, err := privVal.GetPubKey()
	require.NoError(t, err)

	// create validator set with single validator
	validator := tmtypes.NewValidator(pubKey, 1)
	valSet := tmtypes.NewValidatorSet([]*tmtypes.Validator{validator})
	valHash := valSet.Hash()
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(valSet)

	cs := ibctmtypes.NewClientState(chainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, height, commitmenttypes.GetSDKSpecs(), upgradePath, false, false)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash[:])

	params := types.DefaultParams()
	params.Enabled = true

	cases := []struct {
		name     string
		gs       *types.GenesisState
		expError bool
	}{
		{
			"valid new consumer genesis state",
			types.NewInitialGenesisState(cs, consensusState, valUpdates, params),
			false,
		},
		{
			"invalid new consumer genesis state: nil client state",
			types.NewInitialGenesisState(nil, consensusState, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid client state",
			types.NewInitialGenesisState(&ibctmtypes.ClientState{ChainId: "badClientState"},
				consensusState, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: nil consensus state",
			types.NewInitialGenesisState(cs, nil, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid consensus state",
			types.NewInitialGenesisState(cs, &ibctmtypes.ConsensusState{Timestamp: time.Now()},
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: client id not empty",
			&types.GenesisState{
				params,
				"ccvclient",
				"",
				true,
				cs,
				consensusState,
				nil,
				valUpdates,
			},
			true,
		},
		{
			"invalid new consumer genesis state: channel id not empty",
			&types.GenesisState{
				params,
				"",
				"ccvchannel",
				true,
				cs,
				consensusState,
				nil,
				valUpdates,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty unbonding sequences",
			&types.GenesisState{
				params,
				"",
				"",
				true,
				cs,
				consensusState,
				[]types.UnbondingSequence{{}},
				valUpdates,
			},
			true,
		},
		{
			"invalid new consumer genesis state: nil initial validator set",
			types.NewInitialGenesisState(cs, consensusState, nil, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			types.NewInitialGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("wrong_hash")),
				valUpdates, params),
			true,
		},
	}

	for _, c := range cases {
		err := c.gs.Validate()
		if c.expError {
			require.Error(t, err, "%s did not return expected error", c.name)
		} else {
			require.NoError(t, err, "%s returned unexpected error", c.name)
		}
	}
}

func TestValidateRestartGenesisState(t *testing.T) {
	// generate validator private/public key
	privVal := mock.NewPV()
	pubKey, err := privVal.GetPubKey()
	require.NoError(t, err)

	// create validator set with single validator
	validator := tmtypes.NewValidator(pubKey, 1)
	valSet := tmtypes.NewValidatorSet([]*tmtypes.Validator{validator})
	valHash := valSet.Hash()
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(valSet)

	cs := ibctmtypes.NewClientState(chainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, height, commitmenttypes.GetSDKSpecs(), upgradePath, false, false)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash[:])
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	pd1 := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: pk1,
				Power:  30,
			},
			{
				PubKey: pk2,
				Power:  20,
			},
		},
		1,
		nil,
	)
	pdBytes1, err := pd1.Marshal()
	require.NoError(t, err, "cannot marshal packet data")

	pd2 := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: pk1,
				Power:  40,
			},
			{
				PubKey: pk2,
				Power:  80,
			},
		},
		2,
		nil,
	)
	pdBytes2, err := pd2.Marshal()
	require.NoError(t, err, "cannot marshal packet data")

	params := types.DefaultParams()
	params.Enabled = true

	cases := []struct {
		name     string
		gs       *types.GenesisState
		expError bool
	}{
		{
			"valid restart consumer genesis state: empty unbonding sequences",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, valUpdates, params),
			false,
		},
		{
			"valid restart consumer genesis state: unbonding sequences",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.UnbondingSequence{
				types.UnbondingSequence{
					1,
					uint64(time.Now().UnixNano()),
					channeltypes.Packet{
						1, "consumer", "ccvchannel1",
						"provider", "ccvchannel1",
						pdBytes1,
						clienttypes.NewHeight(0, 100), 0,
					},
				},
				types.UnbondingSequence{
					3,
					uint64(time.Now().UnixNano()),
					channeltypes.Packet{
						3, "consumer", "ccvchannel1",
						"provider", "ccvchannel1",
						pdBytes2,
						clienttypes.NewHeight(1, 200), 0,
					},
				},
				types.UnbondingSequence{
					5,
					uint64(time.Now().UnixNano()),
					channeltypes.Packet{
						5, "consumer", "ccvchannel2",
						"provider", "ccvchannel2",
						pdBytes1,
						clienttypes.NewHeight(9, 432), 0,
					},
				},
			}, valUpdates, params),
			false,
		},
		{
			"invalid restart consumer genesis state: channel id is empty",
			types.NewRestartGenesisState("", "ccvchannel", nil, valUpdates, params),
			true,
		},
		{
			"invalid restart consumer genesis state: channel id is empty",
			types.NewRestartGenesisState("ccvclient", "", nil, valUpdates, params),
			true,
		},
		{
			"invalid restart consumer genesis state: unbonding sequence packet is invalid",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.UnbondingSequence{
				types.UnbondingSequence{
					1,
					uint64(time.Now().UnixNano()),
					channeltypes.Packet{
						1, "", "ccvchannel1",
						"provider", "ccvchannel1",
						pdBytes1,
						clienttypes.NewHeight(0, 100), 0,
					},
				},
			}, valUpdates, params),
			true,
		},
		{
			"invalid restart consumer genesis state: unbonding sequence time is invalid",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.UnbondingSequence{
				types.UnbondingSequence{
					1,
					0,
					channeltypes.Packet{
						1, "consumer", "ccvchannel1",
						"provider", "ccvchannel1",
						pdBytes1,
						clienttypes.NewHeight(0, 100), 0,
					},
				},
			}, valUpdates, params),
			true,
		},
		{
			"invalid restart consumer genesis state: unbonding sequence is invalid",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.UnbondingSequence{
				types.UnbondingSequence{
					8,
					uint64(time.Now().UnixNano()),
					channeltypes.Packet{
						1, "", "ccvchannel1",
						"provider", "ccvchannel1",
						pdBytes1,
						clienttypes.NewHeight(0, 100), 0,
					},
				},
			}, valUpdates, params),
			true,
		},
		{
			"invalid restart consumer genesis: client state defined",
			&types.GenesisState{
				params,
				"ccvclient",
				"ccvchannel",
				false,
				cs,
				nil,
				nil,
				valUpdates,
			},
			true,
		},
		{
			"invalid restart consumer genesis: consensus state defined",
			&types.GenesisState{
				params,
				"ccvclient",
				"ccvchannel",
				false,
				nil,
				consensusState,
				nil,
				valUpdates,
			},
			true,
		},
		{
			"invalid restart consumer genesis state: nil initial validator set",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, nil, params),
			true,
		},
	}

	for _, c := range cases {
		err := c.gs.Validate()
		if c.expError {
			require.Error(t, err, "%s did not return expected error", c.name)
		} else {
			require.NoError(t, err, "%s returned unexpected error", c.name)
		}
	}
}
