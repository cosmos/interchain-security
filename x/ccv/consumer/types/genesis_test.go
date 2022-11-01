package types_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"

	tmtypes "github.com/tendermint/tendermint/types"

	testutil "github.com/cosmos/interchain-security/testutil/keeper"

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

// TestValidateInitialGenesisState tests a NewInitialGenesisState instantiation,
// and its Validate() method over different genesis scenarios
func TestValidateInitialGenesisState(t *testing.T) {
	// generate validator public key
	pubKey, err := testutil.GenPubKey()
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
			types.NewInitialGenesisState(cs, consensusState, valUpdates, types.SlashRequests{}, params),
			false,
		},
		{
			"invalid new consumer genesis state: nil client state",
			types.NewInitialGenesisState(nil, consensusState, valUpdates, types.SlashRequests{}, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid client state",
			types.NewInitialGenesisState(&ibctmtypes.ClientState{ChainId: "badClientState"},
				consensusState, valUpdates, types.SlashRequests{}, params),
			true,
		},
		{
			"invalid new consumer genesis state: nil consensus state",
			types.NewInitialGenesisState(cs, nil, valUpdates, types.SlashRequests{}, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid consensus state",
			types.NewInitialGenesisState(cs, &ibctmtypes.ConsensusState{Timestamp: time.Now()},
				valUpdates, types.SlashRequests{}, params),
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
				nil,
				nil,
				types.SlashRequests{},
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
				nil,
				nil,
				types.SlashRequests{},
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
				[]types.MaturingVSCPacket{{}},
				valUpdates,
				nil,
				nil,
				types.SlashRequests{},
			},
			true,
		},
		{
			"invalid new consumer genesis state: nil initial validator set",
			types.NewInitialGenesisState(cs, consensusState, nil, types.SlashRequests{}, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			types.NewInitialGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("wrong_hash")),
				valUpdates, types.SlashRequests{}, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid params",
			types.NewInitialGenesisState(cs, consensusState, valUpdates, types.SlashRequests{},
				types.NewParams(
					true,
					types.DefaultBlocksPerDistributionTransmission,
					"",
					"",
					0, // CCV timeout period cannot be 0
					types.DefaultTransferTimeoutPeriod,
					types.DefaultConsumerRedistributeFrac,
					types.DefaultHistoricalEntries,
					types.DefaultConsumerUnbondingPeriod,
				)),
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

// TestValidateRestartGenesisState tests a NewRestartGenesisState instantiation,
// and its Validate() method over different genesis scenarios
func TestValidateRestartGenesisState(t *testing.T) {
	// generate validator private/public key
	pubKey, err := testutil.GenPubKey()
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
			"valid restart consumer genesis state: empty maturing packets",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, valUpdates, nil, nil, params),
			false,
		},
		{
			"valid restart consumer genesis state: maturing packets",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{1, uint64(time.Now().UnixNano())},
				{3, uint64(time.Now().UnixNano())},
				{5, uint64(time.Now().UnixNano())},
			}, valUpdates, nil, nil, params),
			false,
		},
		{
			"invalid restart consumer genesis state: channel id is empty",
			types.NewRestartGenesisState("", "ccvchannel", nil, valUpdates, nil, nil, params),
			true,
		},
		{
			"invalid restart consumer genesis state: channel id is empty",
			types.NewRestartGenesisState("ccvclient", "", nil, valUpdates, nil, nil, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet vscId is invalid",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{0, uint64(time.Now().UnixNano())},
			}, valUpdates, nil, nil, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet time is invalid",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{1, 0},
			}, valUpdates, nil, nil, params),
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
				nil,
				nil,
				types.SlashRequests{},
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
				nil,
				nil,
				types.SlashRequests{},
			},
			true,
		},
		{
			"invalid restart consumer genesis state: nil initial validator set",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, nil, nil, nil, params),
			true,
		},
		{
			"invalid restart consumer genesis state: invalid params",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, valUpdates, nil, nil,
				types.NewParams(
					true,
					types.DefaultBlocksPerDistributionTransmission,
					"",
					"",
					0, // CCV timeout period cannot be 0
					types.DefaultTransferTimeoutPeriod,
					types.DefaultConsumerRedistributeFrac,
					types.DefaultHistoricalEntries,
					types.DefaultConsumerUnbondingPeriod,
				)),
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
