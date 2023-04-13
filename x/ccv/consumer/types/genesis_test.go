package types_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v4/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"

	tmtypes "github.com/tendermint/tendermint/types"

	testutil "github.com/cosmos/interchain-security/testutil/keeper"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"
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
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash)

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
				nil,
				nil,
				ccv.ConsumerPacketDataList{},
				types.LastTransmissionBlockHeight{},
				false,
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
				ccv.ConsumerPacketDataList{},
				types.LastTransmissionBlockHeight{},
				false,
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
				ccv.ConsumerPacketDataList{},
				types.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty last transmission packet",
			&types.GenesisState{
				params,
				"",
				"",
				true,
				cs,
				consensusState,
				nil,
				valUpdates,
				nil,
				nil,
				ccv.ConsumerPacketDataList{},
				types.LastTransmissionBlockHeight{Height: 1},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty pending consumer packets",
			&types.GenesisState{
				params,
				"",
				"",
				true,
				cs,
				consensusState,
				nil,
				valUpdates,
				nil,
				nil,
				ccv.ConsumerPacketDataList{List: []ccv.ConsumerPacketData{{}}},
				types.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: nil initial validator set",
			types.NewInitialGenesisState(cs, consensusState, nil, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid consensus state validator set hash",
			types.NewInitialGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("wrong_length_hash")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			types.NewInitialGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			types.NewInitialGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid params",
			types.NewInitialGenesisState(cs, consensusState, valUpdates,
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
					types.DefaultSoftOptOutThreshold,
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

	matConsumerPacket := ccv.ConsumerPacketData{
		Type: ccv.VscMaturedPacket,
		Data: &ccv.ConsumerPacketData_VscMaturedPacketData{
			VscMaturedPacketData: ccv.NewVSCMaturedPacketData(1),
		},
	}

	slashConsumerPacket := ccv.ConsumerPacketData{
		Type: ccv.SlashPacket,
		Data: &ccv.ConsumerPacketData_SlashPacketData{
			SlashPacketData: ccv.NewSlashPacketData(
				abci.Validator{Address: pubKey.Address(), Power: int64(1)},
				1,
				stakingtypes.Downtime),
		},
	}

	// create default height to validator set update id mapping
	heightToValsetUpdateID := []types.HeightToValsetUpdateID{
		{Height: 0, ValsetUpdateId: 0},
	}

	cs := ibctmtypes.NewClientState(chainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, height, commitmenttypes.GetSDKSpecs(), upgradePath, false, false)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash)

	params := types.DefaultParams()
	params.Enabled = true

	cases := []struct {
		name     string
		gs       *types.GenesisState
		expError bool
	}{
		{
			"valid restart consumer genesis state: empty maturing packets",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, valUpdates, heightToValsetUpdateID,
				ccv.ConsumerPacketDataList{List: []ccv.ConsumerPacketData{matConsumerPacket, slashConsumerPacket}},
				nil, types.LastTransmissionBlockHeight{Height: 100}, params),
			false,
		},
		{
			"valid restart consumer genesis state: handshake in progress ",
			types.NewRestartGenesisState("ccvclient", "", nil, valUpdates, heightToValsetUpdateID,
				ccv.ConsumerPacketDataList{List: []ccv.ConsumerPacketData{slashConsumerPacket}}, nil, types.LastTransmissionBlockHeight{}, params),
			false,
		},
		{
			"valid restart consumer genesis state: maturing packets",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{1, time.Now().UTC()},
				{3, time.Now().UTC()},
				{5, time.Now().UTC()},
			}, valUpdates, heightToValsetUpdateID, ccv.ConsumerPacketDataList{},
				[]types.OutstandingDowntime{{ValidatorConsensusAddress: sdk.ConsAddress(validator.Address.Bytes()).String()}},
				types.LastTransmissionBlockHeight{}, params),
			false,
		},
		{
			"invalid restart consumer genesis state: provider id is empty",
			types.NewRestartGenesisState("", "ccvchannel", nil, valUpdates, heightToValsetUpdateID, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet vscId is invalid",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{0, time.Now().UTC()},
			}, valUpdates, nil, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet time is invalid",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{1, time.Time{}},
			}, valUpdates, nil, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
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
				ccv.ConsumerPacketDataList{},
				types.LastTransmissionBlockHeight{},
				false,
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
				ccv.ConsumerPacketDataList{},
				types.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid restart consumer genesis state: nil initial validator set",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, nil, nil, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: nil height to validator set id mapping",
			types.NewRestartGenesisState("ccvclient", "",
				[]types.MaturingVSCPacket{{1, time.Time{}}}, valUpdates, nil, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet defined when handshake is still in progress",
			types.NewRestartGenesisState("ccvclient", "",
				[]types.MaturingVSCPacket{{1, time.Time{}}}, valUpdates, heightToValsetUpdateID, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: outstanding downtime defined when handshake is still in progress",
			types.NewRestartGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, ccv.ConsumerPacketDataList{}, []types.OutstandingDowntime{{ValidatorConsensusAddress: "cosmosvalconsxxx"}},
				types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: last transmission block height defined when handshake is still in progress",
			types.NewRestartGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{Height: int64(1)}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: pending maturing packets defined when handshake is still in progress",
			types.NewRestartGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, ccv.ConsumerPacketDataList{
					List: []ccv.ConsumerPacketData{
						{
							Type: ccv.VscMaturedPacket,
							Data: &ccv.ConsumerPacketData_VscMaturedPacketData{VscMaturedPacketData: ccv.NewVSCMaturedPacketData(1)},
						},
					},
				}, nil, types.LastTransmissionBlockHeight{Height: int64(1)}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: invalid params",
			types.NewRestartGenesisState("ccvclient", "ccvchannel", nil, valUpdates, nil, ccv.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{},
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
					types.DefaultSoftOptOutThreshold,
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
