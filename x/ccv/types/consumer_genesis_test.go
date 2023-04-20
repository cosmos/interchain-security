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

	tmtypes "github.com/tendermint/tendermint/types"

	testutil "github.com/cosmos/interchain-security/testutil/keeper"

	"github.com/cosmos/interchain-security/x/ccv/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
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

	params := ccvtypes.DefaultConsumerParams()
	params.Enabled = true

	cases := []struct {
		name     string
		gs       *ccvtypes.ConsumerGenesisState
		expError bool
	}{
		{
			"valid new consumer genesis state",
			ccvtypes.NewInitialConsumerGenesisState(cs, consensusState, valUpdates, params),
			false,
		},
		{
			"invalid new consumer genesis state: nil client state",
			ccvtypes.NewInitialConsumerGenesisState(nil, consensusState, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid client state",
			ccvtypes.NewInitialConsumerGenesisState(&ibctmtypes.ClientState{ChainId: "badClientState"},
				consensusState, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: nil consensus state",
			ccvtypes.NewInitialConsumerGenesisState(cs, nil, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid consensus state",
			ccvtypes.NewInitialConsumerGenesisState(cs, &ibctmtypes.ConsensusState{Timestamp: time.Now()},
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: client id not empty",
			&ccvtypes.ConsumerGenesisState{
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
				ccvtypes.ConsumerPacketDataList{},
				ccvtypes.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: channel id not empty",
			&ccvtypes.ConsumerGenesisState{
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
				ccvtypes.ConsumerPacketDataList{},
				ccvtypes.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty unbonding sequences",
			&ccvtypes.ConsumerGenesisState{
				params,
				"",
				"",
				true,
				cs,
				consensusState,
				[]ccvtypes.MaturingVSCPacket{{}},
				valUpdates,
				nil,
				nil,
				ccvtypes.ConsumerPacketDataList{},
				ccvtypes.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty last transmission packet",
			&ccvtypes.ConsumerGenesisState{
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
				ccvtypes.ConsumerPacketDataList{},
				ccvtypes.LastTransmissionBlockHeight{Height: 1},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty pending consumer packets",
			&ccvtypes.ConsumerGenesisState{
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
				ccvtypes.ConsumerPacketDataList{List: []ccvtypes.ConsumerPacketData{{}}},
				ccvtypes.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: nil initial validator set",
			ccvtypes.NewInitialConsumerGenesisState(cs, consensusState, nil, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid consensus state validator set hash",
			ccvtypes.NewInitialConsumerGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("wrong_length_hash")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			ccvtypes.NewInitialConsumerGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			ccvtypes.NewInitialConsumerGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid params",
			ccvtypes.NewInitialConsumerGenesisState(cs, consensusState, valUpdates,
				ccvtypes.NewConsumerParams(
					true,
					ccvtypes.DefaultBlocksPerDistributionTransmission,
					"",
					"",
					0, // CCV timeout period cannot be 0
					ccvtypes.DefaultTransferTimeoutPeriod,
					ccvtypes.DefaultConsumerRedistributeFrac,
					ccvtypes.DefaultHistoricalEntries,
					ccvtypes.DefaultConsumerUnbondingPeriod,
					ccvtypes.DefaultSoftOptOutThreshold,
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

	matConsumerPacket := ccvtypes.ConsumerPacketData{
		Type: ccvtypes.VscMaturedPacket,
		Data: &ccvtypes.ConsumerPacketData_VscMaturedPacketData{
			VscMaturedPacketData: ccvtypes.NewVSCMaturedPacketData(1),
		},
	}

	slashConsumerPacket := ccvtypes.ConsumerPacketData{
		Type: ccvtypes.SlashPacket,
		Data: &ccvtypes.ConsumerPacketData_SlashPacketData{
			SlashPacketData: ccvtypes.NewSlashPacketData(
				abci.Validator{Address: pubKey.Address(), Power: int64(1)},
				1,
				stakingtypes.Downtime),
		},
	}

	// create default height to validator set update id mapping
	heightToValsetUpdateID := []ccvtypes.HeightToValsetUpdateID{
		{Height: 0, ValsetUpdateId: 0},
	}

	cs := ibctmtypes.NewClientState(chainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, height, commitmenttypes.GetSDKSpecs(), upgradePath, false, false)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash)

	params := ccvtypes.DefaultConsumerParams()
	params.Enabled = true

	cases := []struct {
		name     string
		gs       *ccvtypes.ConsumerGenesisState
		expError bool
	}{
		{
			"valid restart consumer genesis state: empty maturing packets",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", nil, valUpdates, heightToValsetUpdateID,
				ccvtypes.ConsumerPacketDataList{List: []ccvtypes.ConsumerPacketData{matConsumerPacket, slashConsumerPacket}},
				nil, ccvtypes.LastTransmissionBlockHeight{Height: 100}, params),
			false,
		},
		{
			"valid restart consumer genesis state: handshake in progress ",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "", nil, valUpdates, heightToValsetUpdateID,
				ccvtypes.ConsumerPacketDataList{List: []ccvtypes.ConsumerPacketData{slashConsumerPacket}}, nil, ccvtypes.LastTransmissionBlockHeight{}, params),
			false,
		},
		{
			"valid restart consumer genesis state: maturing packets",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", []ccvtypes.MaturingVSCPacket{
				{1, time.Now().UTC()},
				{3, time.Now().UTC()},
				{5, time.Now().UTC()},
			}, valUpdates, heightToValsetUpdateID, ccvtypes.ConsumerPacketDataList{},
				[]ccvtypes.OutstandingDowntime{{ValidatorConsensusAddress: sdk.ConsAddress(validator.Address.Bytes()).String()}},
				ccvtypes.LastTransmissionBlockHeight{}, params),
			false,
		},
		{
			"invalid restart consumer genesis state: provider id is empty",
			ccvtypes.NewRestartConsumerGenesisState("", "ccvchannel", nil, valUpdates, heightToValsetUpdateID, ccvtypes.ConsumerPacketDataList{}, nil, ccvtypes.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet vscId is invalid",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", []ccvtypes.MaturingVSCPacket{
				{0, time.Now().UTC()},
			}, valUpdates, nil, ccvtypes.ConsumerPacketDataList{}, nil, ccvtypes.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet time is invalid",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", []ccvtypes.MaturingVSCPacket{
				{1, time.Time{}},
			}, valUpdates, nil, ccvtypes.ConsumerPacketDataList{}, nil, ccvtypes.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis: client state defined",
			&ccvtypes.ConsumerGenesisState{
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
				ccvtypes.ConsumerPacketDataList{},
				ccvtypes.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid restart consumer genesis: consensus state defined",
			&ccvtypes.ConsumerGenesisState{
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
				ccvtypes.ConsumerPacketDataList{},
				ccvtypes.LastTransmissionBlockHeight{},
				false,
			},
			true,
		},
		{
			"invalid restart consumer genesis state: nil initial validator set",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", nil, nil, nil, ccvtypes.ConsumerPacketDataList{}, nil, ccvtypes.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: nil height to validator set id mapping",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "",
				[]ccvtypes.MaturingVSCPacket{{1, time.Time{}}}, valUpdates, nil, ccvtypes.ConsumerPacketDataList{}, nil, ccvtypes.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet defined when handshake is still in progress",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "",
				[]ccvtypes.MaturingVSCPacket{{1, time.Time{}}}, valUpdates, heightToValsetUpdateID, ccvtypes.ConsumerPacketDataList{}, nil, ccvtypes.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: outstanding downtime defined when handshake is still in progress",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, ccvtypes.ConsumerPacketDataList{}, []ccvtypes.OutstandingDowntime{{ValidatorConsensusAddress: "cosmosvalconsxxx"}},
				ccvtypes.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: last transmission block height defined when handshake is still in progress",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, ccvtypes.ConsumerPacketDataList{}, nil, ccvtypes.LastTransmissionBlockHeight{Height: int64(1)}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: pending maturing packets defined when handshake is still in progress",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, ccvtypes.ConsumerPacketDataList{
					List: []ccvtypes.ConsumerPacketData{
						{
							Type: ccvtypes.VscMaturedPacket,
							Data: &ccvtypes.ConsumerPacketData_VscMaturedPacketData{VscMaturedPacketData: ccvtypes.NewVSCMaturedPacketData(1)},
						},
					},
				}, nil, ccvtypes.LastTransmissionBlockHeight{Height: int64(1)}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: invalid params",
			ccvtypes.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", nil, valUpdates, nil, ccvtypes.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{},
				ccvtypes.NewConsumerParams(
					true,
					ccvtypes.DefaultBlocksPerDistributionTransmission,
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
