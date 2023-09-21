package types_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v7/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"
	tmtypes "github.com/cometbft/cometbft/types"

	"github.com/cosmos/interchain-security/v3/testutil/crypto"
	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
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
	cId := crypto.NewCryptoIdentityFromIntSeed(238934)
	pubKey := cId.TMCryptoPubKey()

	// create validator set with single validator
	validator := tmtypes.NewValidator(pubKey, 1)
	valSet := tmtypes.NewValidatorSet([]*tmtypes.Validator{validator})
	valHash := valSet.Hash()
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(valSet)

	cs := ibctmtypes.NewClientState(chainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, height, commitmenttypes.GetSDKSpecs(), upgradePath)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash)

	params := ccv.DefaultParams()
	params.Enabled = true

	cases := []struct {
		name     string
		gs       *types.PrivateConsumerGenesisState
		expError bool
	}{
		{
			"valid new consumer genesis state",
			types.NewPrivateInitialConsumerGenesisState(cs, consensusState, valUpdates, params),
			false,
		},
		{
			"invalid new consumer genesis state: nil client state",
			types.NewPrivateInitialConsumerGenesisState(nil, consensusState, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid client state",
			types.NewPrivateInitialConsumerGenesisState(&ibctmtypes.ClientState{ChainId: "badClientState"},
				consensusState, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: nil consensus state",
			types.NewPrivateInitialConsumerGenesisState(cs, nil, valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid consensus state",
			types.NewPrivateInitialConsumerGenesisState(cs, &ibctmtypes.ConsensusState{Timestamp: time.Now()},
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: client id not empty",
			&types.PrivateConsumerGenesisState{
				Params:            params,
				ProviderClientId:  "ccvclient",
				ProviderChannelId: "",
				NewChain:          true,
				Provider: ccv.ProviderInfo{ClientState: cs,
					ConsensusState: consensusState,
					InitialValSet:  valUpdates,
				},
				MaturingPackets:             nil,
				HeightToValsetUpdateId:      nil,
				OutstandingDowntimeSlashing: nil,
				PendingConsumerPackets:      types.ConsumerPacketDataList{},
				LastTransmissionBlockHeight: types.LastTransmissionBlockHeight{},
				PreCCV:                      false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: channel id not empty",
			&types.PrivateConsumerGenesisState{
				Params:            params,
				ProviderClientId:  "",
				ProviderChannelId: "ccvchannel",
				NewChain:          true,
				Provider: ccv.ProviderInfo{ClientState: cs,
					ConsensusState: consensusState,
					InitialValSet:  valUpdates,
				},
				MaturingPackets:             nil,
				HeightToValsetUpdateId:      nil,
				OutstandingDowntimeSlashing: nil,
				PendingConsumerPackets:      types.ConsumerPacketDataList{},
				LastTransmissionBlockHeight: types.LastTransmissionBlockHeight{},
				PreCCV:                      false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty unbonding sequences",
			&types.PrivateConsumerGenesisState{
				Params:            params,
				ProviderClientId:  "",
				ProviderChannelId: "",
				NewChain:          true,
				Provider: ccv.ProviderInfo{ClientState: cs,
					ConsensusState: consensusState,
					InitialValSet:  valUpdates,
				},
				MaturingPackets:             []types.MaturingVSCPacket{{}},
				HeightToValsetUpdateId:      nil,
				OutstandingDowntimeSlashing: nil,
				PendingConsumerPackets:      types.ConsumerPacketDataList{},
				LastTransmissionBlockHeight: types.LastTransmissionBlockHeight{},
				PreCCV:                      false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty last transmission packet",
			&types.PrivateConsumerGenesisState{
				Params:            params,
				ProviderClientId:  "",
				ProviderChannelId: "",
				NewChain:          true,
				Provider: ccv.ProviderInfo{ClientState: cs,
					ConsensusState: consensusState,
					InitialValSet:  valUpdates,
				},
				MaturingPackets:             nil,
				HeightToValsetUpdateId:      nil,
				OutstandingDowntimeSlashing: nil,
				PendingConsumerPackets:      types.ConsumerPacketDataList{},
				LastTransmissionBlockHeight: types.LastTransmissionBlockHeight{Height: 1},
				PreCCV:                      false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: non-empty pending consumer packets",
			&types.PrivateConsumerGenesisState{
				Params:            params,
				ProviderClientId:  "",
				ProviderChannelId: "",
				NewChain:          true,
				Provider: ccv.ProviderInfo{ClientState: cs,
					ConsensusState: consensusState,
					InitialValSet:  valUpdates,
				},
				MaturingPackets:             nil,
				HeightToValsetUpdateId:      nil,
				OutstandingDowntimeSlashing: nil,
				PendingConsumerPackets:      types.ConsumerPacketDataList{List: []ccv.ConsumerPacketData{{}}},
				LastTransmissionBlockHeight: types.LastTransmissionBlockHeight{},
				PreCCV:                      false,
			},
			true,
		},
		{
			"invalid new consumer genesis state: nil initial validator set",
			types.NewPrivateInitialConsumerGenesisState(cs, consensusState, nil, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid consensus state validator set hash",
			types.NewPrivateInitialConsumerGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("wrong_length_hash")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			types.NewPrivateInitialConsumerGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: initial validator set does not match validator set hash",
			types.NewPrivateInitialConsumerGenesisState(
				cs, ibctmtypes.NewConsensusState(
					time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), []byte("9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08")),
				valUpdates, params),
			true,
		},
		{
			"invalid new consumer genesis state: invalid params - ccvTimeoutPeriod",
			types.NewPrivateInitialConsumerGenesisState(cs, consensusState, valUpdates,
				ccv.NewParams(
					true,
					ccv.DefaultBlocksPerDistributionTransmission,
					"",
					"",
					0, // CCV timeout period cannot be 0
					ccv.DefaultTransferTimeoutPeriod,
					ccv.DefaultConsumerRedistributeFrac,
					ccv.DefaultHistoricalEntries,
					ccv.DefaultConsumerUnbondingPeriod,
					ccv.DefaultSoftOptOutThreshold,
					[]string{},
					[]string{},
				)),
			true,
		},
		{
			"invalid new consumer genesis state: invalid params - distributionTransmissionChannel",
			types.NewPrivateInitialConsumerGenesisState(cs, consensusState, valUpdates,
				ccv.NewParams(
					true,
					ccv.DefaultBlocksPerDistributionTransmission,
					"badchannel/",
					"",
					ccv.DefaultCCVTimeoutPeriod,
					ccv.DefaultTransferTimeoutPeriod,
					ccv.DefaultConsumerRedistributeFrac,
					ccv.DefaultHistoricalEntries,
					ccv.DefaultConsumerUnbondingPeriod,
					ccv.DefaultSoftOptOutThreshold,
					[]string{},
					[]string{},
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

// TestValidateRestartConsumerGenesisState tests a NewRestartGenesisState instantiation,
// and its Validate() method over different genesis scenarios
func TestValidateRestartConsumerGenesisState(t *testing.T) {
	// generate validator private/public key
	cId := crypto.NewCryptoIdentityFromIntSeed(234234)
	pubKey := cId.TMCryptoPubKey()

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
				stakingtypes.Infraction_INFRACTION_DOWNTIME),
		},
	}

	// create default height to validator set update id mapping
	heightToValsetUpdateID := []types.HeightToValsetUpdateID{
		{Height: 0, ValsetUpdateId: 0},
	}

	cs := ibctmtypes.NewClientState(chainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, height, commitmenttypes.GetSDKSpecs(), upgradePath)
	consensusState := ibctmtypes.NewConsensusState(time.Now(), commitmenttypes.NewMerkleRoot([]byte("apphash")), valHash)

	params := ccv.DefaultParams()
	params.Enabled = true

	cases := []struct {
		name     string
		gs       *types.PrivateConsumerGenesisState
		expError bool
	}{
		{
			"valid restart consumer genesis state: empty maturing packets",
			types.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", nil, valUpdates, heightToValsetUpdateID,
				types.ConsumerPacketDataList{List: []ccv.ConsumerPacketData{matConsumerPacket, slashConsumerPacket}},
				nil, types.LastTransmissionBlockHeight{Height: 100}, params),
			false,
		},
		{
			"valid restart consumer genesis state: handshake in progress ",
			types.NewRestartConsumerGenesisState("ccvclient", "", nil, valUpdates, heightToValsetUpdateID,
				types.ConsumerPacketDataList{List: []ccv.ConsumerPacketData{slashConsumerPacket}}, nil, types.LastTransmissionBlockHeight{}, params),
			false,
		},
		{
			"valid restart consumer genesis state: maturing packets",
			types.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{VscId: 1, MaturityTime: time.Now().UTC()},
				{VscId: 3, MaturityTime: time.Now().UTC()},
				{VscId: 5, MaturityTime: time.Now().UTC()},
			}, valUpdates, heightToValsetUpdateID, types.ConsumerPacketDataList{},
				[]types.OutstandingDowntime{{ValidatorConsensusAddress: sdk.ConsAddress(validator.Address.Bytes()).String()}},
				types.LastTransmissionBlockHeight{}, params),
			false,
		},
		{
			"invalid restart consumer genesis state: provider id is empty",
			types.NewRestartConsumerGenesisState("", "ccvchannel", nil, valUpdates, heightToValsetUpdateID, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet vscId is invalid",
			types.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{VscId: 0, MaturityTime: time.Now().UTC()},
			}, valUpdates, nil, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet time is invalid",
			types.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", []types.MaturingVSCPacket{
				{VscId: 1, MaturityTime: time.Time{}},
			}, valUpdates, nil, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis: client state defined",
			&types.PrivateConsumerGenesisState{
				Params:            params,
				ProviderClientId:  "ccvclient",
				ProviderChannelId: "ccvchannel",
				NewChain:          false,
				Provider: ccv.ProviderInfo{
					ClientState:    cs,
					ConsensusState: nil,
					InitialValSet:  valUpdates,
				},
				MaturingPackets:             nil,
				HeightToValsetUpdateId:      nil,
				OutstandingDowntimeSlashing: nil,
				PendingConsumerPackets:      types.ConsumerPacketDataList{},
				LastTransmissionBlockHeight: types.LastTransmissionBlockHeight{},
				PreCCV:                      false,
			},
			true,
		},
		{
			"invalid restart consumer genesis: consensus state defined",
			&types.PrivateConsumerGenesisState{
				Params:            params,
				ProviderClientId:  "ccvclient",
				ProviderChannelId: "ccvchannel",
				NewChain:          false,
				Provider: ccv.ProviderInfo{
					ClientState:    nil,
					ConsensusState: consensusState,
					InitialValSet:  valUpdates,
				},
				MaturingPackets:             nil,
				HeightToValsetUpdateId:      nil,
				OutstandingDowntimeSlashing: nil,
				PendingConsumerPackets:      types.ConsumerPacketDataList{},
				LastTransmissionBlockHeight: types.LastTransmissionBlockHeight{},
				PreCCV:                      false,
			},
			true,
		},
		{
			"invalid restart consumer genesis state: nil initial validator set",
			types.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", nil, nil, nil, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: nil height to validator set id mapping",
			types.NewRestartConsumerGenesisState("ccvclient", "",
				[]types.MaturingVSCPacket{{VscId: 1, MaturityTime: time.Time{}}}, valUpdates, nil, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: maturing packet defined when handshake is still in progress",
			types.NewRestartConsumerGenesisState("ccvclient", "",
				[]types.MaturingVSCPacket{{VscId: 1, MaturityTime: time.Time{}}}, valUpdates, heightToValsetUpdateID, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: outstanding downtime defined when handshake is still in progress",
			types.NewRestartConsumerGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, types.ConsumerPacketDataList{}, []types.OutstandingDowntime{{ValidatorConsensusAddress: "cosmosvalconsxxx"}},
				types.LastTransmissionBlockHeight{}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: last transmission block height defined when handshake is still in progress",
			types.NewRestartConsumerGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{Height: int64(1)}, params),
			true,
		},
		{
			"invalid restart consumer genesis state: pending maturing packets defined when handshake is still in progress",
			types.NewRestartConsumerGenesisState("ccvclient", "",
				nil, valUpdates, heightToValsetUpdateID, types.ConsumerPacketDataList{
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
			types.NewRestartConsumerGenesisState("ccvclient", "ccvchannel", nil, valUpdates, nil, types.ConsumerPacketDataList{}, nil, types.LastTransmissionBlockHeight{},
				ccv.NewParams(
					true,
					ccv.DefaultBlocksPerDistributionTransmission,
					"",
					"",
					0, // CCV timeout period cannot be 0
					ccv.DefaultTransferTimeoutPeriod,
					ccv.DefaultConsumerRedistributeFrac,
					ccv.DefaultHistoricalEntries,
					ccv.DefaultConsumerUnbondingPeriod,
					ccv.DefaultSoftOptOutThreshold,
					[]string{},
					[]string{},
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
