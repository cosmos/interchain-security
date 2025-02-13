package types_test

import (
	"strings"
	"testing"
	"time"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	cryptoutil "github.com/cosmos/interchain-security/v7/testutil/crypto"
	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
)

func TestValidateStringField(t *testing.T) {
	testCases := []struct {
		name      string
		field     string
		maxLength int
		valid     bool
	}{
		{
			name:      "invalid: empty",
			field:     "",
			maxLength: 5,
			valid:     false,
		},
		{
			name:      "invalid: too long",
			field:     "this field is too long",
			maxLength: 5,
			valid:     false,
		},
		{
			name:      "valid",
			field:     "valid",
			maxLength: 5,
			valid:     true,
		},
	}

	for _, tc := range testCases {
		err := types.ValidateStringField(tc.name, tc.field, tc.maxLength)
		if tc.valid {
			require.NoError(t, err, tc.name)
		} else {
			require.Error(t, err, tc.name)
		}
	}
}

func TestTruncateString(t *testing.T) {
	testCases := []struct {
		str       string
		maxLength int
		expStr    string
	}{
		{"drink", 3, "dri"},
		{"drink", 6, "drink"},
		{"drink", 0, ""},
		{"drink", -1, ""},
		{"drink", 100, "drink"},
		{"pub", 100, "pub"},
		{"こんにちは", 3, "こんに"},
	}

	for _, tc := range testCases {
		truncated := types.TruncateString(tc.str, tc.maxLength)
		require.Equal(t, tc.expStr, truncated)
	}
}

func TestValidateConsumerMetadata(t *testing.T) {
	generateLongString := func(length int) string {
		result := make([]byte, length)
		for i := range result {
			result[i] = byte('a')
		}
		return string(result)
	}

	testCases := []struct {
		name     string
		metadata types.ConsumerMetadata
		valid    bool
	}{
		{
			name: "valid",
			metadata: types.ConsumerMetadata{
				Name:        "name",
				Description: "description",
				Metadata:    "metadata",
			},
			valid: true,
		},
		{
			name: "valid with long strings",
			metadata: types.ConsumerMetadata{
				Name:        generateLongString(types.MaxNameLength),
				Description: generateLongString(types.MaxDescriptionLength),
				Metadata:    generateLongString(types.MaxMetadataLength),
			},
			valid: true,
		},
		{
			name: "invalid name",
			metadata: types.ConsumerMetadata{
				Name:        generateLongString(types.MaxNameLength + 1),
				Description: "description",
				Metadata:    "metadata",
			},
			valid: false,
		},
		{
			name: "invalid description",
			metadata: types.ConsumerMetadata{
				Name:        "name",
				Description: generateLongString(types.MaxDescriptionLength + 1),
				Metadata:    "metadata",
			},
			valid: false,
		},
		{
			name: "invalid metadata",
			metadata: types.ConsumerMetadata{
				Name:        "name",
				Description: "description",
				Metadata:    generateLongString(types.MaxMetadataLength + 1),
			},
			valid: false,
		},
	}

	for _, tc := range testCases {
		err := types.ValidateConsumerMetadata(tc.metadata)
		if tc.valid {
			require.NoError(t, err, tc.name)
		} else {
			require.Error(t, err, tc.name)
		}
	}
}

func TestValidateInitializationParameters(t *testing.T) {
	now := time.Now().UTC()
	coolStr := "Cosmos Hub is the best place to launch a chain. Interchain Security is awesome."
	tooLongHash := []byte(coolStr)

	testCases := []struct {
		name   string
		params types.ConsumerInitializationParameters
		valid  bool
	}{
		{
			name: "valid",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: true,
		},
		{
			name: "invalid - zero height",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.ZeroHeight(),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid - hash too long",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       tooLongHash,
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid - zero spawn time",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         time.Time{},
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: true,
		},
		{
			name: "invalid - zero duration",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   0,
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid -- ConsumerRedistributionFraction > 1",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "1.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid -- ConsumerRedistributionFraction wrong format",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    coolStr,
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid - BlocksPerDistributionTransmission zero",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 0,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid - HistoricalEntries zero",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 0,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid - DistributionTransmissionChannel too long",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   coolStr,
				ConnectionId:                      "",
			},
			valid: false,
		},
		{
			name: "invalid - ConnectionId too long",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01},
				BinaryHash:                        []byte{0x01},
				SpawnTime:                         now,
				UnbondingPeriod:                   time.Duration(100000000000),
				CcvTimeoutPeriod:                  time.Duration(100000000000),
				TransferTimeoutPeriod:             time.Duration(100000000000),
				ConsumerRedistributionFraction:    "0.75",
				BlocksPerDistributionTransmission: 10,
				HistoricalEntries:                 10000,
				DistributionTransmissionChannel:   "",
				ConnectionId:                      coolStr,
			},
			valid: false,
		},
	}

	for _, tc := range testCases {
		err := types.ValidateInitializationParameters(tc.params)
		if tc.valid {
			require.NoError(t, err, tc.name)
		} else {
			require.Error(t, err, tc.name)
		}
	}
}

func TestValidateConsAddressList(t *testing.T) {
	consAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	invalidConsAddr := "cosmosvalcons1nx7n5uh0ztxsynn4sje6ey"

	testCases := []struct {
		name      string
		list      []string
		maxLength int
		valid     bool
	}{
		{
			name:      "valid - empty list",
			list:      []string{},
			maxLength: 10,
			valid:     true,
		},
		{
			name:      "valid - non-empty list",
			list:      []string{consAddr1, consAddr2},
			maxLength: 10,
			valid:     true,
		},
		{
			name:      "invalid - address with wrong format",
			list:      []string{invalidConsAddr},
			maxLength: 10,
			valid:     false,
		},
		{
			name:      "invalid - empty address",
			list:      []string{""},
			maxLength: 10,
			valid:     false,
		},
		{
			name:      "invalid - list length",
			list:      []string{consAddr1, consAddr2},
			maxLength: 1,
			valid:     false,
		},
	}

	for _, tc := range testCases {
		err := types.ValidateConsAddressList(tc.list, tc.maxLength)
		if tc.valid {
			require.NoError(t, err, tc.name)
		} else {
			require.Error(t, err, tc.name)
		}
	}
}

func TestValidateByteSlice(t *testing.T) {
	testCases := []struct {
		name      string
		slice     []byte
		maxLength int
		valid     bool
	}{
		{
			name:      "valid: empty",
			slice:     []byte{},
			maxLength: 5,
			valid:     true,
		},
		{
			name:      "invalid: too long",
			slice:     []byte{0x01, 0x02},
			maxLength: 1,
			valid:     false,
		},
		{
			name:      "valid",
			slice:     []byte{0x01, 0x02},
			maxLength: 5,
			valid:     true,
		},
	}

	for _, tc := range testCases {
		err := types.ValidateByteSlice(tc.slice, tc.maxLength)
		if tc.valid {
			require.NoError(t, err, tc.name)
		} else {
			require.Error(t, err, tc.name)
		}
	}
}

func TestMsgCreateConsumerValidateBasic(t *testing.T) {
	testCases := []struct {
		name                   string
		chainId                string
		powerShapingParameters *types.PowerShapingParameters
		infractionParameters   *types.InfractionParameters
		expPass                bool
	}{
		{
			"empty chain id",
			"",
			nil, // no power-shaping parameters
			nil,
			false,
		},
		{
			"empty chain id after trimming",
			"   	",
			nil, // no power-shaping parameters
			nil,
			false,
		},
		{
			"neutron chain id that cannot be reused",
			"neutron-1",
			nil, // no power-shaping parameters
			nil,
			false,
		},
		{
			"stride chain id that cannot be reused",
			"stride-1",
			nil, // no power-shaping parameters
			nil,
			false,
		},
		{
			"valid chain id",
			"somechain-1",
			nil, // no power-shaping parameters
			&types.InfractionParameters{
				DoubleSign: &types.SlashJailParameters{
					JailDuration:  time.Duration(1<<63 - 1),        // max duration
					SlashFraction: math.LegacyNewDecWithPrec(5, 2), // 0.05
					Tombstone:     true,
				},
				Downtime: &types.SlashJailParameters{
					JailDuration:  600 * time.Second,
					SlashFraction: math.LegacyNewDec(0),
					Tombstone:     false,
				},
			}, // valid infraction params
			true,
		},
		{
			"valid chain id and invalid power-shaping parameters",
			"somechain-1",
			&types.PowerShapingParameters{Top_N: 51}, // TopN cannot be > 0 in MsgCreateConsumer
			nil,
			false,
		},
		{
			"invalid infraction downtime jailing parameters",
			"somechain-1",
			nil,
			&types.InfractionParameters{Downtime: &types.SlashJailParameters{
				JailDuration:  -1,
				SlashFraction: math.LegacyNewDec(0),
			}},
			false,
		},
		{
			"invalid infraction downtime slashing parameters",
			"somechain-1",
			nil,
			&types.InfractionParameters{Downtime: &types.SlashJailParameters{
				JailDuration:  600 * time.Second,
				SlashFraction: math.LegacyNewDec(2),
			}},
			false,
		},
		{
			"invalid infraction double sign jailing parameters",
			"somechain-1",
			nil,
			&types.InfractionParameters{Downtime: &types.SlashJailParameters{
				JailDuration:  -1,
				SlashFraction: math.LegacyNewDec(0),
			}},
			false,
		},
		{
			"invalid infraction double sign slashing parameters",
			"somechain-1",
			nil,
			&types.InfractionParameters{Downtime: &types.SlashJailParameters{
				JailDuration:  600 * time.Second,
				SlashFraction: math.LegacyNewDec(2),
			}},
			false,
		},
	}

	for _, tc := range testCases {
		validConsumerMetadata := types.ConsumerMetadata{Name: "name", Description: "description", Metadata: "metadata"}
		msg, err := types.NewMsgCreateConsumer("submitter", tc.chainId, validConsumerMetadata, nil, tc.powerShapingParameters, nil, tc.infractionParameters)
		require.NoError(t, err)
		err = msg.ValidateBasic()
		if tc.expPass {
			require.NoError(t, err, "valid case: %s should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: '%s' must return error but got none", tc.name)
		}
	}
}

func TestMsgUpdateConsumerValidateBasic(t *testing.T) {
	consAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr3 := "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe"

	testCases := []struct {
		name                   string
		powerShapingParameters types.PowerShapingParameters
		newChainId             string
		expPass                bool
	}{
		{
			"success",
			types.PowerShapingParameters{
				Top_N:              50,
				ValidatorsPowerCap: 100,
				ValidatorSetCap:    34,
				Allowlist:          []string{consAddr1},
				Denylist:           nil,
				MinStake:           0,
				AllowInactiveVals:  false,
				Prioritylist:       []string{consAddr1},
			},
			"validchainid-0",
			true,
		},
		{
			"top N is invalid",
			types.PowerShapingParameters{
				Top_N:              10,
				ValidatorsPowerCap: 0,
				ValidatorSetCap:    0,
				Allowlist:          nil,
				Denylist:           nil,
				Prioritylist:       nil,
			},
			"validchainid-0",
			false,
		},
		{
			"validators power cap is invalid",
			types.PowerShapingParameters{
				Top_N:              50,
				ValidatorsPowerCap: 101,
				ValidatorSetCap:    0,
				Allowlist:          nil,
				Denylist:           nil,
				MinStake:           0,
				AllowInactiveVals:  false,
				Prioritylist:       nil,
			},
			"validchainid-0",
			false,
		},
		{
			"valid proposal",
			types.PowerShapingParameters{
				Top_N:              54,
				ValidatorsPowerCap: 92,
				ValidatorSetCap:    0,
				Allowlist:          []string{consAddr1},
				Denylist:           []string{consAddr2, consAddr3},
				MinStake:           0,
				AllowInactiveVals:  false,
				Prioritylist:       []string{consAddr1},
			},
			"validchainid-0",
			true,
		},
	}

	for _, tc := range testCases {
		// TODO (PERMISSIONLESS) add more tests
		msg, _ := types.NewMsgUpdateConsumer("", "0", "cosmos1p3ucd3ptpw902fluyjzhq3ffgq4ntddac9sa3s", nil, nil, &tc.powerShapingParameters, nil, tc.newChainId, nil)
		err := msg.ValidateBasic()
		if tc.expPass {
			require.NoError(t, err, "valid case: %s should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: '%s' must return error but got none", tc.name)
		}
	}
}

func TestMsgAssignConsumerKeyValidateBasic(t *testing.T) {
	cId1 := cryptoutil.NewCryptoIdentityFromIntSeed(35443543534)
	cId2 := cryptoutil.NewCryptoIdentityFromIntSeed(65465464564)

	valOpAddr1 := cId1.SDKValOpAddress()
	acc1 := sdk.AccAddress(valOpAddr1.Bytes()).String()
	acc2 := sdk.AccAddress(cId2.SDKValOpAddress().Bytes()).String()

	longChainId := "abcdefghijklmnopqrstuvwxyz"
	for i := 0; i < 3; i++ {
		longChainId += longChainId
	}

	testCases := []struct {
		name         string
		chainId      string
		providerAddr string
		signer       string
		consumerKey  string
		consumerId   string
		expErr       bool
	}{
		{
			name:    "invalid: chainId non-empty",
			chainId: "chainId",
			expErr:  true,
		},
		{
			name:       "invalid: consumerId empty",
			consumerId: "",
			expErr:     true,
		},
		{
			name:       "invalid: consumerId is not a number",
			consumerId: "consumerId",
			expErr:     true,
		},
		{
			name:       "invalid: provider address is empty",
			consumerId: "1",
			expErr:     true,
		},
		{
			name:         "invalid: provider address is invalid",
			consumerId:   "1",
			providerAddr: "some address",
			expErr:       true,
		},
		{
			name:         "invalid: provider address != submitter address",
			consumerId:   "1",
			providerAddr: valOpAddr1.String(),
			signer:       acc2,
			expErr:       true,
		},
		{
			name:         "invalid: consumer pubkey empty",
			consumerId:   "1",
			providerAddr: valOpAddr1.String(),
			signer:       acc1,
			expErr:       true,
		},
		{
			name:         "valid",
			consumerId:   "1",
			providerAddr: valOpAddr1.String(),
			signer:       acc1,
			consumerKey:  "{\"@type\": \"/cosmos.crypto.ed25519.PubKey\", \"key\": \"e3BehnEIlGUAnJYn9V8gBXuMh4tXO8xxlxyXD1APGyk=\"}",
			expErr:       false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			msg := types.MsgAssignConsumerKey{
				ChainId:      tc.chainId,
				ConsumerKey:  tc.consumerKey,
				ProviderAddr: tc.providerAddr,
				Signer:       tc.signer,
				ConsumerId:   tc.consumerId,
			}

			err := msg.ValidateBasic()
			if tc.expErr {
				require.Error(t, err, tc.name)
			} else {
				require.NoError(t, err, tc.name)
			}
		})
	}
}

func TestValidateInitialHeight(t *testing.T) {
	testCases := []struct {
		name          string
		chainId       string
		initialHeight clienttypes.Height
		expPass       bool
	}{
		{
			name:    "valid with revision number",
			chainId: "chain-1",
			initialHeight: clienttypes.Height{
				RevisionNumber: 1,
				RevisionHeight: 0,
			},
			expPass: true,
		},
		{
			name:    "valid without revision number",
			chainId: "chain",
			initialHeight: clienttypes.Height{
				RevisionNumber: 0,
				RevisionHeight: 0,
			},
			expPass: true,
		},
		{
			name:    "invalid without revision number",
			chainId: "chain",
			initialHeight: clienttypes.Height{
				RevisionNumber: 1,
				RevisionHeight: 0,
			},
			expPass: false,
		},
		{
			name:    "invalid without revision number",
			chainId: "chain-1",
			initialHeight: clienttypes.Height{
				RevisionNumber: 0,
				RevisionHeight: 0,
			},
			expPass: false,
		},
		{
			name:    "valid: evmos-like chain IDs",
			chainId: "evmos_9001-2",
			initialHeight: clienttypes.Height{
				RevisionNumber: 2,
				RevisionHeight: 0,
			},
			expPass: true,
		},
	}
	for _, tc := range testCases {
		err := types.ValidateInitialHeight(tc.initialHeight, tc.chainId)
		if tc.expPass {
			require.NoError(t, err, "valid case: '%s' should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: '%s' must return error but got none", tc.name)
		}
	}
}

func TestValidateChainId(t *testing.T) {
	testCases := []struct {
		name    string
		chainId string
		expPass bool
	}{
		{
			name:    "valid chain id",
			chainId: "chain-1",
			expPass: true,
		},
		{
			name:    "valid chain id with no revision",
			chainId: "chainId",
			expPass: true,
		},
		{
			name:    "invalid (too long) chain id",
			chainId: strings.Repeat("thisIsAnExtremelyLongChainId", 2),
			expPass: false,
		},
		{
			name:    "reserved chain id",
			chainId: "stride-1",
			expPass: false,
		},
		{
			name:    "reserved chain id",
			chainId: "neutron-1",
			expPass: false,
		},
		{
			name:    "empty chain id",
			chainId: "    ",
			expPass: false,
		},
	}
	for _, tc := range testCases {
		err := types.ValidateChainId("ChainId", tc.chainId)
		if tc.expPass {
			require.NoError(t, err, "valid case: '%s' should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: '%s' must return error but got none", tc.name)
		}
	}
}
