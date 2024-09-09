package types_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	cryptoutil "github.com/cosmos/interchain-security/v6/testutil/crypto"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

func TestValidateConsumerId(t *testing.T) {
	// empty consumer id
	require.Error(t, types.ValidateConsumerId(""))

	// not a `uint64` where `uint64` is in the range [0, 2^64)
	require.Error(t, types.ValidateConsumerId("a"))
	require.Error(t, types.ValidateConsumerId("-2545"))
	require.Error(t, types.ValidateConsumerId("18446744073709551616")) // 2^64

	// valid consumer id
	require.NoError(t, types.ValidateConsumerId("0"))
	require.NoError(t, types.ValidateConsumerId("18446744073709551615")) // 2^64 - 1
}

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

func TestMsgUpdateConsumerValidateBasic(t *testing.T) {
	consAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr3 := "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe"

	testCases := []struct {
		name                   string
		powerShapingParameters types.PowerShapingParameters
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
			},
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
			},
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
			},
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
			},
			true,
		},
	}

	for _, tc := range testCases {
		// TODO (PERMISSIONLESS) add more tests
		msg, _ := types.NewMsgUpdateConsumer("", "0", "cosmos1p3ucd3ptpw902fluyjzhq3ffgq4ntddac9sa3s", nil, nil, &tc.powerShapingParameters)
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
