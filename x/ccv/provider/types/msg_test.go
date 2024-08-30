package types_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
				SpawnTime:                         time.Time{},
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
			name: "invalid - zero duration",
			params: types.ConsumerInitializationParameters{
				InitialHeight:                     clienttypes.NewHeight(3, 4),
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
				GenesisHash:                       []byte{0x01}, // cannot be empty
				BinaryHash:                        []byte{0x01}, // cannot be empty
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
