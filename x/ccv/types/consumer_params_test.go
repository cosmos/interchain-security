package types_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	ccvtypes "github.com/cosmos/interchain-security/x/types"
)

// Tests the validation of consumer params that happens at genesis
func TestValidateConsumerParams(t *testing.T) {
	testCases := []struct {
		name    string
		params  ccvtypes.ConsumerParams
		expPass bool
	}{
		{"default params", ccvtypes.DefaultConsumerParams(), true},
		{
			"custom valid params",
			ccvtypes.NewConsumerParams(true, 5, "", "", 1004, 1005, "0.5", 1000, 24*21*time.Hour, "0.1"), true,
		},
		{
			"custom invalid params, block per dist transmission",
			ccvtypes.NewConsumerParams(true, -5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, dist transmission channel",
			ccvtypes.NewConsumerParams(true, 5, "badchannel/", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, provider fee pool addr string",
			ccvtypes.NewConsumerParams(true, 5, "", "imabadaddress", 5, 1005, "0.5", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, ccv timeout",
			ccvtypes.NewConsumerParams(true, 5, "", "", -5, 1005, "0.5", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, transfer timeout",
			ccvtypes.NewConsumerParams(true, 5, "", "", 1004, -7, "0.5", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, consumer redist fraction is negative",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "-0.5", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, consumer redist fraction is over 1",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "1.2", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, bad consumer redist fraction ",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "notFrac", 1000, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, negative num historical entries",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "0.5", -100, 24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, negative unbonding period",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "0.5", 1000, -24*21*time.Hour, "0.05"), false,
		},
		{
			"custom invalid params, soft opt out threshold is negative",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, "-0.05"), false,
		},
		{
			"custom invalid params, soft opt out threshold is over 0.2",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, "0.44"), false,
		},
		{
			"custom invalid params, bad soft opt out threshold ",
			ccvtypes.NewConsumerParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, "nickelback"), false,
		},
	}

	for _, tc := range testCases {
		err := tc.params.Validate()
		if tc.expPass {
			require.Nil(t, err, "expected error to be nil for test case: %s", tc.name)
		} else {
			require.NotNil(t, err, "expected error but got nil for test case: %s", tc.name)
		}
	}
}
