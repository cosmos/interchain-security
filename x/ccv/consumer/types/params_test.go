package types_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// Tests the validation of consumer params that happens at genesis
func TestValidateParams(t *testing.T) {

	testCases := []struct {
		name    string
		params  consumertypes.Params
		expPass bool
	}{
		{"default params", consumertypes.DefaultParams(), true},
		{"custom valid params",
			consumertypes.NewParams(true, 5, "", "", 1004, 1005, "0.5", 1000, 24*21*time.Hour), true},
		{"custom invalid params, block per dist transmission",
			consumertypes.NewParams(true, -5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour), false},
		{"custom invalid params, dist transmission channel",
			consumertypes.NewParams(true, 5, "badchannel/", "", 5, 1005, "0.5", 1000, 24*21*time.Hour), false},
		{"custom invalid params, provider fee pool addr string",
			consumertypes.NewParams(true, 5, "", "imabadaddress", 5, 1005, "0.5", 1000, 24*21*time.Hour), false},
		{"custom invalid params, ccv timeout",
			consumertypes.NewParams(true, 5, "", "", -5, 1005, "0.5", 1000, 24*21*time.Hour), false},
		{"custom invalid params, transfer timeout",
			consumertypes.NewParams(true, 5, "", "", 1004, -7, "0.5", 1000, 24*21*time.Hour), false},
		{"custom invalid params, consumer redist fraction is negative",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "-0.5", 1000, 24*21*time.Hour), false},
		{"custom invalid params, consumer redist fraction is over 1",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "1.2", 1000, 24*21*time.Hour), false},
		{"custom invalid params, bad consumer redist fraction ",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "notFrac", 1000, 24*21*time.Hour), false},
		{"custom invalid params, negative num historical entries",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "0.5", -100, 24*21*time.Hour), false},
		{"custom invalid params, negative unbonding period",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, -24*21*time.Hour), false},
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
