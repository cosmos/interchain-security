package types_test

import (
	"testing"

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
		{"custom valid params", consumertypes.NewParams(true, 5, "", "", 1004, 1005, "0.5", 1000), true},
		{"custom invalid params, block per dist transmission",
			consumertypes.NewParams(true, -5, "", "", 1004, 1005, "0.5", 1000), false},
		{"custom invalid params, ccv timeout",
			consumertypes.NewParams(true, 5, "", "", -5, 1005, "0.5", 1000), false},
		{"custom invalid params, transfer timeout",
			consumertypes.NewParams(true, 5, "", "", 1004, -7, "0.5", 1000), false},
		{"custom invalid params, consumer redist fraction is negative",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "-0.5", 1000), false},
		{"custom invalid params, consumer redist fraction is over 1",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "1.2", 1000), false},
		{"custom invalid params, consumer redist fraction rubbish",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "rubbish", 1000), false},
		{"custom invalid params, negative num historical entries",
			consumertypes.NewParams(true, 5, "", "", 5, 1005, "rubbish", -100), false},
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
