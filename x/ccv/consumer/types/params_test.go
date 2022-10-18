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
		{"custom valid params", consumertypes.NewParams(true, 5, "", "", 5), true},
		{"custom invalid params, block per dist transmission", consumertypes.NewParams(true, -5, "", "", 5), false},
		{"custom invalid params, dist transmission channel", consumertypes.NewParams(true, 5, "badchannel", "", 5), false},
		{"custom invalid params, provider fee pool addr string", consumertypes.NewParams(true, -5, "", "imabadaddress", 5), false},
		{"custom invalid params, ccv timeout", consumertypes.NewParams(true, 5, "", "", -5), false},
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
