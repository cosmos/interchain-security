package types_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// Tests the validation of consumer params that happens at genesis
func TestValidateParams(t *testing.T) {
	consumerId := "13"
	testCases := []struct {
		name    string
		params  ccvtypes.ConsumerParams
		expPass bool
	}{
		{"default params", ccvtypes.DefaultParams(), true},
		{
			"custom valid params",
			ccvtypes.NewParams(true, 5, "", "", 1004, 1005, "0.5", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), true,
		},
		{
			"custom invalid params, block per dist transmission",
			ccvtypes.NewParams(true, -5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, dist transmission channel",
			ccvtypes.NewParams(true, 5, "badchannel/", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, ccv timeout",
			ccvtypes.NewParams(true, 5, "", "", -5, 1005, "0.5", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, transfer timeout",
			ccvtypes.NewParams(true, 5, "", "", 1004, -7, "0.5", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, consumer redist fraction is negative",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "-0.5", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, consumer redist fraction is over 1",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "1.2", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, bad consumer redist fraction ",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "notFrac", 1000, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, negative num historical entries",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", -100, 24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, negative unbonding period",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, -24*21*time.Hour, []string{"untrn"}, []string{"uatom"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, invalid reward denom",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{"u"}, []string{}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, invalid provider reward denom",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{}, []string{"a"}, 2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, retry delay period is negative",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{}, []string{}, -2*time.Hour, consumerId), false,
		},
		{
			"custom invalid params, retry delay period is zero",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{}, []string{}, 0, consumerId), false,
		},
		{
			"custom invalid params, consumer ID is blank",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{}, []string{}, time.Hour, ""), false,
		},
		{
			"custom invalid params, consumer ID is not a uint64",
			ccvtypes.NewParams(true, 5, "", "", 5, 1005, "0.5", 1000, 24*21*time.Hour, []string{}, []string{}, time.Hour, "consumerId"), false,
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
