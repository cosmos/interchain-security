package types_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestValidateParams(t *testing.T) {

	testCases := []struct {
		name    string
		params  types.Params
		expPass bool
	}{
		{"default params", types.DefaultParams(), true},
		{"custom valid params", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			3, time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", 100), true},
		{"custom invalid params", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			0, clienttypes.Height{}, nil, []string{"ibc", "upgradedIBCState"}, true, false),
			3, time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", 100), false},
		{"blank client", types.NewParams(&ibctmtypes.ClientState{},
			3, time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", 100), false},
		{"nil client", types.NewParams(nil, 3, time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", 100), false},
		{"0 trusting period fraction (denominator)", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			0, time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", 100), false},
		{"0 ccv timeout period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			3, 0, time.Hour, time.Hour, 30*time.Minute, "0.1", 100), false},
		{"0 init timeout period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			3, time.Hour, 0, time.Hour, 30*time.Minute, "0.1", 100), false},
		{"0 vsc timeout period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			3, time.Hour, time.Hour, 0, 30*time.Minute, "0.1", 100), false},
		{"0 slash meter replenish period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			3, time.Hour, time.Hour, 24*time.Hour, 0, "0.1", 100), false},
		{"slash meter replenish fraction over 1", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			3, time.Hour, time.Hour, 24*time.Hour, time.Hour, "1.5", 100), false},
		{"negative max pending slash packets", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false),
			3, time.Hour, time.Hour, 24*time.Hour, time.Hour, "0.1", -100), false},
	}

	for _, tc := range testCases {
		err := tc.params.Validate()
		if tc.expPass {
			require.Nil(t, err, "expected error to be nil for testcase: %s", tc.name)
		} else {
			require.NotNil(t, err, "expected error but got nil for testcase: %s", tc.name)
		}
	}
}
