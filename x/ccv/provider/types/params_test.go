package types_test

import (
	"testing"
	"time"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v8/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

func TestValidateParams(t *testing.T) {
	testCases := []struct {
		name    string
		params  types.Params
		expPass bool
	}{
		{"default params", types.DefaultParams(), true},
		{"custom valid params", types.NewParams(
			ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
				time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), true},
		{"custom invalid params", types.NewParams(
			ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
				0, clienttypes.Height{}, nil, []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		{"blank client", types.NewParams(&ibctmtypes.ClientState{},
			"0.33", time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		{"nil client", types.NewParams(nil, "0.33", time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		// Check if "0.00" is valid or if a zero dec TrustFraction needs to return an error
		{"0 trusting period fraction", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.00", time.Hour, time.Hour, time.Hour, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), true},
		{"0 ccv timeout period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", 0, time.Hour, time.Hour, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		{"0 init timeout period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, 0, time.Hour, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		{"0 vsc timeout period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, time.Hour, 0, 30*time.Minute, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		{"0 slash meter replenish period", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, time.Hour, 24*time.Hour, 0, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		{"slash meter replenish fraction over 1", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, time.Hour, 24*time.Hour, time.Hour, "1.5", sdk.Coin{Denom: "stake", Amount: math.NewInt(10000000)}, 1000), false},
		{"invalid consumer reward denom registration fee denom", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, time.Hour, 24*time.Hour, time.Hour, "0.1", sdk.Coin{Denom: "st", Amount: math.NewInt(10000000)}, 1000), false},
		{"invalid consumer reward denom registration fee amount", types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}),
			"0.33", time.Hour, time.Hour, 24*time.Hour, time.Hour, "0.1", sdk.Coin{Denom: "stake", Amount: math.NewInt(-10000000)}, 1000), false},
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
