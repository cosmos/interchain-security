package keeper_test

import (
	"bytes"
	"errors"
	"sort"
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

// TestConsumerPowerShapingParameters tests the getter and setter of the consumer id to power-shaping parameters methods
func TestConsumerPowerShapingParameters(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "consumerId"
	consAddrs := []string{
		"cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
		"cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
		"cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
		"cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
		"cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
		"cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
	}
	providerConsAddr := []providertypes.ProviderConsAddress{}
	for _, addr := range consAddrs {
		ca, _ := sdk.ConsAddressFromBech32(addr)
		providerConsAddr = append(providerConsAddr, providertypes.NewProviderConsAddress(ca))
	}
	sortProviderConsAddr := func(consAddrs []providertypes.ProviderConsAddress) {
		sort.Slice(consAddrs, func(i, j int) bool {
			return bytes.Compare(consAddrs[i].Address, consAddrs[j].Address) < 0
		})
	}

	_, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.Error(t, err)
	require.True(t, errors.Is(err, ccvtypes.ErrStoreKeyNotFound))

	expectedPowerShapingParameters := providertypes.PowerShapingParameters{
		Top_N:              10,
		ValidatorsPowerCap: 34,
		ValidatorSetCap:    10,
		Allowlist:          []string{consAddrs[0], consAddrs[1]},
		Denylist:           []string{consAddrs[2], consAddrs[3]},
		MinStake:           234,
		AllowInactiveVals:  true,
	}
	expectedAllowlist := []providertypes.ProviderConsAddress{providerConsAddr[0], providerConsAddr[1]}
	sortProviderConsAddr(expectedAllowlist)
	expectedDenylist := []providertypes.ProviderConsAddress{providerConsAddr[2], providerConsAddr[3]}
	sortProviderConsAddr(expectedDenylist)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, expectedPowerShapingParameters)
	require.NoError(t, err)
	actualPowerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))

	// assert that overwriting the current initialization record works
	expectedPowerShapingParameters = providertypes.PowerShapingParameters{
		Top_N:              12,
		ValidatorsPowerCap: 67,
		ValidatorSetCap:    20,
		Allowlist:          []string{consAddrs[4], consAddrs[5]},
		Denylist:           []string{consAddrs[2], consAddrs[3]},
		MinStake:           567,
		AllowInactiveVals:  false,
	}
	expectedAllowlist = []providertypes.ProviderConsAddress{providerConsAddr[4], providerConsAddr[5]}
	sortProviderConsAddr(expectedAllowlist)
	expectedDenylist = []providertypes.ProviderConsAddress{providerConsAddr[2], providerConsAddr[3]}
	sortProviderConsAddr(expectedDenylist)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, expectedPowerShapingParameters)
	require.NoError(t, err)
	actualPowerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))
}

// TestAllowlist tests the `SetAllowlist`, `IsAllowlisted`, `DeleteAllowlist`, and `IsAllowlistEmpty` methods
func TestAllowlist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "consumerId"

	// no validator was allowlisted and hence the allowlist is empty
	require.True(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))

	providerAddr1 := providertypes.NewProviderConsAddress([]byte("providerAddr1"))
	providerKeeper.SetAllowlist(ctx, chainID, providerAddr1)
	require.True(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr1))

	// allowlist is not empty anymore
	require.False(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))

	providerAddr2 := providertypes.NewProviderConsAddress([]byte("providerAddr2"))
	providerKeeper.SetAllowlist(ctx, chainID, providerAddr2)
	require.True(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr2))
	require.False(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))

	providerKeeper.DeleteAllowlist(ctx, chainID)
	require.False(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr1))
	require.False(t, providerKeeper.IsAllowlisted(ctx, chainID, providerAddr2))
	require.True(t, providerKeeper.IsAllowlistEmpty(ctx, chainID))
}

func TestUpdateAllowlist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	providerConsAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr1, _ := sdk.ConsAddressFromBech32(providerConsAddr1)
	providerConsAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr2, _ := sdk.ConsAddressFromBech32(providerConsAddr2)

	providerKeeper.UpdateAllowlist(ctx, consumerId, []string{providerConsAddr1, providerConsAddr2})

	expectedAllowlist := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(consAddr1),
		providertypes.NewProviderConsAddress(consAddr2),
	}
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
}

// TestDenylist tests the `SetDenylist`, `IsDenylisted`, `DeleteDenylist`, and `IsDenylistEmpty` methods
func TestDenylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "consumerId"

	// no validator was denylisted and hence the denylist is empty
	require.True(t, providerKeeper.IsDenylistEmpty(ctx, chainID))

	providerAddr1 := providertypes.NewProviderConsAddress([]byte("providerAddr1"))
	providerKeeper.SetDenylist(ctx, chainID, providerAddr1)
	require.True(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr1))

	// denylist is not empty anymore
	require.False(t, providerKeeper.IsDenylistEmpty(ctx, chainID))

	providerAddr2 := providertypes.NewProviderConsAddress([]byte("providerAddr2"))
	providerKeeper.SetDenylist(ctx, chainID, providerAddr2)
	require.True(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr2))
	require.False(t, providerKeeper.IsDenylistEmpty(ctx, chainID))

	providerKeeper.DeleteDenylist(ctx, chainID)
	require.False(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr1))
	require.False(t, providerKeeper.IsDenylisted(ctx, chainID, providerAddr2))
	require.True(t, providerKeeper.IsDenylistEmpty(ctx, chainID))
}

func TestUpdateDenylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	providerConsAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr1, _ := sdk.ConsAddressFromBech32(providerConsAddr1)
	providerConsAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr2, _ := sdk.ConsAddressFromBech32(providerConsAddr2)

	providerKeeper.UpdateDenylist(ctx, consumerId, []string{providerConsAddr1, providerConsAddr2})

	expectedDenylist := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(consAddr1),
		providertypes.NewProviderConsAddress(consAddr2),
	}
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))
}

// Tests setting, getting and deleting parameters that are stored per-consumer chain.
// The tests cover the following parameters:
// - MinimumPowerInTopN
func TestKeeperConsumerParams(t *testing.T) {
	k, ctx, _, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

	tests := []struct {
		name         string
		settingFunc  func(sdk.Context, string, int64)
		getFunc      func(sdk.Context, string) int64
		deleteFunc   func(sdk.Context, string)
		initialValue int64
		updatedValue int64
	}{
		{
			name:        "Minimum Power In Top N",
			settingFunc: func(ctx sdk.Context, id string, val int64) { k.SetMinimumPowerInTopN(ctx, id, val) },
			getFunc: func(ctx sdk.Context, id string) int64 {
				minimumPowerInTopN, _ := k.GetMinimumPowerInTopN(ctx, id)
				return minimumPowerInTopN
			},
			deleteFunc:   func(ctx sdk.Context, id string) { k.DeleteMinimumPowerInTopN(ctx, id) },
			initialValue: 1000,
			updatedValue: 2000,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			chainID := "consumerId"
			// Set initial value
			tt.settingFunc(ctx, chainID, int64(tt.initialValue))

			// Retrieve and check initial value
			actualValue := tt.getFunc(ctx, chainID)
			require.EqualValues(t, tt.initialValue, actualValue)

			// Update value
			tt.settingFunc(ctx, chainID, int64(tt.updatedValue))

			// Retrieve and check updated value
			newActualValue := tt.getFunc(ctx, chainID)
			require.EqualValues(t, tt.updatedValue, newActualValue)

			// Check non-existent consumer id
			res := tt.getFunc(ctx, "not the consumerId")
			require.Zero(t, res)

			// Delete value
			tt.deleteFunc(ctx, chainID)

			// Check that value was deleted
			res = tt.getFunc(ctx, chainID)
			require.Zero(t, res)

			// Try deleting again
			tt.deleteFunc(ctx, chainID)

			// Check that the value is still deleted
			res = tt.getFunc(ctx, chainID)
			require.Zero(t, res)
		})
	}
}

func TestUpdateMinimumPowerInTopN(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	// test case where Top N is 0 in which case there's no minimum power in top N
	err := providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 0,
	})
	require.NoError(t, err)

	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 0, 0)
	require.NoError(t, err)
	_, found := providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.False(t, found)

	// test cases where Top N > 0 and for this we mock some validators
	powers := []int64{10, 20, 30}
	validators := []stakingtypes.Validator{
		createStakingValidator(ctx, mocks, powers[0], 1), // this validator has ~16 of the total voting power
		createStakingValidator(ctx, mocks, powers[1], 2), // this validator has ~33% of the total voting gpower
		createStakingValidator(ctx, mocks, powers[2], 3), // this validator has 50% of the total voting power
	}
	mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(gomock.Any()).Return(validators, nil).AnyTimes()

	maxProviderConsensusValidators := int64(3)
	params := providerKeeper.GetParams(ctx)
	params.MaxProviderConsensusValidators = maxProviderConsensusValidators
	providerKeeper.SetParams(ctx, params)

	// when top N is 50, the minimum power is 30 (because top validator has to validate)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 50,
	})
	require.NoError(t, err)
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 0, 50)
	require.NoError(t, err)
	minimumPowerInTopN, found := providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(30), minimumPowerInTopN)

	// when top N is 51, the minimum power is 20 (because top 2 validators have to validate)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 51,
	})
	require.NoError(t, err)
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 50, 51)
	require.NoError(t, err)
	minimumPowerInTopN, found = providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(20), minimumPowerInTopN)

	// when top N is 100, the minimum power is 10 (that of the validator with the lowest power)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 100,
	})
	require.NoError(t, err)
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 51, 100)
	require.NoError(t, err)
	minimumPowerInTopN, found = providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(10), minimumPowerInTopN)
}
