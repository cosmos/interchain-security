package keeper_test

import (
	"sort"
	"testing"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// TestStakingKeeperInterface tests
// * IterateBondedValidatorsByPower
// * TotalBondedTokens
// * BondedRatio
func TestStakingKeeperInterface(t *testing.T) {
	tests := []struct {
		name                string
		maxValidators       int64
		powers              []int64
		expectedPowers      []int64
		mockTotalSupply     int64
		expectedTotalBonded math.Int
		expectedBondedRatio math.LegacyDec
	}{
		{
			name:                "no validators",
			maxValidators:       5,
			powers:              []int64{},
			expectedPowers:      []int64{},
			mockTotalSupply:     100,
			expectedTotalBonded: math.ZeroInt(),
			expectedBondedRatio: math.LegacyZeroDec(),
		},
		{
			name:                "validators less than max",
			maxValidators:       5,
			powers:              []int64{10, 20, 30},
			expectedPowers:      []int64{10, 20, 30}, // get all validators back
			mockTotalSupply:     100,
			expectedTotalBonded: math.NewInt(60),
			expectedBondedRatio: math.LegacyNewDec(60).Quo(math.LegacyNewDec(100)), // 60% bonded
		},
		{
			name:            "validators more than max",
			maxValidators:   2,
			powers:          []int64{10, 20, 30},
			expectedPowers:  []int64{30, 20}, // get the top 2 validators back
			mockTotalSupply: 100,
			// 30 + 20 = 50
			expectedTotalBonded: math.NewInt(50),
			expectedBondedRatio: math.LegacyNewDec(50).Quo(math.LegacyNewDec(100)), // 50% bonded
		},
		{
			name:            "validators equal to max",
			maxValidators:   3,
			powers:          []int64{10, 20, 30},
			expectedPowers:  []int64{30, 20, 10}, // get all validators back
			mockTotalSupply: 60,
			// 30 + 20 + 10 = 60
			expectedTotalBonded: math.NewInt(60),
			expectedBondedRatio: math.LegacyNewDec(100).Quo(math.LegacyNewDec(100)), // 100% bonded
		},
		{
			name:            "validators with equal powers",
			maxValidators:   3,
			powers:          []int64{10, 10, 10, 20, 20, 30, 30},
			expectedPowers:  []int64{30, 30, 20}, // get the top 3 validators back
			mockTotalSupply: 1000,
			// 30 + 30 + 20 = 80
			expectedTotalBonded: math.NewInt(80),
			expectedBondedRatio: math.LegacyNewDec(8).Quo(math.LegacyNewDec(100)), // 8% bonded
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
			defer ctrl.Finish()

			counter := int64(0)
			vals, _ := createStakingValidatorsAndMocks(ctx, mocks, tt.powers...)

			params := providerKeeper.GetParams(ctx)
			params.MaxProviderConsensusValidators = tt.maxValidators
			providerKeeper.SetParams(ctx, params)

			// sort vals by descending number of tokens
			sort.Slice(
				vals,
				func(i, j int) bool {
					return vals[i].GetTokens().Int64() > vals[j].GetTokens().Int64()
				},
			)

			mocks.MockStakingKeeper.EXPECT().IterateBondedValidatorsByPower(gomock.Any(), gomock.Any()).DoAndReturn(
				func(ctx sdk.Context, cb func(int64, stakingtypes.ValidatorI) bool) error {
					for i, val := range vals {
						if stop := cb(int64(i), val); stop {
							break
						}
					}
					return nil
				}).AnyTimes()
			actualValPowers := []int64{}
			err := providerKeeper.IterateBondedValidatorsByPower(ctx, func(index int64, validator types.ValidatorI) (stop bool) {
				counter++
				actualValPowers = append(actualValPowers, validator.GetTokens().Int64())
				return false
			})
			require.NoError(t, err)
			// we don't check that the elements exactly match; just matching the powers is good enough
			require.ElementsMatch(t, tt.expectedPowers, actualValPowers)

			// check bonded ratio and total bonded
			mocks.MockStakingKeeper.EXPECT().StakingTokenSupply(gomock.Any()).Return(math.NewInt(tt.mockTotalSupply), nil).AnyTimes()

			totalBonded, err := providerKeeper.TotalBondedTokens(ctx)
			require.NoError(t, err)
			require.Equal(t, tt.expectedTotalBonded, totalBonded)

			bondedRatio, err := providerKeeper.BondedRatio(ctx)
			require.NoError(t, err)
			require.Equal(t, tt.expectedBondedRatio, bondedRatio)
		})
	}
}
