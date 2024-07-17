package keeper_test

import (
	"sort"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// Tests that IterateBondedValidatorsByPower returns the correct validators,
// namely the ones with most power, and stops when the max number of validators is reached.
func TestIterateBondedValidatorsByPower(t *testing.T) {
	tests := []struct {
		name           string
		maxValidators  int64
		powers         []int64
		expectedPowers []int64
	}{
		{
			name:           "no validators",
			maxValidators:  5,
			powers:         []int64{},
			expectedPowers: []int64{},
		},
		{
			name:           "validators less than max",
			maxValidators:  5,
			powers:         []int64{10, 20, 30},
			expectedPowers: []int64{10, 20, 30}, // get all validators back
		},
		{
			name:           "validators more than max",
			maxValidators:  2,
			powers:         []int64{10, 20, 30},
			expectedPowers: []int64{30, 20}, // get the top 2 validators back
		},
		{
			name:           "validators equal to max",
			maxValidators:  3,
			powers:         []int64{10, 20, 30},
			expectedPowers: []int64{30, 20, 10}, // get all validators back
		},
		{
			name:           "validators with equal powers",
			maxValidators:  3,
			powers:         []int64{10, 10, 10, 20, 20, 30, 30},
			expectedPowers: []int64{30, 30, 20}, // get the top 3 validators back
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
				})
			actualValPowers := []int64{}
			err := providerKeeper.IterateBondedValidatorsByPower(ctx, func(index int64, validator types.ValidatorI) (stop bool) {
				counter++
				actualValPowers = append(actualValPowers, validator.GetTokens().Int64())
				return false
			})
			require.NoError(t, err)
			// we don't check that the elements exactly match; just matching the powers is good enough
			require.ElementsMatch(t, tt.expectedPowers, actualValPowers)
		})
	}
}
