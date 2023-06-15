package keeper_test

import (
	"testing"

	tmtypes "github.com/cometbft/cometbft/types"
	"github.com/stretchr/testify/require"

	"github.com/octopus-network/interchain-security/testutil/crypto"
	testkeeper "github.com/octopus-network/interchain-security/testutil/keeper"
	"github.com/octopus-network/interchain-security/x/ccv/consumer/types"
)

// Tests that UpdateSmallestNonOptOutPower updates the smallest validator power that cannot soft opt out.
// Soft opt out allows the bottom [SoftOptOutThreshold] portion of validators in the set to opt out.
// UpdateSmallestNonOptOutPower should update the smallest validator power that cannot opt out.
func TestUpdateSmallestNonOptOutPower(t *testing.T) {
	cIds := crypto.GenMultipleCryptoIds(7, 682934679238)

	testCases := []struct {
		name string
		// soft opt out threshold set as param
		optOutThresh string
		// validators to set in store
		validators []*tmtypes.Validator
		// expected smallest power of validator which cannot opt out
		expSmallestNonOptOutValPower int64
	}{
		{
			name:         "One",
			optOutThresh: "0.05",
			validators: []*tmtypes.Validator{
				tmtypes.NewValidator(cIds[0].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[1].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[2].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[3].TMCryptoPubKey(), 3),
				tmtypes.NewValidator(cIds[4].TMCryptoPubKey(), 49),
				tmtypes.NewValidator(cIds[5].TMCryptoPubKey(), 51),
			},
			// 107 total power, validator with 3 power passes 0.05 threshold (6 / 107 = 0.056) and cannot opt out
			expSmallestNonOptOutValPower: 3,
		},
		{
			name:         "One in different order",
			optOutThresh: "0.05",
			validators: []*tmtypes.Validator{
				tmtypes.NewValidator(cIds[0].TMCryptoPubKey(), 3),
				tmtypes.NewValidator(cIds[1].TMCryptoPubKey(), 51),
				tmtypes.NewValidator(cIds[2].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[3].TMCryptoPubKey(), 49),
				tmtypes.NewValidator(cIds[4].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[5].TMCryptoPubKey(), 1),
			},
			// Same result as first test case, just confirms order of validators doesn't matter
			expSmallestNonOptOutValPower: 3,
		},
		{
			name:         "Two",
			optOutThresh: "0.05",
			validators: []*tmtypes.Validator{
				tmtypes.NewValidator(cIds[0].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[1].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[2].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[3].TMCryptoPubKey(), 3),
				tmtypes.NewValidator(cIds[4].TMCryptoPubKey(), 500),
			},
			// 506 total power, validator with 500 passes 0.05 threshold and cannot opt out
			expSmallestNonOptOutValPower: 500,
		},
		{
			name:         "Three",
			optOutThresh: "0.199999",
			validators: []*tmtypes.Validator{
				tmtypes.NewValidator(cIds[0].TMCryptoPubKey(), 54),
				tmtypes.NewValidator(cIds[1].TMCryptoPubKey(), 53),
				tmtypes.NewValidator(cIds[2].TMCryptoPubKey(), 52),
				tmtypes.NewValidator(cIds[3].TMCryptoPubKey(), 51),
				tmtypes.NewValidator(cIds[4].TMCryptoPubKey(), 50),
				tmtypes.NewValidator(cIds[5].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[6].TMCryptoPubKey(), 1),
			},
			// 262 total power, (50 + 1 + 1) / 262 ~= 0.19, validator with 51 passes 0.199999 threshold and cannot opt out
			expSmallestNonOptOutValPower: 51,
		},
		{
			name:         "soft opt-out disabled",
			optOutThresh: "0",
			validators: []*tmtypes.Validator{
				tmtypes.NewValidator(cIds[0].TMCryptoPubKey(), 54),
				tmtypes.NewValidator(cIds[1].TMCryptoPubKey(), 53),
				tmtypes.NewValidator(cIds[2].TMCryptoPubKey(), 52),
				tmtypes.NewValidator(cIds[3].TMCryptoPubKey(), 51),
				tmtypes.NewValidator(cIds[4].TMCryptoPubKey(), 50),
				tmtypes.NewValidator(cIds[5].TMCryptoPubKey(), 1),
				tmtypes.NewValidator(cIds[6].TMCryptoPubKey(), 1),
			},
			expSmallestNonOptOutValPower: 0,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
			moduleParams := types.DefaultParams()
			moduleParams.SoftOptOutThreshold = tc.optOutThresh
			consumerKeeper.SetParams(ctx, moduleParams)
			defer ctrl.Finish()

			// set validators in store
			SetCCValidators(t, consumerKeeper, ctx, tc.validators)

			// update smallest power of validator which cannot opt out
			consumerKeeper.UpdateSmallestNonOptOutPower(ctx)

			// expect smallest power of validator which cannot opt out to be updated
			require.Equal(t, tc.expSmallestNonOptOutValPower, consumerKeeper.GetSmallestNonOptOutPower(ctx))
		})
	}
}
