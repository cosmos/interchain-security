package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v3/testutil/crypto"
	uthelpers "github.com/cosmos/interchain-security/v3/testutil/keeper"
)

func TestChangeoverToConsumer(t *testing.T) {
	cIds := []crypto.CryptoIdentity{}
	for i := 0; i < 10; i++ {
		cIds = append(cIds, *crypto.NewCryptoIdentityFromIntSeed(i + 42834729))
	}

	// Instantiate 5 sov validators for use in test
	sovVals := []stakingtypes.Validator{
		cIds[0].SDKStakingValidator(),
		cIds[1].SDKStakingValidator(),
		cIds[2].SDKStakingValidator(),
		cIds[3].SDKStakingValidator(),
		cIds[4].SDKStakingValidator(),
	}

	// Instantiate 5 ics val updates for use in test
	initialValUpdates := []abci.ValidatorUpdate{
		{Power: 55, PubKey: cIds[5].TMProtoCryptoPublicKey()},
		{Power: 87324, PubKey: cIds[6].TMProtoCryptoPublicKey()},
		{Power: 2, PubKey: cIds[7].TMProtoCryptoPublicKey()},
		{Power: 42389479, PubKey: cIds[8].TMProtoCryptoPublicKey()},
		{Power: 9089080, PubKey: cIds[9].TMProtoCryptoPublicKey()},
	}

	testCases := []struct {
		name string
		// Last standalone validators that will be mock returned from stakingKeeper.GetLastValidators()
		lastSovVals []stakingtypes.Validator
		// Val updates corresponding to initial valset set for ccv set initGenesis
		initialValUpdates []abci.ValidatorUpdate
		// Expected length of val updates returned from ChangeoverToConsumer()
		expectedReturnValUpdatesLen int
	}{
		{
			name:                        "no sov vals, no initial val updates",
			lastSovVals:                 []stakingtypes.Validator{},
			initialValUpdates:           []abci.ValidatorUpdate{},
			expectedReturnValUpdatesLen: 0,
		},
		{
			name:                        "one sov val, no initial val updates",
			lastSovVals:                 []stakingtypes.Validator{sovVals[0]},
			initialValUpdates:           []abci.ValidatorUpdate{},
			expectedReturnValUpdatesLen: 1,
		},
		{
			name:                        "no sov vals, one initial val update",
			lastSovVals:                 []stakingtypes.Validator{},
			initialValUpdates:           []abci.ValidatorUpdate{initialValUpdates[0]},
			expectedReturnValUpdatesLen: 1,
		},
		{
			name:                        "one sov val, one initial val update",
			lastSovVals:                 []stakingtypes.Validator{sovVals[0]},
			initialValUpdates:           []abci.ValidatorUpdate{initialValUpdates[0]},
			expectedReturnValUpdatesLen: 2,
		},
		{
			name:                        "five sov vals, five initial val updates",
			lastSovVals:                 sovVals,
			initialValUpdates:           initialValUpdates,
			expectedReturnValUpdatesLen: 10,
		},
		{
			name:        "validator is contained in both sov val set and initial val updates, using cIds[7]",
			lastSovVals: []stakingtypes.Validator{cIds[7].SDKStakingValidator()},
			initialValUpdates: []abci.ValidatorUpdate{
				{Power: 55, PubKey: cIds[7].TMProtoCryptoPublicKey()},
			},
			expectedReturnValUpdatesLen: 1,
		},
	}

	for _, tc := range testCases {

		keeperParams := uthelpers.NewInMemKeeperParams(t)
		consumerKeeper, ctx, ctrl, mocks := uthelpers.GetConsumerKeeperAndCtx(t, keeperParams)
		defer ctrl.Finish()

		// Set PRECCV to true, as would be done in InitGenesis
		consumerKeeper.SetPreCCVTrue(ctx)

		// Set initial valset, as would be done in InitGenesis
		consumerKeeper.SetInitialValSet(ctx, tc.initialValUpdates)

		// Setup mocked return value for stakingKeeper.GetLastValidators()
		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().GetLastValidators(ctx).Return(tc.lastSovVals, nil),
		)

		// Add ref to standalone staking keeper
		consumerKeeper.SetStandaloneStakingKeeper(mocks.MockStakingKeeper)

		returnedInitialValUpdates := consumerKeeper.ChangeoverToConsumer(ctx)

		// PreCCV should now be toggled false
		require.False(t, consumerKeeper.IsPreCCV(ctx))

		// Cross chain validator states should be populated with initial valset
		ccVals := consumerKeeper.GetAllCCValidator(ctx)
		require.Len(t, ccVals, len(tc.initialValUpdates))

		// For each initial val update, assert that a corresponding ccVal entry exists
		// with the same power and pubkey
		for _, valUpdate := range tc.initialValUpdates {
			found := false
			for _, ccVal := range ccVals {
				ccvValPubKey, err := ccVal.ConsPubKey()
				require.NoError(t, err)
				tmProtoPubKey, err := sdkcryptocodec.ToTmProtoPublicKey(ccvValPubKey)
				require.NoError(t, err)
				if tmProtoPubKey.Equal(valUpdate.PubKey) {
					found = true
					require.Equal(t, valUpdate.Power, ccVal.Power)
				}
			}
			require.True(t, found)
		}

		// Assert that initial val updates returned from ChangeoverToConsumer are formulated s.t.
		// the "old" validators returned from standalone chain's staking module
		// are given zero power, and the "new" validators are given their full power.
		for _, returnedValUpdate := range returnedInitialValUpdates {
			found := false
			// Check all initial val updates for a pubkey match
			for _, valUpdate := range tc.initialValUpdates {
				if returnedValUpdate.PubKey.Equal(valUpdate.PubKey) {
					require.Equal(t, valUpdate.Power, returnedValUpdate.Power)
					found = true
				}
			}
			// Check all standalone validators for a pubkey match
			for _, val := range tc.lastSovVals {
				ccvValPubKey, err := val.ConsPubKey()
				require.NoError(t, err)
				tmProtoPubKey, err := sdkcryptocodec.ToTmProtoPublicKey(ccvValPubKey)
				require.NoError(t, err)
				if returnedValUpdate.PubKey.Equal(tmProtoPubKey) {
					// If val was already matched to a val update for new set, it's power won't be 0
					if found {
						continue
					}
					// Assert power of the val update is zero
					require.Equal(t, int64(0), returnedValUpdate.Power)
					found = true
				}
			}
			// Assert that a match was found
			require.True(t, found)
		}

		// Assert no extraneous entries
		require.Len(t, returnedInitialValUpdates, tc.expectedReturnValUpdatesLen)
	}
}
