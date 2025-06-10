package keeper_test

import (
	"testing"

	crypto2 "github.com/cometbft/cometbft/v2/crypto"
	"github.com/cometbft/cometbft/v2/crypto/encoding"
	"github.com/cosmos/cosmos-sdk/crypto/keys"
	"github.com/stretchr/testify/require"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/v2/abci/types"

	"github.com/cosmos/interchain-security/v7/testutil/crypto"
	uthelpers "github.com/cosmos/interchain-security/v7/testutil/keeper"
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

	pks := make([]crypto2.PubKey, 0, len(cIds))
	for _, ci := range cIds {
		pk, err := encoding.PubKeyFromProto(ci.TMProtoCryptoPublicKey())
		require.NoError(t, err)
		pks = append(pks, pk)
	}
	// Instantiate 5 ics val updates for use in test
	initialValUpdates := []abci.ValidatorUpdate{
		{Power: 55, PubKeyBytes: pks[5].Bytes(), PubKeyType: pks[5].Type()},
		{Power: 87324, PubKeyBytes: pks[6].Bytes(), PubKeyType: pks[6].Type()},
		{Power: 2, PubKeyBytes: pks[7].Bytes(), PubKeyType: pks[7].Type()},
		{Power: 42389479, PubKeyBytes: pks[8].Bytes(), PubKeyType: pks[8].Type()},
		{Power: 9089080, PubKeyBytes: pks[9].Bytes(), PubKeyType: pks[9].Type()},
	}

	testCases := []struct {
		name string
		// Last standalone validators that will be mock returned from consumerKeeper.GetLastBondedValidators()
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
				{Power: 55, PubKeyType: pks[7].Type(), PubKeyBytes: pks[7].Bytes()},
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

		// Setup mocked return value for consumerkeeper.GetLastBondedValidators()
		uthelpers.SetupMocksForLastBondedValidatorsExpectation(
			mocks.MockStakingKeeper,
			180, // max validators
			tc.lastSovVals,
			-1) // any times

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
				require.NoError(t, err)
				valPk, err := keys.PubKeyFromCometTypeAndBytes(valUpdate.PubKeyType, valUpdate.PubKeyBytes)
				require.NoError(t, err)
				if ccvValPubKey.Equals(valPk) {
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
				returnedValPK, err := encoding.PubKeyFromTypeAndBytes(returnedValUpdate.PubKeyType, returnedValUpdate.PubKeyBytes)
				require.NoError(t, err)
				returnedValPkProto, err := encoding.PubKeyToProto(returnedValPK)
				require.NoError(t, err)

				valUpdatePK, err := encoding.PubKeyFromTypeAndBytes(valUpdate.PubKeyType, valUpdate.PubKeyBytes)
				require.NoError(t, err)
				valUpdatePkProto, err := encoding.PubKeyToProto(valUpdatePK)

				if returnedValPkProto.Equal(valUpdatePkProto) {
					require.Equal(t, valUpdate.Power, returnedValUpdate.Power)
					found = true
				}
			}
			// Check all standalone validators for a pubkey match
			for _, val := range tc.lastSovVals {
				ccvValPubKey, err := val.ConsPubKey()
				require.NoError(t, err)
				tmProtoPubKey, err := sdkcryptocodec.ToCmtProtoPublicKey(ccvValPubKey)
				require.NoError(t, err)

				pk, err := encoding.PubKeyFromTypeAndBytes(returnedValUpdate.PubKeyType, returnedValUpdate.PubKeyBytes)
				require.NoError(t, err)
				returnedValPk, err := encoding.PubKeyToProto(pk)
				require.NoError(t, err)

				if returnedValPk.Equal(tmProtoPubKey) {
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
