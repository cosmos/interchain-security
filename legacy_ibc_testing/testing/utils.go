package testing

import (
	"testing"

	abci "github.com/cometbft/cometbft/abci/types"
	tmtypes "github.com/cometbft/cometbft/types"
	"github.com/stretchr/testify/require"
)

/*
TODO: Remove after upgrading to ibc-go v5
legacy_ibc_testing is temporarily copied into the interchain-security repository for the purpose of testing only.
The integration test suites rely on modifications to ibc-go's test framework that cannot be back-ported to the canonical version that ics will rely on.
These files will be deprecated once ICS is able to upgrade to ibc-go v5.
*/

// ApplyValSetChanges takes in tmtypes.ValidatorSet and []abci.ValidatorUpdate and will return a new tmtypes.ValidatorSet which has the
// provided validator updates applied to the provided validator set.
func ApplyValSetChanges(t *testing.T, valSet *tmtypes.ValidatorSet, valUpdates []abci.ValidatorUpdate) *tmtypes.ValidatorSet {
	t.Helper()
	updates, err := tmtypes.PB2TM.ValidatorUpdates(valUpdates)
	require.NoError(t, err)

	// must copy since validator set will mutate with UpdateWithChangeSet
	newVals := valSet.Copy()
	err = newVals.UpdateWithChangeSet(updates)
	require.NoError(t, err)

	return newVals
}
