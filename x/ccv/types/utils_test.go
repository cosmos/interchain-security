package types_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/x/types"
	ututil "github.com/cosmos/interchain-security/x/types/unit_test_util"
)

func TestAccumulateChanges(t *testing.T) {

	cId1 := ututil.NewCryptoIdentityFromIntSeed(1)
	cId2 := ututil.NewCryptoIdentityFromIntSeed(2)

	tmPubKey := cId1.TMProtoCryptoPublicKey()
	tmPubKey2 := cId2.TMProtoCryptoPublicKey()

	testCases := []struct {
		name     string
		changes1 []abci.ValidatorUpdate
		changes2 []abci.ValidatorUpdate
		expected []abci.ValidatorUpdate
	}{
		{
			name:     "no changes",
			changes1: []abci.ValidatorUpdate{},
			changes2: []abci.ValidatorUpdate{},
			expected: []abci.ValidatorUpdate(nil),
		},
		{
			name: "one change",
			changes1: []abci.ValidatorUpdate{
				{PubKey: tmPubKey, Power: 1},
			},
			changes2: []abci.ValidatorUpdate{},
			expected: []abci.ValidatorUpdate{
				{PubKey: tmPubKey, Power: 1},
			},
		},
		{
			name: "two changes",
			changes1: []abci.ValidatorUpdate{
				{PubKey: tmPubKey, Power: 1},
			},
			changes2: []abci.ValidatorUpdate{
				{PubKey: tmPubKey, Power: 2},
			},
			expected: []abci.ValidatorUpdate{
				{PubKey: tmPubKey, Power: 2},
			},
		},
		{
			name: "two changes with different pubkeys",
			changes1: []abci.ValidatorUpdate{
				{PubKey: tmPubKey, Power: 1},
			},
			changes2: []abci.ValidatorUpdate{
				{PubKey: tmPubKey2, Power: 2},
			},
			expected: []abci.ValidatorUpdate{
				{PubKey: tmPubKey2, Power: 2},
				{PubKey: tmPubKey, Power: 1},
			},
		},
		{
			name: "two changes with different pubkeys and same power",
			changes1: []abci.ValidatorUpdate{
				{PubKey: tmPubKey, Power: 1},
			},
			changes2: []abci.ValidatorUpdate{
				{PubKey: tmPubKey2, Power: 1},
			},
			expected: []abci.ValidatorUpdate{
				{PubKey: tmPubKey2, Power: 1},
				{PubKey: tmPubKey, Power: 1},
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			changes := types.AccumulateChanges(tc.changes1, tc.changes2)
			require.Equal(t, tc.expected, changes)
		})
	}
}
