package types_test

import (
	"testing"

	core "github.com/cosmos/interchain-security/core"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
)

func TestAccumulateChanges(t *testing.T) {

	tmPubKey := core.NewCryptoIdentityFromIntSeed(73489243).TMProtoCryptoPublicKey()
	tmPubKey2 := core.NewCryptoIdentityFromIntSeed(73489244).TMProtoCryptoPublicKey()

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
			changes := core.AccumulateChanges(tc.changes1, tc.changes2)
			require.Equal(t, tc.expected, changes)
		})
	}
}
