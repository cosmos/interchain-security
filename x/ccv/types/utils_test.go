package types_test

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/types"
)

func TestAccumulateChanges(t *testing.T) {
	_, testKeys, _ := ibctesting.GenerateKeys(t, 2)

	tmPubKey, _ := cryptocodec.ToTmProtoPublicKey(testKeys[0])
	tmPubKey2, _ := cryptocodec.ToTmProtoPublicKey(testKeys[1])

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
			require.ElementsMatch(t, tc.expected, changes)
		})
	}
}
