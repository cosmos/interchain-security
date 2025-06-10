package types_test

import (
	"testing"

	"github.com/cometbft/cometbft/v2/crypto/encoding"
	ibctesting "github.com/cosmos/ibc-go/v10/testing"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/cometbft/cometbft/v2/abci/types"

	"github.com/cosmos/interchain-security/v7/x/ccv/types"
)

func TestAccumulateChanges(t *testing.T) {
	_, testKeys, _ := ibctesting.GenerateKeys(t, 2)

	tmPubKey, _ := cryptocodec.ToCmtProtoPublicKey(testKeys[0])
	pk1, err := encoding.PubKeyFromProto(tmPubKey)
	require.NoError(t, err)

	tmPubKey2, _ := cryptocodec.ToCmtProtoPublicKey(testKeys[1])
	pk2, err := encoding.PubKeyFromProto(tmPubKey2)
	require.NoError(t, err)

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
				{PubKeyBytes: pk1.Bytes(), PubKeyType: pk1.Type(), Power: 1},
			},
			changes2: []abci.ValidatorUpdate{},
			expected: []abci.ValidatorUpdate{
				{PubKeyType: pk1.Type(), PubKeyBytes: pk1.Bytes(), Power: 1},
			},
		},
		{
			name: "two changes",
			changes1: []abci.ValidatorUpdate{
				{PubKeyBytes: pk1.Bytes(), PubKeyType: pk1.Type(), Power: 1},
			},
			changes2: []abci.ValidatorUpdate{
				{PubKeyBytes: pk1.Bytes(), PubKeyType: pk1.Type(), Power: 2},
			},
			expected: []abci.ValidatorUpdate{
				{PubKeyBytes: pk1.Bytes(), PubKeyType: pk1.Type(), Power: 2},
			},
		},
		{
			name: "two changes with different pubkeys",
			changes1: []abci.ValidatorUpdate{
				{PubKeyType: pk1.Type(), PubKeyBytes: pk1.Bytes(), Power: 1},
			},
			changes2: []abci.ValidatorUpdate{
				{PubKeyBytes: pk2.Bytes(), PubKeyType: pk2.Type(), Power: 2},
			},
			expected: []abci.ValidatorUpdate{
				{PubKeyType: pk2.Type(), PubKeyBytes: pk2.Bytes(), Power: 2},
				{PubKeyBytes: pk1.Bytes(), PubKeyType: pk1.Type(), Power: 1},
			},
		},
		{
			name: "two changes with different pubkeys and same power",
			changes1: []abci.ValidatorUpdate{
				{PubKeyBytes: pk1.Bytes(), PubKeyType: pk1.Type(), Power: 1},
			},
			changes2: []abci.ValidatorUpdate{
				{PubKeyType: pk2.Type(), PubKeyBytes: pk2.Bytes(), Power: 1},
			},
			expected: []abci.ValidatorUpdate{
				{PubKeyBytes: pk2.Bytes(), PubKeyType: pk2.Type(), Power: 1},
				{PubKeyType: pk1.Type(), PubKeyBytes: pk1.Bytes(), Power: 1},
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
