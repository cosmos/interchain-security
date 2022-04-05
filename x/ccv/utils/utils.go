package utils

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	abci "github.com/tendermint/tendermint/abci/types"
)

func AccumulateChanges(currentChanges, newChanges []abci.ValidatorUpdate) []abci.ValidatorUpdate {
	m := make(map[string]abci.ValidatorUpdate)

	for i := 0; i < len(currentChanges); i++ {
		m[currentChanges[i].PubKey.String()] = currentChanges[i]
	}

	for i := 0; i < len(newChanges); i++ {
		m[newChanges[i].PubKey.String()] = newChanges[i]
	}

	var out []abci.ValidatorUpdate

	for _, update := range m {
		out = append(out, update)
	}
	return out
}

func GetChangePubKeyAddress(change abci.ValidatorUpdate) (addr []byte) {
	pk, err := cryptocodec.FromTmProtoPublicKey(change.PubKey)
	if err != nil {
		panic(err)
	}

	return pk.Address()
}
