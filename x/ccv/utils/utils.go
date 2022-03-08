package utils

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
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

// GetNewChanges returns the validator changes for whom their validator is not
// part of the validator set
func GetNewChanges(changes []abci.ValidatorUpdate, valset tmtypes.ValidatorSet) ([]abci.ValidatorUpdate, error) {
	newChanges := []abci.ValidatorUpdate{}
	for _, change := range changes {
		pk, err := cryptocodec.FromTmProtoPublicKey(change.PubKey)
		if err != nil {
			return nil, err
		}
		if !valset.HasAddress(pk.Address()) {
			newChanges = append(newChanges, change)
		}
	}

	return newChanges, nil
}

func ChangesToValset(changes []abci.ValidatorUpdate) (valset tmtypes.ValidatorSet, err error) {
	vals, err := tmtypes.PB2TM.ValidatorUpdates(changes)
	if err != nil {
		return
	}

	valset = *tmtypes.NewValidatorSet(vals)
	return
}
