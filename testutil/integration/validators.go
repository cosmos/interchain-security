package integration

import (
	"github.com/cosmos/cosmos-sdk/testutil/mock"

	"github.com/cometbft/cometbft/abci/types"
	tmencoding "github.com/cometbft/cometbft/crypto/encoding"
	tmtypes "github.com/cometbft/cometbft/types"
)

func CreateValidators(n int) (
	*tmtypes.ValidatorSet, []types.ValidatorUpdate, map[string]tmtypes.PrivValidator, error,
) {
	// generate validators private/public key
	var (
		validators       []*tmtypes.Validator
		signersByAddress = make(map[string]tmtypes.PrivValidator, n)
	)
	for i := 0; i < n; i++ {
		privVal := mock.NewPV()
		pubKey, err := privVal.GetPubKey()
		if err != nil {
			return nil, nil, nil, err
		}
		val := tmtypes.NewValidator(pubKey, 1)
		validators = append(validators, val)
		signersByAddress[pubKey.Address().String()] = privVal
	}
	// construct validator set;
	// Note that the validators are sorted by voting power
	// or, if equal, by address lexical order
	valSet := tmtypes.NewValidatorSet(validators)
	valUpdates, err := ToValidatorUpdates(valSet)
	return valSet, valUpdates, signersByAddress, err
}

func ToValidatorUpdates(valSet *tmtypes.ValidatorSet) (valUpdates []types.ValidatorUpdate, err error) {
	for _, val := range valSet.Validators {
		protoPubKey, err := tmencoding.PubKeyToProto(val.PubKey)
		valUpdates = append(valUpdates, types.ValidatorUpdate{
			PubKey: protoPubKey,
			Power:  val.VotingPower,
		})
		if err != nil {
			return nil, err
		}
	}
	return valUpdates, nil
}
