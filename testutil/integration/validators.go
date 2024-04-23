package integration

import (
<<<<<<< HEAD
=======
	"fmt"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	"github.com/cosmos/cosmos-sdk/testutil/mock"

>>>>>>> main
	"github.com/cometbft/cometbft/abci/types"
	tmencoding "github.com/cometbft/cometbft/crypto/encoding"
	tmtypes "github.com/cometbft/cometbft/types"
)

// CreateValidators creates a set of validators for testing purposes
// and returns the validator set, validator updates, and a map of signers by address
// n is the number of validators to create
// chainId is the chain id to use for the private keys. it is only important to get different private keys
// for different chains, so it is fine to not have this chainId match the chainId in the context where the
// validators will be used, but the same string shouldn't be repeated across different invocations of this in the same scope.
func CreateValidators(n int, chainId string) (
	*tmtypes.ValidatorSet, []types.ValidatorUpdate, map[string]tmtypes.PrivValidator, error,
) {
	// generate validators private/public key
	var (
		validators       []*tmtypes.Validator
		signersByAddress = make(map[string]tmtypes.PrivValidator, n)
	)
	for i := 0; i < n; i++ {
		// privVal := tmtypes.NewMockPV()
		privVal := mock.PV{PrivKey: ed25519.GenPrivKeyFromSecret([]byte(chainId + fmt.Sprint(i)))}
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
