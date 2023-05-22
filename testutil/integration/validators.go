package integration

import (
	"testing"

	"github.com/cometbft/cometbft/abci/types"
	tmencoding "github.com/cometbft/cometbft/crypto/encoding"
	tmtypes "github.com/cometbft/cometbft/types"
	"github.com/cosmos/cosmos-sdk/testutil/mock"
	"github.com/stretchr/testify/require"
)

func CreateValidators(t *testing.T, n int) (
	*tmtypes.ValidatorSet, []types.ValidatorUpdate, map[string]tmtypes.PrivValidator,
) {
	// generate validators private/public key
	var (
		validators       []*tmtypes.Validator
		signersByAddress = make(map[string]tmtypes.PrivValidator, n)
	)
	for i := 0; i < n; i++ {
		privVal := mock.NewPV()
		pubKey, err := privVal.GetPubKey()
		require.NoError(t, err)
		val := tmtypes.NewValidator(pubKey, 1)
		validators = append(validators, val)
		signersByAddress[pubKey.Address().String()] = privVal
	}
	// construct validator set;
	// Note that the validators are sorted by voting power
	// or, if equal, by address lexical order
	valSet := tmtypes.NewValidatorSet(validators)
	return valSet, ToValidatorUpdates(t, valSet), signersByAddress
}

func ToValidatorUpdates(t *testing.T, valSet *tmtypes.ValidatorSet) (valUpdates []types.ValidatorUpdate) {
	for _, val := range valSet.Validators {
		protoPubKey, err := tmencoding.PubKeyToProto(val.PubKey)
		require.NoError(t, err)
		valUpdates = append(valUpdates, types.ValidatorUpdate{
			PubKey: protoPubKey,
			Power:  val.VotingPower,
		})
	}
	return
}
