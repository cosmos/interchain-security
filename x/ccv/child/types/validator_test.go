package types_test

import (
	"testing"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/ibc-go/testing/mock"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	"github.com/stretchr/testify/require"
	tmtypes "github.com/tendermint/tendermint/types"
)

func TestNewValidator(t *testing.T) {
	pubKey := ed25519.GenPrivKey().PubKey()
	expConsAddr := sdk.ConsAddress(pubKey.Address())
	votingPower := int64(1)

	// verify voting power
	val, err := types.NewValidator(pubKey, votingPower)
	require.NoError(t, err)
	require.NotZero(t, val)
	require.Equal(t, votingPower, val.VotingPower)

	// verify pubkey
	pk, err := val.ConsPubKey()
	require.NoError(t, err)
	require.EqualValues(t, pubKey.Bytes(), pk.Bytes())

	// verify consensus address
	consAddr, err := val.GetConsAddr()
	require.NoError(t, err)
	require.EqualValues(t, expConsAddr, consAddr)
}

func TestTmValidatorConversion(t *testing.T) {
	// create TM validator
	privVal := mock.NewPV()
	pubKey, err := privVal.GetPubKey()
	require.NoError(t, err)
	tmVal := tmtypes.NewValidator(pubKey, 1)

	// convert to module validator type
	val, err := types.FromTmValidator(*tmVal)
	require.NoError(t, err)
	require.NotNil(t, val)
	consAddr, err := val.GetConsAddr()
	require.NoError(t, err)
	require.EqualValues(t, sdk.ConsAddress(pubKey.Address()), consAddr)
	require.Equal(t, int64(1), val.VotingPower)

	// convert back and compare
	res, err := val.ToTmValidator()
	require.NoError(t, err)
	require.EqualValues(t, *tmVal, res)
}
