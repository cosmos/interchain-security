package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	cryptotestutil "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/stretchr/testify/require"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type assignedKeys struct {
	chainID        string
	providerAddr   sdk.ConsAddress
	consumerPubKey tmprotocrypto.PublicKey
}

func TestSetAndGetValidatorConsumerPubKey(t *testing.T) {
	chainID := "consumer"
	providerAddr := sdk.ConsAddress([]byte("providerAddr"))
	consumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	keeper.SetValidatorConsumerPubKey(ctx, chainID, providerAddr, consumerKey)

	consumerPubKey, found := keeper.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	require.True(t, found, "consumer pubkey not found")
	require.NotEmpty(t, consumerPubKey, "consumer pubkey is empty")
	require.Equal(t, consumerPubKey, consumerKey)
}

func TestDeleteValidatorConsumerPubKey(t *testing.T) {
	chainID := "consumer"
	providerAddr := sdk.ConsAddress([]byte("providerAddr"))
	consumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	keeper.SetValidatorConsumerPubKey(ctx, chainID, providerAddr, consumerKey)

	consumerPubKey, found := keeper.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	require.True(t, found, "consumer pubkey not found")
	require.NotEmpty(t, consumerPubKey, "consumer pubkey is empty")
	require.Equal(t, consumerPubKey, consumerKey)

	keeper.DeleteValidatorConsumerPubKey(ctx, chainID, providerAddr)
	consumerPubKey, found = keeper.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	require.False(t, found, "consumer pubkey was found")
	require.Empty(t, consumerPubKey, "consumer pubkey was returned")
	require.NotEqual(t, consumerPubKey, consumerKey)
}

func TestIterateValidatorConsumerPubKeys(t *testing.T) {

	chainID := "consumer"
	testAssignments := []assignedKeys{
		{
			providerAddr:   sdk.ConsAddress([]byte("validator-1")),
			consumerPubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey(),
		},
		{
			providerAddr:   sdk.ConsAddress([]byte("validator-2")),
			consumerPubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(2).TMProtoCryptoPublicKey(),
		},
		{
			providerAddr:   sdk.ConsAddress([]byte("validator-3")),
			consumerPubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(3).TMProtoCryptoPublicKey(),
		},
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, assignment := range testAssignments {
		keeper.SetValidatorConsumerPubKey(ctx, chainID, assignment.providerAddr, assignment.consumerPubKey)
	}

	result := []assignedKeys{}
	cbFunc := func(iteratorProviderAddr sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool) {
		result = append(result, assignedKeys{
			providerAddr:   iteratorProviderAddr,
			consumerPubKey: consumerKey,
		})
		return false
	}

	keeper.IterateValidatorConsumerPubKeys(ctx, chainID, cbFunc)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched consumer key assignment in case %d", i)
	}

}

func TestIterateAllValidatorConsumerPubKeys(t *testing.T) {
	providerAddr := sdk.ConsAddress([]byte("validator-1"))
	testAssignments := []assignedKeys{
		{
			chainID:        "consumer-1",
			providerAddr:   providerAddr,
			consumerPubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey(),
		},
		{
			chainID:        "consumer-2",
			providerAddr:   providerAddr,
			consumerPubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(2).TMProtoCryptoPublicKey(),
		},
		{
			chainID:        "consumer-3",
			providerAddr:   providerAddr,
			consumerPubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(3).TMProtoCryptoPublicKey(),
		},
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, assignment := range testAssignments {
		keeper.SetValidatorConsumerPubKey(ctx, assignment.chainID, assignment.providerAddr, assignment.consumerPubKey)
	}

	result := []assignedKeys{}
	cbFunc := func(chainID string, iteratorProviderAddr sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool) {
		require.Equal(t, providerAddr, iteratorProviderAddr, "unexpected provider address in iterator - expecting just 1 provider address")
		result = append(result, assignedKeys{
			chainID:        chainID,
			providerAddr:   iteratorProviderAddr,
			consumerPubKey: consumerKey,
		})
		return false
	}

	keeper.IterateAllValidatorConsumerPubKeys(ctx, cbFunc)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched consumer key assignment in case %d", i)
	}
}

// TODO msalopek
func TestGetValidatorByConsumerAddr(t *testing.T)         {}
func TestSetValidatorByConsumerAddr(t *testing.T)         {}
func TestIterateValidatorsByConsumerAddr(t *testing.T)    {}
func TestIterateAllValidatorsByConsumerAddr(t *testing.T) {}
func TestDeleteValidatorByConsumerAddr(t *testing.T)      {}
func TestGetPendingKeyAssignment(t *testing.T)            {}
func TestSetPendingKeyAssignment(t *testing.T)            {}
func TestIteratePendingKeyAssignments(t *testing.T)       {}
func TestDeletePendingKeyAssignment(t *testing.T)         {}
