package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	cryptotestutil "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/stretchr/testify/require"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

// TODO: msalopek name this better
type assignedKeys struct {
	chainID        string
	providerAddr   sdk.ConsAddress
	consumerAddr   sdk.ConsAddress
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

func TestSetAndGetValidatorByConsumerAddr(t *testing.T) {
	chainID := "consumer"
	providerAddr := sdk.ConsAddress([]byte("providerAddr"))
	consumerAddr := sdk.ConsAddress([]byte("consumerAddr"))

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	keeper.SetValidatorByConsumerAddr(ctx, chainID, consumerAddr, providerAddr)

	providerAddrResult, found := keeper.GetValidatorByConsumerAddr(ctx, chainID, consumerAddr)
	require.True(t, found, "provider address not found")
	require.NotEmpty(t, providerAddrResult, "provider address is empty")
	require.Equal(t, providerAddr, providerAddrResult)
}

func TestDeleteValidatorByConsumerAddr(t *testing.T) {
	chainID := "consumer"
	providerAddr := sdk.ConsAddress([]byte("providerAddr"))
	consumerAddr := sdk.ConsAddress([]byte("consumerAddr"))

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	keeper.SetValidatorByConsumerAddr(ctx, chainID, consumerAddr, providerAddr)

	providerAddrResult, found := keeper.GetValidatorByConsumerAddr(ctx, chainID, consumerAddr)
	require.True(t, found, "provider address not found")
	require.NotEmpty(t, providerAddrResult, "provider address is empty")
	require.Equal(t, providerAddr, providerAddrResult)

	keeper.DeleteValidatorByConsumerAddr(ctx, chainID, consumerAddr)
	providerAddrResult, found = keeper.GetValidatorByConsumerAddr(ctx, chainID, consumerAddr)
	require.False(t, found, "provider address was found")
	require.Empty(t, providerAddrResult, "provider address not empty")
	require.NotEqual(t, providerAddr, providerAddrResult)
}

func TestIterateValidatorsByConsumerAddr(t *testing.T) {
	chainID := "consumer"
	testAssignments := []assignedKeys{
		{
			providerAddr: sdk.ConsAddress([]byte("validator-1")),
			consumerAddr: sdk.ConsAddress([]byte("consumer-1")),
		},
		{
			providerAddr: sdk.ConsAddress([]byte("validator-2")),
			consumerAddr: sdk.ConsAddress([]byte("consumer-2")),
		},
		{
			providerAddr: sdk.ConsAddress([]byte("validator-3")),
			consumerAddr: sdk.ConsAddress([]byte("consumer-3")),
		},
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, assignment := range testAssignments {
		keeper.SetValidatorByConsumerAddr(ctx, chainID, assignment.consumerAddr, assignment.providerAddr)
	}

	result := []assignedKeys{}
	cbIterateAll := func(consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, assignedKeys{
			providerAddr: providerAddr,
			consumerAddr: consumerAddr,
		})
		return false // continue iteration
	}

	keeper.IterateValidatorsByConsumerAddr(ctx, chainID, cbIterateAll)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched consumer address assignment in case %d", i)
	}

	result = []assignedKeys{}
	cbIterateOne := func(consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, assignedKeys{
			providerAddr: providerAddr,
			consumerAddr: consumerAddr,
		})
		return true // stop after first
	}

	keeper.IterateValidatorsByConsumerAddr(ctx, chainID, cbIterateOne)
	require.Len(t, result, 1, "incorrect result len - should be 1, got %d", len(result))

	require.Equal(t, testAssignments[0], result[0], "mismatched consumer address assignment in iterate one")
}

func TestIterateAllValidatorsByConsumerAddr(t *testing.T) {
	providerAddr := sdk.ConsAddress([]byte("validator-1"))
	testAssignments := []assignedKeys{
		{
			chainID:      "consumer-1",
			providerAddr: providerAddr,
			consumerAddr: sdk.ConsAddress([]byte("consumer-1")),
		},
		{
			chainID:      "consumer-2",
			providerAddr: providerAddr,
			consumerAddr: sdk.ConsAddress([]byte("consumer-2")),
		},
		{
			chainID:      "consumer-3",
			providerAddr: providerAddr,
			consumerAddr: sdk.ConsAddress([]byte("consumer-3")),
		},
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, assignment := range testAssignments {
		keeper.SetValidatorByConsumerAddr(ctx, assignment.chainID, assignment.consumerAddr, assignment.providerAddr)
	}

	result := []assignedKeys{}
	cbIterateAll := func(chainID string, consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, assignedKeys{
			chainID:      chainID,
			providerAddr: providerAddr,
			consumerAddr: consumerAddr,
		})
		return false // continue iteration
	}

	keeper.IterateAllValidatorsByConsumerAddr(ctx, cbIterateAll)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched consumer address assignment in case %d", i)
	}

	result = []assignedKeys{}
	cbIterateOne := func(chainID string, consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, assignedKeys{
			chainID: chainID,

			providerAddr: providerAddr,
			consumerAddr: consumerAddr,
		})
		return true // stop after first
	}

	keeper.IterateAllValidatorsByConsumerAddr(ctx, cbIterateOne)
	require.Len(t, result, 1, "incorrect result len - should be 1, got %d", len(result))

	require.Equal(t, testAssignments[0], result[0], "mismatched consumer address assignment in iterate one")
}

func TestSetAndGetPendingKeyAssignment(t *testing.T) {

}

func TestDeletePendingKeyAssignment(t *testing.T) {}

func TestIteratePendingKeyAssignments(t *testing.T) {}
