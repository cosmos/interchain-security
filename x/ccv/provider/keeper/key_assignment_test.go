package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	cryptotestutil "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type testAssignment struct {
	chainID        string
	providerAddr   sdk.ConsAddress
	consumerAddr   sdk.ConsAddress
	consumerPubKey tmprotocrypto.PublicKey
	valsetUpdate   abci.ValidatorUpdate
	vscID          uint64
}

func TestValidatorConsumerPubKeyCRUD(t *testing.T) {
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
	testAssignments := []testAssignment{
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

	result := []testAssignment{}
	cbIterateAll := func(iteratorProviderAddr sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool) {
		result = append(result, testAssignment{
			providerAddr:   iteratorProviderAddr,
			consumerPubKey: consumerKey,
		})
		return false
	}

	keeper.IterateValidatorConsumerPubKeys(ctx, chainID, cbIterateAll)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched consumer key assignment in case %d", i)
	}

	result = []testAssignment{}
	cbIterateOne := func(iteratorProviderAddr sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool) {
		result = append(result, testAssignment{
			providerAddr:   iteratorProviderAddr,
			consumerPubKey: consumerKey,
		})
		return true
	}

	keeper.IterateValidatorConsumerPubKeys(ctx, chainID, cbIterateOne)
	require.Len(t, result, 1, "incorrect result len - should be 1, got %d", len(result))

	require.Equal(t, testAssignments[0], result[0], "mismatched consumer key assignment in iterate one")

}

func TestIterateAllValidatorConsumerPubKeys(t *testing.T) {
	providerAddr := sdk.ConsAddress([]byte("validator-1"))
	testAssignments := []testAssignment{
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

	result := []testAssignment{}
	cbIterateAll := func(chainID string, iteratorProviderAddr sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool) {
		require.Equal(t, providerAddr, iteratorProviderAddr, "unexpected provider address in iterator - expecting just 1 provider address")
		result = append(result, testAssignment{
			chainID:        chainID,
			providerAddr:   iteratorProviderAddr,
			consumerPubKey: consumerKey,
		})
		return false
	}

	keeper.IterateAllValidatorConsumerPubKeys(ctx, cbIterateAll)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched consumer key assignment in case %d", i)
	}

	result = []testAssignment{}
	cbIterateOne := func(chainID string, iteratorProviderAddr sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool) {
		require.Equal(t, providerAddr, iteratorProviderAddr, "unexpected provider address in iterator - expecting just 1 provider address")
		result = append(result, testAssignment{
			chainID:        chainID,
			providerAddr:   iteratorProviderAddr,
			consumerPubKey: consumerKey,
		})
		return false
	}

	keeper.IterateAllValidatorConsumerPubKeys(ctx, cbIterateOne)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be 1, got %d", len(result))

	require.Equal(t, testAssignments[0], result[0], "mismatched consumer key assignment in iterate one")
}

func TestValidatorByConsumerAddrCRUD(t *testing.T) {
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
	testAssignments := []testAssignment{
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

	result := []testAssignment{}
	cbIterateAll := func(consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, testAssignment{
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

	result = []testAssignment{}
	cbIterateOne := func(consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, testAssignment{
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
	testAssignments := []testAssignment{
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

	result := []testAssignment{}
	cbIterateAll := func(chainID string, consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, testAssignment{
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

	result = []testAssignment{}
	cbIterateOne := func(chainID string, consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		result = append(result, testAssignment{
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

func TestPendingKeyAssignmentCRUD(t *testing.T) {
	chainID := "consumer"
	providerAddr := sdk.ConsAddress([]byte("providerAddr"))
	consumerPubKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	valUpdate := abci.ValidatorUpdate{
		Power:  100,
		PubKey: consumerPubKey,
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	keeper.SetPendingKeyAssignment(ctx, chainID, providerAddr, valUpdate)

	pendingAssignment, found := keeper.GetPendingKeyAssignment(ctx, chainID, providerAddr)
	require.True(t, found, "pending assignment not found")
	require.NotEmpty(t, pendingAssignment, "pending assignment is empty")
	require.Equal(t, pendingAssignment, valUpdate)

	keeper.DeletePendingKeyAssignment(ctx, chainID, providerAddr)
	pendingAssignment, found = keeper.GetPendingKeyAssignment(ctx, chainID, providerAddr)
	require.False(t, found, "pending assignment was found")
	require.Empty(t, pendingAssignment, "pending assignment not empty")
	require.NotEqual(t, pendingAssignment, valUpdate)
}

func TestIteratePendingKeyAssignments(t *testing.T) {
	chainID := "consumer"
	testAssignments := []testAssignment{
		{
			providerAddr: sdk.ConsAddress([]byte("validator-1")),
			valsetUpdate: abci.ValidatorUpdate{
				Power:  100,
				PubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey(),
			},
		},
		{
			providerAddr: sdk.ConsAddress([]byte("validator-2")),
			valsetUpdate: abci.ValidatorUpdate{
				Power:  100,
				PubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(2).TMProtoCryptoPublicKey(),
			},
		},
		{
			providerAddr: sdk.ConsAddress([]byte("validator-3")),
			valsetUpdate: abci.ValidatorUpdate{
				Power:  100,
				PubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(3).TMProtoCryptoPublicKey(),
			},
		},
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, assignment := range testAssignments {
		keeper.SetPendingKeyAssignment(ctx, chainID, assignment.providerAddr, assignment.valsetUpdate)
	}

	result := []testAssignment{}
	cbIterateAll := func(providerAddr sdk.ConsAddress, pendingKeyAssignment abci.ValidatorUpdate) (stop bool) {
		result = append(result, testAssignment{
			providerAddr: providerAddr,
			valsetUpdate: pendingKeyAssignment,
		})
		return false // continue iteration
	}

	keeper.IteratePendingKeyAssignments(ctx, chainID, cbIterateAll)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched pending key assignment in case %d", i)
	}

	result = []testAssignment{}
	cbIterateOne := func(providerAddr sdk.ConsAddress, pendingKeyAssignment abci.ValidatorUpdate) (stop bool) {
		result = append(result, testAssignment{
			providerAddr: providerAddr,
			valsetUpdate: pendingKeyAssignment,
		})
		return true // stop after first
	}

	keeper.IteratePendingKeyAssignments(ctx, chainID, cbIterateOne)
	require.Len(t, result, 1, "incorrect result len - should be 1, got %d", len(result))

	require.Equal(t, testAssignments[0], result[0], "mismatched pending key assignment in iterate one")
}

func TestConsumerAddrsToPruneCRUD(t *testing.T) {
	chainID := "consumer"
	consumerAddr := sdk.ConsAddress([]byte("consumerAddr1"))
	vscID := uint64(1)

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	keeper.AppendConsumerAddrsToPrune(ctx, chainID, vscID, consumerAddr)

	addrToPrune := keeper.GetConsumerAddrsToPrune(ctx, chainID, vscID)
	require.NotEmpty(t, addrToPrune, "address to prune is empty")
	require.Len(t, addrToPrune, 1, "address to prune is not len 1")
	require.Equal(t, sdk.ConsAddress(addrToPrune[0]), consumerAddr)

	keeper.DeleteConsumerAddrsToPrune(ctx, chainID, vscID)
	addrToPrune = keeper.GetConsumerAddrsToPrune(ctx, chainID, vscID)
	require.Empty(t, addrToPrune, "address to prune was returned")
}

func TestIterateAllConsumerAddrsToPrune(t *testing.T) {
	testAssignments := []testAssignment{
		{
			chainID:      "consumer-1",
			providerAddr: sdk.ConsAddress([]byte("validator-1")),
			consumerAddr: sdk.ConsAddress([]byte("validator-1-consumer-1-key")),
			vscID:        1,
		},
		{
			chainID:      "consumer-1",
			providerAddr: sdk.ConsAddress([]byte("validator-2")),
			consumerAddr: sdk.ConsAddress([]byte("validator-2-consumer-1-key")),
			vscID:        1,
		},
		{
			chainID:      "consumer-3",
			providerAddr: sdk.ConsAddress([]byte("validator-1")),
			consumerAddr: sdk.ConsAddress([]byte("validator-1-consumer-3-key")),
			vscID:        2,
		},
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, ta := range testAssignments {
		keeper.AppendConsumerAddrsToPrune(ctx, ta.chainID, ta.vscID, ta.consumerAddr)
	}

	addrToPrune := keeper.GetConsumerAddrsToPrune(ctx, testAssignments[0].chainID, testAssignments[0].vscID)
	require.NotEmpty(t, addrToPrune, "address to prune is empty")
	require.Len(t, addrToPrune, 2, "address to prune is not len 2")
	require.Equal(t, sdk.ConsAddress(addrToPrune[0]), testAssignments[0].consumerAddr)
	require.Equal(t, sdk.ConsAddress(addrToPrune[1]), testAssignments[1].consumerAddr)

	type iterResult struct {
		vscID                uint64
		consumerAddrsToPrune [][]byte
	}
	results := []iterResult{}
	cbIterateAll := func(chainID string, vscID uint64, consumerAddrsToPrune [][]byte) (stop bool) {
		results = append(results, iterResult{
			vscID:                vscID,
			consumerAddrsToPrune: consumerAddrsToPrune,
		})
		return false // continue iteration
	}

	keeper.IterateAllConsumerAddrsToPrune(ctx, cbIterateAll)
	require.Len(t, results, 2, "incorrect results len - should be 2, got %d", len(results))

	// 2 keys for vscID == 1
	require.Equal(t, results[0].vscID, uint64(1), "mismatched vscID in iterate all")
	vsc1Addrs := results[0].consumerAddrsToPrune
	require.Len(t, vsc1Addrs, 2, "wrong len of addrs to prune")
	require.Equal(t, testAssignments[0].consumerAddr, sdk.ConsAddress(vsc1Addrs[0]), "mismatched consumer address")
	require.Equal(t, testAssignments[1].consumerAddr, sdk.ConsAddress(vsc1Addrs[1]), "mismatched consumer address")

	// 1 key for vscID == 2
	require.Equal(t, results[1].vscID, uint64(2), "mismatched vscID in iterate all")
	vsc2Addrs := results[1].consumerAddrsToPrune
	require.Len(t, vsc2Addrs, 1, "wrong len of addrs to prune")
	require.Equal(t, testAssignments[2].consumerAddr, sdk.ConsAddress(vsc2Addrs[0]), "mismatched consumer address")

	results = []iterResult{}
	cbIterateOne := func(chainID string, vscID uint64, consumerAddrsToPrune [][]byte) (stop bool) {
		results = append(results, iterResult{
			vscID:                vscID,
			consumerAddrsToPrune: consumerAddrsToPrune,
		})
		return true // stop iteration
	}

	keeper.IterateAllConsumerAddrsToPrune(ctx, cbIterateOne)
	require.Len(t, results, 1, "incorrect results len - should be 1, got %d", len(results))

	// 2 keys for vscID == 1
	require.Equal(t, results[0].vscID, uint64(1), "mismatched vscID in iterate")
	vsc1Addrs = results[0].consumerAddrsToPrune
	require.Len(t, vsc1Addrs, 2, "wrong len of addrs to prune")
	require.Equal(t, testAssignments[0].consumerAddr, sdk.ConsAddress(vsc1Addrs[0]), "mismatched consumer address")
	require.Equal(t, testAssignments[1].consumerAddr, sdk.ConsAddress(vsc1Addrs[1]), "mismatched consumer address")
}
