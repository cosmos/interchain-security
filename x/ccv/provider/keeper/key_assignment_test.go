package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	cryptotestutil "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type testAssignment struct {
	chainID        string
	providerAddr   sdk.ConsAddress
	consumerAddr   sdk.ConsAddress
	consumerPubKey tmprotocrypto.PublicKey
	pubKeyAndPower abci.ValidatorUpdate
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

func TestKeyAssignmentReplacementCRUD(t *testing.T) {
	chainID := "consumer"
	providerAddr := sdk.ConsAddress([]byte("providerAddr"))
	expCPubKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	var expPower int64 = 100

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	keeper.SetKeyAssignmentReplacement(ctx, chainID, providerAddr, expCPubKey, expPower)

	cPubKey, power, found := keeper.GetKeyAssignmentReplacement(ctx, chainID, providerAddr)
	require.True(t, found, "key assignment replacement not found")
	require.Equal(t, expCPubKey, cPubKey, "previous consumer key not matching")
	require.Equal(t, expPower, power, "power not matching")

	keeper.DeleteKeyAssignmentReplacement(ctx, chainID, providerAddr)
	_, _, found = keeper.GetKeyAssignmentReplacement(ctx, chainID, providerAddr)
	require.False(t, found, "key assignment replacement found")
}

func TestIterateKeyAssignmentReplacements(t *testing.T) {
	chainID := "consumer"
	testAssignments := []testAssignment{
		{
			providerAddr: sdk.ConsAddress([]byte("validator-1")),
			pubKeyAndPower: abci.ValidatorUpdate{
				Power:  100,
				PubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey(),
			},
		},
		{
			providerAddr: sdk.ConsAddress([]byte("validator-2")),
			pubKeyAndPower: abci.ValidatorUpdate{
				Power:  100,
				PubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(2).TMProtoCryptoPublicKey(),
			},
		},
		{
			providerAddr: sdk.ConsAddress([]byte("validator-3")),
			pubKeyAndPower: abci.ValidatorUpdate{
				Power:  100,
				PubKey: cryptotestutil.NewCryptoIdentityFromIntSeed(3).TMProtoCryptoPublicKey(),
			},
		},
	}

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, assignment := range testAssignments {
		keeper.SetKeyAssignmentReplacement(ctx, chainID, assignment.providerAddr, assignment.pubKeyAndPower.PubKey, assignment.pubKeyAndPower.Power)
	}

	result := []testAssignment{}
	cbIterateAll := func(providerAddr sdk.ConsAddress, prevCKey tmprotocrypto.PublicKey, power int64) (stop bool) {
		result = append(result, testAssignment{
			providerAddr:   providerAddr,
			pubKeyAndPower: abci.ValidatorUpdate{PubKey: prevCKey, Power: power},
		})
		return false // continue iteration
	}

	keeper.IterateKeyAssignmentReplacements(ctx, chainID, cbIterateAll)
	require.Len(t, result, len(testAssignments), "incorrect result len - should be %d, got %d", len(testAssignments), len(result))

	for i, res := range result {
		require.Equal(t, testAssignments[i], res, "mismatched key assignment replacement in case %d", i)
	}

	result = []testAssignment{}
	cbIterateOne := func(providerAddr sdk.ConsAddress, prevCKey tmprotocrypto.PublicKey, power int64) (stop bool) {
		result = append(result, testAssignment{
			providerAddr:   providerAddr,
			pubKeyAndPower: abci.ValidatorUpdate{PubKey: prevCKey, Power: power},
		})
		return true // stop after first
	}

	keeper.IterateKeyAssignmentReplacements(ctx, chainID, cbIterateOne)
	require.Len(t, result, 1, "incorrect result len - should be 1, got %d", len(result))

	require.Equal(t, testAssignments[0], result[0], "mismatched key assignment replacement in iterate one")
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

// CheckCorrectPruningProperty checks that the pruning property is correct for a given
// consumer chain. See AppendConsumerAddrsToPrune for a formulation of the property.
func CheckCorrectPruningProperty(ctx sdk.Context, k providerkeeper.Keeper, chainID string) bool {
	/*
		For each consumer address cAddr in ValidatorByConsumerAddr,
		  - either there exists a provider address pAddr in ValidatorConsumerPubKey,
		    s.t. hash(ValidatorConsumerPubKey(pAddr)) = cAddr
		  - or there exists a vscID in ConsumerAddrsToPrune s.t. cAddr in ConsumerAddrsToPrune(vscID)
	*/
	willBePruned := map[string]bool{}
	k.IterateConsumerAddrsToPrune(ctx, chainID, func(vscID uint64, consumerAddrsToPrune [][]byte) (stop bool) {
		for _, cAddr := range consumerAddrsToPrune {
			addr := sdk.ConsAddress(cAddr)
			willBePruned[addr.String()] = true
		}
		return false
	})
	good := true
	k.IterateAllValidatorsByConsumerAddr(ctx, func(chainID string, consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool) {
		if _, ok := willBePruned[consumerAddr.String()]; ok {
			// Address will be pruned, everything is fine.
			return false
		}
		// Try to find a validator who has this consumer address currently assigned
		isCurrentlyAssigned := false
		k.IterateValidatorConsumerPubKeys(ctx, chainID,
			func(_ sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool) {
				if utils.TMCryptoPublicKeyToConsAddr(consumerKey).Equals(consumerAddr) {
					isCurrentlyAssigned = true
					return true // stop iterating early
				}
				return false
			},
		)
		if !isCurrentlyAssigned {
			// Will not be pruned, and is not currently assigned: violation
			good = false
			return true // breakout early
		}
		return false
	})
	return good
}

func TestAssignConsensusKeyForConsumerChain(t *testing.T) {

	chainID := "chainID"
	providerIdentities := []*cryptotestutil.CryptoIdentity{
		cryptotestutil.NewCryptoIdentityFromIntSeed(0),
		cryptotestutil.NewCryptoIdentityFromIntSeed(1),
	}
	consumerIdentities := []*cryptotestutil.CryptoIdentity{
		cryptotestutil.NewCryptoIdentityFromIntSeed(2),
		cryptotestutil.NewCryptoIdentityFromIntSeed(3),
	}

	testCases := []struct {
		name string
		// State-mutating mockSetup specific to this test case
		mockSetup func(sdk.Context, providerkeeper.Keeper, testkeeper.MockedKeepers)
		doActions func(sdk.Context, providerkeeper.Keeper)
	}{
		/*
			0. Consumer     registered: Assign PK0->CK0 and retrieve PK0->CK0
			1. Consumer     registered: Assign PK0->CK0, PK0->CK1 and retrieve PK0->CK1
			2. Consumer     registered: Assign PK0->CK0, PK1->CK0 and error
			3. Consumer     registered: Assign PK1->PK0 and error (TODO: see https://github.com/cosmos/interchain-security/issues/503)
			4. Consumer not registered: Assign PK0->CK0 and retrieve PK0->CK0
			5. Consumer not registered: Assign PK0->CK0, PK0->CK1 and retrieve PK0->CK1
			6. Consumer not registered: Assign PK0->CK0, PK1->CK0 and error
			7. Consumer not registered: Assign PK1->PK0 and error (TODO: see https://github.com/cosmos/interchain-security/issues/503)
		*/
		{
			name: "0",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValAddress(),
					).Return(int64(0)),
				)
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				k.SetConsumerClientId(ctx, chainID, "")
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerIdentities[0].SDKConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].SDKConsAddress(), providerAddr)
			},
		},
		{
			name: "1",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValAddress(),
					).Return(int64(0)),
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValAddress(),
					).Return(int64(0)),
				)
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				k.SetConsumerClientId(ctx, chainID, "")
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				err = k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[1].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerIdentities[1].SDKConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].SDKConsAddress(), providerAddr)
			},
		},
		{
			name: "2",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValAddress(),
					).Return(int64(0)),
				)
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				k.SetConsumerClientId(ctx, chainID, "")
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				err = k.AssignConsumerKey(ctx, chainID,
					providerIdentities[1].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.Error(t, err)
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerIdentities[0].SDKConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].SDKConsAddress(), providerAddr)
			},
		},
		// (TODO: see https://github.com/cosmos/interchain-security/issues/503)
		// {
		// 	name: "3",
		// 	mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
		// 	},
		// 	doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
		// 	},
		// },
		{
			name: "4",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerIdentities[0].SDKConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].SDKConsAddress(), providerAddr)
			},
		},
		{
			name: "5",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				err = k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[1].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerIdentities[1].SDKConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].SDKConsAddress(), providerAddr)
			},
		},
		{
			name: "6",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				err = k.AssignConsumerKey(ctx, chainID,
					providerIdentities[1].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.Error(t, err)
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerIdentities[0].SDKConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].SDKConsAddress(), providerAddr)
			},
		},
		// (TODO: see https://github.com/cosmos/interchain-security/issues/503)
		// {
		// 	name: "7",
		// 	mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
		// 	},
		// 	doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
		// 	},
		// },
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {

			k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

			tc.mockSetup(ctx, k, mocks)
			tc.doActions(ctx, k)
			require.True(t, CheckCorrectPruningProperty(ctx, k, chainID))

			ctrl.Finish()
		})
	}
}
