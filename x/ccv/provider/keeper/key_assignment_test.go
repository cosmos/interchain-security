package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	cryptotestutil "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"

	"math/rand"

	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	"github.com/golang/mock/gomock"
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

	addrToPrune := keeper.GetConsumerAddrsToPrune(ctx, chainID, vscID).Addresses
	require.NotEmpty(t, addrToPrune, "address to prune is empty")
	require.Len(t, addrToPrune, 1, "address to prune is not len 1")
	require.Equal(t, sdk.ConsAddress(addrToPrune[0]), consumerAddr)

	keeper.DeleteConsumerAddrsToPrune(ctx, chainID, vscID)
	addrToPrune = keeper.GetConsumerAddrsToPrune(ctx, chainID, vscID).Addresses
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

	addrToPrune := keeper.GetConsumerAddrsToPrune(ctx, testAssignments[0].chainID, testAssignments[0].vscID).Addresses
	require.NotEmpty(t, addrToPrune, "address to prune is empty")
	require.Len(t, addrToPrune, 2, "address to prune is not len 2")
	require.Equal(t, sdk.ConsAddress(addrToPrune[0]), testAssignments[0].consumerAddr)
	require.Equal(t, sdk.ConsAddress(addrToPrune[1]), testAssignments[1].consumerAddr)

	type iterResult struct {
		vscID    uint64
		addrList providertypes.AddressList
	}
	results := []iterResult{}
	cbIterateAll := func(chainID string, vscID uint64, addrList providertypes.AddressList) (stop bool) {
		results = append(results, iterResult{
			vscID:    vscID,
			addrList: addrList,
		})
		return false // continue iteration
	}

	keeper.IterateAllConsumerAddrsToPrune(ctx, cbIterateAll)
	require.Len(t, results, 2, "incorrect results len - should be 2, got %d", len(results))

	// 2 keys for vscID == 1
	require.Equal(t, results[0].vscID, uint64(1), "mismatched vscID in iterate all")
	vsc1Addrs := results[0].addrList.Addresses
	require.Len(t, vsc1Addrs, 2, "wrong len of addrs to prune")
	require.Equal(t, testAssignments[0].consumerAddr, sdk.ConsAddress(vsc1Addrs[0]), "mismatched consumer address")
	require.Equal(t, testAssignments[1].consumerAddr, sdk.ConsAddress(vsc1Addrs[1]), "mismatched consumer address")

	// 1 key for vscID == 2
	require.Equal(t, results[1].vscID, uint64(2), "mismatched vscID in iterate all")
	vsc2Addrs := results[1].addrList.Addresses
	require.Len(t, vsc2Addrs, 1, "wrong len of addrs to prune")
	require.Equal(t, testAssignments[2].consumerAddr, sdk.ConsAddress(vsc2Addrs[0]), "mismatched consumer address")

	results = []iterResult{}
	cbIterateOne := func(chainID string, vscID uint64, addrList providertypes.AddressList) (stop bool) {
		results = append(results, iterResult{
			vscID:    vscID,
			addrList: addrList,
		})
		return true // stop iteration
	}

	keeper.IterateAllConsumerAddrsToPrune(ctx, cbIterateOne)
	require.Len(t, results, 1, "incorrect results len - should be 1, got %d", len(results))

	// 2 keys for vscID == 1
	require.Equal(t, results[0].vscID, uint64(1), "mismatched vscID in iterate")
	vsc1Addrs = results[0].addrList.Addresses
	require.Len(t, vsc1Addrs, 2, "wrong len of addrs to prune")
	require.Equal(t, testAssignments[0].consumerAddr, sdk.ConsAddress(vsc1Addrs[0]), "mismatched consumer address")
	require.Equal(t, testAssignments[1].consumerAddr, sdk.ConsAddress(vsc1Addrs[1]), "mismatched consumer address")
}

// checkCorrectPruningProperty checks that the pruning property is correct for a given
// consumer chain. See AppendConsumerAddrsToPrune for a formulation of the property.
func checkCorrectPruningProperty(ctx sdk.Context, k providerkeeper.Keeper, chainID string) bool {
	/*
		For each consumer address cAddr in ValidatorByConsumerAddr,
		  - either there exists a provider address pAddr in ValidatorConsumerPubKey,
		    s.t. hash(ValidatorConsumerPubKey(pAddr)) = cAddr
		  - or there exists a vscID in ConsumerAddrsToPrune s.t. cAddr in ConsumerAddrsToPrune(vscID)
	*/
	willBePruned := map[string]bool{}
	k.IterateConsumerAddrsToPrune(ctx, chainID, func(vscID uint64, addrList providertypes.AddressList) (stop bool) {
		for _, cAddr := range addrList.Addresses {
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
			require.True(t, checkCorrectPruningProperty(ctx, k, chainID))

			ctrl.Finish()
		})
	}
}

// Represents the validator set of a chain
type ValSet struct {
	identities []*cryptotestutil.CryptoIdentity
	// indexed by same index as identities
	power []int64
}

func CreateValSet(identities []*cryptotestutil.CryptoIdentity) ValSet {
	return ValSet{
		identities: identities,
		power:      make([]int64, len(identities)),
	}
}

// Apply a list of validator power updates
func (vs *ValSet) apply(updates []abci.ValidatorUpdate) {
	// precondition: updates must all have unique keys
	// note: an insertion index should always be found
	for _, u := range updates {
		for i, id := range vs.identities { // n2 looping but n is tiny
			// cons := sdk.ConsAddress(utils.GetChangePubKeyAddress(u))
			cons := utils.TMCryptoPublicKeyToConsAddr(u.PubKey)
			if id.SDKConsAddress().Equals(cons) {
				vs.power[i] = u.Power
			}
		}

	}
}

// A key assignment action to be done
type Assignment struct {
	val stakingtypes.Validator
	ck  tmprotocrypto.PublicKey
}

// TestSimulatedAssignmentsAndUpdateApplication tests a series
// of simulated scenarios where random key assignments and validator
// set updates are generated.
// TODO: this does not yet fully test the correct lookup of a provider
// validator from a consumer consensus address, as is needed for handling
// (double sign) slash packets.
func TestSimulatedAssignmentsAndUpdateApplication(t *testing.T) {

	CHAINID := "chainID"
	// The number of full test executions to run
	NUM_EXECUTIONS := 100
	// Each test execution mimics the adding of a consumer chain and the
	// assignments and power updates of several blocks
	NUM_BLOCKS_PER_EXECUTION := 40
	// The number of validators to be simulated
	NUM_VALIDATORS := 4
	// The number of keys that can be used. Keeping this number small is
	// good because it increases the chance that different assignments will
	// use the same keys, which is something we want to test.
	NUM_ASSIGNABLE_KEYS := 12
	// The maximum number of key assignment actions to simulate in each
	// simulated block, and before the consumer chain is registered.
	NUM_ASSIGNMENTS_PER_BLOCK_MAX := 8

	// Create some identities for the simulated provider validators to use
	providerIdentities := []*cryptotestutil.CryptoIdentity{}
	// Create some identities which the provider validators can assign to the consumer chain
	consumerIdentities := []*cryptotestutil.CryptoIdentity{}
	for i := 0; i < NUM_VALIDATORS; i++ {
		providerIdentities = append(providerIdentities, cryptotestutil.NewCryptoIdentityFromIntSeed(i))
	}
	for i := NUM_VALIDATORS; i < NUM_ASSIGNABLE_KEYS+NUM_VALIDATORS; i++ {
		// ATTENTION: uses a different domain of keys for assignments
		//
		// (TODO: allow consumer identities to overlap with provider identities
		// this will be enabled after the testnet
		// see https://github.com/cosmos/interchain-security/issues/503)
		//
		consumerIdentities = append(consumerIdentities, cryptotestutil.NewCryptoIdentityFromIntSeed(i))
	}

	// Helper: simulates creation of staking module EndBlock updates.
	getStakingUpdates := func() (ret []abci.ValidatorUpdate) {
		// Get a random set of validators to update. It is important to test subsets of all validators.
		validators := rand.Perm(NUM_VALIDATORS)[0:rand.Intn(NUM_VALIDATORS+1)]
		for _, i := range validators {
			// Power 0, 1, or 2 represents
			// deletion, update (from 0 or 2), update (from 0 or 1)
			power := rand.Intn(3)
			ret = append(ret, abci.ValidatorUpdate{
				PubKey: providerIdentities[i].TMProtoCryptoPublicKey(),
				Power:  int64(power),
			})
		}
		return
	}

	// Helper: simulates creation of assignment tx's to be done.
	getAssignments := func() (ret []Assignment) {
		for i, numAssignments := 0, rand.Intn(NUM_ASSIGNMENTS_PER_BLOCK_MAX); i < numAssignments; i++ {
			randomIxP := rand.Intn(NUM_VALIDATORS)
			randomIxC := rand.Intn(NUM_ASSIGNABLE_KEYS)
			ret = append(ret, Assignment{
				val: providerIdentities[randomIxP].SDKStakingValidator(),
				ck:  consumerIdentities[randomIxC].TMProtoCryptoPublicKey(),
			})
		}
		return
	}

	// Run a randomly simulated execution and test that desired properties hold
	// Helper: run a randomly simulated scenario where a consumer chain is added
	// (after key assignment actions are done), followed by a series of validator power updates
	// and key assignments tx's. For each simulated 'block', the validator set replication
	// properties and the pruning property are checked.
	runRandomExecution := func() {

		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

		// Create validator sets for the provider and consumer. These are used to check the validator set
		// replication property.
		providerValset := CreateValSet(providerIdentities)
		// NOTE: consumer must have space for provider identities because default key assignments are to provider keys
		consumerValset := CreateValSet(append(providerIdentities, consumerIdentities...))

		// Mock calls to GetLastValidatorPower to return directly from the providerValset
		mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
			gomock.Any(),
			gomock.Any(),
		).DoAndReturn(func(_ interface{}, valAddr sdk.ValAddress) int64 {
			// When the mocked method is called, locate the appropriate validator
			// in the provider valset and return its power.
			for i, id := range providerIdentities {
				if id.SDKStakingValidator().GetOperator().Equals(valAddr) {
					return providerValset.power[i]
				}
			}
			panic("must find validator")
			// This can be called 0 or more times per block depending on the random
			// assignments that occur
		}).AnyTimes()

		// Helper: apply some updates to both the provider and consumer valsets
		applyUpdates := func(updates []abci.ValidatorUpdate) {
			providerValset.apply(updates)
			updates, err := k.ApplyKeyAssignmentToValUpdates(ctx, CHAINID, updates)
			require.NoError(t, err)
			consumerValset.apply(updates)
		}

		// Helper: apply some key assignment transactions to the system
		applyAssignments := func(assignments []Assignment) {
			for _, a := range assignments {
				// ignore err return, it can be possible for an error to occur
				_ = k.AssignConsumerKey(ctx, CHAINID, a.val, a.ck)
			}
		}

		// The consumer chain has not yet been registered
		// Apply some randomly generated key assignments
		applyAssignments(getAssignments())
		// And generate a random provider valset which, in the real system, will
		// be put into the consumer genesis.
		applyUpdates(getStakingUpdates())

		// Register the consumer chain
		k.SetConsumerClientId(ctx, CHAINID, "")

		// Analogous to the last vscid received from the consumer in a maturity
		// Used to check the correct pruning property
		greatestPrunedVSCID := -1

		// Simulate a number of 'blocks'
		// Each block consists of a number of random key assignment tx's
		// and a random set of validator power updates
		for block := 0; block < NUM_BLOCKS_PER_EXECUTION; block++ {

			// Generate and apply assignments and power updates
			applyAssignments(getAssignments())
			applyUpdates(getStakingUpdates())

			// Randomly fast forward the greatest pruned VSCID. This simulates
			// delivery of maturity packets from the consumer chain.
			prunedVscid := greatestPrunedVSCID + rand.Intn(int(k.GetValidatorSetUpdateId(ctx))+1)
			k.PruneKeyAssignments(ctx, CHAINID, uint64(prunedVscid))
			greatestPrunedVSCID = prunedVscid

			/*

				Properties: Validator Set Replication
				Each validator set on the provider must be replicated on the consumer.
				The property in the real system is somewhat weaker, because the consumer chain can
				forward updates to tendermint in batches.
				(See https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties)
				We test the stronger property, because we abstract over implementation of the consumer
				chain. The stronger property implies the weaker property.

			*/

			// Check validator set replication forward direction
			for i, idP := range providerValset.identities {
				// For each active validator on the provider chain
				if 0 < providerValset.power[i] {
					// Get the assigned key
					ck, found := k.GetValidatorConsumerPubKey(ctx, CHAINID, idP.SDKConsAddress())
					if !found {
						// Use default if unassigned
						ck = idP.TMProtoCryptoPublicKey()
					}
					consC := utils.TMCryptoPublicKeyToConsAddr(ck)
					// Find the corresponding consumer validator (must always be found)
					for j, idC := range consumerValset.identities {
						if consC.Equals(idC.SDKConsAddress()) {
							require.Equal(t, providerValset.power[i], consumerValset.power[j])
						}
					}
				}
			}
			// Check validator set replication backward direction
			for i := range consumerValset.identities {
				// For each active validator on the consumer chain
				consC := consumerValset.identities[i].SDKConsAddress()
				if 0 < consumerValset.power[i] {
					// Get the provider who assigned the key
					consP := k.GetProviderAddrFromConsumerAddr(ctx, CHAINID, consC)
					// Find the corresponding provider validator (must always be found)
					for j, idP := range providerValset.identities {
						if idP.SDKConsAddress().Equals(consP) {
							require.Equal(t, providerValset.power[j], consumerValset.power[i])
						}
					}
				}
			}

			// Check that all keys have been or will eventually be pruned.

			require.True(t, checkCorrectPruningProperty(ctx, k, CHAINID))

		}
		ctrl.Finish()
	}

	for i := 0; i < NUM_EXECUTIONS; i++ {
		runRandomExecution()
	}
}
