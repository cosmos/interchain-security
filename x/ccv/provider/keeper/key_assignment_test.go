package keeper_test

import (
	"bytes"
	"math/rand"
	"sort"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	cryptotestutil "github.com/cosmos/interchain-security/v2/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v2/testutil/keeper"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"

	providerkeeper "github.com/cosmos/interchain-security/v2/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
	"github.com/golang/mock/gomock"
)

func TestValidatorConsumerPubKeyCRUD(t *testing.T) {
	chainID := consumer
	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))
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

func TestGetAllValidatorConsumerPubKey(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	rand.Seed(time.Now().Unix())
	chainIDs := []string{"consumer-1", "consumer-2", "consumer-3"}
	numAssignments := 10
	testAssignments := []types.ValidatorConsumerPubKey{}
	for i := 0; i < numAssignments; i++ {
		consumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(i).TMProtoCryptoPublicKey()
		providerAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(numAssignments + i).ProviderConsAddress()
		testAssignments = append(testAssignments,
			types.ValidatorConsumerPubKey{
				ChainId:      chainIDs[rand.Intn(len(chainIDs))],
				ProviderAddr: providerAddr.ToSdkConsAddr(),
				ConsumerKey:  &consumerKey,
			},
		)
	}
	// select a chainID with more than two assignments
	var chainID string
	for i := range chainIDs {
		chainID = chainIDs[i]
		count := 0
		for _, assignment := range testAssignments {
			if assignment.ChainId == chainID {
				count++
			}
		}
		if count > 2 {
			break
		}
	}
	expectedGetAllOneConsumerOrder := []types.ValidatorConsumerPubKey{}
	for _, assignment := range testAssignments {
		if assignment.ChainId == chainID {
			expectedGetAllOneConsumerOrder = append(expectedGetAllOneConsumerOrder, assignment)
		}
	}
	// sorting by ValidatorConsumerPubKey.ProviderAddr
	sort.Slice(expectedGetAllOneConsumerOrder, func(i, j int) bool {
		return bytes.Compare(expectedGetAllOneConsumerOrder[i].ProviderAddr, expectedGetAllOneConsumerOrder[j].ProviderAddr) == -1
	})

	for _, assignment := range testAssignments {
		providerAddr := types.NewProviderConsAddress(assignment.ProviderAddr)
		pk.SetValidatorConsumerPubKey(ctx, assignment.ChainId, providerAddr, *assignment.ConsumerKey)
	}

	result := pk.GetAllValidatorConsumerPubKeys(ctx, &chainID)
	require.Equal(t, expectedGetAllOneConsumerOrder, result)

	result = pk.GetAllValidatorConsumerPubKeys(ctx, nil)
	require.Len(t, result, len(testAssignments))
}

func TestValidatorByConsumerAddrCRUD(t *testing.T) {
	chainID := consumer
	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))
	consumerAddr := types.NewConsumerConsAddress([]byte("consumerAddr"))

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

func TestGetAllValidatorsByConsumerAddr(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	rand.Seed(time.Now().Unix())
	chainIDs := []string{"consumer-1", "consumer-2", "consumer-3"}
	numAssignments := 10
	testAssignments := []types.ValidatorByConsumerAddr{}
	for i := 0; i < numAssignments; i++ {
		consumerAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(i).ConsumerConsAddress()
		providerAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(numAssignments + i).ProviderConsAddress()
		testAssignments = append(testAssignments,
			types.ValidatorByConsumerAddr{
				ChainId:      chainIDs[rand.Intn(len(chainIDs))],
				ConsumerAddr: consumerAddr.ToSdkConsAddr(),
				ProviderAddr: providerAddr.ToSdkConsAddr(),
			},
		)
	}
	// select a chainID with more than two assignments
	var chainID string
	for i := range chainIDs {
		chainID = chainIDs[i]
		count := 0
		for _, assignment := range testAssignments {
			if assignment.ChainId == chainID {
				count++
			}
		}
		if count > 2 {
			break
		}
	}
	expectedGetAllOneConsumerOrder := []types.ValidatorByConsumerAddr{}
	for _, assignment := range testAssignments {
		if assignment.ChainId == chainID {
			expectedGetAllOneConsumerOrder = append(expectedGetAllOneConsumerOrder, assignment)
		}
	}
	// sorting by ValidatorByConsumerAddr.ConsumerAddr
	sort.Slice(expectedGetAllOneConsumerOrder, func(i, j int) bool {
		return bytes.Compare(expectedGetAllOneConsumerOrder[i].ConsumerAddr, expectedGetAllOneConsumerOrder[j].ConsumerAddr) == -1
	})

	for _, assignment := range testAssignments {
		consumerAddr := types.NewConsumerConsAddress(assignment.ConsumerAddr)
		providerAddr := types.NewProviderConsAddress(assignment.ProviderAddr)
		pk.SetValidatorByConsumerAddr(ctx, assignment.ChainId, consumerAddr, providerAddr)
	}

	result := pk.GetAllValidatorsByConsumerAddr(ctx, &chainID)
	require.Equal(t, expectedGetAllOneConsumerOrder, result)

	result = pk.GetAllValidatorsByConsumerAddr(ctx, nil)
	require.Len(t, result, len(testAssignments))
}

func TestKeyAssignmentReplacementCRUD(t *testing.T) {
	chainID := consumer
	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))
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

func TestGetAllKeyAssignmentReplacements(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "consumer-1"

	rand.Seed(time.Now().Unix())
	numAssignments := 10
	testAssignments := []types.KeyAssignmentReplacement{}
	for i := 0; i < numAssignments; i++ {
		consumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(i).TMProtoCryptoPublicKey()
		providerAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(numAssignments + i).ProviderConsAddress()
		testAssignments = append(testAssignments,
			types.KeyAssignmentReplacement{
				ProviderAddr: providerAddr.ToSdkConsAddr(),
				PrevCKey:     &consumerKey,
				Power:        rand.Int63(),
			},
		)
	}
	expectedGetAllOrder := testAssignments
	// sorting by KeyAssignmentReplacement.ProviderAddr
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		return bytes.Compare(expectedGetAllOrder[i].ProviderAddr, expectedGetAllOrder[j].ProviderAddr) == -1
	})

	firstTestAssignmentProviderAddr := types.NewProviderConsAddress(testAssignments[0].ProviderAddr)
	pk.SetKeyAssignmentReplacement(ctx, "consumer-2", firstTestAssignmentProviderAddr, *testAssignments[0].PrevCKey, testAssignments[0].Power)
	for _, assignment := range testAssignments {
		providerAddr := types.NewProviderConsAddress(assignment.ProviderAddr)
		pk.SetKeyAssignmentReplacement(ctx, chainID, providerAddr, *assignment.PrevCKey, assignment.Power)
	}

	result := pk.GetAllKeyAssignmentReplacements(ctx, chainID)
	require.Len(t, result, len(testAssignments))
	require.Equal(t, expectedGetAllOrder, result)
}

func TestConsumerAddrsToPruneCRUD(t *testing.T) {
	chainID := consumer
	consumerAddr := types.NewConsumerConsAddress([]byte("consumerAddr1"))
	vscID := uint64(1)

	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	addrsToPrune := keeper.GetConsumerAddrsToPrune(ctx, chainID, vscID).Addresses
	require.Empty(t, addrsToPrune)

	keeper.AppendConsumerAddrsToPrune(ctx, chainID, vscID, consumerAddr)

	addrsToPrune = keeper.GetConsumerAddrsToPrune(ctx, chainID, vscID).Addresses
	require.NotEmpty(t, addrsToPrune, "addresses to prune is empty")
	require.Len(t, addrsToPrune, 1, "addresses to prune is not len 1")
	require.Equal(t, addrsToPrune[0], consumerAddr.ToSdkConsAddr().Bytes())

	keeper.DeleteConsumerAddrsToPrune(ctx, chainID, vscID)
	addrsToPrune = keeper.GetConsumerAddrsToPrune(ctx, chainID, vscID).Addresses
	require.Empty(t, addrsToPrune, "addresses to prune was returned")
}

func TestGetAllConsumerAddrsToPrune(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	rand.Seed(time.Now().Unix())
	chainIDs := []string{"consumer-1", "consumer-2", "consumer-3"}
	numAssignments := 10
	testAssignments := []types.ConsumerAddrsToPrune{}
	for i := 0; i < numAssignments; i++ {
		consumerAddresses := types.AddressList{}
		for j := 0; j < 2*(i+1); j++ {
			addr := cryptotestutil.NewCryptoIdentityFromIntSeed(i * j).SDKValConsAddress()
			consumerAddresses.Addresses = append(consumerAddresses.Addresses, addr)
		}
		testAssignments = append(testAssignments,
			types.ConsumerAddrsToPrune{
				ChainId:       chainIDs[rand.Intn(len(chainIDs))],
				VscId:         rand.Uint64(),
				ConsumerAddrs: &consumerAddresses,
			},
		)
	}
	// select a chainID with more than two assignments
	var chainID string
	for i := range chainIDs {
		chainID = chainIDs[i]
		count := 0
		for _, assignment := range testAssignments {
			if assignment.ChainId == chainID {
				count++
			}
		}
		if count > 2 {
			break
		}
	}
	expectedGetAllOrder := []types.ConsumerAddrsToPrune{}
	for _, assignment := range testAssignments {
		if assignment.ChainId == chainID {
			expectedGetAllOrder = append(expectedGetAllOrder, assignment)
		}
	}
	// sorting by ConsumerAddrsToPrune.VscId
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		return expectedGetAllOrder[i].VscId < expectedGetAllOrder[j].VscId
	})

	for _, assignment := range testAssignments {
		for _, addr := range assignment.ConsumerAddrs.Addresses {
			consumerAddr := types.NewConsumerConsAddress(addr)
			pk.AppendConsumerAddrsToPrune(ctx, assignment.ChainId, assignment.VscId, consumerAddr)
		}
	}

	result := pk.GetAllConsumerAddrsToPrune(ctx, chainID)
	require.Equal(t, expectedGetAllOrder, result)
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
	for _, consAddrToPrune := range k.GetAllConsumerAddrsToPrune(ctx, chainID) {
		for _, cAddr := range consAddrToPrune.ConsumerAddrs.Addresses {
			willBePruned[string(cAddr)] = true
		}
	}

	good := true
	for _, valByConsAddr := range k.GetAllValidatorsByConsumerAddr(ctx, nil) {
		if _, ok := willBePruned[string(valByConsAddr.ConsumerAddr)]; ok {
			// Address will be pruned, everything is fine.
			continue
		}
		// Try to find a validator who has this consumer address currently assigned
		isCurrentlyAssigned := false
		for _, valconsPubKey := range k.GetAllValidatorConsumerPubKeys(ctx, &valByConsAddr.ChainId) {
			consumerAddr, _ := ccvtypes.TMCryptoPublicKeyToConsAddr(*valconsPubKey.ConsumerKey)
			if consumerAddr.Equals(sdk.ConsAddress(valByConsAddr.ConsumerAddr)) {
				isCurrentlyAssigned = true
				break
			}
		}

		if !isCurrentlyAssigned {
			// Will not be pruned, and is not currently assigned: violation
			good = false
			break
		}
	}

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
			3. Consumer     registered: Assign PK1->PK0 and error
			4. Consumer not registered: Assign PK0->CK0 and retrieve PK0->CK0
			5. Consumer not registered: Assign PK0->CK0, PK0->CK1 and retrieve PK0->CK1
			6. Consumer not registered: Assign PK0->CK0, PK1->CK0 and error
			7. Consumer not registered: Assign PK1->PK0 and error
		*/
		{
			name: "0",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValOpAddress(),
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
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID,
					consumerIdentities[0].ConsumerConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].ProviderConsAddress(), providerAddr)
			},
		},
		{
			name: "1",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValOpAddress(),
					).Return(int64(0)),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[1].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValOpAddress(),
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
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID,
					consumerIdentities[1].ConsumerConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].ProviderConsAddress(), providerAddr)
			},
		},
		{
			name: "2",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
					mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
						ctx, providerIdentities[0].SDKValOpAddress(),
					).Return(int64(0)),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
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
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID,
					consumerIdentities[0].ConsumerConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].ProviderConsAddress(), providerAddr)
			},
		},
		{
			name: "3",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						providerIdentities[0].SDKValConsAddress(),
					).Return(providerIdentities[0].SDKStakingValidator(), true),
				)
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				k.SetConsumerClientId(ctx, chainID, "")
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[1].SDKStakingValidator(),
					providerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.Error(t, err)
			},
		},
		{
			name: "4",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
				)
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[0].SDKStakingValidator(),
					consumerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.NoError(t, err)
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID,
					consumerIdentities[0].ConsumerConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].ProviderConsAddress(), providerAddr)
			},
		},
		{
			name: "5",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[1].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
				)
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
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID,
					consumerIdentities[1].ConsumerConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].ProviderConsAddress(), providerAddr)
			},
		},
		{
			name: "6",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerIdentities[0].SDKValConsAddress(),
					).Return(stakingtypes.Validator{}, false),
				)
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
				providerAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID,
					consumerIdentities[0].ConsumerConsAddress())
				require.True(t, found)
				require.Equal(t, providerIdentities[0].ProviderConsAddress(), providerAddr)
			},
		},
		{
			name: "7",
			mockSetup: func(ctx sdk.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						providerIdentities[0].SDKValConsAddress(),
					).Return(providerIdentities[0].SDKStakingValidator(), true),
				)
			},
			doActions: func(ctx sdk.Context, k providerkeeper.Keeper) {
				err := k.AssignConsumerKey(ctx, chainID,
					providerIdentities[1].SDKStakingValidator(),
					providerIdentities[0].TMProtoCryptoPublicKey(),
				)
				require.Error(t, err)
			},
		},
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

// TestCannotReassignDefaultKeyAssignment tests that a validator cannot assign the key it uses on a provider,
// to a consumer, if that validator has not already assigned the key to a consumer.
// Ie. the default key assignment is that a validator uses the same key on a provider as it does on a consumer.
// A validator cannot re-assign the default key assignment if it already uses the default key assignment.
//
// TODO: guarding against edge cases like this could be avoided by refactoring key assignment logic to have less cyclomatic complexity.
func TestCannotReassignDefaultKeyAssignment(t *testing.T) {
	// We only need one identity, a single validator / single key
	cId := cryptotestutil.NewCryptoIdentityFromIntSeed(49827489)

	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Mock that the validator is validating with the single key, as confirmed by provider's staking keeper
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
			cId.SDKValConsAddress(),
		).Return(cId.SDKStakingValidator(), true), // found = true
	)

	// AssignConsumerKey should return an error if we try to re-assign the already existing default key assignment
	err := providerKeeper.AssignConsumerKey(ctx, "chain", cId.SDKStakingValidator(), cId.TMProtoCryptoPublicKey())
	require.Error(t, err)

	// Confirm we're not returning an error for some other reason
	require.Equal(t, "a validator cannot assign the default key assignment unless its key on that consumer has already been assigned: cannot re-assign default key assignment", err.Error())
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
			cons, _ := ccvtypes.TMCryptoPublicKeyToConsAddr(u.PubKey)
			if id.SDKValConsAddress().Equals(cons) {
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
	providerIDS := []*cryptotestutil.CryptoIdentity{}
	// Create some identities which the provider validators can assign to the consumer chain
	assignableIDS := []*cryptotestutil.CryptoIdentity{}
	for i := 0; i < NUM_VALIDATORS; i++ {
		providerIDS = append(providerIDS, cryptotestutil.NewCryptoIdentityFromIntSeed(i))
	}
	// Notice that the assignable identities include the provider identities
	for i := 0; i < NUM_VALIDATORS+NUM_ASSIGNABLE_KEYS; i++ {
		assignableIDS = append(assignableIDS, cryptotestutil.NewCryptoIdentityFromIntSeed(i))
	}

	// Helper: simulates creation of staking module EndBlock updates.
	getStakingUpdates := func() (ret []abci.ValidatorUpdate) {
		// Get a random set of validators to update. It is important to test subsets of all validators.
		validators := rand.Perm(len(providerIDS))[0:rand.Intn(len(providerIDS)+1)]
		for _, i := range validators {
			// Power 0, 1, or 2 represents
			// deletion, update (from 0 or 2), update (from 0 or 1)
			power := rand.Intn(3)
			ret = append(ret, abci.ValidatorUpdate{
				PubKey: providerIDS[i].TMProtoCryptoPublicKey(),
				Power:  int64(power),
			})
		}
		return
	}

	// Helper: simulates creation of assignment tx's to be done.
	getAssignments := func() (ret []Assignment) {
		for i, numAssignments := 0, rand.Intn(NUM_ASSIGNMENTS_PER_BLOCK_MAX); i < numAssignments; i++ {
			randomIxP := rand.Intn(len(providerIDS))
			randomIxC := rand.Intn(len(assignableIDS))
			ret = append(ret, Assignment{
				val: providerIDS[randomIxP].SDKStakingValidator(),
				ck:  assignableIDS[randomIxC].TMProtoCryptoPublicKey(),
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
		providerValset := CreateValSet(providerIDS)
		// NOTE: consumer must have space for provider identities because default key assignments are to provider keys
		consumerValset := CreateValSet(assignableIDS)
		// For each validator on the consumer, record the corresponding provider
		// address as looked up on the provider using GetProviderAddrFromConsumerAddr
		// at a given vscid.
		// consumer consAddr -> vscid -> provider consAddr
		historicSlashQueries := map[string]map[uint64]string{}

		// Sanity check that the validator set update is initialised to 0, for clarity.
		require.Equal(t, k.GetValidatorSetUpdateId(ctx), uint64(0))

		// Mock calls to GetLastValidatorPower to return directly from the providerValset
		mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(
			gomock.Any(),
			gomock.Any(),
		).DoAndReturn(func(_ interface{}, valAddr sdk.ValAddress) int64 {
			// When the mocked method is called, locate the appropriate validator
			// in the provider valset and return its power.
			for i, id := range providerIDS {
				if id.SDKStakingValidator().GetOperator().Equals(valAddr) {
					return providerValset.power[i]
				}
			}
			panic("must find validator")
			// This can be called 0 or more times per block depending on the random
			// assignments that occur
		}).AnyTimes()

		// This implements the assumption that all the provider IDS are added
		// to the system at the beginning of the simulation.
		mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
			gomock.Any(),
			gomock.Any(),
		).DoAndReturn(func(_ interface{}, consP sdk.ConsAddress) (stakingtypes.Validator, bool) {
			for _, id := range providerIDS {
				if id.SDKValConsAddress().Equals(consP) {
					return id.SDKStakingValidator(), true
				}
			}
			return stakingtypes.Validator{}, false
		}).AnyTimes()

		// Helper: apply some updates to both the provider and consumer valsets
		// and increment the provider vscid.
		applyUpdatesAndIncrementVSCID := func(updates []abci.ValidatorUpdate) {
			providerValset.apply(updates)
			updates = k.MustApplyKeyAssignmentToValUpdates(ctx, CHAINID, updates)
			consumerValset.apply(updates)
			// Simulate the VSCID update in EndBlock
			k.IncrementValidatorSetUpdateId(ctx)
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
		applyUpdatesAndIncrementVSCID(getStakingUpdates())

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
			applyUpdatesAndIncrementVSCID(getStakingUpdates())

			// Randomly fast forward the greatest pruned VSCID. This simulates
			// delivery of maturity packets from the consumer chain.
			prunedVscid := greatestPrunedVSCID +
				// +1 and -1 because id was incremented (-1), (+1) to make upper bound inclusive
				rand.Intn(int(k.GetValidatorSetUpdateId(ctx))+1-1-greatestPrunedVSCID)
			k.PruneKeyAssignments(ctx, CHAINID, uint64(prunedVscid))
			greatestPrunedVSCID = prunedVscid

			/*

				Property: Validator Set Replication
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
					ck, found := k.GetValidatorConsumerPubKey(ctx, CHAINID, idP.ProviderConsAddress())
					if !found {
						// Use default if unassigned
						ck = idP.TMProtoCryptoPublicKey()
					}
					consC, err := ccvtypes.TMCryptoPublicKeyToConsAddr(ck)
					require.NoError(t, err)
					// Find the corresponding consumer validator (must always be found)
					for j, idC := range consumerValset.identities {
						if consC.Equals(idC.SDKValConsAddress()) {
							// Ensure powers are the same
							require.Equal(t, providerValset.power[i], consumerValset.power[j])
						}
					}
				}
			}
			// Check validator set replication backward direction
			for i := range consumerValset.identities {
				// For each active validator on the consumer chain
				consC := consumerValset.identities[i].ConsumerConsAddress()
				if 0 < consumerValset.power[i] {
					// Get the provider who assigned the key
					consP := k.GetProviderAddrFromConsumerAddr(ctx, CHAINID, consC)
					// Find the corresponding provider validator (must always be found)
					for j, idP := range providerValset.identities {
						if idP.SDKValConsAddress().Equals(consP.ToSdkConsAddr()) {
							// Ensure powers are the same
							require.Equal(t, providerValset.power[j], consumerValset.power[i])
						}
					}
				}
			}

			/*
				Property: Pruning (bounded storage)
				Check that all keys have been or will eventually be pruned.
			*/

			require.True(t, checkCorrectPruningProperty(ctx, k, CHAINID))

			/*
				Property: Correct Consumer Initiated Slash Lookup

				Check that since the last pruning, it has never been possible to query
				two different provider addresses from the same consumer address.
				We know that the queried provider address was correct at least once,
				from checking the validator set replication property. These two facts
				together guarantee that the slash lookup is always correct.
			*/

			// Build up the historicSlashQueries data structure
			for i := range consumerValset.identities {
				// For each active validator on the consumer chain
				consC := consumerValset.identities[i].ConsumerConsAddress()
				if 0 < consumerValset.power[i] {
					// Get the provider who assigned the key
					consP := k.GetProviderAddrFromConsumerAddr(ctx, CHAINID, consC)

					if _, found := historicSlashQueries[consC.String()]; !found {
						historicSlashQueries[consC.String()] = map[uint64]string{}
					}

					vscid := k.GetValidatorSetUpdateId(ctx) - 1 // -1 since it was incremented before
					// Record the slash query result obtained at this block
					historicSlashQueries[consC.String()][vscid] = consP.String()
				}
			}

			// Check that, for each address known the consumer at some block
			// with vscid st. greatestPrunedVSCID < vscid, there were never
			// conflicting slash query results.
			for _, vscidToConsP := range historicSlashQueries {
				seen := map[string]bool{}
				for vscid, consP := range vscidToConsP {
					if uint64(greatestPrunedVSCID) < vscid {
						// The provider would have returned
						seen[consP] = true
					}
				}
				// No conflicts.
				require.True(t, len(seen) < 2)
			}

		}
		ctrl.Finish()
	}

	for i := 0; i < NUM_EXECUTIONS; i++ {
		runRandomExecution()
	}
}
