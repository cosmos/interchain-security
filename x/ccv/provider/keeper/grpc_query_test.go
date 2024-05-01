package keeper_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	sdktypes "github.com/cosmos/cosmos-sdk/types"

	cryptotestutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

func TestQueryAllPairsValConAddrByConsumerChainID(t *testing.T) {
	chainID := consumer

	providerConsAddress, err := sdktypes.ConsAddressFromBech32("cosmosvalcons1wpex7anfv3jhystyv3eq20r35a")
	require.NoError(t, err)
	providerAddr := types.NewProviderConsAddress(providerConsAddress)

	consumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	consumerAddr, err := ccvtypes.TMCryptoPublicKeyToConsAddr(consumerKey)
	require.NoError(t, err)

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	pk.SetValidatorConsumerPubKey(ctx, chainID, providerAddr, consumerKey)

	consumerPubKey, found := pk.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	require.True(t, found, "consumer pubkey not found")
	require.NotEmpty(t, consumerPubKey, "consumer pubkey is empty")
	require.Equal(t, consumerPubKey, consumerKey)

	// Request is nil
	_, err = pk.QueryAllPairsValConAddrByConsumerChainID(ctx, nil)
	require.Error(t, err)

	// Request with chainId is empty
	_, err = pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{})
	require.Error(t, err)

	// Request with chainId is invalid
	response, err := pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{ChainId: "invalidChainId"})
	require.NoError(t, err)
	require.Equal(t, []*types.PairValConAddrProviderAndConsumer{}, response.PairValConAddr)

	// Request is valid
	response, err = pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{ChainId: chainID})
	require.NoError(t, err)

	expectedResult := types.PairValConAddrProviderAndConsumer{
		ProviderAddress: providerConsAddress.String(),
		ConsumerAddress: consumerAddr.String(),
		ConsumerKey:     &consumerKey,
	}
	require.Equal(t, &consumerKey, response.PairValConAddr[0].ConsumerKey)
	require.Equal(t, &expectedResult, response.PairValConAddr[0])
}

func TestQueryOldestUnconfirmedVsc(t *testing.T) {
	chainID := consumer

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now().UTC()
	pk.SetVscSendTimestamp(ctx, chainID, 2, now)
	pk.SetVscSendTimestamp(ctx, chainID, 1, now)
	pk.SetConsumerClientId(ctx, chainID, "client-1")

	// Request is nil
	_, err := pk.QueryOldestUnconfirmedVsc(ctx, nil)
	require.Error(t, err)

	// Request with chainId is empty
	_, err = pk.QueryOldestUnconfirmedVsc(ctx, &types.QueryOldestUnconfirmedVscRequest{})
	require.Error(t, err)

	// Request with chainId is invalid
	_, err = pk.QueryOldestUnconfirmedVsc(ctx, &types.QueryOldestUnconfirmedVscRequest{ChainId: "invalidChainId"})
	require.Error(t, err)

	// Request is valid
	response, err := pk.QueryOldestUnconfirmedVsc(ctx, &types.QueryOldestUnconfirmedVscRequest{ChainId: chainID})
	require.NoError(t, err)
	expectedResult := types.VscSendTimestamp{
		VscId:     1,
		Timestamp: now,
	}
	require.Equal(t, expectedResult, response.VscSendTimestamp)

	// Make sure that the oldest is queried
	pk.DeleteVscSendTimestamp(ctx, chainID, 1)
	response, err = pk.QueryOldestUnconfirmedVsc(ctx, &types.QueryOldestUnconfirmedVscRequest{ChainId: chainID})
	require.NoError(t, err)
	expectedResult = types.VscSendTimestamp{
		VscId:     2,
		Timestamp: now,
	}
	require.Equal(t, expectedResult, response.VscSendTimestamp)
}
