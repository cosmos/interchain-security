package keeper_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	cryptotestutil "github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

func TestQueryAllPairsValConAddrByConsumerChainID(t *testing.T) {
	chainID := consumer
	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))
	consumerAddr := types.NewConsumerConsAddress([]byte("consumerAddr"))

	consumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	pk.SetValidatorByConsumerAddr(ctx, chainID, consumerAddr, providerAddr)
	pk.SetValidatorConsumerPubKey(ctx, chainID, providerAddr, consumerKey)
	pk.SetKeyAssignmentReplacement(ctx, chainID, providerAddr, consumerKey, 100)

	consumerPubKey, found := pk.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	require.True(t, found, "consumer pubkey not found")
	require.NotEmpty(t, consumerPubKey, "consumer pubkey is empty")
	require.Equal(t, consumerPubKey, consumerKey)

	// Request is nil
	_, err := pk.QueryAllPairsValConAddrByConsumerChainID(ctx, nil)
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
		ProviderAddress: "providerAddr",
		ConsumerAddress: "consumerAddr",
		ConsumerKey:     &consumerKey,
	}
	require.Equal(t, &consumerKey, response.PairValConAddr[0].ConsumerKey)
	require.Equal(t, &expectedResult, response.PairValConAddr[0])
}
