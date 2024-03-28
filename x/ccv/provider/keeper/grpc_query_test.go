package keeper_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	cryptotestutil "github.com/cosmos/interchain-security/v4/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

func TestQueryAllPairsValConAddrByConsumerChainID(t *testing.T) {
	chainID := consumer
	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

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
		ProviderAddress: "providerAddr",
		ConsumerAddress: string(consumerAddr),
		ConsumerKey:     &consumerKey,
	}
	require.Equal(t, &consumerKey, response.PairValConAddr[0].ConsumerKey)
	require.Equal(t, &expectedResult, response.PairValConAddr[0])
}

func TestQueryFirstVscSendTimestamp(t *testing.T) {
	chainID := consumer

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	var vscID uint64 = 1
	now := time.Now().UTC()
	pk.SetVscSendTimestamp(ctx, chainID, vscID, now)

	// Request is nil
	_, err := pk.QueryFirstVscSendTimestamp(ctx, nil)
	require.Error(t, err)

	// Request with chainId is empty
	_, err = pk.QueryFirstVscSendTimestamp(ctx, &types.QueryFirstVscSendTimestampRequest{})
	require.Error(t, err)

	// Request with chainId is invalid
	_, err = pk.QueryFirstVscSendTimestamp(ctx, &types.QueryFirstVscSendTimestampRequest{ChainId: "invalidChainId"})
	require.Error(t, err)

	// Request is valid
	response, err := pk.QueryFirstVscSendTimestamp(ctx, &types.QueryFirstVscSendTimestampRequest{ChainId: chainID})
	require.NoError(t, err)
	expectedResult := types.VscSendTimestamp{
		VscId:     vscID,
		Timestamp: now,
	}
	require.Equal(t, expectedResult, response.VscSendTimestamp)
}
