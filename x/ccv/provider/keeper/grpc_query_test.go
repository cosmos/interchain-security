package keeper_test

import (
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	sdktypes "github.com/cosmos/cosmos-sdk/types"

	cryptotestutil "github.com/cosmos/interchain-security/v4/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
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

func TestQueryConsumerChainOptedInValidators(t *testing.T) {
	chainID := "chainID"

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	req := types.QueryConsumerChainOptedInValidatorsRequest{
		ChainId: chainID,
	}

	// error returned from not yet proposed or not yet registered chain
	_, err := pk.QueryConsumerChainOptedInValidators(ctx, &req)
	require.Error(t, err)

	pk.SetProposedConsumerChain(ctx, chainID, 1)

	providerAddr1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	providerAddr2 := types.NewProviderConsAddress([]byte("providerAddr2"))
	expectedResponse := types.QueryConsumerChainOptedInValidatorsResponse{
		ValidatorsProviderAddresses: []string{providerAddr1.String(), providerAddr2.String()},
	}

	pk.SetOptedIn(ctx, chainID, providerAddr1)
	pk.SetOptedIn(ctx, chainID, providerAddr2)
	res, err := pk.QueryConsumerChainOptedInValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expectedResponse, res)
}

func TestQueryConsumerChainConsumerValidators(t *testing.T) {
	chainID := "chainID"

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	req := types.QueryConsumerChainConsumerValidatorsRequest{
		ChainId: chainID,
	}

	// error returned from not-started chain
	_, err := pk.QueryConsumerChainConsumerValidators(ctx, &req)
	require.Error(t, err)

	providerAddr1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	consumerKey1 := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	consumerValidator1 := types.ConsumerValidator{ProviderConsAddr: providerAddr1.ToSdkConsAddr(), Power: 1, ConsumerPublicKey: &consumerKey1}

	providerAddr2 := types.NewProviderConsAddress([]byte("providerAddr2"))
	consumerKey2 := cryptotestutil.NewCryptoIdentityFromIntSeed(2).TMProtoCryptoPublicKey()
	consumerValidator2 := types.ConsumerValidator{ProviderConsAddr: providerAddr2.ToSdkConsAddr(), Power: 2, ConsumerPublicKey: &consumerKey2}

	expectedResponse := types.QueryConsumerChainConsumerValidatorsResponse{
		Validators: []*types.QueryConsumerChainConsumerValidator{
			{providerAddr1.String(), &consumerKey1, 1},
			{providerAddr2.String(), &consumerKey2, 2},
		},
	}

	// set up the client id so the chain looks like it "started"
	pk.SetConsumerClientId(ctx, chainID, "clientID")
	pk.SetConsumerValSet(ctx, chainID, []types.ConsumerValidator{consumerValidator1, consumerValidator2})

	res, err := pk.QueryConsumerChainConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expectedResponse, res)
}

func TestQueryConsumerChainsValidatorHasToValidate(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	val := createStakingValidator(ctx, mocks, 1, 1)
	valConsAddr, _ := val.GetConsAddr()
	providerAddr := types.NewProviderConsAddress(valConsAddr)
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valConsAddr).Return(val, true).AnyTimes()
	mocks.MockStakingKeeper.EXPECT().GetLastValidators(ctx).Return([]stakingtypes.Validator{val}).AnyTimes()

	req := types.QueryConsumerChainsValidatorHasToValidateRequest{
		ProviderAddress: providerAddr.String(),
	}

	// set up some consumer chains
	consumerChains := []string{"chain1", "chain2", "chain3", "chain4"}
	for _, cc := range consumerChains {
		pk.SetConsumerClientId(ctx, cc, "clientID")
	}

	// set `providerAddr` as a consumer validator on "chain1"
	pk.SetConsumerValidator(ctx, "chain1", types.ConsumerValidator{
		ProviderConsAddr: providerAddr.ToSdkConsAddr(),
		Power:            1,
		ConsumerPublicKey: &crypto.PublicKey{
			Sum: &crypto.PublicKey_Ed25519{
				Ed25519: []byte{1},
			}}})

	// set `providerAddr` as an opted-in validator on "chain3"
	pk.SetOptedIn(ctx, "chain3", providerAddr)

	// `providerAddr` has to validate "chain1" because it is a consumer validator in this chain, as well as "chain3"
	// because it opted in, in "chain3" and `providerAddr` belongs to the bonded validators (see the mocking of `GetLastValidators`
	// above)
	expectedChains := []string{"chain1", "chain3"}

	res, err := pk.QueryConsumerChainsValidatorHasToValidate(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, expectedChains, res.ConsumerChainIds)
}

func TestQueryValidatorConsumerCommissionRate(t *testing.T) {
	chainID := "chainID"

	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))
	req := types.QueryValidatorConsumerCommissionRateRequest{
		ChainId:         chainID,
		ProviderAddress: providerAddr.String(),
	}

	// error returned from not yet proposed or not yet registered chain
	_, err := pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Error(t, err)

	pk.SetProposedConsumerChain(ctx, chainID, 1)
	// validator with set consumer commission rate
	expectedCommissionRate, _ := sdktypes.NewDecFromStr("0.123")
	pk.SetConsumerCommissionRate(ctx, chainID, providerAddr, expectedCommissionRate)
	res, _ := pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Equal(t, expectedCommissionRate, res.Rate)

	// validator with no set consumer commission rate
	pk.DeleteConsumerCommissionRate(ctx, chainID, providerAddr)
	expectedCommissionRate, _ = sdktypes.NewDecFromStr("0.456")

	// because no consumer commission rate is set, the validator's set commission rate on the provider is used
	val := stakingtypes.Validator{Commission: stakingtypes.Commission{CommissionRates: stakingtypes.CommissionRates{Rate: expectedCommissionRate}}}
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
		ctx, providerAddr.ToSdkConsAddr()).Return(val, true).Times(1)
	res, _ = pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Equal(t, expectedCommissionRate, res.Rate)
}
