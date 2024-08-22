package keeper_test

import (
	"fmt"
	"testing"
	"time"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cometbft/cometbft/proto/tendermint/crypto"

	cryptotestutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

func TestQueryAllPairsValConAddrByConsumerChainID(t *testing.T) {
	consumerId := "0"

	providerConsAddress, err := sdk.ConsAddressFromBech32("cosmosvalcons1wpex7anfv3jhystyv3eq20r35a")
	require.NoError(t, err)
	providerAddr := types.NewProviderConsAddress(providerConsAddress)

	consumerKey := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	consumerAddr, err := ccvtypes.TMCryptoPublicKeyToConsAddr(consumerKey)
	require.NoError(t, err)

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	pk.SetValidatorConsumerPubKey(ctx, consumerId, providerAddr, consumerKey)

	consumerPubKey, found := pk.GetValidatorConsumerPubKey(ctx, consumerId, providerAddr)
	require.True(t, found, "consumer pubkey not found")
	require.NotEmpty(t, consumerPubKey, "consumer pubkey is empty")
	require.Equal(t, consumerPubKey, consumerKey)

	// Request is nil
	_, err = pk.QueryAllPairsValConAddrByConsumerChainID(ctx, nil)
	require.Error(t, err)

	// Request with empty consumer id
	_, err = pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{})
	require.Error(t, err)

	// Request with invalid consumer id
	response, err := pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{ConsumerId: "invalidConsumerId"})
	require.Error(t, err)

	// Request is valid
	response, err = pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{ConsumerId: consumerId})
	require.NoError(t, err)

	expectedResult := types.PairValConAddrProviderAndConsumer{
		ProviderAddress: providerConsAddress.String(),
		ConsumerAddress: consumerAddr.String(),
		ConsumerKey:     &consumerKey,
	}
	require.Equal(t, &consumerKey, response.PairValConAddr[0].ConsumerKey)
	require.Equal(t, &expectedResult, response.PairValConAddr[0])
}

func TestQueryConsumerChainOptedInValidators(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	req := types.QueryConsumerChainOptedInValidatorsRequest{
		ConsumerId: consumerId,
	}

	// error returned from not yet proposed or not yet registered chain
	_, err := pk.QueryConsumerChainOptedInValidators(ctx, &req)
	require.Error(t, err)

	pk.FetchAndIncrementConsumerId(ctx)
	pk.SetConsumerPhase(ctx, consumerId, keeper.Initialized)

	providerAddr1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	providerAddr2 := types.NewProviderConsAddress([]byte("providerAddr2"))
	expectedResponse := types.QueryConsumerChainOptedInValidatorsResponse{
		ValidatorsProviderAddresses: []string{providerAddr1.String(), providerAddr2.String()},
	}

	pk.SetOptedIn(ctx, consumerId, providerAddr1)
	pk.SetOptedIn(ctx, consumerId, providerAddr2)
	res, err := pk.QueryConsumerChainOptedInValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expectedResponse, res)
}

func TestQueryConsumerValidators(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	req := types.QueryConsumerValidatorsRequest{
		ConsumerId: consumerId,
	}

	// error returned from not-existing chain
	_, err := pk.QueryConsumerValidators(ctx, &req)
	require.Error(t, err)

	// set consumer initialization and power shaping params
	blockTimePlus1Hour := ctx.BlockTime().Add(time.Hour)
	pk.SetConsumerInitializationParameters(ctx, consumerId, types.ConsumerInitializationParameters{SpawnTime: &blockTimePlus1Hour})
	pk.SetConsumerPowerShapingParameters(ctx, consumerId, types.PowerShapingParameters{Top_N: 0})

	// create bonded validators
	val1 := createStakingValidator(ctx, mocks, 1, 1, 1)
	pk1, _ := val1.CmtConsPublicKey()
	valConsAddr1, _ := val1.GetConsAddr()
	providerAddr1 := types.NewProviderConsAddress(valConsAddr1)

	val2 := createStakingValidator(ctx, mocks, 1, 2, 2)
	pk2, _ := val2.CmtConsPublicKey()
	valConsAddr2, _ := val2.GetConsAddr()
	providerAddr2 := types.NewProviderConsAddress(valConsAddr2)

	// set expectation to return bonded validators
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 2, []stakingtypes.Validator{val1, val2}, []int64{1, 2}, -1) // -1 to allow the calls "AnyTimes"

	// set max provider consensus vals to include all validators
	params := pk.GetParams(ctx)
	params.MaxProviderConsensusValidators = 2
	pk.SetParams(ctx, params)

	// expect no validator to be returned since the consumer is Opt-In
	res, err := pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Len(t, res.Validators, 0)

	// opt in one validator
	pk.SetOptedIn(ctx, consumerId, providerAddr1)

	// expect opted-in validators
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Len(t, res.Validators, 1)
	require.Equal(t, res.Validators[0].ProviderAddress, providerAddr1.String())

	// update consumer TopN param
	pk.SetConsumerPowerShapingParameters(ctx, consumerId, types.PowerShapingParameters{Top_N: 50})

	// expect both opted-in and topN validator
	expRes := types.QueryConsumerValidatorsResponse{
		Validators: []*types.QueryConsumerValidatorsValidator{
			{ProviderAddress: providerAddr1.String(), ConsumerKey: &pk1, Power: 1},
			{ProviderAddress: providerAddr2.String(), ConsumerKey: &pk2, Power: 2},
		},
	}
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expRes, res)

	// advance time so that the chain looks like it "launched"
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Hour))

	// expect an empty consumer valset
	// since neither QueueVSCPackets or MakeConsumerGenesis was called at this point
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Empty(t, res)

	// set consumer valset
	pk.SetConsumerValSet(ctx, consumerId, []types.ConsensusValidator{
		{
			ProviderConsAddr: providerAddr1.Address.Bytes(),
			Power:            1,
			PublicKey:        &pk1,
		},
		{
			ProviderConsAddr: providerAddr2.Address.Bytes(),
			Power:            2,
			PublicKey:        &pk2,
		},
	})

	// expect same response as before
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expRes, res)
}

func TestQueryConsumerChainsValidatorHasToValidate(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	val := createStakingValidator(ctx, mocks, 1, 1, 1)
	valConsAddr, _ := val.GetConsAddr()
	providerAddr := types.NewProviderConsAddress(valConsAddr)
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valConsAddr).Return(val, nil).AnyTimes()
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 1, []stakingtypes.Validator{val}, []int64{1}, -1) // -1 to allow the calls "AnyTimes"

	req := types.QueryConsumerChainsValidatorHasToValidateRequest{
		ProviderAddress: providerAddr.String(),
	}

	// set up some consumer chains
	consumerChains := []string{"chain1", "chain2", "chain3", "chain4"}
	for _, cc := range consumerChains {
		pk.SetConsumerClientId(ctx, cc, "clientID")
	}

	// set `providerAddr` as a consumer validator on "chain1"
	pk.SetConsumerValidator(ctx, "chain1", types.ConsensusValidator{
		ProviderConsAddr: providerAddr.ToSdkConsAddr(),
		Power:            1,
		PublicKey: &crypto.PublicKey{
			Sum: &crypto.PublicKey_Ed25519{
				Ed25519: []byte{1},
			},
		},
	})

	// set `providerAddr` as an opted-in validator on "chain3"
	pk.SetOptedIn(ctx, "chain3", providerAddr)

	// set max provider consensus vals to include all validators
	params := pk.GetParams(ctx)
	params.MaxProviderConsensusValidators = 3
	pk.SetParams(ctx, params)

	// `providerAddr` has to validate "chain1" because it is a consumer validator in this chain, as well as "chain3"
	// because it opted in, in "chain3" and `providerAddr` belongs to the bonded validators
	expectedChains := []string{"chain1", "chain3"}

	res, err := pk.QueryConsumerChainsValidatorHasToValidate(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, expectedChains, res.ConsumerChainIds)
}

func TestQueryValidatorConsumerCommissionRate(t *testing.T) {
	consumerId := "0"

	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))
	req := types.QueryValidatorConsumerCommissionRateRequest{
		ConsumerId:      consumerId,
		ProviderAddress: providerAddr.String(),
	}

	// error returned from not yet proposed or not yet registered chain
	_, err := pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Error(t, err)

	pk.FetchAndIncrementConsumerId(ctx)
	pk.SetConsumerPhase(ctx, consumerId, keeper.Initialized)

	// validator with set consumer commission rate
	expectedCommissionRate := math.LegacyMustNewDecFromStr("0.123")
	pk.SetConsumerCommissionRate(ctx, consumerId, providerAddr, expectedCommissionRate)
	res, _ := pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Equal(t, expectedCommissionRate, res.Rate)

	// validator with no set consumer commission rate
	pk.DeleteConsumerCommissionRate(ctx, consumerId, providerAddr)
	expectedCommissionRate = math.LegacyMustNewDecFromStr("0.456")

	// because no consumer commission rate is set, the validator's set commission rate on the provider is used
	val := stakingtypes.Validator{Commission: stakingtypes.Commission{CommissionRates: stakingtypes.CommissionRates{Rate: expectedCommissionRate}}}
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
		ctx, providerAddr.ToSdkConsAddr()).Return(val, nil).Times(1)
	res, _ = pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Equal(t, expectedCommissionRate, res.Rate)
}

// TestGetConsumerChain tests GetConsumerChain behaviour correctness
func TestGetConsumerChain(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainIDs := []string{"chain-1", "chain-2", "chain-3", "chain-4"}

	// mock the validator set
	vals := []stakingtypes.Validator{
		{OperatorAddress: "cosmosvaloper1c4k24jzduc365kywrsvf5ujz4ya6mwympnc4en"}, // 50 power
		{OperatorAddress: "cosmosvaloper196ax4vc0lwpxndu9dyhvca7jhxp70rmcvrj90c"}, // 150 power
		{OperatorAddress: "cosmosvaloper1clpqr4nrk4khgkxj78fcwwh6dl3uw4epsluffn"}, // 300 power
		{OperatorAddress: "cosmosvaloper1tflk30mq5vgqjdly92kkhhq3raev2hnz6eete3"}, // 500 power
	}
	powers := []int64{50, 150, 300, 500} // sum = 1000
	maxValidators := uint32(180)
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, maxValidators, vals, powers, -1) // -1 to allow the calls "AnyTimes"

	for i, val := range vals {
		valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
		require.NoError(t, err)
		mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), valAddr).Return(powers[i], nil).AnyTimes()
	}

	// set Top N parameters, client ids and expected result
	topNs := []uint32{0, 70, 90, 100}
	expectedMinPowerInTopNs := []int64{
		-1,  // Top N is 0, so not a Top N chain
		300, // 500 and 300 are in Top 70%
		150, // 150 is also in the top 90%,
		50,  // everyone is in the top 100%
	}

	validatorSetCaps := []uint32{0, 5, 10, 20}
	validatorPowerCaps := []uint32{0, 5, 10, 33}
	allowlists := [][]types.ProviderConsAddress{
		{},
		{types.NewProviderConsAddress([]byte("providerAddr1")), types.NewProviderConsAddress([]byte("providerAddr2"))},
		{types.NewProviderConsAddress([]byte("providerAddr3"))},
		{},
	}

	denylists := [][]types.ProviderConsAddress{
		{types.NewProviderConsAddress([]byte("providerAddr4")), types.NewProviderConsAddress([]byte("providerAddr5"))},
		{},
		{types.NewProviderConsAddress([]byte("providerAddr6"))},
		{},
	}

	expectedGetAllOrder := []types.Chain{}
	for i, chainID := range chainIDs {
		clientID := fmt.Sprintf("client-%d", len(chainIDs)-i)
		topN := topNs[i]
		pk.SetConsumerClientId(ctx, chainID, clientID)
		pk.SetConsumerPowerShapingParameters(ctx, chainID, types.PowerShapingParameters{
			Top_N:              topN,
			ValidatorSetCap:    validatorSetCaps[i],
			ValidatorsPowerCap: validatorPowerCaps[i],
		})
		pk.SetMinimumPowerInTopN(ctx, chainID, expectedMinPowerInTopNs[i])
		for _, addr := range allowlists[i] {
			pk.SetAllowlist(ctx, chainID, addr)
		}
		for _, addr := range denylists[i] {
			pk.SetDenylist(ctx, chainID, addr)
		}
		strAllowlist := make([]string, len(allowlists[i]))
		for j, addr := range allowlists[i] {
			strAllowlist[j] = addr.String()
		}

		strDenylist := make([]string, len(denylists[i]))
		for j, addr := range denylists[i] {
			strDenylist[j] = addr.String()
		}

		expectedGetAllOrder = append(expectedGetAllOrder,
			types.Chain{
				ChainId:            chainID,
				ClientId:           clientID,
				Top_N:              topN,
				MinPowerInTop_N:    expectedMinPowerInTopNs[i],
				ValidatorSetCap:    validatorSetCaps[i],
				ValidatorsPowerCap: validatorPowerCaps[i],
				Allowlist:          strAllowlist,
				Denylist:           strDenylist,
			})
	}

	for i, chainID := range pk.GetAllActiveConsumerIds(ctx) {
		c, err := pk.GetConsumerChain(ctx, chainID)
		require.NoError(t, err)
		require.Equal(t, expectedGetAllOrder[i], c)
	}
}

func TestQueryConsumerIdFromClientId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.QueryConsumerIdFromClientId(ctx, &types.QueryConsumerIdFromClientIdRequest{ClientId: "clientId"})
	require.Error(t, err)
	require.ErrorContains(t, err, "no known consumer chain")

	expectedConsumerId := "consumerId"
	providerKeeper.SetClientIdToConsumerId(ctx, "clientId", expectedConsumerId)

	res, err := providerKeeper.QueryConsumerIdFromClientId(ctx, &types.QueryConsumerIdFromClientIdRequest{ClientId: "clientId"})
	require.NoError(t, err)
	require.Equal(t, expectedConsumerId, res.ConsumerId)
}
