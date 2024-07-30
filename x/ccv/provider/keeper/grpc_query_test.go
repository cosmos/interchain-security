package keeper_test

import (
	"fmt"
	"testing"

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
	chainID := consumer

	providerConsAddress, err := sdk.ConsAddressFromBech32("cosmosvalcons1wpex7anfv3jhystyv3eq20r35a")
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
	response, err := pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{ConsumerId: "invalidChainId"})
	require.NoError(t, err)
	require.Equal(t, []*types.PairValConAddrProviderAndConsumer{}, response.PairValConAddr)

	// Request is valid
	response, err = pk.QueryAllPairsValConAddrByConsumerChainID(ctx, &types.QueryAllPairsValConAddrByConsumerChainIDRequest{ConsumerId: chainID})
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
	chainID := "chainID"

	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	req := types.QueryConsumerChainOptedInValidatorsRequest{
		ConsumerId: chainID,
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

func TestQueryConsumerValidators(t *testing.T) {
	chainID := "chainID"

	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	req := types.QueryConsumerValidatorsRequest{
		ConsumerId: chainID,
	}

	// error returned from not-started chain
	_, err := pk.QueryConsumerValidators(ctx, &req)
	require.Error(t, err)

	providerAddr1 := types.NewProviderConsAddress([]byte("providerAddr1"))
	consumerKey1 := cryptotestutil.NewCryptoIdentityFromIntSeed(1).TMProtoCryptoPublicKey()
	consumerValidator1 := types.ConsensusValidator{ProviderConsAddr: providerAddr1.ToSdkConsAddr(), Power: 1, PublicKey: &consumerKey1}
	expectedCommissionRate1 := math.LegacyMustNewDecFromStr("0.123")
	pk.SetConsumerCommissionRate(ctx, chainID, providerAddr1, expectedCommissionRate1)

	providerAddr2 := types.NewProviderConsAddress([]byte("providerAddr2"))
	consumerKey2 := cryptotestutil.NewCryptoIdentityFromIntSeed(2).TMProtoCryptoPublicKey()
	consumerValidator2 := types.ConsensusValidator{ProviderConsAddr: providerAddr2.ToSdkConsAddr(), Power: 2, PublicKey: &consumerKey2}
	expectedCommissionRate2 := math.LegacyMustNewDecFromStr("0.123")
	pk.SetConsumerCommissionRate(ctx, chainID, providerAddr2, expectedCommissionRate2)

	expectedResponse := types.QueryConsumerValidatorsResponse{
		Validators: []*types.QueryConsumerValidatorsValidator{
			{ProviderAddress: providerAddr1.String(), ConsumerKey: &consumerKey1, Power: 1, Rate: expectedCommissionRate1},
			{ProviderAddress: providerAddr2.String(), ConsumerKey: &consumerKey2, Power: 2, Rate: expectedCommissionRate2},
		},
	}

	// set up the client id so the chain looks like it "started"
	pk.SetConsumerClientId(ctx, chainID, "clientID")
	pk.SetConsumerValSet(ctx, chainID, []types.ConsensusValidator{consumerValidator1, consumerValidator2})

	res, err := pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expectedResponse, res)

	// validator with no set consumer commission rate
	pk.DeleteConsumerCommissionRate(ctx, chainID, providerAddr1)
	expectedCommissionRate := math.LegacyMustNewDecFromStr("0.456")
	// because no consumer commission rate is set, the validator's set commission rate on the provider is used
	val := stakingtypes.Validator{Commission: stakingtypes.Commission{CommissionRates: stakingtypes.CommissionRates{Rate: expectedCommissionRate}}}
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
		ctx, providerAddr1.ToSdkConsAddr()).Return(val, nil).Times(1)
	res, _ = pk.QueryConsumerValidators(ctx, &req)
	require.Equal(t, expectedCommissionRate, res.Validators[0].Rate)
}

func TestQueryConsumerChainsValidatorHasToValidate(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	val := createStakingValidator(ctx, mocks, 1, 1, 1)
	valConsAddr, _ := val.GetConsAddr()
	providerAddr := types.NewProviderConsAddress(valConsAddr)
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valConsAddr).Return(val, nil).AnyTimes()
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 1, []stakingtypes.Validator{val}, -1) // -1 to allow the calls "AnyTimes"

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
	chainID := "chainID"

	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))
	req := types.QueryValidatorConsumerCommissionRateRequest{
		ConsumerId:      chainID,
		ProviderAddress: providerAddr.String(),
	}

	// error returned from not yet proposed or not yet registered chain
	_, err := pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Error(t, err)

	pk.SetProposedConsumerChain(ctx, chainID, 1)
	// validator with set consumer commission rate
	expectedCommissionRate := math.LegacyMustNewDecFromStr("0.123")
	pk.SetConsumerCommissionRate(ctx, chainID, providerAddr, expectedCommissionRate)
	res, _ := pk.QueryValidatorConsumerCommissionRate(ctx, &req)
	require.Equal(t, expectedCommissionRate, res.Rate)

	// validator with no set consumer commission rate
	pk.DeleteConsumerCommissionRate(ctx, chainID, providerAddr)
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
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, maxValidators, vals, -1) // -1 to allow the calls "AnyTimes"

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
		pk.SetTopN(ctx, chainID, topN)
		pk.SetValidatorSetCap(ctx, chainID, validatorSetCaps[i])
		pk.SetValidatorsPowerCap(ctx, chainID, validatorPowerCaps[i])
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

	for i, chainID := range pk.GetAllRegisteredAndProposedChainIDs(ctx) {
		c, err := pk.GetConsumerChain(ctx, chainID)
		require.NoError(t, err)
		require.Equal(t, expectedGetAllOrder[i], c)
	}
}
