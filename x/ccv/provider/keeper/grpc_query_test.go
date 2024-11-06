package keeper_test

import (
	"bytes"
	"fmt"
	"sort"
	"strconv"
	"testing"
	"time"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"

	"github.com/cometbft/cometbft/proto/tendermint/crypto"

	sdkquery "github.com/cosmos/cosmos-sdk/types/query"
	ibcexported "github.com/cosmos/ibc-go/v8/modules/core/exported"
	ibctm "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	cryptotestutil "github.com/cosmos/interchain-security/v6/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

func TestQueryAllPairsValConsAddrByConsumer(t *testing.T) {
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
	_, err = pk.QueryAllPairsValConsAddrByConsumer(ctx, nil)
	require.Error(t, err)

	// Request with empty consumer id
	_, err = pk.QueryAllPairsValConsAddrByConsumer(ctx, &types.QueryAllPairsValConsAddrByConsumerRequest{})
	require.Error(t, err)

	// Request with invalid consumer id
	_, err = pk.QueryAllPairsValConsAddrByConsumer(ctx, &types.QueryAllPairsValConsAddrByConsumerRequest{ConsumerId: "invalidConsumerId"})
	require.Error(t, err)

	// Request is valid
	response, err := pk.QueryAllPairsValConsAddrByConsumer(ctx, &types.QueryAllPairsValConsAddrByConsumerRequest{ConsumerId: consumerId})
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
	pk.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_INITIALIZED)

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

	// set the consumer to the "registered" phase
	pk.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_REGISTERED)

	// set power shaping params
	err = pk.SetConsumerPowerShapingParameters(ctx, consumerId, types.PowerShapingParameters{})
	require.NoError(t, err)

	// expect empty valset
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 0, []stakingtypes.Validator{}, 1) // -1 to allow the calls "AnyTimes"
	res, err := pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Len(t, res.Validators, 0)

	// create bonded validators
	val1 := createStakingValidator(ctx, mocks, 1, 1)
	pk1, _ := val1.CmtConsPublicKey()
	valConsAddr1, _ := val1.GetConsAddr()
	providerAddr1 := types.NewProviderConsAddress(valConsAddr1)
	consumerValidator1 := types.ConsensusValidator{ProviderConsAddr: providerAddr1.ToSdkConsAddr(), Power: 1, PublicKey: &pk1}
	val1.Tokens = sdk.TokensFromConsensusPower(1, sdk.DefaultPowerReduction)
	val1.Description = stakingtypes.Description{Moniker: "ConsumerValidator1"}
	val1.Commission.Rate = math.LegacyMustNewDecFromStr("0.123")

	val2 := createStakingValidator(ctx, mocks, 2, 2)
	pk2, _ := val2.CmtConsPublicKey()
	valConsAddr2, _ := val2.GetConsAddr()
	providerAddr2 := types.NewProviderConsAddress(valConsAddr2)
	consumerValidator2 := types.ConsensusValidator{ProviderConsAddr: providerAddr2.ToSdkConsAddr(), Power: 2, PublicKey: &pk2}
	val2.Tokens = sdk.TokensFromConsensusPower(2, sdk.DefaultPowerReduction)
	val2.Description = stakingtypes.Description{Moniker: "ConsumerValidator2"}
	val2.Commission.Rate = math.LegacyMustNewDecFromStr("0.456")

	val3 := createStakingValidator(ctx, mocks, 3, 3)
	pk3, _ := val3.CmtConsPublicKey()
	valConsAddr3, _ := val3.GetConsAddr()
	providerAddr3 := types.NewProviderConsAddress(valConsAddr3)
	consumerValidator3 := types.ConsensusValidator{ProviderConsAddr: providerAddr3.ToSdkConsAddr(), Power: 3, PublicKey: &pk3}
	val3.Tokens = sdk.TokensFromConsensusPower(3, sdk.DefaultPowerReduction)
	val3.Description = stakingtypes.Description{Moniker: "ConsumerValidator3"}

	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valConsAddr1).Return(val1, nil).AnyTimes()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valConsAddr2).Return(val2, nil).AnyTimes()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valConsAddr3).Return(val3, nil).AnyTimes()
	mocks.MockStakingKeeper.EXPECT().PowerReduction(ctx).Return(sdk.DefaultPowerReduction).AnyTimes()
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 2, []stakingtypes.Validator{val1, val2}, -1) // -1 to allow the calls "AnyTimes"

	// set max provider consensus vals to include all validators
	params := pk.GetParams(ctx)
	params.MaxProviderConsensusValidators = 3
	pk.SetParams(ctx, params)

	// expect no validator to be returned since the consumer is Opt-In
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Len(t, res.Validators, 0)

	// opt in one validator
	pk.SetOptedIn(ctx, consumerId, providerAddr1)

	// set a consumer commission rate for val1
	val1ConsComRate := math.LegacyMustNewDecFromStr("0.789")
	pk.SetConsumerCommissionRate(ctx, consumerId, providerAddr1, val1ConsComRate)

	// expect opted-in validator
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Len(t, res.Validators, 1)
	require.Equal(t, res.Validators[0].ProviderAddress, providerAddr1.String())

	// update consumer TopN param
	err = pk.SetConsumerPowerShapingParameters(ctx, consumerId, types.PowerShapingParameters{Top_N: 50})
	require.NoError(t, err)

	// expect both opted-in and topN validator
	expRes := types.QueryConsumerValidatorsResponse{
		Validators: []*types.QueryConsumerValidatorsValidator{
			{
				ProviderAddress:         providerAddr1.String(),
				ConsumerKey:             &pk1,
				ConsumerPower:           1,
				ConsumerCommissionRate:  val1ConsComRate,
				Description:             val1.Description,
				ProviderOperatorAddress: val1.OperatorAddress,
				Jailed:                  val1.Jailed,
				Status:                  val1.Status,
				ProviderTokens:          val1.Tokens,
				ProviderCommissionRate:  val1.Commission.Rate,
				ProviderPower:           1,
				ValidatesCurrentEpoch:   true,
			},
			{
				ProviderAddress:         providerAddr2.String(),
				ConsumerKey:             &pk2,
				ConsumerPower:           2,
				ConsumerCommissionRate:  val2.Commission.Rate,
				Description:             val2.Description,
				ProviderOperatorAddress: val2.OperatorAddress,
				Jailed:                  val2.Jailed,
				Status:                  val2.Status,
				ProviderTokens:          val2.Tokens,
				ProviderCommissionRate:  val2.Commission.Rate,
				ProviderPower:           2,
				ValidatesCurrentEpoch:   true,
			},
		},
	}

	// sort the address of the validators by ascending lexical order as they were persisted to the store
	sort.Slice(expRes.Validators, func(i, j int) bool {
		return bytes.Compare(
			expRes.Validators[i].ConsumerKey.GetEd25519(),
			expRes.Validators[j].ConsumerKey.GetEd25519(),
		) == -1
	})

	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expRes, res)

	// expect same result when consumer is in "initialized" phase
	pk.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_INITIALIZED)
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expRes, res)

	// set consumer to the "launched" phase
	pk.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_LAUNCHED)

	// expect an empty consumer valset
	// since neither QueueVSCPackets or MakeConsumerGenesis was called at this point
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Empty(t, res)

	// set consumer valset
	err = pk.SetConsumerValSet(ctx, consumerId, []types.ConsensusValidator{
		consumerValidator1,
		consumerValidator2,
		consumerValidator3,
	})
	require.NoError(t, err)

	expRes.Validators = append(expRes.Validators, &types.QueryConsumerValidatorsValidator{
		ProviderAddress:         providerAddr3.String(),
		ConsumerKey:             &pk3,
		ConsumerPower:           3,
		ConsumerCommissionRate:  val3.Commission.Rate,
		Description:             val3.Description,
		ProviderOperatorAddress: val3.OperatorAddress,
		Jailed:                  val3.Jailed,
		Status:                  val3.Status,
		ProviderTokens:          val3.Tokens,
		ProviderCommissionRate:  val3.Commission.Rate,
		ProviderPower:           3,
		ValidatesCurrentEpoch:   true,
	})

	// sort the address of the validators by ascending lexical order as they were persisted to the store
	sort.Slice(expRes.Validators, func(i, j int) bool {
		return bytes.Compare(
			expRes.Validators[i].ConsumerKey.GetEd25519(),
			expRes.Validators[j].ConsumerKey.GetEd25519(),
		) == -1
	})

	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expRes, res)

	// validator with no set consumer commission rate
	pk.DeleteConsumerCommissionRate(ctx, consumerId, providerAddr1)
	// because no consumer commission rate is set, the validator's set commission rate on the provider is used
	res, err = pk.QueryConsumerValidators(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, val1.Commission.Rate, res.Validators[0].ConsumerCommissionRate)
}

func TestQueryConsumerChainsValidatorHasToValidate(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	val := createStakingValidator(ctx, mocks, 1, 1)
	valConsAddr, _ := val.GetConsAddr()
	providerAddr := types.NewProviderConsAddress(valConsAddr)
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valConsAddr).Return(val, nil).AnyTimes()
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 1, []stakingtypes.Validator{val}, -1) // -1 to allow the calls "AnyTimes"

	req := types.QueryConsumerChainsValidatorHasToValidateRequest{
		ProviderAddress: providerAddr.String(),
	}

	consumerNum := 4
	consumerIds := make([]string, consumerNum)

	msgServer := keeper.NewMsgServerImpl(&pk)

	// set up some consumer chains
	for i := 0; i < consumerNum; i++ {
		revisionNumber := i + 1
		chainID := "consumer-" + strconv.Itoa(revisionNumber)
		metadata := types.ConsumerMetadata{Name: chainID}
		initializationParameters := types.DefaultConsumerInitializationParameters()
		initializationParameters.InitialHeight.RevisionNumber = uint64(revisionNumber)
		msg := types.MsgCreateConsumer{
			ChainId:                  chainID,
			Metadata:                 metadata,
			InitializationParameters: &initializationParameters,
		}
		resp, err := msgServer.CreateConsumer(ctx, &msg)
		require.NoError(t, err)
		consumerId := resp.ConsumerId

		// set a consumer client id, so that `GetAllConsumersWithIBCClients` is non-empty
		clientID := "client-" + strconv.Itoa(i)
		pk.SetConsumerClientId(ctx, consumerId, clientID)

		pk.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_LAUNCHED)
		consumerIds[i] = consumerId
	}

	// set `providerAddr` as a consumer validator on first consumer chain
	err := pk.SetConsumerValidator(ctx, consumerIds[0], types.ConsensusValidator{
		ProviderConsAddr: providerAddr.ToSdkConsAddr(),
		Power:            1,
		PublicKey: &crypto.PublicKey{
			Sum: &crypto.PublicKey_Ed25519{
				Ed25519: []byte{1},
			},
		},
	})
	require.NoError(t, err)

	// set `providerAddr` as an opted-in validator on third consumer chain
	pk.SetOptedIn(ctx, consumerIds[2], providerAddr)

	// set max provider consensus vals to include all validators
	params := pk.GetParams(ctx)
	params.MaxProviderConsensusValidators = 3
	pk.SetParams(ctx, params)

	// `providerAddr` has to validate
	// - first consumer because it is a consumer validator in this chain,
	// - third consumer because it opted in
	expectedChains := []string{consumerIds[0], consumerIds[2]}

	res, err := pk.QueryConsumerChainsValidatorHasToValidate(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, expectedChains, res.ConsumerIds)
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
	pk.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_INITIALIZED)

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

	consumerIDs := []string{"1", "23", "345", "6789"}

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
	prioritylists := [][]types.ProviderConsAddress{
		{},
		{types.NewProviderConsAddress([]byte("providerAddr1")), types.NewProviderConsAddress([]byte("providerAddr2"))},
		{types.NewProviderConsAddress([]byte("providerAddr3"))},
		{},
	}
	allowInactiveVals := []bool{true, false, true, false}

	minStakes := []math.Int{
		math.NewInt(0),
		math.NewInt(100),
		math.NewInt(200),
		math.NewInt(300),
	}

	metadataLists := []types.ConsumerMetadata{}

	allowlistedRewardDenoms := []*types.AllowlistedRewardDenoms{
		{}, // no denoms
		{Denoms: []string{"ibc/1", "ibc/2"}},
		{Denoms: []string{"ibc/3", "ibc/4", "ibc/5"}},
		{Denoms: []string{"ibc/6"}}}

	expectedGetAllOrder := []types.Chain{}
	for i, consumerID := range consumerIDs {
		pk.SetConsumerChainId(ctx, consumerID, chainIDs[i])
		clientID := fmt.Sprintf("client-%d", len(consumerID)-i)
		topN := topNs[i]
		pk.SetConsumerClientId(ctx, consumerID, clientID)
		err := pk.SetConsumerPowerShapingParameters(ctx, consumerID, types.PowerShapingParameters{
			Top_N:              topN,
			ValidatorSetCap:    validatorSetCaps[i],
			ValidatorsPowerCap: validatorPowerCaps[i],
			MinStake:           minStakes[i].Uint64(),
			AllowInactiveVals:  allowInactiveVals[i],
		})
		require.NoError(t, err)
		pk.SetMinimumPowerInTopN(ctx, consumerID, expectedMinPowerInTopNs[i])
		for _, addr := range allowlists[i] {
			pk.SetAllowlist(ctx, consumerID, addr)
		}
		for _, addr := range denylists[i] {
			pk.SetDenylist(ctx, consumerID, addr)
		}
		for _, addr := range prioritylists[i] {
			pk.SetPrioritylist(ctx, consumerID, addr)
		}
		strAllowlist := make([]string, len(allowlists[i]))
		for j, addr := range allowlists[i] {
			strAllowlist[j] = addr.String()
		}

		strDenylist := make([]string, len(denylists[i]))
		for j, addr := range denylists[i] {
			strDenylist[j] = addr.String()
		}

		strPrioritylist := make([]string, len(prioritylists[i]))
		for j, addr := range prioritylists[i] {
			strPrioritylist[j] = addr.String()
		}

		metadataLists = append(metadataLists, types.ConsumerMetadata{Name: chainIDs[i]})
		pk.SetConsumerMetadata(ctx, consumerID, metadataLists[i])

		pk.SetAllowlistedRewardDenoms(ctx, consumerID, allowlistedRewardDenoms[i].Denoms)

		phase := types.ConsumerPhase(int32(i + 1))
		pk.SetConsumerPhase(ctx, consumerID, phase)

		expectedGetAllOrder = append(expectedGetAllOrder,
			types.Chain{
				ChainId:                 chainIDs[i],
				ClientId:                clientID,
				Top_N:                   topN,
				MinPowerInTop_N:         expectedMinPowerInTopNs[i],
				ValidatorSetCap:         validatorSetCaps[i],
				ValidatorsPowerCap:      validatorPowerCaps[i],
				Allowlist:               strAllowlist,
				Denylist:                strDenylist,
				Phase:                   phase.String(),
				Metadata:                metadataLists[i],
				AllowInactiveVals:       allowInactiveVals[i],
				MinStake:                minStakes[i].Uint64(),
				ConsumerId:              consumerIDs[i],
				AllowlistedRewardDenoms: allowlistedRewardDenoms[i],
				Prioritylist:            strPrioritylist,
			})
	}

	for i, cId := range consumerIDs {
		c, err := pk.GetConsumerChain(ctx, cId)
		require.NoError(t, err)
		require.Equal(t, expectedGetAllOrder[i], c)
	}
}

func TestQueryConsumerChain(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"
	chainId := "consumer"

	req := types.QueryConsumerChainRequest{
		ConsumerId: consumerId,
	}

	// expect error when consumer isn't associated with a chain id
	_, err := providerKeeper.QueryConsumerChain(ctx, &req)
	require.Error(t, err)

	providerKeeper.SetConsumerChainId(ctx, consumerId, chainId)

	// expect error when consumer doesn't have an owner address set
	_, err = providerKeeper.QueryConsumerChain(ctx, &req)
	require.Error(t, err)

	providerKeeper.SetConsumerOwnerAddress(ctx, consumerId, providerKeeper.GetAuthority())

	// expect error when consumer doesn't have a valid phase
	_, err = providerKeeper.QueryConsumerChain(ctx, &req)
	require.Error(t, err)

	providerKeeper.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_REGISTERED)

	// expect error when consumer doesn't have metadata
	_, err = providerKeeper.QueryConsumerChain(ctx, &req)
	require.Error(t, err)

	err = providerKeeper.SetConsumerMetadata(ctx, consumerId, types.ConsumerMetadata{Name: chainId})
	require.NoError(t, err)

	expRes := types.QueryConsumerChainResponse{
		ChainId:            chainId,
		ConsumerId:         consumerId,
		OwnerAddress:       providerKeeper.GetAuthority(),
		Metadata:           types.ConsumerMetadata{Name: chainId},
		Phase:              types.CONSUMER_PHASE_REGISTERED.String(),
		InitParams:         &types.ConsumerInitializationParameters{},
		PowerShapingParams: &types.PowerShapingParameters{},
	}

	// expect no error when neither the consumer init and power shaping params are set
	res, err := providerKeeper.QueryConsumerChain(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expRes, res)

	err = providerKeeper.SetConsumerInitializationParameters(
		ctx,
		consumerId,
		types.ConsumerInitializationParameters{SpawnTime: ctx.BlockTime()},
	)
	require.NoError(t, err)

	err = providerKeeper.SetConsumerPowerShapingParameters(
		ctx,
		consumerId,
		types.PowerShapingParameters{Top_N: uint32(50)},
	)
	require.NoError(t, err)

	expRes.InitParams = &types.ConsumerInitializationParameters{SpawnTime: ctx.BlockTime()}
	expRes.PowerShapingParams = &types.PowerShapingParameters{Top_N: uint32(50)}

	// expect no error
	res, err = providerKeeper.QueryConsumerChain(ctx, &req)
	require.NoError(t, err)
	require.Equal(t, &expRes, res)
}

func TestQueryConsumerIdFromClientId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.QueryConsumerIdFromClientId(ctx, &types.QueryConsumerIdFromClientIdRequest{ClientId: "clientId"})
	require.Error(t, err)
	require.ErrorContains(t, err, "no known consumer chain")

	expectedConsumerId := CONSUMER_ID
	providerKeeper.SetConsumerClientId(ctx, expectedConsumerId, "clientId")

	res, err := providerKeeper.QueryConsumerIdFromClientId(ctx, &types.QueryConsumerIdFromClientIdRequest{ClientId: "clientId"})
	require.NoError(t, err)
	require.Equal(t, expectedConsumerId, res.ConsumerId)
}

func TestQueryConsumerChains(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerNum := 4
	consumerIds := make([]string, consumerNum)
	consumers := make([]*types.Chain, consumerNum)

	// expect no error and returned chains
	res, err := pk.QueryConsumerChains(ctx, &types.QueryConsumerChainsRequest{})
	require.NoError(t, err)
	require.Len(t, res.Chains, 0)

	msgServer := keeper.NewMsgServerImpl(&pk)

	phases := []types.ConsumerPhase{
		types.CONSUMER_PHASE_REGISTERED,
		types.CONSUMER_PHASE_INITIALIZED,
		types.CONSUMER_PHASE_LAUNCHED,
		types.CONSUMER_PHASE_STOPPED,
	}

	// create four consumer chains in different phase
	for i := 0; i < consumerNum; i++ {
		revisionNumber := i + 1
		chainID := "consumer-" + strconv.Itoa(revisionNumber)
		metadata := types.ConsumerMetadata{Name: chainID}
		initializationParameters := types.DefaultConsumerInitializationParameters()
		initializationParameters.InitialHeight.RevisionNumber = uint64(revisionNumber)
		msg := types.MsgCreateConsumer{
			ChainId:                  chainID,
			Metadata:                 metadata,
			InitializationParameters: &initializationParameters,
		}
		resp, err := msgServer.CreateConsumer(ctx, &msg)
		require.NoError(t, err)
		consumerId := resp.ConsumerId

		pk.SetConsumerPhase(ctx, consumerId, phases[i])
		c := types.Chain{
			ChainId:                 chainID,
			MinPowerInTop_N:         -1,
			ValidatorsPowerCap:      0,
			ValidatorSetCap:         0,
			Allowlist:               []string{},
			Denylist:                []string{},
			Phase:                   phases[i].String(),
			Metadata:                metadata,
			ConsumerId:              consumerId,
			AllowlistedRewardDenoms: &types.AllowlistedRewardDenoms{Denoms: []string{}},
			Prioritylist:            []string{},
		}
		consumerIds[i] = consumerId
		consumers[i] = &c
	}

	testCases := []struct {
		name         string
		setup        func(ctx sdk.Context, pk keeper.Keeper)
		phase_filter types.ConsumerPhase
		limit        uint64
		total        uint64
		expConsumers []*types.Chain
	}{
		{
			name:         "expect all consumers when phase filter isn't set",
			setup:        func(ctx sdk.Context, pk keeper.Keeper) {},
			expConsumers: consumers,
			total:        4,
		},
		{
			name:         "expect an amount of consumer equal to the limit",
			setup:        func(ctx sdk.Context, pk keeper.Keeper) {},
			expConsumers: consumers[:3],
			limit:        3,
			total:        4,
		},
		{
			name: "expect registered consumers when phase filter is set to Registered",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {
				consumers[0].Phase = types.CONSUMER_PHASE_REGISTERED.String()
				pk.SetConsumerPhase(ctx, consumerIds[0], types.CONSUMER_PHASE_REGISTERED)
			},
			phase_filter: types.CONSUMER_PHASE_REGISTERED,
			expConsumers: consumers[0:1],
			total:        1,
		},
		{
			name: "expect initialized consumers when phase is set to Initialized",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {
				consumers[1].Phase = types.CONSUMER_PHASE_INITIALIZED.String()
				pk.SetConsumerPhase(ctx, consumerIds[1], types.CONSUMER_PHASE_INITIALIZED)
			},
			phase_filter: types.CONSUMER_PHASE_INITIALIZED,
			expConsumers: consumers[1:2],
			total:        1,
		},
		{
			name: "expect launched consumers when phase is set to Launched",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {
				consumers[2].Phase = types.CONSUMER_PHASE_LAUNCHED.String()
				pk.SetConsumerPhase(ctx, consumerIds[2], types.CONSUMER_PHASE_LAUNCHED)
			},
			phase_filter: types.CONSUMER_PHASE_LAUNCHED,
			expConsumers: consumers[2:3],
			total:        1,
		},
		{
			name: "expect stopped consumers when phase is set to Stopped",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {
				consumers[3].Phase = types.CONSUMER_PHASE_STOPPED.String()
				pk.SetConsumerPhase(ctx, consumerIds[3], types.CONSUMER_PHASE_STOPPED)
			},
			phase_filter: types.CONSUMER_PHASE_STOPPED,
			expConsumers: consumers[3:],
			total:        1,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tc.setup(ctx, pk)
			req := types.QueryConsumerChainsRequest{
				Phase: tc.phase_filter,
				Pagination: &sdkquery.PageRequest{
					Limit:      tc.limit,
					CountTotal: true,
				},
			}
			expectedResponse := types.QueryConsumerChainsResponse{
				Chains: tc.expConsumers,
			}
			res, err := pk.QueryConsumerChains(ctx, &req)
			require.NoError(t, err)
			require.Equal(t, expectedResponse.GetChains(), res.GetChains(), tc.name)
			if tc.limit != 0 {
				require.Len(t, res.GetChains(), int(tc.limit), tc.name)
			}
			if tc.total != 0 {
				require.Equal(t, res.Pagination.Total, tc.total, tc.name)
			}
		})
	}
}

func TestQueryConsumerGenesisTime(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"
	chainId := "consumer-1"
	initialHeight := clienttypes.Height{RevisionNumber: 1, RevisionHeight: 1}
	clientId := "07-tendermint-0"
	genesisTime := time.Now()
	req := &types.QueryConsumerGenesisTimeRequest{
		ConsumerId: consumerId,
	}

	testCases := []struct {
		name           string
		setup          func(ctx sdk.Context, pk keeper.Keeper)
		req            *types.QueryConsumerGenesisTimeRequest
		expErr         bool
		expGenesisTime time.Time
	}{
		{
			name:   "expect error when request is empty",
			setup:  func(ctx sdk.Context, pk keeper.Keeper) {},
			req:    nil,
			expErr: true,
		},
		{
			name:  "expect error when consumer Id is invalid",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {},
			req: &types.QueryConsumerGenesisTimeRequest{
				ConsumerId: "invalidCID",
			},
			expErr: true,
		},
		{
			name:   "expect error when there is no consumer chain with this consumer id",
			setup:  func(ctx sdk.Context, pk keeper.Keeper) {},
			req:    req,
			expErr: true,
		},
		{
			name: "expect error when consumer hasn't been launched yet",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {
				pk.SetConsumerChainId(
					ctx,
					consumerId,
					chainId,
				)
				err := pk.SetConsumerInitializationParameters(
					ctx,
					consumerId,
					types.ConsumerInitializationParameters{
						InitialHeight: initialHeight,
					},
				)
				require.NoError(t, err)
			},
			req:    req,
			expErr: true,
		},
		{
			name: "expect error when consensus state cannot be found for consumer initial height",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {
				pk.SetConsumerChainId(
					ctx,
					consumerId,
					chainId,
				)
				err := pk.SetConsumerInitializationParameters(
					ctx,
					consumerId,
					types.ConsumerInitializationParameters{
						InitialHeight: initialHeight,
					},
				)
				require.NoError(t, err)

				pk.SetConsumerClientId(ctx, consumerId, clientId)
				mocks.MockClientKeeper.EXPECT().GetClientConsensusState(ctx, clientId, initialHeight).Return(
					nil, false,
				)
			},
			req:    req,
			expErr: true,
		},
		{
			name: "expect no error when there is a consensus state for the consumer initial height",
			setup: func(ctx sdk.Context, pk keeper.Keeper) {
				pk.SetConsumerChainId(
					ctx,
					consumerId,
					chainId,
				)
				err := pk.SetConsumerInitializationParameters(
					ctx,
					consumerId,
					types.ConsumerInitializationParameters{
						InitialHeight: initialHeight,
					},
				)
				require.NoError(t, err)

				pk.SetConsumerClientId(ctx, consumerId, clientId)
				mocks.MockClientKeeper.EXPECT().GetClientConsensusState(ctx, clientId, initialHeight).Return(
					ibcexported.ConsensusState(&ibctm.ConsensusState{Timestamp: genesisTime}), true,
				)
			},
			req:            req,
			expErr:         false,
			expGenesisTime: genesisTime,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tc.setup(ctx, providerKeeper)
			res, err := providerKeeper.QueryConsumerGenesisTime(ctx, tc.req)
			if !tc.expErr {
				require.NoError(t, err)
				require.True(t, tc.expGenesisTime.Equal(res.GenesisTime))
			} else {
				require.Error(t, err)
				require.Equal(t, res, (*types.QueryConsumerGenesisTimeResponse)(nil))
			}
		})
	}
}
