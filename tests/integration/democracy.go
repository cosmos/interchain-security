package integration

import (
	"time"

	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	"github.com/stretchr/testify/suite"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"

	sdkdistrkeeper "github.com/cosmos/cosmos-sdk/x/distribution/keeper"
	icstestingutils "github.com/cosmos/interchain-security/v3/testutil/ibc_testing"
	testutil "github.com/cosmos/interchain-security/v3/testutil/integration"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
)

type ConsumerDemocracyTestSuite struct {
	suite.Suite
	coordinator   *ibctesting.Coordinator
	consumerChain *ibctesting.TestChain
	consumerApp   testutil.DemocConsumerApp
	setupCallback DemocSetupCallback
}

// NewCCVTestSuite returns a new instance of ConsumerDemocracyTestSuite,
// ready to be tested against using suite.Run().
func NewConsumerDemocracyTestSuite[T testutil.DemocConsumerApp](
	democConsumerAppIniter icstestingutils.ValSetAppIniter,
) *ConsumerDemocracyTestSuite {
	democSuite := new(ConsumerDemocracyTestSuite)

	democSuite.setupCallback = func(s *suite.Suite) (
		*ibctesting.Coordinator,
		*ibctesting.TestChain,
		testutil.DemocConsumerApp,
	) {
		s.T().Helper()
		// Instantiate the test coordinator
		coordinator := ibctesting.NewCoordinator(s.T(), 0)

		// Add single democracy consumer to coordinator, store returned test chain and app.
		democConsumer, democConsumerApp := icstestingutils.AddDemocracyConsumer[T](
			coordinator, s, democConsumerAppIniter)

		// Pass variables to suite.
		return coordinator, democConsumer, democConsumerApp
	}
	return democSuite
}

// Callback for instantiating a new coordinator, consumer test chain, and consumer app
// before every test defined on the suite.
type DemocSetupCallback func(s *suite.Suite) (
	coord *ibctesting.Coordinator,
	consumerChain *ibctesting.TestChain,
	consumerApp testutil.DemocConsumerApp,
)

// SetupTest sets up in-mem state before every test relevant to ccv with a democracy consumer
func (suite *ConsumerDemocracyTestSuite) SetupTest() {
	// Instantiate new test utils using callback
	suite.coordinator, suite.consumerChain,
		suite.consumerApp = suite.setupCallback(&suite.Suite)
}

func (s *ConsumerDemocracyTestSuite) TestDemocracyRewardsDistribution() {
	s.consumerChain.NextBlock()
	stakingKeeper := s.consumerApp.GetTestStakingKeeper()
	accountKeeper := s.consumerApp.GetTestAccountKeeper()
	distrKeeper := s.consumerApp.GetTestDistributionKeeper()
	bankKeeper := s.consumerApp.GetTestBankKeeper()
	bondDenom, err := stakingKeeper.BondDenom(s.consumerCtx())
	s.Require().NoError(err)

	currentRepresentativesRewards := map[string]math.LegacyDec{}
	nextRepresentativesRewards := map[string]math.LegacyDec{}
	representativesTokens := map[string]math.Int{}

	representatives, err := stakingKeeper.GetAllValidators(s.consumerCtx())
	s.Require().NoError(err)
	for _, representative := range representatives {
		currentRepresentativesRewards[representative.OperatorAddress] = math.LegacyNewDec(0)
		nextRepresentativesRewards[representative.OperatorAddress] = math.LegacyNewDec(0)
		representativesTokens[representative.OperatorAddress] = representative.GetTokens()
	}

	distrModuleAccount := distrKeeper.GetDistributionAccount(s.consumerCtx())
	providerRedistributeAccount := accountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerToSendToProviderName)
	// balance of consumer redistribute address will always be 0 when checked between 2 NextBlock() calls

	dk, ok := distrKeeper.(sdkdistrkeeper.Keeper)
	s.Require().True(ok)
	feePool, err := dk.FeePool.Get(s.consumerCtx().Context())
	s.Require().NoError(err)
	s.Require().NotEmpty(feePool)
	currentDistrModuleAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), distrModuleAccount.GetAddress(), bondDenom).Amount)
	currentProviderFeeAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount)
	currentCommunityPoolBalance := feePool.GetCommunityPool().AmountOf(bondDenom)
	for key := range currentRepresentativesRewards {
		representativeAddr, _ := sdk.ValAddressFromBech32(key)
		representativeReward, err := distrKeeper.GetValidatorOutstandingRewards(s.consumerCtx(), representativeAddr)
		s.Require().NoError(err)
		currentRepresentativesRewards[key] = representativeReward.Rewards.AmountOf(bondDenom)
	}

	s.consumerChain.NextBlock()

	nextDistrModuleAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), distrModuleAccount.GetAddress(), bondDenom).Amount)
	nextProviderFeeAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount)
	nextCommunityPoolBalance := feePool.GetCommunityPool().AmountOf(bondDenom)
	for key := range nextRepresentativesRewards {
		representativeAddr, _ := sdk.ValAddressFromBech32(key)
		representativeReward, err := distrKeeper.GetValidatorOutstandingRewards(s.consumerCtx(), representativeAddr)
		s.Require().NoError(err)
		nextRepresentativesRewards[key] = representativeReward.Rewards.AmountOf(bondDenom)
	}

	distrModuleDifference := nextDistrModuleAccountBalance.Sub(currentDistrModuleAccountBalance)
	providerDifference := nextProviderFeeAccountBalance.Sub(currentProviderFeeAccountBalance)
	communityPoolDifference := nextCommunityPoolBalance.Sub(currentCommunityPoolBalance)
	representativeDifference := map[string]math.LegacyDec{}
	consumerRedistributeDifference := communityPoolDifference

	for key, currentReward := range currentRepresentativesRewards {
		representativeDifference[key] = nextRepresentativesRewards[key].Sub(currentReward)
		consumerRedistributeDifference = consumerRedistributeDifference.Add(representativeDifference[key])
	}

	consumerRedistributionFraction := math.LegacyMustNewDecFromStr(s.consumerApp.GetConsumerKeeper().GetConsumerRedistributionFrac(s.consumerCtx()))

	// confirm that the total amount given to the community pool plus all representatives is equal to the total amount taken out of distribution
	s.Require().Equal(distrModuleDifference, consumerRedistributeDifference)
	// confirm that the percentage given to the community pool is equal to the configured community tax percentage.
	tax, err := distrKeeper.GetCommunityTax(s.consumerCtx())
	s.Require().NoError(err)
	s.Require().Equal(communityPoolDifference.Quo(consumerRedistributeDifference), tax)
	// check that the fraction actually kept by the consumer is the correct fraction. using InEpsilon because the math code uses truncations
	s.Require().InEpsilon(distrModuleDifference.Quo(
		providerDifference.Add(distrModuleDifference)).MustFloat64(),
		consumerRedistributionFraction.MustFloat64(), float64(0.0001))
	// check that the fraction actually kept by the provider is the correct fraction. using InEpsilon because the math code uses truncations
	s.Require().InEpsilon(providerDifference.Quo(
		providerDifference.Add(distrModuleDifference)).MustFloat64(),
		math.LegacyNewDec(1).Sub(consumerRedistributionFraction).MustFloat64(), float64(0.0001))

	totalRepresentativePower, err := stakingKeeper.GetValidatorSet().TotalBondedTokens(s.consumerCtx())
	s.Require().NoError(err)

	// check that each representative has gotten the correct amount of rewards
	for key, representativeTokens := range representativesTokens {
		powerFraction := math.LegacyNewDecFromInt(representativeTokens).QuoTruncate(math.LegacyNewDecFromInt(totalRepresentativePower))
		s.Require().Equal(powerFraction, representativeDifference[key].Quo(consumerRedistributeDifference.Sub(communityPoolDifference)))
	}
}

// @MSalopek -> this is broken for v50
func (s *ConsumerDemocracyTestSuite) TestDemocracyGovernanceWhitelisting() {
	govKeeper := s.consumerApp.GetTestGovKeeper()
	params, err := govKeeper.Params.Get(s.consumerCtx())
	s.Require().NoError(err)

	stakingKeeper := s.consumerApp.GetTestStakingKeeper()
	bankKeeper := s.consumerApp.GetTestBankKeeper()
	accountKeeper := s.consumerApp.GetTestAccountKeeper()
	mintKeeper := s.consumerApp.GetTestMintKeeper()
	newAuthParamValue := uint64(128)
	newMintParamValue := math.LegacyNewDecWithPrec(1, 1) // "0.100000000000000000"
	votingAccounts := s.consumerChain.SenderAccounts
	bondDenom, err := stakingKeeper.BondDenom(s.consumerCtx())
	s.Require().NoError(err)
	depositAmount := params.MinDeposit
	duration := (3 * time.Second)
	params.VotingPeriod = &duration
	err = govKeeper.Params.Set(s.consumerCtx(), params)
	s.Assert().NoError(err)
	proposer := s.consumerChain.SenderAccount
	s.consumerChain.NextBlock()
	votersOldBalances := getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts)

	// submit proposal with forbidden and allowed changes
	mintParams, err := mintKeeper.Params.Get(s.consumerCtx())
	s.Require().NoError(err)
	mintParams.InflationMax = newMintParamValue
	msg_1 := &minttypes.MsgUpdateParams{
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		Params:    mintParams,
	}
	authParams := accountKeeper.GetParams(s.consumerCtx())
	authParams.MaxMemoCharacters = newAuthParamValue
	msg_2 := &authtypes.MsgUpdateParams{
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		Params:    authParams,
	}
	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), []sdk.Msg{msg_1, msg_2}, votingAccounts, proposer.GetAddress(), depositAmount)
	s.Assert().NoError(err)
	// set current header time to be equal or later than voting end time in order to process proposal from active queue,
	// once the proposal is added to the chain
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(*params.VotingPeriod)
	s.consumerChain.NextBlock()
	// at this moment, proposal is added, but not yet executed. we are saving old param values for comparison
	oldAuthParamValue := accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	oldMintParams, err := mintKeeper.Params.Get(s.consumerCtx())
	s.Require().NoError(err)
	oldMintParamValue := oldMintParams.InflationMax
	s.consumerChain.NextBlock()
	// at this moment, proposal is executed or deleted if forbidden
	currentAuthParamValue := accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	currentMintParam, err := mintKeeper.Params.Get(s.consumerCtx())
	s.Require().NoError(err)
	currentMintParamValue := currentMintParam.InflationMax
	// check that parameters are not changed, since the proposal contained both forbidden and allowed changes
	s.Assert().Equal(oldAuthParamValue, currentAuthParamValue)
	s.Assert().NotEqual(newAuthParamValue, currentAuthParamValue)
	s.Assert().Equal(oldMintParamValue, currentMintParamValue)
	s.Assert().NotEqual(newMintParamValue, currentMintParamValue)
	// deposit is refunded
	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))

	// submit proposal with allowed changes
	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), []sdk.Msg{msg_1}, votingAccounts, proposer.GetAddress(), depositAmount)
	s.Assert().NoError(err)
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(*params.VotingPeriod)
	s.consumerChain.NextBlock()
	oldMintParam, err := mintKeeper.Params.Get(s.consumerCtx())
	s.Require().NoError(err)
	oldMintParamValue = oldMintParam.InflationMax
	s.consumerChain.NextBlock()
	currentMintParam, err = mintKeeper.Params.Get(s.consumerCtx())
	s.Require().NoError(err)

	currentMintParamValue = currentMintParam.InflationMax
	// check that parameters are changed, since the proposal contained only allowed changes
	s.Assert().Equal(newMintParamValue, currentMintParamValue)
	s.Assert().NotEqual(oldMintParamValue, currentMintParamValue)
	// deposit is refunded
	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))

	// submit proposal with forbidden changes

	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), []sdk.Msg{msg_2}, votingAccounts, proposer.GetAddress(), depositAmount)
	s.Assert().NoError(err)
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(*params.VotingPeriod)
	s.consumerChain.NextBlock()
	oldAuthParamValue = accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	s.consumerChain.NextBlock()
	currentAuthParamValue = accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	// check that parameters are not changed, since the proposal contained forbidden changes
	s.Assert().Equal(oldAuthParamValue, currentAuthParamValue)
	s.Assert().NotEqual(newAuthParamValue, currentAuthParamValue)
	// deposit is refunded
	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))
}

func submitProposalWithDepositAndVote(govKeeper govkeeper.Keeper, ctx sdk.Context, msgs []sdk.Msg,
	accounts []ibctesting.SenderAccount, proposer sdk.AccAddress, depositAmount sdk.Coins,
) error {
	proposal, err := govKeeper.SubmitProposal(ctx, msgs, "", "title", "summary", proposer, false)
	if err != nil {
		return err
	}
	_, err = govKeeper.AddDeposit(ctx, proposal.Id, accounts[0].SenderAccount.GetAddress(), depositAmount) // proposal becomes active
	if err != nil {
		return err
	}

	for _, account := range accounts {
		err = govKeeper.AddVote(ctx, proposal.Id, account.SenderAccount.GetAddress(), govv1.NewNonSplitVoteOption(govv1.OptionYes), "")
		if err != nil {
			return err
		}
	}
	return nil
}

func getAccountsBalances(ctx sdk.Context, bankKeeper testutil.TestBankKeeper, bondDenom string, accounts []ibctesting.SenderAccount) map[string]math.Int {
	accountsBalances := map[string]math.Int{}
	for _, acc := range accounts {
		accountsBalances[string(acc.SenderAccount.GetAddress())] = bankKeeper.GetBalance(ctx, acc.SenderAccount.GetAddress(), bondDenom).Amount
	}

	return accountsBalances
}

func (s *ConsumerDemocracyTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}
