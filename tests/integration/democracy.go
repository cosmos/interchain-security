package integration

import (
	"time"

	ibctesting "github.com/cosmos/ibc-go/v9/testing"
	"github.com/stretchr/testify/suite"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	sdkdistrkeeper "github.com/cosmos/cosmos-sdk/x/distribution/keeper"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

	icstestingutils "github.com/cosmos/interchain-security/v7/testutil/ibc_testing"
	testutil "github.com/cosmos/interchain-security/v7/testutil/integration"
	consumertypes "github.com/cosmos/interchain-security/v7/x/ccv/consumer/types"
)

type ConsumerDemocracyTestSuite struct {
	suite.Suite
	coordinator   *ibctesting.Coordinator
	consumerChain *ibctesting.TestChain
	consumerApp   testutil.DemocConsumerApp
	setupCallback DemocSetupCallback
}

// NewConsumerDemocracyTestSuite returns a new instance of ConsumerDemocracyTestSuite,
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

// TestDemocracyRewardsDistribution checks that rewards to democracy representatives, community pool, and provider redistribution account are done correctly.
// @Long Description@
// * Set up a democracy consumer chain.
// * Create a new block.
// * Check that rewards to democracy representatives, community pool, and provider redistribution account are distributed in the right proportions.
func (s *ConsumerDemocracyTestSuite) TestDemocracyRewardsDistribution() {
	s.consumerChain.NextBlock()
	stakingKeeper := s.consumerApp.GetTestStakingKeeper()
	accountKeeper := s.consumerApp.GetTestAccountKeeper()
	distrKeeper := s.consumerApp.GetTestDistributionKeeper()
	bankKeeper := s.consumerApp.GetTestBankKeeper()
	bondDenom, err := stakingKeeper.BondDenom(s.consumerCtx())
	s.Require().NoError(err)

	previousRepresentativesRewards := map[string]math.LegacyDec{}
	nextRepresentativesRewards := map[string]math.LegacyDec{}
	representativesTokens := map[string]math.Int{}

	representatives, err := stakingKeeper.GetAllValidators(s.consumerCtx())
	s.Require().NoError(err)
	for _, representative := range representatives {
		previousRepresentativesRewards[representative.OperatorAddress] = math.LegacyNewDec(0)
		nextRepresentativesRewards[representative.OperatorAddress] = math.LegacyNewDec(0)
		representativesTokens[representative.OperatorAddress] = representative.GetTokens()
	}

	distrModuleAccount := distrKeeper.GetDistributionAccount(s.consumerCtx())
	providerRedistributeAccount := accountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerToSendToProviderName)
	consumerRedistributeAccount := accountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerRedistributeName)

	dk, ok := distrKeeper.(sdkdistrkeeper.Keeper)
	s.Require().True(ok)
	feePool, err := dk.FeePool.Get(s.consumerCtx())
	s.Require().NoError(err)
	s.Require().NotEmpty(feePool)

	// take balance of relevant accounts before advancing to the next block
	previousDistrModuleAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), distrModuleAccount.GetAddress(), bondDenom).Amount)
	previousProviderFeeAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount)
	previousConsumerRedistributeBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), consumerRedistributeAccount.GetAddress(), bondDenom).Amount)
	previousCommunityPoolBalance := feePool.GetCommunityPool().AmountOf(bondDenom)
	for key := range previousRepresentativesRewards {
		representativeAddr, _ := sdk.ValAddressFromBech32(key)
		representativeReward, err := distrKeeper.GetValidatorOutstandingRewards(s.consumerCtx(), representativeAddr)
		s.Require().NoError(err)
		previousRepresentativesRewards[key] = representativeReward.Rewards.AmountOf(bondDenom)
	}

	// NextBlock will call the begin block and end block, respectively. Democracy module in the begin blocker sends the tokens from
	// the consumer redistribute address to the distribution module, giving representatives and community fee pool its portion of rewards.
	// Consumer module in endblocker, sends the fees from fee collector(auth module) to the consumer redistribute address and to
	// provider rewards address
	s.consumerChain.NextBlock()

	// take balance of relevant accounts after new block is created
	nextDistrModuleAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), distrModuleAccount.GetAddress(), bondDenom).Amount)
	nextProviderFeeAccountBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount)
	nextConsumerRedistributeBalance := math.LegacyNewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), consumerRedistributeAccount.GetAddress(), bondDenom).Amount)
	feePool, err = dk.FeePool.Get(s.consumerCtx())
	s.Require().NoError(err)
	s.Require().NotEmpty(feePool)
	nextCommunityPoolBalance := feePool.GetCommunityPool().AmountOf(bondDenom)
	for key := range nextRepresentativesRewards {
		representativeAddr, _ := sdk.ValAddressFromBech32(key)
		representativeReward, err := distrKeeper.GetValidatorOutstandingRewards(s.consumerCtx(), representativeAddr)
		s.Require().NoError(err)
		nextRepresentativesRewards[key] = representativeReward.Rewards.AmountOf(bondDenom)
	}

	distrModuleDifference := nextDistrModuleAccountBalance.Sub(previousDistrModuleAccountBalance)
	providerDifference := nextProviderFeeAccountBalance.Sub(previousProviderFeeAccountBalance)
	communityPoolDifference := nextCommunityPoolBalance.Sub(previousCommunityPoolBalance)
	representativeDifference := map[string]math.LegacyDec{}
	totalRepresentativeDifference := math.LegacyZeroDec()
	for key, currentReward := range previousRepresentativesRewards {
		diff := nextRepresentativesRewards[key].Sub(currentReward)
		representativeDifference[key] = diff
		totalRepresentativeDifference = totalRepresentativeDifference.Add(diff)
	}

	// confirm endblocker changes: consumer module distributes fees from fee collector to consumer redistribute address
	// and address aimed for provider rewards
	consumerRedistributionFraction := math.LegacyMustNewDecFromStr(s.consumerApp.GetConsumerKeeper().GetConsumerRedistributionFrac(s.consumerCtx()))
	// since we cannot know the balance of the fee collector when the consumer module transfers the fees, we can only calculate the total fees
	// as a sum of the provider and consumer rewards and check if the reward is distributed in the expected proportion
	totalFees := nextConsumerRedistributeBalance.Add(providerDifference)
	s.Require().Equal(totalFees.Mul(consumerRedistributionFraction), nextConsumerRedistributeBalance)

	// confirm begin blocker changes: democracy module distributes the fees from consumer redistribute address to representatives
	// and community fee pool
	// distribution module got tokens from previous consumer redistribute balance
	s.Require().Equal(distrModuleDifference, previousConsumerRedistributeBalance)
	// confirm that the percentage given to the community pool is equal to the configured community tax percentage.
	tax, err := distrKeeper.GetCommunityTax(s.consumerCtx())
	s.Require().NoError(err)

	s.Require().Equal(communityPoolDifference.Quo(previousConsumerRedistributeBalance), tax)
	// confirm that the total amount given to the community pool plus all representatives is equal to the previous consumer redistribute balance
	s.Require().Equal(previousConsumerRedistributeBalance, communityPoolDifference.Add(totalRepresentativeDifference))

	// check that each representative has gotten the correct amount of rewards
	totalRepresentativePower, err := stakingKeeper.GetValidatorSet().TotalBondedTokens(s.consumerCtx())
	s.Require().NoError(err)

	for key, representativeTokens := range representativesTokens {
		powerFraction := math.LegacyNewDecFromInt(representativeTokens).QuoTruncate(math.LegacyNewDecFromInt(totalRepresentativePower))
		s.Require().Equal(powerFraction, representativeDifference[key].Quo(previousConsumerRedistributeBalance.Sub(communityPoolDifference)))
	}
}

// TestDemocracyMsgUpdateParams checks that the consumer parameters can be updated through a governance proposal.
// @Long Description@
// * Set up a democracy consumer chain.
// * Submit a proposal containing changes to the consumer module parameters.
// * Check that the proposal is executed, and the parameters are updated.
func (s *ConsumerDemocracyTestSuite) TestDemocracyMsgUpdateParams() {
	govKeeper := s.consumerApp.GetTestGovKeeper()
	params, err := govKeeper.Params.Get(s.consumerCtx())
	s.Require().NoError(err)

	stakingKeeper := s.consumerApp.GetTestStakingKeeper()
	bankKeeper := s.consumerApp.GetTestBankKeeper()
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

	oldParams := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	modifiedParams := oldParams
	modifiedParams.RetryDelayPeriod = 7200 * time.Second
	s.Require().NotEqual(oldParams.RetryDelayPeriod, modifiedParams.RetryDelayPeriod)

	msg := &consumertypes.MsgUpdateParams{
		Authority: authtypes.NewModuleAddress(govtypes.ModuleName).String(),
		Params:    modifiedParams,
	}

	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), []sdk.Msg{msg}, votingAccounts, proposer.GetAddress(), depositAmount)
	s.Assert().NoError(err)
	// set current header time to be equal or later than voting end time in order to process proposal from active queue,
	// once the proposal is added to the chain
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(*params.VotingPeriod)

	s.consumerChain.NextBlock()

	newParams := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	s.Assert().NotEqual(oldParams, newParams)
	s.Assert().Equal(modifiedParams, newParams)
	s.Assert().NotEqual(oldParams.RetryDelayPeriod, newParams.RetryDelayPeriod)
	s.Assert().Equal(modifiedParams.RetryDelayPeriod, newParams.RetryDelayPeriod)

	// deposit is refunded
	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))
}

// TestDemocracyValidatorUnjail checks that the consumer validator can be unjailed when there is a standalone staking keeper available.
// @Long Description@
// * Set up a democracy consumer chain.
// * Jail a validator.
// * Check that the validator is jailed.
// * Unjail the validator.
// * Check that the validator is unjailed.
func (s *ConsumerDemocracyTestSuite) TestDemocracyValidatorUnjail() {
	stakingKeeper := s.consumerApp.GetTestStakingKeeper()
	consumerKeeper := s.consumerApp.GetConsumerKeeper()

	validators, err := stakingKeeper.GetAllValidators(s.consumerCtx())
	s.Require().NoError(err)

	// setting up pre-conditions
	// validator[0] is expected to be jailed
	expectJailed := validators[0]
	consAddr, err := expectJailed.GetConsAddr()
	s.Require().NoError(err)
	stakingKeeper.GetValidatorSet().Jail(s.consumerCtx(), consAddr)

	s.consumerChain.NextBlock()

	validators, err = stakingKeeper.GetAllValidators(s.consumerCtx())
	s.Require().NoError(err)
	for _, validator := range validators {
		if validator.OperatorAddress == expectJailed.OperatorAddress {
			s.Require().True(validator.IsJailed())
		} else {
			s.Require().False(validator.IsJailed())
		}
	}

	// confirm unjail will not error and properly unjail
	// in case of a consumer chain without standalone staking the call is a no-op
	err = consumerKeeper.Unjail(s.consumerCtx(), consAddr)
	s.Require().NoError(err)
	s.consumerChain.NextBlock()

	validators, err = stakingKeeper.GetAllValidators(s.consumerCtx())
	s.Require().NoError(err)
	for _, validator := range validators {
		s.Require().False(validator.IsJailed())
	}
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
