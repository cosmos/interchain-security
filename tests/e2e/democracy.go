package e2e

import (
	"fmt"
	"strconv"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	"github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	proposaltypes "github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	"github.com/cosmos/interchain-security/testutil/e2e"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/stretchr/testify/suite"
)

type ConsumerDemocracyTestSuite struct {
	suite.Suite
	coordinator   *ibctesting.Coordinator
	consumerChain *ibctesting.TestChain
	consumerApp   e2e.DemocConsumerApp
	setupCallback DemocSetupCallback
}

// NewCCVTestSuite returns a new instance of ConsumerDemocracyTestSuite,
// ready to be tested against using suite.Run().
func NewConsumerDemocracyTestSuite(setupCallback DemocSetupCallback) *ConsumerDemocracyTestSuite {
	democSuite := new(ConsumerDemocracyTestSuite)
	democSuite.setupCallback = setupCallback
	return democSuite
}

// Callback for instantiating a new coordinator, consumer test chain, and consumer app
// before every test defined on the suite.
type DemocSetupCallback func(t *testing.T) (
	coord *ibctesting.Coordinator,
	consumerChain *ibctesting.TestChain,
	consumerApp e2e.DemocConsumerApp,
)

// SetupTest sets up in-mem state before every test relevant to ccv with a democracy consumer
func (suite *ConsumerDemocracyTestSuite) SetupTest() {
	// Instantiate new test utils using callback
	suite.coordinator, suite.consumerChain,
		suite.consumerApp = suite.setupCallback(suite.T())
}

func (s *ConsumerDemocracyTestSuite) TestDemocracyRewardsDistribution() {

	s.consumerChain.NextBlock()
	stakingKeeper := s.consumerApp.GetE2eStakingKeeper()
	accountKeeper := s.consumerApp.GetE2eAccountKeeper()
	distrKeeper := s.consumerApp.GetE2eDistributionKeeper()
	bankKeeper := s.consumerApp.GetE2eBankKeeper()
	bondDenom := stakingKeeper.BondDenom(s.consumerCtx())

	currentRepresentativesRewards := map[string]sdk.Dec{}
	nextRepresentativesRewards := map[string]sdk.Dec{}
	representativesTokens := map[string]sdk.Int{}

	for _, representative := range stakingKeeper.GetAllValidators(s.consumerCtx()) {
		currentRepresentativesRewards[representative.OperatorAddress] = sdk.NewDec(0)
		nextRepresentativesRewards[representative.OperatorAddress] = sdk.NewDec(0)
		representativesTokens[representative.OperatorAddress] = representative.GetTokens()
	}

	distrModuleAccount := distrKeeper.GetDistributionAccount(s.consumerCtx())
	providerRedistributeAccount := accountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerToSendToProviderName)
	//balance of consumer redistribute address will always be 0 when checked between 2 NextBlock() calls

	currentDistrModuleAccountBalance := sdk.NewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), distrModuleAccount.GetAddress(), bondDenom).Amount)
	currentProviderFeeAccountBalance := sdk.NewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount)
	currentCommunityPoolBalance := distrKeeper.GetFeePoolCommunityCoins(s.consumerCtx()).AmountOf(bondDenom)
	for key := range currentRepresentativesRewards {
		representativeAddr, _ := sdk.ValAddressFromBech32(key)
		representativeReward := distrKeeper.GetValidatorOutstandingRewards(s.consumerCtx(), representativeAddr).Rewards.AmountOf(bondDenom)
		currentRepresentativesRewards[key] = representativeReward
	}

	s.consumerChain.NextBlock()

	nextDistrModuleAccountBalance := sdk.NewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), distrModuleAccount.GetAddress(), bondDenom).Amount)
	nextProviderFeeAccountBalance := sdk.NewDecFromInt(bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount)
	nextCommunityPoolBalance := distrKeeper.GetFeePoolCommunityCoins(s.consumerCtx()).AmountOf(bondDenom)
	for key := range nextRepresentativesRewards {
		representativeAddr, _ := sdk.ValAddressFromBech32(key)
		representativeReward := distrKeeper.GetValidatorOutstandingRewards(s.consumerCtx(), representativeAddr).Rewards.AmountOf(bondDenom)
		nextRepresentativesRewards[key] = representativeReward
	}

	distrModuleDifference := nextDistrModuleAccountBalance.Sub(currentDistrModuleAccountBalance)
	providerDifference := nextProviderFeeAccountBalance.Sub(currentProviderFeeAccountBalance)
	communityPoolDifference := nextCommunityPoolBalance.Sub(currentCommunityPoolBalance)
	representativeDifference := map[string]sdk.Dec{}
	consumerRedistributeDifference := communityPoolDifference

	for key, currentReward := range currentRepresentativesRewards {
		representativeDifference[key] = nextRepresentativesRewards[key].Sub(currentReward)
		consumerRedistributeDifference = consumerRedistributeDifference.Add(representativeDifference[key])
	}

	consumerRedistributionFraction := sdk.MustNewDecFromStr(s.consumerApp.GetConsumerKeeper().GetConsumerRedistributionFrac(s.consumerCtx()))

	//confirm that the total amount given to the community pool plus all representatives is equal to the total amount taken out of distribution
	s.Require().Equal(distrModuleDifference, consumerRedistributeDifference)
	//confirm that the percentage given to the community pool is equal to the configured community tax percentage.
	s.Require().Equal(communityPoolDifference.Quo(consumerRedistributeDifference),
		distrKeeper.GetCommunityTax(s.consumerCtx()))
	//check that the fraction actually kept by the consumer is the correct fraction. using InEpsilon because the math code uses truncations
	s.Require().InEpsilon(distrModuleDifference.Quo(
		providerDifference.Add(distrModuleDifference)).MustFloat64(),
		consumerRedistributionFraction.MustFloat64(), float64(0.0001))
	//check that the fraction actually kept by the provider is the correct fraction. using InEpsilon because the math code uses truncations
	s.Require().InEpsilon(providerDifference.Quo(
		providerDifference.Add(distrModuleDifference)).MustFloat64(),
		sdk.NewDec(1).Sub(consumerRedistributionFraction).MustFloat64(), float64(0.0001))

	totalRepresentativePower := stakingKeeper.GetValidatorSet().TotalBondedTokens(s.consumerCtx())

	//check that each representative has gotten the correct amount of rewards
	for key, representativeTokens := range representativesTokens {
		powerFraction := sdk.NewDecFromInt(representativeTokens).QuoTruncate(sdk.NewDecFromInt(totalRepresentativePower))
		s.Require().Equal(powerFraction, representativeDifference[key].Quo(consumerRedistributeDifference.Sub(communityPoolDifference)))
	}
}

func (s *ConsumerDemocracyTestSuite) TestDemocracyGovernanceWhitelisting() {
	govKeeper := s.consumerApp.GetE2eGovKeeper()
	stakingKeeper := s.consumerApp.GetE2eStakingKeeper()
	bankKeeper := s.consumerApp.GetE2eBankKeeper()
	accountKeeper := s.consumerApp.GetE2eAccountKeeper()
	mintKeeper := s.consumerApp.GetE2eMintKeeper()
	newAuthParamValue := uint64(128)
	newMintParamValue := sdk.NewDecWithPrec(1, 1) // "0.100000000000000000"
	allowedChange := proposal.ParamChange{Subspace: minttypes.ModuleName, Key: "InflationMax", Value: fmt.Sprintf("\"%s\"", newMintParamValue)}
	forbiddenChange := proposal.ParamChange{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: fmt.Sprintf("\"%s\"", strconv.FormatUint(newAuthParamValue, 10))}
	votingAccounts := s.consumerChain.SenderAccounts
	bondDenom := stakingKeeper.BondDenom(s.consumerCtx())
	depositAmount := govKeeper.GetDepositParams(s.consumerCtx()).MinDeposit
	votingParams := govKeeper.GetVotingParams(s.consumerCtx())
	votingParams.VotingPeriod = 3 * time.Second
	govKeeper.SetVotingParams(s.consumerCtx(), votingParams)
	s.consumerChain.NextBlock()
	votersOldBalances := getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts)

	//submit proposal with forbidden and allowed changes
	paramChange := proposaltypes.ParameterChangeProposal{Changes: []proposaltypes.ParamChange{allowedChange, forbiddenChange}}
	err := submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), paramChange, votingAccounts, depositAmount)
	s.Assert().NoError(err)
	//set current header time to be equal or later than voting end time in order to process proposal from active queue,
	//once the proposal is added to the chain
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(votingParams.VotingPeriod)
	s.consumerChain.NextBlock()
	//at this moment, proposal is added, but not yet executed. we are saving old param values for comparison
	oldAuthParamValue := accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	oldMintParamValue := mintKeeper.GetParams(s.consumerCtx()).InflationMax
	s.consumerChain.NextBlock()
	//at this moment, proposal is executed or deleted if forbidden
	currentAuthParamValue := accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	currentMintParamValue := mintKeeper.GetParams(s.consumerCtx()).InflationMax
	//check that parameters are not changed, since the proposal contained both forbidden and allowed changes
	s.Assert().Equal(oldAuthParamValue, currentAuthParamValue)
	s.Assert().NotEqual(newAuthParamValue, currentAuthParamValue)
	s.Assert().Equal(oldMintParamValue, currentMintParamValue)
	s.Assert().NotEqual(newMintParamValue, currentMintParamValue)
	//deposit is refunded
	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))

	//submit proposal with allowed changes
	paramChange = proposaltypes.ParameterChangeProposal{Changes: []proposaltypes.ParamChange{allowedChange}}
	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), paramChange, votingAccounts, depositAmount)
	s.Assert().NoError(err)
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(votingParams.VotingPeriod)
	s.consumerChain.NextBlock()
	oldMintParamValue = mintKeeper.GetParams(s.consumerCtx()).InflationMax
	s.consumerChain.NextBlock()
	currentMintParamValue = mintKeeper.GetParams(s.consumerCtx()).InflationMax
	//check that parameters are changed, since the proposal contained only allowed changes
	s.Assert().Equal(newMintParamValue, currentMintParamValue)
	s.Assert().NotEqual(oldMintParamValue, currentMintParamValue)
	//deposit is refunded
	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))

	//submit proposal with forbidden changes
	paramChange = proposaltypes.ParameterChangeProposal{Changes: []proposaltypes.ParamChange{forbiddenChange}}
	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), paramChange, votingAccounts, depositAmount)
	s.Assert().NoError(err)
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(votingParams.VotingPeriod)
	s.consumerChain.NextBlock()
	oldAuthParamValue = accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	s.consumerChain.NextBlock()
	currentAuthParamValue = accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	//check that parameters are not changed, since the proposal contained forbidden changes
	s.Assert().Equal(oldAuthParamValue, currentAuthParamValue)
	s.Assert().NotEqual(newAuthParamValue, currentAuthParamValue)
	//deposit is refunded
	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))
}

func submitProposalWithDepositAndVote(govKeeper e2e.E2eGovKeeper, ctx sdk.Context, paramChange proposaltypes.ParameterChangeProposal,
	accounts []ibctesting.SenderAccount, depositAmount sdk.Coins) error {
	proposal, err := govKeeper.SubmitProposal(ctx, &paramChange)
	if err != nil {
		return err
	}
	_, err = govKeeper.AddDeposit(ctx, proposal.ProposalId, accounts[0].SenderAccount.GetAddress(), depositAmount) //proposal becomes active
	if err != nil {
		return err
	}

	for _, account := range accounts {
		err = govKeeper.AddVote(ctx, proposal.ProposalId, account.SenderAccount.GetAddress(), govtypes.NewNonSplitVoteOption(govtypes.OptionYes))
		if err != nil {
			return err
		}
	}
	return nil
}

func getAccountsBalances(ctx sdk.Context, bankKeeper e2e.E2eBankKeeper, bondDenom string, accounts []ibctesting.SenderAccount) map[string]sdk.Int {
	accountsBalances := map[string]sdk.Int{}
	for _, acc := range accounts {
		accountsBalances[string(acc.SenderAccount.GetAddress())] =
			bankKeeper.GetBalance(ctx, acc.SenderAccount.GetAddress(), bondDenom).Amount
	}

	return accountsBalances
}

func (s *ConsumerDemocracyTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}
