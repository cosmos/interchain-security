package e2e

import (
	"fmt"
	"strconv"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"

	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	proposaltypes "github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	e2eutil "github.com/cosmos/interchain-security/testutil/e2e"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/stretchr/testify/suite"
)

type ConsumerDemocracyTestSuite struct {
	suite.Suite
	coordinator   *ibctesting.Coordinator
	consumerChain *ibctesting.TestChain
	consumerApp   e2eutil.DemocConsumerApp
	setupCallback DemocSetupCallback
}

// NewCCVTestSuite returns a new instance of ConsumerDemocracyTestSuite,
// ready to be tested against using suite.Run().
func NewConsumerDemocracyTestSuite[T e2eutil.DemocConsumerApp](
	democConsumerAppIniter ibctesting.AppIniter,
) *ConsumerDemocracyTestSuite {
	democSuite := new(ConsumerDemocracyTestSuite)

	democSuite.setupCallback = func(t *testing.T) (
		*ibctesting.Coordinator,
		*ibctesting.TestChain,
		e2eutil.DemocConsumerApp,
	) {
		// Instantiate the test coordinator
		coordinator := ibctesting.NewCoordinator(t, 0)

		// Add single democracy consumer to coordinator, store returned test chain and app.
		democConsumer, democConsumerApp := icstestingutils.AddDemocracyConsumer[T](
			coordinator, t, democConsumerAppIniter)

		// Pass variables to suite.
		return coordinator, democConsumer, democConsumerApp
	}
	return democSuite
}

// Callback for instantiating a new coordinator, consumer test chain, and consumer app
// before every test defined on the suite.
type DemocSetupCallback func(t *testing.T) (
	coord *ibctesting.Coordinator,
	consumerChain *ibctesting.TestChain,
	consumerApp e2eutil.DemocConsumerApp,
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


	s.Require().Equal(distrModuleDifference, consumerRedistributeDifference)

	s.Require().Equal(communityPoolDifference.Quo(consumerRedistributeDifference),
		distrKeeper.GetCommunityTax(s.consumerCtx()))

	s.Require().InEpsilon(distrModuleDifference.Quo(
		providerDifference.Add(distrModuleDifference)).MustFloat64(),
		consumerRedistributionFraction.MustFloat64(), float64(0.0001))

	s.Require().InEpsilon(providerDifference.Quo(
		providerDifference.Add(distrModuleDifference)).MustFloat64(),
		sdk.NewDec(1).Sub(consumerRedistributionFraction).MustFloat64(), float64(0.0001))

	totalRepresentativePower := stakingKeeper.GetValidatorSet().TotalBondedTokens(s.consumerCtx())


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
	allowedChange := proposaltypes.ParamChange{Subspace: minttypes.ModuleName, Key: "InflationMax", Value: fmt.Sprintf("\"%s\"", newMintParamValue)}
	forbiddenChange := proposaltypes.ParamChange{Subspace: authtypes.ModuleName, Key: "MaxMemoCharacters", Value: fmt.Sprintf("\"%s\"", strconv.FormatUint(newAuthParamValue, 10))}
	votingAccounts := s.consumerChain.SenderAccounts
	bondDenom := stakingKeeper.BondDenom(s.consumerCtx())
	depositAmount := govKeeper.GetDepositParams(s.consumerCtx()).MinDeposit
	votingParams := govKeeper.GetVotingParams(s.consumerCtx())
	votingParams.VotingPeriod = 3 * time.Second
	govKeeper.SetVotingParams(s.consumerCtx(), votingParams)
	s.consumerChain.NextBlock()
	votersOldBalances := getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts)


	paramChange := proposaltypes.ParameterChangeProposal{Changes: []proposaltypes.ParamChange{allowedChange, forbiddenChange}}
	err := submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), paramChange, votingAccounts, depositAmount)
	s.Assert().NoError(err)

	//once the proposal is added to the chain
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(votingParams.VotingPeriod)
	s.consumerChain.NextBlock()

	oldAuthParamValue := accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	oldMintParamValue := mintKeeper.GetParams(s.consumerCtx()).InflationMax
	s.consumerChain.NextBlock()

	currentAuthParamValue := accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	currentMintParamValue := mintKeeper.GetParams(s.consumerCtx()).InflationMax

	s.Assert().Equal(oldAuthParamValue, currentAuthParamValue)
	s.Assert().NotEqual(newAuthParamValue, currentAuthParamValue)
	s.Assert().Equal(oldMintParamValue, currentMintParamValue)
	s.Assert().NotEqual(newMintParamValue, currentMintParamValue)

	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))


	paramChange = proposaltypes.ParameterChangeProposal{Changes: []proposaltypes.ParamChange{allowedChange}}
	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), paramChange, votingAccounts, depositAmount)
	s.Assert().NoError(err)
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(votingParams.VotingPeriod)
	s.consumerChain.NextBlock()
	oldMintParamValue = mintKeeper.GetParams(s.consumerCtx()).InflationMax
	s.consumerChain.NextBlock()
	currentMintParamValue = mintKeeper.GetParams(s.consumerCtx()).InflationMax

	s.Assert().Equal(newMintParamValue, currentMintParamValue)
	s.Assert().NotEqual(oldMintParamValue, currentMintParamValue)

	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))


	paramChange = proposaltypes.ParameterChangeProposal{Changes: []proposaltypes.ParamChange{forbiddenChange}}
	err = submitProposalWithDepositAndVote(govKeeper, s.consumerCtx(), paramChange, votingAccounts, depositAmount)
	s.Assert().NoError(err)
	s.consumerChain.CurrentHeader.Time = s.consumerChain.CurrentHeader.Time.Add(votingParams.VotingPeriod)
	s.consumerChain.NextBlock()
	oldAuthParamValue = accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters
	s.consumerChain.NextBlock()
	currentAuthParamValue = accountKeeper.GetParams(s.consumerCtx()).MaxMemoCharacters

	s.Assert().Equal(oldAuthParamValue, currentAuthParamValue)
	s.Assert().NotEqual(newAuthParamValue, currentAuthParamValue)

	s.Assert().Equal(votersOldBalances, getAccountsBalances(s.consumerCtx(), bankKeeper, bondDenom, votingAccounts))
}

func submitProposalWithDepositAndVote(govKeeper e2eutil.E2eGovKeeper, ctx sdk.Context, paramChange proposaltypes.ParameterChangeProposal,
	accounts []ibctesting.SenderAccount, depositAmount sdk.Coins,
) error {
	proposal, err := govKeeper.SubmitProposal(ctx, &paramChange)
	if err != nil {
		return err
	}

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

func getAccountsBalances(ctx sdk.Context, bankKeeper e2eutil.E2eBankKeeper, bondDenom string, accounts []ibctesting.SenderAccount) map[string]sdk.Int {
	accountsBalances := map[string]sdk.Int{}
	for _, acc := range accounts {
		accountsBalances[string(acc.SenderAccount.GetAddress())] = bankKeeper.GetBalance(ctx, acc.SenderAccount.GetAddress(), bondDenom).Amount
	}

	return accountsBalances
}

func (s *ConsumerDemocracyTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}
