package interchain

import (
	"testing"
	"time"

	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	"github.com/strangelove-ventures/interchaintest/v8/testutil"
	"github.com/stretchr/testify/suite"
)

type MultiValidatorProviderSuite struct {
	ProviderSuite
}

func TestMultiValidatorProviderSuite(t *testing.T) {
	s := &MultiValidatorProviderSuite{}
	s.ValidatorNodes = 2

	suite.Run(t, s)
}

// TestOptInChainCanOnlyStartIfActiveValidatorOptedIn tests that only if an active validator opts in to an Opt-In chain, the chain can launch.
// Scenario 1: Inactive validators opts in, the chain does not launch.
// Scenario 2: Active validator opts in, the chain launches.
func (s *MultiValidatorProviderSuite) TestOptInChainCanOnlyStartIfActiveValidatorOptedIn() {
	testAcc := s.Provider.TestWallets[2].FormattedAddress()
	testAccKey := s.Provider.TestWallets[2].KeyName()

	activeValIndex := 0
	inactiveValIndex := 1

	// Scenario 1: Inactive validators opts in, the chain does not launch.
	chainName := "optInActiveInactiveVal-1"
	spawnTime := time.Now().Add(time.Hour)
	consumerInitParams := consumerInitParamsTemplate(&spawnTime)
	createConsumerMsg := msgCreateConsumer(chainName, consumerInitParams, powerShapingParamsTemplate(), nil, testAcc)
	consumerId, err := s.Provider.CreateConsumer(s.GetContext(), createConsumerMsg, testAccKey)
	s.Require().NoError(err)
	consumerChain, err := s.Provider.GetConsumerChain(s.GetContext(), consumerId)
	s.Require().NoError(err)
	// inactive validator opts in
	s.Require().NoError(s.Provider.OptIn(s.GetContext(), consumerChain.ConsumerID, inactiveValIndex))
	consumerInitParams.SpawnTime = time.Now()
	upgradeMsg := &providertypes.MsgUpdateConsumer{
		Owner:                    testAcc,
		ConsumerId:               consumerChain.ConsumerID,
		NewOwnerAddress:          testAcc,
		InitializationParameters: consumerInitParams,
		PowerShapingParameters:   powerShapingParamsTemplate(),
	}
	s.Require().NoError(s.Provider.UpdateConsumer(s.GetContext(), upgradeMsg, testAccKey))
	s.Require().NoError(testutil.WaitForBlocks(s.GetContext(), 1, s.Provider))
	consumerChain, err = s.Provider.GetConsumerChain(s.GetContext(), consumerId)
	s.Require().NoError(err)
	s.Require().Equal(providertypes.CONSUMER_PHASE_REGISTERED.String(), consumerChain.Phase)

	// Scenario 2: Active validator opts in, the chain launches.
	// active validator opts in
	s.Require().NoError(s.Provider.OptIn(s.GetContext(), consumerChain.ConsumerID, activeValIndex))

	s.Require().NoError(s.Provider.UpdateConsumer(s.GetContext(), upgradeMsg, testAccKey))
	s.Require().NoError(testutil.WaitForBlocks(s.GetContext(), 1, s.Provider))
	consumerChain, err = s.Provider.GetConsumerChain(s.GetContext(), consumerId)
	s.Require().NoError(err)
	s.Require().Equal(providertypes.CONSUMER_PHASE_LAUNCHED.String(), consumerChain.Phase)
}
