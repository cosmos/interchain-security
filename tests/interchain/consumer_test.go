package interchain

import (
	"cosmos/interchain-security/tests/interchain/chainsuite"
	"testing"

	"github.com/stretchr/testify/suite"
)

func TestConsumerSuite(t *testing.T) {
	s := &ConsumerSuite{}

	suite.Run(t, s)
}

func (s *ConsumerSuite) TestDummyTest() {

	consumer, err := s.Provider.AddConsumerChain(s.GetContext(), s.Relayer, chainsuite.ConsumerChainID, s.GetConsumerSpec(s.GetContext()))
	s.Require().NoError(err)

	//send packet, expect error

	err = chainsuite.ConnectProviderConsumer(s.GetContext(), s.Provider, consumer, s.Relayer)
	s.Require().NoError(err)

	//s.Require().NoError(s.Provider.UpdateAndVerifyStakeChange(s.GetContext(), consumer, s.Relayer, 1_000_000, 0))
}
