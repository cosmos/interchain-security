package interchain

import (
	"context"
	"cosmos/interchain-security/tests/interchain/chainsuite"
	"fmt"
	"testing"
	"time"

	upgradetypes "cosmossdk.io/x/upgrade/types"

	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"

	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/testutil"
	"github.com/stretchr/testify/suite"
	"github.com/tidwall/sjson"
	"golang.org/x/sync/errgroup"
)

func TestChangeoverSuite(t *testing.T) {
	s := &ChangeoverSuite{}

	suite.Run(t, s)
}

func (s *ChangeoverSuite) TestSovereignToConsumer() {
	// submit MsgCreateConsumer and verify that the chain is in launched phase
	currentHeight, err := s.Consumer.Height(s.GetContext())
	s.Require().NoError(err)
	spawnTime := time.Now().Add(time.Hour)
	initializationParams := consumerInitParamsTemplate(&spawnTime)
	initialHeight := uint64(currentHeight) + 60
	initializationParams.InitialHeight = clienttypes.Height{
		RevisionNumber: clienttypes.ParseChainID(s.Consumer.Config().ChainID),
		RevisionHeight: initialHeight,
	}
	powerShapingParams := powerShapingParamsTemplate()
	createConsumerMsg := msgCreateConsumer(s.Consumer.Config().ChainID, initializationParams, powerShapingParams, nil, s.Provider.ValidatorWallets[0].Address)
	consumerID, err := s.Provider.CreateConsumer(s.GetContext(), createConsumerMsg, chainsuite.ValidatorMoniker)
	s.Require().NoError(err)
	// opt in validator
	s.Require().NoError(s.Provider.OptIn(s.GetContext(), consumerID, 0))
	// assign consumer key
	valConsumerKey, err := s.Consumer.GetValidatorKey(s.GetContext(), 0)
	s.Require().NoError(err)
	s.Require().NoError(s.Provider.AssignKey(s.GetContext(), consumerID, 0, valConsumerKey))
	// update spawn time
	initializationParams.SpawnTime = time.Now()
	updateMsg := &providertypes.MsgUpdateConsumer{
		Owner:                    s.Provider.ValidatorWallets[0].Address,
		ConsumerId:               consumerID,
		NewOwnerAddress:          s.Provider.ValidatorWallets[0].Address,
		InitializationParameters: initializationParams,
		PowerShapingParameters:   powerShapingParams,
	}
	s.Require().NoError(s.Provider.UpdateConsumer(s.GetContext(), updateMsg, s.Provider.ValidatorWallets[0].Address))
	s.Require().NoError(testutil.WaitForBlocks(s.GetContext(), 2, s.Provider))
	consumerChain, err := s.Provider.GetConsumerChain(s.GetContext(), consumerID)
	s.Require().NoError(err)
	s.Require().Equal(providertypes.CONSUMER_PHASE_LAUNCHED.String(), consumerChain.Phase)

	// submit sw upgrade proposal
	upgradeMsg := &upgradetypes.MsgSoftwareUpgrade{
		Authority: chainsuite.ConsumerGovModuleAddress,
		Plan: upgradetypes.Plan{
			Name:   "sovereign-changeover",
			Height: int64(initialHeight) - 3,
		},
	}
	s.Require().NoError(s.Consumer.ExecuteProposalMsg(s.GetContext(), upgradeMsg, chainsuite.ConsumerGovModuleAddress, "Changeover", cosmos.ProposalVoteYes, govv1.StatusPassed, false))

	// wait for sw upgrade height
	currentHeight, err = s.Consumer.Height(s.GetContext())
	s.Require().NoError(err)
	timeoutCtx, timeoutCtxCancel := context.WithTimeout(s.GetContext(), (time.Duration(int64(initialHeight)-currentHeight)+10)*chainsuite.CommitTimeout)
	defer timeoutCtxCancel()
	err = testutil.WaitForBlocks(timeoutCtx, int(int64(initialHeight)-currentHeight)+3, s.Consumer)
	s.Require().Error(err)

	// stop sovereign chain
	s.Require().NoError(s.Consumer.StopAllNodes(s.GetContext()))

	genesis, err := s.Consumer.GetNode().GenesisFileContent(s.GetContext())
	s.Require().NoError(err)

	// insert consumer genesis section
	ccvState, _, err := s.Provider.GetNode().ExecQuery(s.GetContext(), "provider", "consumer-genesis", consumerID)
	s.Require().NoError(err)
	genesis, err = sjson.SetRawBytes(genesis, "app_state.ccvconsumer", ccvState)
	s.Require().NoError(err)

	eg := errgroup.Group{}
	for _, val := range s.Consumer.Validators {
		val := val
		eg.Go(func() error {
			if err := val.OverwriteGenesisFile(s.GetContext(), []byte(genesis)); err != nil {
				return err
			}
			return val.WriteFile(s.GetContext(), []byte(genesis), ".sovereign/config/genesis.json")
		})
	}
	s.Require().NoError(eg.Wait())

	// replace the binary and restart consumer node
	s.Consumer.ChangeBinary(s.GetContext(), "interchain-security-cdd")
	s.Require().NoError(s.Consumer.StartAllNodes(s.GetContext()))
	s.Require().NoError(s.Relayer.ConnectProviderConsumer(s.GetContext(), s.Provider, s.Consumer))
	s.Require().NoError(s.Relayer.StopRelayer(s.GetContext(), chainsuite.GetRelayerExecReporter(s.GetContext())))
	s.Require().NoError(s.Relayer.StartRelayer(s.GetContext(), chainsuite.GetRelayerExecReporter(s.GetContext())))
	params, err := s.Consumer.GetCcvConsumerParams(s.ctx)
	s.Require().NoError(err)
	s.Require().True(params.Params.HistoricalEntries == fmt.Sprint(initializationParams.HistoricalEntries))
	// check if consumer is connected and functional
	s.Require().NoError(s.Provider.UpdateAndVerifyStakeChange(s.GetContext(), s.Consumer, s.Relayer, 1_000_000, 0))
}
