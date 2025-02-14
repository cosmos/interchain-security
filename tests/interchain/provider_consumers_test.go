package interchain

import (
	"context"
	"fmt"
	"testing"
	"time"

	"cosmos/interchain-security/tests/interchain/chainsuite"

	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"

	sdkmath "cosmossdk.io/math"
	upgradetypes "cosmossdk.io/x/upgrade/types"

	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"

	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	"github.com/strangelove-ventures/interchaintest/v8"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"
	"github.com/strangelove-ventures/interchaintest/v8/testutil"
	"github.com/stretchr/testify/suite"
	"github.com/tidwall/sjson"
	"golang.org/x/sync/errgroup"
)

func TestProviderConsumersSuite(t *testing.T) {
	s := &ProviderConsumersSuite{}

	suite.Run(t, s)
}

func (s *ProviderConsumersSuite) TestSovereignToConsumerChangeover() {
	// submit MsgCreateConsumer and verify that the chain is in launched phase
	currentHeight, err := s.Sovereign.Height(s.GetContext())
	s.Require().NoError(err)
	spawnTime := time.Now().Add(time.Hour)
	initializationParams := consumerInitParamsTemplate(&spawnTime)
	initialHeight := uint64(currentHeight) + 60
	initializationParams.InitialHeight = clienttypes.Height{
		RevisionNumber: clienttypes.ParseChainID(s.Sovereign.Config().ChainID),
		RevisionHeight: initialHeight,
	}
	powerShapingParams := powerShapingParamsTemplate()
	createConsumerMsg := msgCreateConsumer(s.Sovereign.Config().ChainID, initializationParams, powerShapingParams, nil, s.Provider.ValidatorWallets[0].Address)
	consumerID, err := s.Provider.CreateConsumer(s.GetContext(), createConsumerMsg, chainsuite.ValidatorMoniker)
	s.Require().NoError(err)
	// opt in validator
	s.Require().NoError(s.Provider.OptIn(s.GetContext(), consumerID, 0))
	// assign consumer key
	valConsumerKey, err := s.Sovereign.GetValidatorKey(s.GetContext(), 0)
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
	s.Require().NoError(s.Sovereign.ExecuteProposalMsg(s.GetContext(), upgradeMsg, chainsuite.ConsumerGovModuleAddress, "Changeover", cosmos.ProposalVoteYes, govv1.StatusPassed, false))

	// wait for sw upgrade height
	currentHeight, err = s.Sovereign.Height(s.GetContext())
	s.Require().NoError(err)
	timeoutCtx, timeoutCtxCancel := context.WithTimeout(s.GetContext(), (time.Duration(int64(initialHeight)-currentHeight)+10)*chainsuite.CommitTimeout)
	defer timeoutCtxCancel()
	err = testutil.WaitForBlocks(timeoutCtx, int(int64(initialHeight)-currentHeight)+3, s.Sovereign)
	s.Require().Error(err)

	// stop sovereign chain
	s.Require().NoError(s.Sovereign.StopAllNodes(s.GetContext()))

	genesis, err := s.Sovereign.GetNode().GenesisFileContent(s.GetContext())
	s.Require().NoError(err)

	// insert consumer genesis section
	ccvState, _, err := s.Provider.GetNode().ExecQuery(s.GetContext(), "provider", "consumer-genesis", consumerID)
	s.Require().NoError(err)
	genesis, err = sjson.SetRawBytes(genesis, "app_state.ccvconsumer", ccvState)
	s.Require().NoError(err)

	genesis, err = sjson.SetBytes(genesis, "app_state.ccvconsumer.preCCV", true)
	s.Require().NoError(err)

	eg := errgroup.Group{}
	for _, val := range s.Sovereign.Validators {
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
	s.Sovereign.ChangeBinary(s.GetContext(), chainsuite.ConsumerBin)
	s.Require().NoError(s.Sovereign.StartAllNodes(s.GetContext()))
	s.Require().NoError(s.Relayer.ConnectProviderConsumer(s.GetContext(), s.Provider, s.Sovereign))
	s.Require().NoError(s.Relayer.StopRelayer(s.GetContext(), chainsuite.GetRelayerExecReporter(s.GetContext())))
	s.Require().NoError(s.Relayer.StartRelayer(s.GetContext(), chainsuite.GetRelayerExecReporter(s.GetContext())))
	params, err := s.Sovereign.GetCcvConsumerParams(s.ctx)
	s.Require().NoError(err)
	s.Require().True(params.Params.HistoricalEntries == fmt.Sprint(initializationParams.HistoricalEntries))
	// check if consumer is connected and functional
	s.Require().NoError(s.Provider.UpdateAndVerifyStakeChange(s.GetContext(), s.Sovereign, s.Relayer, 1_000_000, 0))
}

func (s *ProviderConsumersSuite) TestRewards() {
	transferCh, err := s.Relayer.GetTransferChannel(s.GetContext(), s.Provider, s.Consumer)
	s.Require().NoError(err)
	s.Require().True(transferCh != nil)
	rewardDenom := ccvtypes.ParseDenomTrace(ccvtypes.GetPrefixedDenom("transfer", transferCh.ChannelID,
		s.Consumer.Config().Denom)).IBCDenom()

	govAuthority, err := s.Provider.GetGovernanceAddress(s.GetContext())
	s.Require().NoError(err)
	rewardDenomsProp := &providertypes.MsgChangeRewardDenoms{
		DenomsToAdd: []string{rewardDenom},
		Authority:   govAuthority,
	}
	s.Require().NoError(s.Provider.ExecuteProposalMsg(s.GetContext(), rewardDenomsProp, chainsuite.ProviderGovModuleAddress, "change reward denoms", cosmos.ProposalVoteYes, govv1.StatusPassed, false))

	s.Require().NoError(s.Consumer.SendFunds(s.GetContext(), interchaintest.FaucetAccountKeyName, ibc.WalletAmount{
		Amount:  sdkmath.NewInt(10000),
		Denom:   s.Consumer.Config().Denom,
		Address: s.Consumer.ValidatorWallets[0].Address,
	}))

	s.Require().NoError(testutil.WaitForBlocks(s.GetContext(), chainsuite.BlocksPerDistribution+2, s.Provider, s.Consumer))
	s.Require().NoError(testutil.WaitForBlocks(s.GetContext(), 2, s.Provider, s.Consumer))

	rewardStr, err := s.Provider.QueryJSON(
		s.GetContext(), fmt.Sprintf("total.#(%%\"*%s\")", rewardDenom),
		"distribution", "rewards", s.Provider.ValidatorWallets[0].Address,
	)
	s.Require().NoError(err)
	rewards, err := StrToSDKInt(rewardStr.String())
	s.Require().NoError(err)
	s.Require().True(rewards.GT(sdkmath.NewInt(0)), "rewards: %s", rewards.String())
}
