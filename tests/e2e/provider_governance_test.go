package e2e

import (
	"fmt"
	"time"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	paramsproposal "github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	upgradetypes "github.com/cosmos/cosmos-sdk/x/upgrade/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func (s *CCVTestSuite) TestProviderGovernance() {
	s.SetupCCVChannel()
	s.SetupGovernanceICAChannel()

	// Bond some tokens on provider to change validator powers
	bondAmt := sdk.NewInt(1000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)
	s.providerChain.NextBlock()
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// this will add gov module ICA account as admin on consumer chain
	s.consumerChain.NextBlock()

	// set provider voting period to 0s so that proposal passes immediately
	govKeeper := s.providerChain.App.(*appProvider.App).GovKeeper
	deposit := govKeeper.GetDepositParams(s.providerCtx()).MinDeposit
	votingParams := govKeeper.GetVotingParams(s.providerCtx())
	votingParams.VotingPeriod = 0 * time.Second
	govKeeper.SetVotingParams(s.providerCtx(), votingParams)
	s.providerChain.NextBlock()

	// test software upgrade proposal type
	swUpgradeProposal := upgradetypes.SoftwareUpgradeProposal{
		Title:       "SW Upgrade Title",
		Description: "SW Upgrade Description",
		Plan: upgradetypes.Plan{
			Name:   "SW Upgrade 1",
			Height: 10000,
			Info:   "Upgrade Info",
		},
	}

	swUpgradeProposalAny, err := codectypes.NewAnyWithValue(&swUpgradeProposal)
	s.Require().NoError(err)
	consumerGovernanceProposal := &types.ConsumerGovernanceProposal{
		ConnectionId: s.icaPath.EndpointA.ConnectionID,
		Content:      swUpgradeProposalAny,
	}

	_, havePlan := s.consumerChain.App.(*appConsumer.App).UpgradeKeeper.GetUpgradePlan(s.consumerCtx())
	s.Assert().False(havePlan)

	// submits consumer SW upgrade proposal to the provider chain
	err = submitProposalAndVote(s.providerCtx(), govKeeper, consumerGovernanceProposal, s.providerChain.SenderAccounts, deposit)
	s.Require().NoError(err)
	s.providerChain.NextBlock()
	relayAllCommittedPackets(s, s.providerChain, s.icaPath, s.icaPath.EndpointB.ChannelConfig.PortID, s.icaPath.EndpointB.ChannelID, 1)
	s.consumerChain.NextBlock()

	// check that proposal passed on the consumer chain (it will be archived in the adminmodule)
	archivedProposals := s.consumerChain.App.(*appConsumer.App).AdminmoduleKeeper.GetArchivedProposals(s.consumerCtx())
	s.Assert().Equal(govtypes.StatusPassed, archivedProposals[0].Status)

	// check that upgrade plan is queued for execution
	plan, havePlan := s.consumerChain.App.(*appConsumer.App).UpgradeKeeper.GetUpgradePlan(s.consumerCtx())
	s.Assert().True(havePlan)
	s.Assert().Equal(swUpgradeProposal.Plan.Name, plan.Name)
	s.Assert().Equal(swUpgradeProposal.Plan.Height, plan.Height)

	// test param change proposal
	var newSignedBlocksVal int64 = 70
	paramChangeProposal := paramsproposal.ParameterChangeProposal{
		Title:       "SignedBlocksWindow Change",
		Description: "SignedBlocksWindow Description",
		Changes: []paramsproposal.ParamChange{
			paramsproposal.NewParamChange("slashing", "SignedBlocksWindow", fmt.Sprintf("\"%d\"", newSignedBlocksVal)),
		},
	}

	paramChangeProposalAny, err := codectypes.NewAnyWithValue(&paramChangeProposal)
	s.Require().NoError(err)
	consumerGovernanceProposal = &types.ConsumerGovernanceProposal{
		ConnectionId: s.icaPath.EndpointA.ConnectionID,
		Content:      paramChangeProposalAny,
	}

	signedBlockWindowOld := s.consumerChain.App.(*appConsumer.App).SlashingKeeper.SignedBlocksWindow(s.consumerCtx())

	// submits consumer param change proposal to the provider chain
	err = submitProposalAndVote(s.providerCtx(), govKeeper, consumerGovernanceProposal, s.providerChain.SenderAccounts, deposit)
	s.Require().NoError(err)
	s.providerChain.NextBlock()
	relayAllCommittedPackets(s, s.providerChain, s.icaPath, s.icaPath.EndpointB.ChannelConfig.PortID, s.icaPath.EndpointB.ChannelID, 1)
	s.consumerChain.NextBlock()

	// check that proposal passed on the consumer chain (it will be archived in the adminmodule)
	archivedProposals = s.consumerChain.App.(*appConsumer.App).AdminmoduleKeeper.GetArchivedProposals(s.consumerCtx())
	s.Assert().Equal(govtypes.StatusPassed, archivedProposals[1].Status)

	// check that signed blocks window has changed
	signedBlockWindowNew := s.consumerChain.App.(*appConsumer.App).SlashingKeeper.SignedBlocksWindow(s.consumerCtx())
	s.Assert().NotEqual(signedBlockWindowOld, signedBlockWindowNew)
	s.Assert().Equal(newSignedBlocksVal, signedBlockWindowNew)
}

func submitProposalAndVote(ctx sdk.Context, govKeeper govkeeper.Keeper, content govtypes.Content,
	accounts []ibctesting.SenderAccount, depositAmount sdk.Coins) error {
	proposal, err := govKeeper.SubmitProposal(ctx, content)
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
