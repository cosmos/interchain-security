package integration

import (
	"time"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	"github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"

	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
)

// TestAfterPropSubmissionAndVotingPeriodEnded tests the results of GetProviderInfo method.
// @Long Description
// The test sets up the account that will submit the proposal, and then the proposal is created.
// After the proposal is submitted the AfterProposalSubmission hook is triggered
// and it should handle the submission of the proposal in the provider module.
// Proposal submission is then verified, and lastly AfterProposalVotingPeriodEnded is triggered.
// Tests verifies the deletion of the proposal.
func (s *CCVTestSuite) TestAfterPropSubmissionAndVotingPeriodEnded() {
	ctx := s.providerChain.GetContext()
	providerKeeper := s.providerApp.GetProviderKeeper()
	govKeeper := s.providerApp.GetTestGovKeeper()
	proposer := s.providerChain.SenderAccount

	content := testkeeper.GetTestConsumerAdditionProp()
	content.ChainId = "newchain-0"
	legacyPropContent, err := v1.NewLegacyContent(
		content,
		authtypes.NewModuleAddress("gov").String(),
	)
	s.Require().NoError(err)

	proposal, err := v1.NewProposal([]sdk.Msg{legacyPropContent}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", proposer.GetAddress(), false)
	s.Require().NoError(err)

	err = govKeeper.SetProposal(ctx, proposal)
	s.Require().NoError(err)

	providerKeeper.Hooks().AfterProposalSubmission(ctx, proposal.Id)

	// verify that the proposal ID is created
	proposalIdOnProvider, ok := providerKeeper.GetProposedConsumerChain(ctx, proposal.Id)
	s.Require().True(ok)
	s.Require().NotEmpty(proposalIdOnProvider)
	s.Require().Equal(content.ChainId, proposalIdOnProvider)

	providerKeeper.Hooks().AfterProposalVotingPeriodEnded(ctx, proposal.Id)
	// verify that the proposal ID is deleted
	s.Require().Empty(providerKeeper.GetProposedConsumerChain(ctx, proposal.Id))
}

// TestGetConsumerAdditionLegacyPropFromProp manually calls the GetConsumerAdditionLegacyPropFromProp hook on
// various types of proposals to test the behavior of the hook.
// @Long Description@
// The tes case created a provider chain,
// then submits a Proposal with various different types of content.
// Then, it tries to get the ConsumerAdditionProposal from the proposal using the hook.
// Test cases include a proposal with no messages; a proposal with a transfer message; a proposal with an unrelated legacy proposal;
// a proposal with an invalid legacy proposal; and a proposal with a ConsumerAdditionProposal.
// In the case of a valid ConsumerAdditionProposal, the test verifies that the proposal is found and returned by the hook.
func (s *CCVTestSuite) TestGetConsumerAdditionLegacyPropFromProp() {
	ctx := s.providerChain.GetContext()
	proposer := s.providerChain.SenderAccount

	// create a dummy bank send message
	dummyMsg := &banktypes.MsgSend{
		FromAddress: sdk.AccAddress(proposer.GetAddress()).String(),
		ToAddress:   sdk.AccAddress(proposer.GetAddress()).String(),
		Amount:      sdk.NewCoins(sdk.NewCoin("stake", math.OneInt())),
	}

	textProp, err := v1.NewLegacyContent(
		v1beta1.NewTextProposal("a title", "a legacy text prop"),
		authtypes.NewModuleAddress("gov").String(),
	)
	s.Require().NoError(err)

	addConsumerProp, err := v1.NewLegacyContent(
		testkeeper.GetTestConsumerAdditionProp(),
		authtypes.NewModuleAddress("gov").String(),
	)
	s.Require().NoError(err)

	testCases := []struct {
		name                    string
		propMsg                 sdk.Msg
		expectConsumerPropFound bool
		expPanic                bool
	}{
		{
			name:                    "prop not found",
			propMsg:                 nil,
			expectConsumerPropFound: false,
			expPanic:                false,
		},
		{
			name:                    "msgs in prop contain no legacy props",
			propMsg:                 dummyMsg,
			expectConsumerPropFound: false,
			expPanic:                false,
		},
		{
			name:                    "msgs contain a legacy prop but not of ConsumerAdditionProposal type",
			propMsg:                 textProp,
			expectConsumerPropFound: false,
		},
		{
			name:                    "msgs contain an invalid legacy prop",
			propMsg:                 &v1.MsgExecLegacyContent{},
			expectConsumerPropFound: false,
			expPanic:                true,
		},
		{
			name:                    "msg contains a prop of ConsumerAdditionProposal type - hook should create a new proposed chain",
			propMsg:                 addConsumerProp,
			expectConsumerPropFound: true,
			expPanic:                false,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			providerKeeper := s.providerApp.GetProviderKeeper()
			govKeeper := s.providerApp.GetTestGovKeeper()

			var proposal v1.Proposal
			var err error

			if tc.propMsg == nil {
				// cover edgecase where proposal has no messages
				proposal, err = v1.NewProposal([]sdk.Msg{}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", proposer.GetAddress(), false)
				s.Require().NoError(err)
			} else {
				// cover various cases where proposal has messages but only some are consumer addition proposals
				proposal, err = v1.NewProposal([]sdk.Msg{tc.propMsg}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", proposer.GetAddress(), false)
				s.Require().NoError(err)
			}

			err = govKeeper.SetProposal(ctx, proposal)
			s.Require().NoError(err)

			if tc.expPanic {
				s.Require().Panics(func() {
					// this panics with a nil pointer dereference because the proposal is invalid and cannot be unmarshalled
					providerKeeper.Hooks().GetConsumerAdditionLegacyPropFromProp(ctx, proposal.Id)
				})
				return
			}

			savedProp, found := providerKeeper.Hooks().GetConsumerAdditionLegacyPropFromProp(ctx, proposal.Id)
			if tc.expectConsumerPropFound {
				s.Require().True(found)
				s.Require().NotEmpty(savedProp, savedProp)
			} else {
				s.Require().False(found)
				s.Require().Empty(savedProp)
			}
		})
	}
}
