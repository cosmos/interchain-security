package keeper

import (
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
	sdkgov "github.com/cosmos/cosmos-sdk/x/gov/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

	"github.com/cosmos/gogoproto/proto"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

type GovHooks struct {
	gk govkeeper.Keeper
	k  *Keeper
}

// Implements GovHooks interface
// GovHooks exist in cosmos-sdk/x/gov/keeper/hooks.go of v0.45.16-lsm-ics and on
var _ sdkgov.GovHooks = GovHooks{}

func (k *Keeper) GovHooks(gk govkeeper.Keeper) GovHooks {
	return GovHooks{
		gk: gk,
		k:  k,
	}
}

// AfterProposalSubmission - call hook if registered
// After consumerAddition proposal submission, the consumer chainID is stored
func (gh GovHooks) AfterProposalSubmission(ctx sdk.Context, proposalID uint64) {
	p, ok := gh.gk.GetProposal(ctx, proposalID)
	if !ok {
		panic(fmt.Errorf("failed to get proposal %d in  gov hook", proposalID))
	}
	msgs := p.GetMessages()

	var msgLegacyContent v1.MsgExecLegacyContent
	err := proto.Unmarshal(msgs[0].Value, &msgLegacyContent)
	if err != nil {
		panic(fmt.Errorf("failed to unmarshal proposal content in gov hook: %w", err))
	}

	// if the proposal is not ConsumerAdditionProposal, return
	var consadditionProp types.ConsumerAdditionProposal
	if err := proto.Unmarshal(msgLegacyContent.Content.Value, &consadditionProp); err != nil {
		return
	}

	if consadditionProp.ProposalType() == types.ProposalTypeConsumerRemoval {
		gh.k.SetChainsInProposal(ctx, consadditionProp.ChainId, proposalID)
	}
}

// AfterProposalVotingPeriodEnded - call hook if registered
// After proposal voting ends, the consumer chainID in store is deleted.
// When a proposal passes, this chainID will be available in providerKeeper.GetAllPendingConsumerAdditionProps
// or providerKeeper.GetAllConsumerChains(ctx).
func (gh GovHooks) AfterProposalVotingPeriodEnded(ctx sdk.Context, proposalID uint64) {
	p, ok := gh.gk.GetProposal(ctx, proposalID)
	if !ok {
		panic(fmt.Errorf("failed to get proposal %d in  gov hook", proposalID))
	}
	msgs := p.GetMessages()

	var msgLegacyContent v1.MsgExecLegacyContent
	err := proto.Unmarshal(msgs[0].Value, &msgLegacyContent)
	if err != nil {
		panic(fmt.Errorf("failed to unmarshal proposal content in gov hook: %w", err))
	}
	var consadditionProp types.ConsumerAdditionProposal

	// if the proposal is not ConsumerAdditionProposal, return
	if err := proto.Unmarshal(msgLegacyContent.Content.Value, &consadditionProp); err != nil {
		return
	}

	gh.k.DeleteChainsInProposal(ctx, consadditionProp.ChainId)
}

func (gh GovHooks) AfterProposalDeposit(ctx sdk.Context, proposalID uint64, depositorAddr sdk.AccAddress) {
}
func (gh GovHooks) AfterProposalVote(ctx sdk.Context, proposalID uint64, voterAddr sdk.AccAddress) {}
func (gh GovHooks) AfterProposalFailedMinDeposit(ctx sdk.Context, proposalID uint64)               {}
