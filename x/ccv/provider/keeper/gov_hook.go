package keeper

import (
	"fmt"

	"github.com/cosmos/gogoproto/proto"

	sdk "github.com/cosmos/cosmos-sdk/types"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
	sdkgov "github.com/cosmos/cosmos-sdk/x/gov/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

type GovHooks struct {
	gk *govkeeper.Keeper
	k  *Keeper
}

// Implements GovHooks interface
// GovHooks exist in cosmos-sdk/x/gov/keeper/hooks.go of v0.45.16-lsm-ics and on
var _ sdkgov.GovHooks = GovHooks{}

func (k *Keeper) GovHooks(gk *govkeeper.Keeper) GovHooks {
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

	for _, msg := range msgs {
		var msgLegacyContent v1.MsgExecLegacyContent
		err := proto.Unmarshal(msg.Value, &msgLegacyContent)
		if err != nil {
			panic(fmt.Errorf("failed to unmarshal proposal content in gov hook: %w", err))
		}

		// if the proposal is not ConsumerAdditionProposal, continue
		if msgLegacyContent.Content.TypeUrl != "/interchain_security.ccv.provider.v1.ConsumerAdditionProposal" {
			continue
		}
		// if the consumer addition proposal cannot be unmarshaled, continue
		var consAdditionProp types.ConsumerAdditionProposal
		if err := proto.Unmarshal(msgLegacyContent.Content.Value, &consAdditionProp); err != nil {
			continue
		}

		if consAdditionProp.ProposalType() == types.ProposalTypeConsumerAddition {
			gh.k.SetProposedConsumerChain(ctx, consAdditionProp.ChainId, proposalID)
		}
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

	for _, msg := range msgs {
		var msgLegacyContent v1.MsgExecLegacyContent
		err := proto.Unmarshal(msg.Value, &msgLegacyContent)
		if err != nil {
			panic(fmt.Errorf("failed to unmarshal proposal content in gov hook: %w", err))
		}

		if msgLegacyContent.Content.TypeUrl != "/interchain_security.ccv.provider.v1.ConsumerAdditionProposal" {
			continue
		}
		var consAdditionProp types.ConsumerAdditionProposal
		// if the proposal is not ConsumerAdditionProposal, return
		if err := proto.Unmarshal(msgLegacyContent.Content.Value, &consAdditionProp); err != nil {
			continue
		}

		if consAdditionProp.ProposalType() == types.ProposalTypeConsumerAddition {
			gh.k.DeleteChainsInProposal(ctx, consAdditionProp.ChainId, proposalID)
		}

	}
}

func (gh GovHooks) AfterProposalDeposit(ctx sdk.Context, proposalID uint64, depositorAddr sdk.AccAddress) {
}
func (gh GovHooks) AfterProposalVote(ctx sdk.Context, proposalID uint64, voterAddr sdk.AccAddress) {}
func (gh GovHooks) AfterProposalFailedMinDeposit(ctx sdk.Context, proposalID uint64)               {}
