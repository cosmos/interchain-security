package keeper

import (
	"context"
	"fmt"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkgov "github.com/cosmos/cosmos-sdk/x/gov/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// Wrapper struct
type Hooks struct {
	k *Keeper
}

var (
	_ stakingtypes.StakingHooks = Hooks{}
	_ sdkgov.GovHooks           = Hooks{}
)

// Returns new provider hooks
func (k *Keeper) Hooks() Hooks {
	return Hooks{k}
}

//
// staking hooks
//

// This stores a record of each unbonding op from staking, allowing us to track which consumer chains have unbonded
func (h Hooks) AfterUnbondingInitiated(goCtx context.Context, id uint64) error {
	var consumerChainIDS []string

	ctx := sdk.UnwrapSDKContext(goCtx)
	for _, chain := range h.k.GetAllConsumerChains(ctx) {

		consumerChainIDS = append(consumerChainIDS, chain.ChainId)
	}

	if len(consumerChainIDS) == 0 {
		// Do not put the unbonding op on hold if there are no consumer chains
		return nil
	}

	valsetUpdateID := h.k.GetValidatorSetUpdateId(ctx)
	unbondingOp := providertypes.UnbondingOp{
		Id:                      id,
		UnbondingConsumerChains: consumerChainIDS,
	}

	// Add to indexes
	for _, consumerChainID := range consumerChainIDS {
		index, _ := h.k.GetUnbondingOpIndex(ctx, consumerChainID, valsetUpdateID)
		index = append(index, id)
		h.k.SetUnbondingOpIndex(ctx, consumerChainID, valsetUpdateID, index)
	}

	h.k.SetUnbondingOp(ctx, unbondingOp)

	// Call back into staking to tell it to stop this op from unbonding when the unbonding period is complete
	if err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, id); err != nil {
		// If there was an error putting the unbonding on hold, panic to end execution for
		// the current tx and prevent committal of this invalid state.
		//
		// Note: that in the case of a validator unbonding, AfterUnbondingInitiated is called
		// from staking.EndBlock, thus the following panic would halt the chain.

		// In this case PutUnbondingOnHold fails if either the unbonding operation was
		// not found or the UnbondingOnHoldRefCount is negative. In either cases,
		// the state of the x/staking module of cosmos-sdk is invalid.
		panic(fmt.Errorf("unbonding could not be put on hold: %w", err))
	}
	return nil
}

func (h Hooks) AfterValidatorCreated(goCtx context.Context, valAddr sdk.ValAddress) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	if h.k.ValidatorConsensusKeyInUse(ctx, valAddr) {
		// Abort TX, do NOT allow validator to be created
		panic("cannot create a validator with a consensus key that is already in use or was recently in use as an assigned consumer chain key")
	}
	return nil
}

func (h Hooks) AfterValidatorRemoved(goCtx context.Context, valConsAddr sdk.ConsAddress, valAddr sdk.ValAddress) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	for _, validatorConsumerPubKey := range h.k.GetAllValidatorConsumerPubKeys(ctx, nil) {
		if sdk.ConsAddress(validatorConsumerPubKey.ProviderAddr).Equals(valConsAddr) {
			consumerAddrTmp, err := ccvtypes.TMCryptoPublicKeyToConsAddr(*validatorConsumerPubKey.ConsumerKey)
			if err != nil {
				// An error here would indicate something is very wrong
				panic("cannot get address of consumer key")
			}
			consumerAddr := providertypes.NewConsumerConsAddress(consumerAddrTmp)
			h.k.DeleteValidatorByConsumerAddr(ctx, validatorConsumerPubKey.ChainId, consumerAddr)
			providerAddr := providertypes.NewProviderConsAddress(validatorConsumerPubKey.ProviderAddr)
			h.k.DeleteValidatorConsumerPubKey(ctx, validatorConsumerPubKey.ChainId, providerAddr)
		}
	}

	return nil
}

func (h Hooks) BeforeDelegationCreated(_ context.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeDelegationSharesModified(_ context.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterDelegationModified(_ context.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeValidatorSlashed(_ context.Context, _ sdk.ValAddress, _ math.LegacyDec) error {
	return nil
}

func (h Hooks) BeforeValidatorModified(_ context.Context, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterValidatorBonded(_ context.Context, _ sdk.ConsAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterValidatorBeginUnbonding(_ context.Context, _ sdk.ConsAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeDelegationRemoved(_ context.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

//
// gov hooks
//

// AfterProposalSubmission - call hook if registered
// After a consumerAddition proposal submission, a record is created
// that maps the proposal ID to the consumer chain ID.
func (h Hooks) AfterProposalSubmission(goCtx context.Context, proposalID uint64) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	if p, ok := h.GetConsumerAdditionLegacyPropFromProp(ctx, proposalID); ok {
		h.k.SetProposedConsumerChain(ctx, p.ChainId, proposalID)
	}
	return nil
}

// AfterProposalVotingPeriodEnded - call hook if registered
// After proposal voting ends, the consumer chainID in store is deleted.
// When a consumerAddition proposal passes, the consumer chainID is available in providerKeeper.GetAllPendingConsumerAdditionProps
// or providerKeeper.GetAllConsumerChains(ctx).
func (h Hooks) AfterProposalVotingPeriodEnded(goCtx context.Context, proposalID uint64) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	if _, ok := h.GetConsumerAdditionLegacyPropFromProp(ctx, proposalID); ok {
		h.k.DeleteProposedConsumerChainInStore(ctx, proposalID)
	}
	return nil
}

func (h Hooks) AfterProposalDeposit(ctx context.Context, proposalID uint64, depositorAddr sdk.AccAddress) error {
	return nil
}

func (h Hooks) AfterProposalVote(ctx context.Context, proposalID uint64, voterAddr sdk.AccAddress) error {
	return nil
}

func (h Hooks) AfterProposalFailedMinDeposit(ctx context.Context, proposalID uint64) error {
	return nil
}

// GetConsumerAdditionLegacyPropFromProp extracts a consumer addition legacy proposal from
// the proposal with the given ID
func (h Hooks) GetConsumerAdditionLegacyPropFromProp(
	ctx sdk.Context,
	proposalID uint64,
) (providertypes.ConsumerAdditionProposal, bool) {
	p, err := h.k.govKeeper.Proposals.Get(ctx, proposalID)
	if err != nil {
		return providertypes.ConsumerAdditionProposal{}, false
	}

	// Iterate over the messages in the proposal
	// Note that it's assumed that at most ONE message can contain a consumer addition proposal
	for _, msg := range p.GetMessages() {
		sdkMsg, isLegacyProposal := msg.GetCachedValue().(*v1.MsgExecLegacyContent)
		if !isLegacyProposal {
			continue
		}

		content, err := v1.LegacyContentFromMessage(sdkMsg)
		if err != nil {
			panic(fmt.Errorf("failed to get legacy proposal %d from prop message", proposalID))
		}

		// returns if legacy prop is of ConsumerAddition proposal type
		prop, ok := content.(*providertypes.ConsumerAdditionProposal)
		if ok {
			return *prop, true
		}
	}
	return providertypes.ConsumerAdditionProposal{}, false
}

func (h Hooks) BeforeTokenizeShareRecordRemoved(_ sdk.Context, _ uint64) error {
	return nil
}
