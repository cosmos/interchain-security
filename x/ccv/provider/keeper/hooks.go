package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkgov "github.com/cosmos/cosmos-sdk/x/gov/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
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
func (h Hooks) AfterUnbondingInitiated(ctx sdk.Context, id uint64) error {
	var consumerChainIDS []string

	for _, chain := range h.k.GetAllConsumerChains(ctx) {
		consumerChainIDS = append(consumerChainIDS, chain.ChainId)
	}

	if len(consumerChainIDS) == 0 {
		// Do not put the unbonding op on hold if there are no consumer chains
		return nil
	}
	// Call back into staking to tell it to stop this op from unbonding when the unbonding period is complete
	if err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, id); err != nil {
		// Note: that in the case of a validator unbonding, AfterUnbondingInitiated is called
		// from staking.EndBlock.

		// In this case PutUnbondingOnHold fails if either the unbonding operation was
		// not found or the UnbondingOnHoldRefCount is negative.

		// This change should be updated for SDK v0.48 because it will include changes in handling
		// check: https://github.com/cosmos/cosmos-sdk/pull/16043
		ctx.Logger().Error("unbonding could not be put on hold: %w", err)
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

	// NOTE: This is a temporary fix for v0.47 -> we should not panic in this edge case
	// since the AfterUnbondInitiatedHook can be called with a non-existing UnbondingEntry.id
	// check: https://github.com/cosmos/cosmos-sdk/pull/16043
	//
	// Call back into staking to tell it to stop this op from unbonding when the unbonding period is complete
	// if err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, id); err != nil {
	// 	// If there was an error putting the unbonding on hold, panic to end execution for
	// 	// the current tx and prevent committal of this invalid state.
	// 	//
	// 	// Note: that in the case of a validator unbonding, AfterUnbondingInitiated is called
	// 	// from staking.EndBlock, thus the following panic would halt the chain.
	// 	// In this case PutUnbondingOnHold fails if either the unbonding operation was
	// 	// not found or the UnbondingOnHoldRefCount is negative. In either cases,
	// 	// the state of the x/staking module of cosmos-sdk is invalid.
	// 	panic(fmt.Errorf("unbonding could not be put on hold: %w", err))
	// }
	return nil
}

// ValidatorConsensusKeyInUse is called when a new validator is created
// in the x/staking module of cosmos-sdk. In case it panics, the TX aborts
// and thus, the validator is not created. See AfterValidatorCreated hook.
func ValidatorConsensusKeyInUse(k *Keeper, ctx sdk.Context, valAddr sdk.ValAddress) bool {
	// Get the validator being added in the staking module.
	val, found := k.stakingKeeper.GetValidator(ctx, valAddr)
	if !found {
		// Abort TX, do NOT allow validator to be created
		panic("did not find newly created validator in staking module")
	}

	// Get the consensus address of the validator being added
	consensusAddr, err := val.GetConsAddr()
	if err != nil {
		// Abort TX, do NOT allow validator to be created
		panic("could not get validator cons addr ")
	}

	allConsumerChains := []string{}
	consumerChains := k.GetAllConsumerChains(ctx)
	for _, consumerChain := range consumerChains {
		allConsumerChains = append(allConsumerChains, consumerChain.ChainId)
	}
	proposedChains := k.GetAllProposedConsumerChainIDs(ctx)
	for _, proposedChain := range proposedChains {
		allConsumerChains = append(allConsumerChains, proposedChain.ChainID)
	}
	pendingChainIDs := k.GetAllPendingConsumerChainIDs(ctx)
	allConsumerChains = append(allConsumerChains, pendingChainIDs...)

	for _, c := range allConsumerChains {
		if _, exist := k.GetValidatorByConsumerAddr(
			ctx,
			c,
			providertypes.NewConsumerConsAddress(consensusAddr)); exist {
			return true
		}
	}

	return false
}

func (h Hooks) AfterValidatorCreated(ctx sdk.Context, valAddr sdk.ValAddress) error {
	if ValidatorConsensusKeyInUse(h.k, ctx, valAddr) {
		// Abort TX, do NOT allow validator to be created
		panic("cannot create a validator with a consensus key that is already in use or was recently in use as an assigned consumer chain key")
	}
	return nil
}

func (h Hooks) AfterValidatorRemoved(ctx sdk.Context, valConsAddr sdk.ConsAddress, valAddr sdk.ValAddress) error {
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

func (h Hooks) BeforeDelegationCreated(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeDelegationSharesModified(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterDelegationModified(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeValidatorSlashed(_ sdk.Context, _ sdk.ValAddress, _ sdk.Dec) error {
	return nil
}

func (h Hooks) BeforeValidatorModified(_ sdk.Context, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterValidatorBonded(_ sdk.Context, _ sdk.ConsAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) AfterValidatorBeginUnbonding(_ sdk.Context, _ sdk.ConsAddress, _ sdk.ValAddress) error {
	return nil
}

func (h Hooks) BeforeDelegationRemoved(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) error {
	return nil
}

//
// gov hooks
//

// AfterProposalSubmission - call hook if registered
// After a consumerAddition proposal submission, a record is created
// that maps the proposal ID to the consumer chain ID.
func (h Hooks) AfterProposalSubmission(ctx sdk.Context, proposalID uint64) {
	if p, ok := h.GetConsumerAdditionLegacyPropFromProp(ctx, proposalID); ok {
		h.k.SetProposedConsumerChain(ctx, p.ChainId, proposalID)
	}
}

// AfterProposalVotingPeriodEnded - call hook if registered
// After proposal voting ends, the consumer chainID in store is deleted.
// When a consumerAddition proposal passes, the consumer chainID is available in providerKeeper.GetAllPendingConsumerAdditionProps
// or providerKeeper.GetAllConsumerChains(ctx).
func (h Hooks) AfterProposalVotingPeriodEnded(ctx sdk.Context, proposalID uint64) {
	if _, ok := h.GetConsumerAdditionLegacyPropFromProp(ctx, proposalID); ok {
		h.k.DeleteProposedConsumerChainInStore(ctx, proposalID)
	}
}

func (h Hooks) AfterProposalDeposit(ctx sdk.Context, proposalID uint64, depositorAddr sdk.AccAddress) {
}

func (h Hooks) AfterProposalVote(ctx sdk.Context, proposalID uint64, voterAddr sdk.AccAddress) {
}

func (h Hooks) AfterProposalFailedMinDeposit(ctx sdk.Context, proposalID uint64) {
}

// GetConsumerAdditionLegacyPropFromProp extracts a consumer addition legacy proposal from
// the proposal with given ID
func (h Hooks) GetConsumerAdditionLegacyPropFromProp(
	ctx sdk.Context,
	proposalID uint64,
) (types.ConsumerAdditionProposal, bool) {
	p, ok := h.k.govKeeper.GetProposal(ctx, proposalID)
	if !ok {
		panic(fmt.Errorf("failed to get proposal %d from store", proposalID))
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
		prop, ok := content.(*types.ConsumerAdditionProposal)
		if ok {
			return *prop, true
		}
	}
	return types.ConsumerAdditionProposal{}, false
}
