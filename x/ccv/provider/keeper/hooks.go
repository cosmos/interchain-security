package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
)

// Wrapper struct
type Hooks struct {
	k         *Keeper
	govKeeper ccv.GovKeeper
}

var (
	_ stakingtypes.StakingHooks = Hooks{}
	_ govtypes.GovHooks         = Hooks{}
)

// Returns new provider hooks
func (k *Keeper) Hooks(govKeeper ccv.GovKeeper) Hooks {
	return Hooks{
		k:         k,
		govKeeper: govKeeper,
	}
}

//-----------------------------------------
// Staking Hooks

// This stores a record of each unbonding op from staking, allowing us to track which consumer chains have unbonded
func (h Hooks) AfterUnbondingInitiated(ctx sdk.Context, ID uint64) error {
	var consumerChainIDS []string

	for _, chain := range h.k.GetAllConsumerChains(ctx) {
		consumerChainIDS = append(consumerChainIDS, chain.ChainId)
	}

	if len(consumerChainIDS) == 0 {
		// Do not put the unbonding op on hold if there are no consumer chains
		return nil
	}
	valsetUpdateID := h.k.GetValidatorSetUpdateId(ctx)
	unbondingOp := providertypes.UnbondingOp{
		Id:                      ID,
		UnbondingConsumerChains: consumerChainIDS,
	}

	// Add to indexes
	for _, consumerChainID := range consumerChainIDS {
		index, _ := h.k.GetUnbondingOpIndex(ctx, consumerChainID, valsetUpdateID)
		index = append(index, ID)
		h.k.SetUnbondingOpIndex(ctx, consumerChainID, valsetUpdateID, index)
	}

	h.k.SetUnbondingOp(ctx, unbondingOp)

	// Call back into staking to tell it to stop this op from unbonding when the unbonding period is complete
	if err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, ID); err != nil {
		// If there was an error putting the unbonding on hold, panic to end execution for
		// the current tx and prevent committal of this invalid state.
		//
		// Note: that in the case of a validator unbonding, AfterUnbondingInitiated is called
		// form staking.EndBlock, thus the following panic would halt the chain.
		// In this case PutUnbondingOnHold fails if either the unbonding operation was
		// not found or the UnbondingOnHoldRefCount is negative. In either cases,
		// the state of the x/staking module of cosmos-sdk is invalid.
		panic(fmt.Errorf("unbonding could not be put on hold: %w", err))
	}
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

	inUse := false

	for _, validatorConsumerAddrs := range k.GetAllValidatorsByConsumerAddr(ctx, nil) {
		if validatorConsumerAddrs.ConsumerAddr.ToSdkConsAddr().Equals(consensusAddr) {
			inUse = true
			break
		}
	}

	return inUse
}

func (h Hooks) AfterValidatorCreated(ctx sdk.Context, valAddr sdk.ValAddress) {
	if ValidatorConsensusKeyInUse(h.k, ctx, valAddr) {
		// Abort TX, do NOT allow validator to be created
		panic("cannot create a validator with a consensus key that is already in use or was recently in use as an assigned consumer chain key")
	}
}

func (h Hooks) AfterValidatorRemoved(ctx sdk.Context, valConsAddr sdk.ConsAddress, valAddr sdk.ValAddress) {
	for _, validatorConsumerPubKey := range h.k.GetAllValidatorConsumerPubKeys(ctx, nil) {
		if validatorConsumerPubKey.ProviderAddr.ToSdkConsAddr().Equals(valConsAddr) {
			consumerAddrTmp, err := utils.TMCryptoPublicKeyToConsAddr(*validatorConsumerPubKey.ConsumerKey)
			if err != nil {
				// An error here would indicate something is very wrong
				panic("cannot get address of consumer key")
			}
			consumerAddr := providertypes.NewConsumerConsAddress(consumerAddrTmp)
			h.k.DeleteValidatorByConsumerAddr(ctx, validatorConsumerPubKey.ChainId, consumerAddr)
			h.k.DeleteValidatorConsumerPubKey(ctx, validatorConsumerPubKey.ChainId, *validatorConsumerPubKey.ProviderAddr)
		}
	}
}

func (h Hooks) BeforeDelegationCreated(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) {
}
func (h Hooks) BeforeDelegationSharesModified(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) {
}
func (h Hooks) AfterDelegationModified(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) {
}
func (h Hooks) BeforeValidatorSlashed(_ sdk.Context, _ sdk.ValAddress, _ sdk.Dec) {
}
func (h Hooks) BeforeValidatorModified(_ sdk.Context, _ sdk.ValAddress) {
}
func (h Hooks) AfterValidatorBonded(_ sdk.Context, _ sdk.ConsAddress, _ sdk.ValAddress) {
}
func (h Hooks) AfterValidatorBeginUnbonding(_ sdk.Context, _ sdk.ConsAddress, _ sdk.ValAddress) {
}
func (h Hooks) BeforeDelegationRemoved(_ sdk.Context, _ sdk.AccAddress, _ sdk.ValAddress) {
}

//-----------------------------------------
// Gov Hooks

func (h Hooks) AfterProposalSubmission(ctx sdk.Context, proposalID uint64) {}

func (h Hooks) AfterProposalDeposit(ctx sdk.Context, proposalID uint64, _ sdk.AccAddress) {
	if h.k.HasEquivocationProposal(ctx, proposalID) {
		// already handled, skip
		return
	}
	prop, found := h.govKeeper.GetProposal(ctx, proposalID)
	if !found {
		panic(fmt.Sprintf("cannot find proposal %d", proposalID))
	}
	if prop.Status != govtypes.StatusVotingPeriod {
		// skip if proposal is not in voting period
		return
	}
	eqProp, ok := prop.GetContent().(*types.EquivocationProposal)
	if !ok {
		// skip if not an equivocation proposal
		return
	}
	// Mark proposal has handled
	h.k.SetEquivocationProposal(ctx, proposalID)
	for _, eq := range eqProp.Equivocations {
		ids, err := h.getUnbondingOpsIDsForValidator(ctx, eq.ConsensusAddress)
		if err != nil {
			panic(fmt.Errorf("can get unbondings of validator '%s': %w", eq.ConsensusAddress, err))
		}
		for _, id := range ids {
			err := h.k.stakingKeeper.PutUnbondingOnHold(ctx, id)
			if err != nil {
				panic(fmt.Errorf("cannot PutUnbondingOnHold for id %d: %w", id, err))
			}
		}
	}
}

func (h Hooks) AfterProposalVote(_ sdk.Context, _ uint64, _ sdk.AccAddress) {}
func (h Hooks) AfterProposalFailedMinDeposit(_ sdk.Context, _ uint64)       {}

func (h Hooks) AfterProposalVotingPeriodEnded(ctx sdk.Context, proposalID uint64) {
	prop, found := h.govKeeper.GetProposal(ctx, proposalID)
	if !found {
		panic(fmt.Sprintf("cannot find proposal %d", proposalID))
	}
	eqProp, ok := prop.GetContent().(*types.EquivocationProposal)
	if !ok {
		// skip if not an equivocation proposal
		return
	}
	for _, eq := range eqProp.Equivocations {
		ids, err := h.getUnbondingOpsIDsForValidator(ctx, eq.ConsensusAddress)
		if err != nil {
			panic(fmt.Errorf("can get unbondings of validator '%s': %w", eq.ConsensusAddress, err))
		}
		for _, id := range ids {
			err := h.k.stakingKeeper.UnbondingCanComplete(ctx, id)
			if err != nil {
				panic(fmt.Errorf("cannot UnbondingCanComplete for id %d: %w", id, err))
			}
		}
	}
	// Remove equivocation proposal flag
	h.k.DeleteEquivocationProposal(ctx, proposalID)
}

// getUnbondingOpsIDsForValidator returns all pending unbonding operations for
// validator consensus address consAddrStr.
func (h Hooks) getUnbondingOpsIDsForValidator(ctx sdk.Context, consAddrStr string) ([]uint64, error) {
	consAddr, err := sdk.ConsAddressFromBech32(consAddrStr)
	if err != nil {
		return nil, fmt.Errorf("cannot convert '%s' to consensus address", consAddrStr)
	}
	val, found := h.k.stakingKeeper.GetValidatorByConsAddr(ctx, consAddr)
	if !found {
		return nil, fmt.Errorf("cannot find validator for consensus address '%s'", consAddr)
	}
	var ids []uint64
	// pause all unbonding delegation
	ubds := h.k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, val.GetOperator())
	for _, ubd := range ubds {
		for _, entry := range ubd.Entries {
			ids = append(ids, entry.UnbondingId)
		}
	}
	// pause all redelegations
	reds := h.k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, val.GetOperator())
	for _, red := range reds {
		for _, entry := range red.Entries {
			ids = append(ids, entry.UnbondingId)
		}
	}
	// pause all unbonding validator
	ids = append(ids, val.UnbondingIds...)
	return ids, nil
}
