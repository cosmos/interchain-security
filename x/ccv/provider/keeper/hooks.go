package keeper

import (
	"context"
	"cosmossdk.io/math"
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkgov "github.com/cosmos/cosmos-sdk/x/gov/types"
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

func (h Hooks) AfterUnbondingInitiated(goCtx context.Context, id uint64) error {
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

func (h Hooks) BeforeTokenizeShareRecordRemoved(_ context.Context, _ uint64) error {
	return nil
}

//
// gov hooks
//

// AfterProposalSubmission - call hook if registered
// If an update consumer message exists in the proposal, a record is created that maps the proposal id to the consumer id
func (h Hooks) AfterProposalSubmission(goCtx context.Context, proposalId uint64) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	p, err := h.k.govKeeper.Proposals.Get(ctx, proposalId)
	if err != nil {
		return fmt.Errorf("cannot retrieve proposal with id: %d", proposalId)
	}

	hasUpdateConsumerMsg := false
	for _, msg := range p.GetMessages() {
		sdkMsg, isMsgUpdateConsumer := msg.GetCachedValue().(*providertypes.MsgUpdateConsumer)
		if isMsgUpdateConsumer {
			// A `MsgUpdateConsumer` can only succeed if the owner of the consumer chain is the gov module.
			// If that's not the case, we immediately fail the proposal.
			// Note that someone could potentially change the owner of a chain to be that of the gov module
			// while a proposal is active and before the proposal is executed. Even then, we still do not allow
			// `MsgUpdateConsumer` proposals if the owner of the chain is not the gov module to avoid someone forgetting
			// to change the owner address while the proposal is active.
			ownerAddress, err := h.k.GetConsumerOwnerAddress(ctx, sdkMsg.ConsumerId)
			if err != nil {
				return fmt.Errorf("cannot find owner address for consumer with consumer id (%s): %s", sdkMsg.ConsumerId, err.Error())
			} else if ownerAddress != h.k.GetAuthority() {
				return fmt.Errorf("owner address (%s) is not the gov module (%s)", ownerAddress, h.k.GetAuthority())
			}

			if hasUpdateConsumerMsg {
				return fmt.Errorf("proposal can contain at most one `MsgUpdateConsumer` message")
			}
			hasUpdateConsumerMsg = true
			h.k.SetProposalIdToConsumerId(ctx, proposalId, sdkMsg.ConsumerId)
		}

		// if the proposal contains a deprecated message, cancel the proposal
		_, isMsgConsumerAddition := msg.GetCachedValue().(*providertypes.MsgConsumerAddition)
		if isMsgConsumerAddition {
			return fmt.Errorf("proposal cannot contain deprecated `MsgConsumerAddition`; use `MsgCreateConsumer` instead")
		}

		_, isMsgConsumerModification := msg.GetCachedValue().(*providertypes.MsgConsumerModification)
		if isMsgConsumerModification {
			return fmt.Errorf("proposal cannot contain deprecated `MsgConsumerModification`; use `MsgUpdateConsumer` instead")
		}
		_, isMsgConsumerRemoval := msg.GetCachedValue().(*providertypes.MsgConsumerRemoval)
		if isMsgConsumerRemoval {
			return fmt.Errorf("proposal cannot contain deprecated `MsgConsumerRemoval`; use `MsgRemoveConsumer` instead")
		}
	}

	return nil
}

// AfterProposalVotingPeriodEnded - call hook if registered
// After proposal voting ends, the consumer to proposal id record in store is deleted.
func (h Hooks) AfterProposalVotingPeriodEnded(goCtx context.Context, proposalId uint64) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	p, err := h.k.govKeeper.Proposals.Get(ctx, proposalId)
	if err != nil {
		return fmt.Errorf("cannot retrieve proposal with id: %d", proposalId)
	}

	for _, msg := range p.GetMessages() {
		_, isUpdateConsumer := msg.GetCachedValue().(*providertypes.MsgUpdateConsumer)
		if isUpdateConsumer {
			h.k.DeleteProposalIdToConsumerId(ctx, proposalId)
			return nil
		}
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

// GetConsumerAdditionFromProp extracts a consumer addition proposal from
// the proposal with the given ID
func (h Hooks) GetConsumerAdditionFromProp(
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
		sdkMsg, isConsumerAddition := msg.GetCachedValue().(*providertypes.MsgConsumerAddition)
		if !isConsumerAddition {
			continue
		}

		proposal := providertypes.ConsumerAdditionProposal{
			Title:                             p.Title,
			Description:                       p.Summary,
			ChainId:                           sdkMsg.ChainId,
			InitialHeight:                     sdkMsg.InitialHeight,
			GenesisHash:                       sdkMsg.GenesisHash,
			BinaryHash:                        sdkMsg.BinaryHash,
			SpawnTime:                         sdkMsg.SpawnTime,
			UnbondingPeriod:                   sdkMsg.UnbondingPeriod,
			CcvTimeoutPeriod:                  sdkMsg.CcvTimeoutPeriod,
			TransferTimeoutPeriod:             sdkMsg.TransferTimeoutPeriod,
			ConsumerRedistributionFraction:    sdkMsg.ConsumerRedistributionFraction,
			BlocksPerDistributionTransmission: sdkMsg.BlocksPerDistributionTransmission,
			HistoricalEntries:                 sdkMsg.HistoricalEntries,
			DistributionTransmissionChannel:   sdkMsg.DistributionTransmissionChannel,
			Top_N:                             sdkMsg.Top_N,
			ValidatorsPowerCap:                sdkMsg.ValidatorsPowerCap,
			ValidatorSetCap:                   sdkMsg.ValidatorSetCap,
			Allowlist:                         sdkMsg.Allowlist,
			Denylist:                          sdkMsg.Denylist,
		}
		return proposal, true
	}
	return providertypes.ConsumerAdditionProposal{}, false
}
