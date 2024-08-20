package keeper

import (
	"context"
	"cosmossdk.io/math"
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
// After a consumerAddition proposal submission, a record is created
// that maps the proposal ID to the consumer chain ID.
func (h Hooks) AfterProposalSubmission(goCtx context.Context, proposalID uint64) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	if _, ok := h.GetConsumerAdditionFromProp(ctx, proposalID); ok {
		consumerId := h.k.FetchAndIncrementConsumerId(ctx)
		h.k.SetProposedConsumerChain(ctx, consumerId, proposalID)
	}
	return nil
}

// AfterProposalVotingPeriodEnded - call hook if registered
// After proposal voting ends, the consumer consumerId in store is deleted.
// When a consumerAddition proposal passes, the consumer consumerId is available in providerKeeper.GetAllPendingConsumerAdditionProps
// or providerKeeper.GetAllConsumerChains(ctx).
func (h Hooks) AfterProposalVotingPeriodEnded(goCtx context.Context, proposalID uint64) error {
	ctx := sdk.UnwrapSDKContext(goCtx)

	if _, ok := h.GetConsumerAdditionFromProp(ctx, proposalID); ok {
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
