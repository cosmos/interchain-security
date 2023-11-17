package keeper

import (
	"bytes"
	"encoding/binary"
	"fmt"

	errorsmod "cosmossdk.io/errors"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ibcclienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	providertypes "github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

//
// Double Voting section
//

// HandleConsumerDoubleVoting verifies a double voting evidence for a given a consumer chain ID
// and a public key and, if successful, executes the jailing of the malicious validator.
func (k Keeper) HandleConsumerDoubleVoting(
	ctx sdk.Context,
	evidence *tmtypes.DuplicateVoteEvidence,
	chainID string,
	pubkey cryptotypes.PubKey,
) error {
	// check that the evidence is for an ICS consumer chain
	if _, found := k.GetConsumerClientId(ctx, chainID); !found {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"cannot find consumer chain %s",
			chainID,
		)
	}

	// check that the evidence is not too old
	minHeight := k.GetEquivocationEvidenceMinHeight(ctx, chainID)
	if uint64(evidence.VoteA.Height) < minHeight {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"evidence for consumer chain %s is too old - evidence height (%d), min (%d)",
			chainID,
			evidence.VoteA.Height,
			minHeight,
		)
	}

	// verifies the double voting evidence using the consumer chain public key
	if err := k.VerifyDoubleVotingEvidence(*evidence, chainID, pubkey); err != nil {
		return err
	}

	// get the validator's consensus address on the provider
	providerAddr := k.GetProviderAddrFromConsumerAddr(
		ctx,
		chainID,
		providertypes.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress.Bytes())),
	)

	if err := k.SlashValidator(ctx, providerAddr); err != nil {
		return err
	}
	if err := k.JailAndTombstoneValidator(ctx, providerAddr); err != nil {
		return err
	}

	k.Logger(ctx).Info(
		"confirmed equivocation",
		"byzantine validator address", providerAddr.String(),
	)

	return nil
}

// VerifyDoubleVotingEvidence verifies a double voting evidence
// for a given chain id and a validator public key
func (k Keeper) VerifyDoubleVotingEvidence(
	evidence tmtypes.DuplicateVoteEvidence,
	chainID string,
	pubkey cryptotypes.PubKey,
) error {
	if pubkey == nil {
		return fmt.Errorf("validator public key cannot be empty")
	}

	// check that the validator address in the evidence is derived from the provided public key
	if !bytes.Equal(pubkey.Address(), evidence.VoteA.ValidatorAddress) {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"public key %s doesn't correspond to the validator address %s in double vote evidence",
			pubkey.String(), evidence.VoteA.ValidatorAddress.String(),
		)
	}

	// Note that since we're only jailing validators for double voting on a consumer chain,
	// the age of the evidence is irrelevant and therefore isn't checked.

	// height/round/type must be the same
	if evidence.VoteA.Height != evidence.VoteB.Height ||
		evidence.VoteA.Round != evidence.VoteB.Round ||
		evidence.VoteA.Type != evidence.VoteB.Type {
		return sdkerrors.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"h/r/s does not match: %d/%d/%v vs %d/%d/%v",
			evidence.VoteA.Height, evidence.VoteA.Round, evidence.VoteA.Type,
			evidence.VoteB.Height, evidence.VoteB.Round, evidence.VoteB.Type)
	}

	// Addresses must be the same
	if !bytes.Equal(evidence.VoteA.ValidatorAddress, evidence.VoteB.ValidatorAddress) {
		return sdkerrors.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"validator addresses do not match: %X vs %X",
			evidence.VoteA.ValidatorAddress,
			evidence.VoteB.ValidatorAddress,
		)
	}

	// BlockIDs must be different
	if evidence.VoteA.BlockID.Equals(evidence.VoteB.BlockID) {
		return sdkerrors.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"block IDs are the same (%v) - not a real duplicate vote",
			evidence.VoteA.BlockID,
		)
	}

	va := evidence.VoteA.ToProto()
	vb := evidence.VoteB.ToProto()

	// signatures must be valid
	if !pubkey.VerifySignature(tmtypes.VoteSignBytes(chainID, va), evidence.VoteA.Signature) {
		return fmt.Errorf("verifying VoteA: %w", tmtypes.ErrVoteInvalidSignature)
	}
	if !pubkey.VerifySignature(tmtypes.VoteSignBytes(chainID, vb), evidence.VoteB.Signature) {
		return fmt.Errorf("verifying VoteB: %w", tmtypes.ErrVoteInvalidSignature)
	}

	return nil
}

//
// Light Client Attack (IBC misbehavior) section
//

// HandleConsumerMisbehaviour checks if the given IBC misbehaviour corresponds to an equivocation light client attack,
// and in this case, slashes, jails, and tombstones
func (k Keeper) HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	logger := k.Logger(ctx)

	// Check that the misbehaviour is valid and that the client consensus states at trusted heights are within trusting period
	if err := k.CheckMisbehaviour(ctx, misbehaviour); err != nil {
		logger.Info("Misbehaviour rejected", err.Error())

		return err
	}

	// Since the misbehaviour packet was received within the trusting period
	// w.r.t to the trusted consensus states the infraction age
	// isn't too old. see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go

	// Get Byzantine validators from the conflicting headers
	byzantineValidators, err := k.GetByzantineValidators(ctx, misbehaviour)
	if err != nil {
		return err
	}

	provAddrs := make([]providertypes.ProviderConsAddress, len(byzantineValidators))

	// slash, jail, and tombstone the Byzantine validators
	for _, v := range byzantineValidators {
		providerAddr := k.GetProviderAddrFromConsumerAddr(
			ctx,
			misbehaviour.Header1.Header.ChainID,
			providertypes.NewConsumerConsAddress(sdk.ConsAddress(v.Address.Bytes())),
		)
		err := k.SlashValidator(ctx, providerAddr)
		if err != nil {
			logger.Error("failed to slash validator: %s", err)
			continue
		}
		err = k.JailAndTombstoneValidator(ctx, providerAddr)
		// JailAndTombstoneValidator should never return an error if
		// SlashValidator succeeded because both methods fail if the malicious
		// validator is either or both !found, unbonded and tombstoned.
		if err != nil {
			panic(err)
		}

		provAddrs = append(provAddrs, providerAddr)
	}

	// Return an error if no validators were punished
	if len(provAddrs) == 0 {
		return fmt.Errorf("failed to slash, jail, or tombstone all validators: %v", byzantineValidators)
	}

	logger.Info(
		"confirmed equivocation light client attack",
		"byzantine validators slashed, jailed and tombstoned", provAddrs,
	)

	return nil
}

// GetByzantineValidators returns the validators that signed both headers.
// If the misbehavior is an equivocation light client attack, then these
// validators are the Byzantine validators.
func (k Keeper) GetByzantineValidators(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) (validators []*tmtypes.Validator, err error) {
	// construct the trusted and conflicted light blocks
	lightBlock1, err := headerToLightBlock(*misbehaviour.Header1)
	if err != nil {
		return
	}
	lightBlock2, err := headerToLightBlock(*misbehaviour.Header2)
	if err != nil {
		return
	}

	// Check if the misbehaviour corresponds to an Amnesia attack,
	// meaning that the conflicting headers have both valid state transitions
	// and different commit rounds. In this case, we return no validators as
	// we can't identify the byzantine validators.
	//
	// Note that we cannot differentiate which of the headers is trusted or malicious,
	if !headersStateTransitionsAreConflicting(*lightBlock1.Header, *lightBlock2.Header) && lightBlock1.Commit.Round != lightBlock2.Commit.Round {
		return
	}

	// compare the signatures of the headers
	// and return the intersection of validators who signed both

	// create a map with the validators' address that signed header1
	header1Signers := map[string]int{}
	for idx, sign := range lightBlock1.Commit.Signatures {
		if sign.Absent() {
			continue
		}
		header1Signers[sign.ValidatorAddress.String()] = idx
	}

	// iterate over the header2 signers and check if they signed header1
	for sigIdxHeader2, sign := range lightBlock2.Commit.Signatures {
		if sign.Absent() {
			continue
		}
		if sigIdxHeader1, ok := header1Signers[sign.ValidatorAddress.String()]; ok {
			if err := verifyLightBlockCommitSig(*lightBlock1, sigIdxHeader1); err != nil {
				return nil, err
			}

			if err := verifyLightBlockCommitSig(*lightBlock2, sigIdxHeader2); err != nil {
				return nil, err
			}

			_, val := lightBlock1.ValidatorSet.GetByAddress(sign.ValidatorAddress)
			validators = append(validators, val)
		}
	}

	return validators, nil
}

// headerToLightBlock returns a CometBFT light block from the given IBC header
func headerToLightBlock(h ibctmtypes.Header) (*tmtypes.LightBlock, error) {
	sh, err := tmtypes.SignedHeaderFromProto(h.SignedHeader)
	if err != nil {
		return nil, err
	}

	vs, err := tmtypes.ValidatorSetFromProto(h.ValidatorSet)
	if err != nil {
		return nil, err
	}

	return &tmtypes.LightBlock{
		SignedHeader: sh,
		ValidatorSet: vs,
	}, nil
}

// CheckMisbehaviour checks that headers in the given misbehaviour forms
// a valid light client attack from an ICS consumer chain and that the light client isn't expired
func (k Keeper) CheckMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	consumerChainID := misbehaviour.Header1.Header.ChainID

	// check that the misbehaviour is for an ICS consumer chain
	clientId, found := k.GetConsumerClientId(ctx, consumerChainID)
	if !found {
		return fmt.Errorf("incorrect misbehaviour with conflicting headers from a non-existent consumer chain: %s", consumerChainID)
	} else if misbehaviour.ClientId != clientId {
		return fmt.Errorf("incorrect misbehaviour: expected client ID for consumer chain %s is %s got %s",
			consumerChainID,
			clientId,
			misbehaviour.ClientId,
		)
	}

	// Check that the headers are at the same height to ensure that
	// the misbehaviour is for a light client attack and not a time violation,
	// see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go
	if !misbehaviour.Header1.GetHeight().EQ(misbehaviour.Header2.GetHeight()) {
		return sdkerrors.Wrap(ibcclienttypes.ErrInvalidMisbehaviour, "headers are not at same height")
	}

	// Check that the evidence is not too old
	minHeight := k.GetEquivocationEvidenceMinHeight(ctx, consumerChainID)
	evidenceHeight := misbehaviour.Header1.GetHeight().GetRevisionHeight()
	// Note that the revision number is not relevant for checking the age of evidence
	// as it's already part of the chain ID and the minimum height is mapped to chain IDs
	if evidenceHeight < minHeight {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"evidence for consumer chain %s is too old - evidence height (%d), min (%d)",
			consumerChainID,
			evidenceHeight,
			minHeight,
		)
	}

	clientState, found := k.clientKeeper.GetClientState(ctx, clientId)
	if !found {
		return sdkerrors.Wrapf(ibcclienttypes.ErrClientNotFound, "cannot check misbehaviour for client with ID %s", misbehaviour.GetClientID())
	}

	clientStore := k.clientKeeper.ClientStore(ctx, misbehaviour.GetClientID())

	// CheckMisbehaviourAndUpdateState verifies the misbehaviour against the trusted consensus states
	// but does NOT update the light client state.
	// Note that the IBC CheckMisbehaviourAndUpdateState method returns an error if the trusted consensus states are expired,
	// see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go
	_, err := clientState.CheckMisbehaviourAndUpdateState(ctx, k.cdc, clientStore, &misbehaviour)
	if err != nil {
		return err
	}

	return nil
}

// Check if the given block headers have conflicting state transitions.
// Note that this method was copied from ConflictingHeaderIsInvalid in CometBFT,
// see https://github.com/cometbft/cometbft/blob/v0.34.27/types/evidence.go#L285
func headersStateTransitionsAreConflicting(h1, h2 tmtypes.Header) bool {
	return !bytes.Equal(h1.ValidatorsHash, h2.ValidatorsHash) ||
		!bytes.Equal(h1.NextValidatorsHash, h2.NextValidatorsHash) ||
		!bytes.Equal(h1.ConsensusHash, h2.ConsensusHash) ||
		!bytes.Equal(h1.AppHash, h2.AppHash) ||
		!bytes.Equal(h1.LastResultsHash, h2.LastResultsHash)
}

func verifyLightBlockCommitSig(lightBlock tmtypes.LightBlock, sigIdx int) error {
	// get signature
	sig := lightBlock.Commit.Signatures[sigIdx]

	// get validator
	idx, val := lightBlock.ValidatorSet.GetByAddress(sig.ValidatorAddress)
	if idx == -1 {
		return fmt.Errorf("incorrect signature: validator address %s isn't part of the validator set", sig.ValidatorAddress.String())
	}

	// verify validator pubkey corresponds to signature validator address
	if !bytes.Equal(val.PubKey.Address(), sig.ValidatorAddress) {
		return fmt.Errorf("validator public key doesn't correspond to signature validator address: %s!= %s", val.PubKey.Address(), sig.ValidatorAddress)
	}

	// validate signature
	voteSignBytes := lightBlock.Commit.VoteSignBytes(lightBlock.ChainID, int32(sigIdx))
	if !val.PubKey.VerifySignature(voteSignBytes, sig.Signature) {
		return fmt.Errorf("wrong signature (#%d): %X", sigIdx, sig.Signature)
	}

	return nil
}

//
// Punish Validator section
//

// JailAndTombstoneValidator jails and tombstones the validator with the given provider consensus address
func (k Keeper) JailAndTombstoneValidator(ctx sdk.Context, providerAddr providertypes.ProviderConsAddress) error {
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		return errorsmod.Wrapf(slashingtypes.ErrNoValidatorForAddress, "provider consensus address: %s", providerAddr.String())
	}

	if validator.IsUnbonded() {
		return fmt.Errorf("validator is unbonded. provider consensus address: %s", providerAddr.String())
	}

	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		return fmt.Errorf("validator is tombstoned. provider consensus address: %s", providerAddr.String())
	}

	// jail validator if not already
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerAddr.ToSdkConsAddr())
	}

	k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime)

	// Tombstone the validator so that we cannot slash the validator more than once
	// Note that we cannot simply use the fact that a validator is jailed to avoid slashing more than once
	// because then a validator could i) perform an equivocation, ii) get jailed (e.g., through downtime)
	// and in such a case the validator would not get slashed when we call `SlashValidator`.
	k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr())

	return nil
}

// ComputePowerToSlash computes the power to be slashed based on the tokens in non-matured `undelegations` and
// `redelegations`, as well as the current `power` of the validator.
// Note that this method does not perform any slashing.
func (k Keeper) ComputePowerToSlash(ctx sdk.Context, validator stakingtypes.Validator, undelegations []stakingtypes.UnbondingDelegation,
	redelegations []stakingtypes.Redelegation, power int64, powerReduction sdk.Int,
) int64 {
	// compute the total numbers of tokens currently being undelegated
	undelegationsInTokens := sdk.NewInt(0)

	// Note that we use a **cached** context to avoid any actual slashing of undelegations or redelegations.
	cachedCtx, _ := ctx.CacheContext()
	for _, u := range undelegations {
		amountSlashed := k.stakingKeeper.SlashUnbondingDelegation(cachedCtx, u, 0, sdk.NewDec(1))
		undelegationsInTokens = undelegationsInTokens.Add(amountSlashed)
	}

	// compute the total numbers of tokens currently being redelegated
	redelegationsInTokens := sdk.NewInt(0)
	for _, r := range redelegations {
		amountSlashed := k.stakingKeeper.SlashRedelegation(cachedCtx, validator, r, 0, sdk.NewDec(1))
		redelegationsInTokens = redelegationsInTokens.Add(amountSlashed)
	}

	// The power we pass to staking's keeper `Slash` method is the current power of the validator together with the total
	// power of all the currently undelegated and redelegated tokens (see docs/docs/adrs/adr-013-equivocation-slashing.md).
	undelegationsAndRedelegationsInPower := sdk.TokensToConsensusPower(
		undelegationsInTokens.Add(redelegationsInTokens), powerReduction)

	return power + undelegationsAndRedelegationsInPower
}

// SlashValidator slashes validator with `providerAddr`
func (k Keeper) SlashValidator(ctx sdk.Context, providerAddr providertypes.ProviderConsAddress) error {
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		return errorsmod.Wrapf(slashingtypes.ErrNoValidatorForAddress, "provider consensus address: %s", providerAddr.String())
	}

	if validator.IsUnbonded() {
		return fmt.Errorf("validator is unbonded. provider consensus address: %s", providerAddr.String())
	}

	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		return fmt.Errorf("validator is tombstoned. provider consensus address: %s", providerAddr.String())
	}

	undelegations := k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, validator.GetOperator())
	redelegations := k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, validator.GetOperator())
	lastPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
	powerReduction := k.stakingKeeper.PowerReduction(ctx)
	totalPower := k.ComputePowerToSlash(ctx, validator, undelegations, redelegations, lastPower, powerReduction)
	slashFraction := k.slashingKeeper.SlashFractionDoubleSign(ctx)

	k.stakingKeeper.Slash(ctx, providerAddr.ToSdkConsAddr(), 0, totalPower, slashFraction, stakingtypes.DoubleSign)
	return nil
}

//
// CRUD section
//

// SetEquivocationEvidenceMinHeight sets the the minimum height
// of a valid consumer equivocation evidence for a given consumer chain ID
func (k Keeper) SetEquivocationEvidenceMinHeight(ctx sdk.Context, chainID string, height uint64) {
	store := ctx.KVStore(k.storeKey)
	heightBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(heightBytes, height)

	store.Set(providertypes.EquivocationEvidenceMinHeightKey(chainID), heightBytes)
}

// GetEquivocationEvidenceMinHeight returns the the minimum height
// of a valid consumer equivocation evidence for a given consumer chain ID
func (k Keeper) GetEquivocationEvidenceMinHeight(ctx sdk.Context, chainID string) uint64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.EquivocationEvidenceMinHeightKey(chainID))
	if bz == nil {
		return 0
	}

	return binary.BigEndian.Uint64(bz)
}

// DeleteEquivocationEvidenceMinHeight deletes the the minimum height
// of a valid consumer equivocation evidence for a given consumer chain ID
func (k Keeper) DeleteEquivocationEvidenceMinHeight(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(providertypes.EquivocationEvidenceMinHeightKey(chainID))
}
