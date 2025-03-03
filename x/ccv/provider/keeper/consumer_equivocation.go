package keeper

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"

	ibcclienttypes "github.com/cosmos/ibc-go/v10/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v10/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmtypes "github.com/cometbft/cometbft/types"

	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

//
// Double Voting section
//

// HandleConsumerDoubleVoting verifies a double voting evidence for a given a consumer id
// and a public key and, if successful, executes the slashing, jailing, and tombstoning of the malicious validator.
func (k Keeper) HandleConsumerDoubleVoting(
	ctx sdk.Context,
	consumerId string,
	evidence *tmtypes.DuplicateVoteEvidence,
	pubkey cryptotypes.PubKey,
) error {
	// check that the evidence is for an ICS consumer chain
	if _, found := k.GetConsumerClientId(ctx, consumerId); !found {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"cannot find consumer chain %s",
			consumerId,
		)
	}

	// check that the evidence is not too old
	minHeight := k.GetEquivocationEvidenceMinHeight(ctx, consumerId)
	if uint64(evidence.VoteA.Height) < minHeight {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"evidence for consumer chain %s is too old - evidence height (%d), min (%d)",
			consumerId,
			evidence.VoteA.Height,
			minHeight,
		)
	}

	// get the chainId of this consumer chain to verify the double-voting evidence
	chainId, err := k.GetConsumerChainId(ctx, consumerId)
	if err != nil {
		return err
	}

	// verifies the double voting evidence using the consumer chain public key
	if err = k.VerifyDoubleVotingEvidence(*evidence, chainId, pubkey); err != nil {
		return err
	}

	// get the validator's consensus address on the provider
	providerAddr := k.GetProviderAddrFromConsumerAddr(
		ctx,
		consumerId,
		types.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress.Bytes())),
	)

	// get the consumer's infraction parameters
	infractionParams, err := k.GetInfractionParameters(ctx, consumerId)
	if err != nil {
		return err
	}

	if err = k.SlashValidator(ctx, providerAddr, infractionParams.DoubleSign); err != nil {
		return err
	}
	if err = k.JailAndTombstoneValidator(ctx, providerAddr, infractionParams.DoubleSign); err != nil {
		return err
	}

	k.Logger(ctx).Info(
		"confirmed equivocation",
		"consumerId", consumerId,
		"chainId", chainId,
		"byzantine validator address", providerAddr.String(),
	)

	return nil
}

// VerifyDoubleVotingEvidence verifies a double voting evidence
// for a given chain id and a validator public key
func (k Keeper) VerifyDoubleVotingEvidence(
	evidence tmtypes.DuplicateVoteEvidence,
	chainId string,
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

	// Note the age of the evidence isn't checked.

	// height/round/type must be the same
	if evidence.VoteA.Height != evidence.VoteB.Height ||
		evidence.VoteA.Round != evidence.VoteB.Round ||
		evidence.VoteA.Type != evidence.VoteB.Type {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"height/round/type are not the same: %d/%d/%v vs %d/%d/%v",
			evidence.VoteA.Height, evidence.VoteA.Round, evidence.VoteA.Type,
			evidence.VoteB.Height, evidence.VoteB.Round, evidence.VoteB.Type)
	}

	// Addresses must be the same
	if !bytes.Equal(evidence.VoteA.ValidatorAddress, evidence.VoteB.ValidatorAddress) {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"validator addresses do not match: %X vs %X",
			evidence.VoteA.ValidatorAddress,
			evidence.VoteB.ValidatorAddress,
		)
	}

	// BlockIDs must be different
	if evidence.VoteA.BlockID.Equals(evidence.VoteB.BlockID) {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"block IDs are the same (%v) - not a real duplicate vote",
			evidence.VoteA.BlockID,
		)
	}

	va := evidence.VoteA.ToProto()
	vb := evidence.VoteB.ToProto()

	// signatures must be valid
	if !pubkey.VerifySignature(tmtypes.VoteSignBytes(chainId, va), evidence.VoteA.Signature) {
		return fmt.Errorf("verifying VoteA: %w", tmtypes.ErrVoteInvalidSignature)
	}
	if !pubkey.VerifySignature(tmtypes.VoteSignBytes(chainId, vb), evidence.VoteB.Signature) {
		return fmt.Errorf("verifying VoteB: %w", tmtypes.ErrVoteInvalidSignature)
	}

	return nil
}

//
// Light Client Attack (IBC misbehavior) section
//

// HandleConsumerMisbehaviour checks if the given IBC misbehaviour corresponds to an equivocation light client attack,
// and in this case, slashes, jails, and tombstones
func (k Keeper) HandleConsumerMisbehaviour(ctx sdk.Context, consumerId string, misbehaviour ibctmtypes.Misbehaviour) error {
	logger := k.Logger(ctx)

	// Check that the misbehaviour is valid and that the client consensus states at trusted heights are within trusting period
	if err := k.CheckMisbehaviour(ctx, consumerId, misbehaviour); err != nil {
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

	provAddrs := make([]types.ProviderConsAddress, 0, len(byzantineValidators))

	infractionParams, err := k.GetInfractionParameters(ctx, consumerId)
	if err != nil {
		return err
	}

	// slash, jail, and tombstone the Byzantine validators
	for _, v := range byzantineValidators {
		providerAddr := k.GetProviderAddrFromConsumerAddr(
			ctx,
			consumerId,
			types.NewConsumerConsAddress(sdk.ConsAddress(v.Address.Bytes())),
		)
		err := k.SlashValidator(ctx, providerAddr, infractionParams.DoubleSign)
		if err != nil {
			logger.Error("failed to slash validator: %s", err)
			continue
		}
		err = k.JailAndTombstoneValidator(ctx, providerAddr, infractionParams.DoubleSign)
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
		"consumerId", consumerId,
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
		return validators, err
	}
	lightBlock2, err := headerToLightBlock(*misbehaviour.Header2)
	if err != nil {
		return validators, err
	}

	// Check if the misbehaviour corresponds to an Amnesia attack,
	// meaning that the conflicting headers have both valid state transitions
	// and different commit rounds. In this case, we return no validators as
	// we can't identify the byzantine validators.
	//
	// Note that we cannot differentiate which of the headers is trusted or malicious,
	if !headersStateTransitionsAreConflicting(*lightBlock1.Header, *lightBlock2.Header) && lightBlock1.Commit.Round != lightBlock2.Commit.Round {
		return validators, nil
	}

	// compare the signatures of the headers
	// and return the intersection of validators who signed both

	// create a map with the validators' address that signed header1
	header1Signers := map[string]int{}
	for idx, sign := range lightBlock1.Commit.Signatures {
		if sign.BlockIDFlag == tmtypes.BlockIDFlagAbsent {
			continue
		}
		header1Signers[sign.ValidatorAddress.String()] = idx
	}

	// iterate over the header2 signers and check if they signed header1
	for sigIdxHeader2, sign := range lightBlock2.Commit.Signatures {
		if sign.BlockIDFlag == tmtypes.BlockIDFlagAbsent {
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
func (k Keeper) CheckMisbehaviour(ctx sdk.Context, consumerId string, misbehaviour ibctmtypes.Misbehaviour) error {
	chainId := misbehaviour.Header1.Header.ChainID

	consumerChainId, err := k.GetConsumerChainId(ctx, consumerId)
	if err != nil {
		return err
	} else if consumerChainId != chainId {
		return fmt.Errorf("incorrect misbehaviour for a different chain id (%s) than that of the consumer chain %s (consumerId: %s)",
			chainId,
			consumerChainId,
			consumerId)
	}

	// check that the misbehaviour is for an ICS consumer chain
	clientId, found := k.GetConsumerClientId(ctx, consumerId)
	if !found {
		return fmt.Errorf("incorrect misbehaviour with conflicting headers from a non-existent consumer chain (consumerId: %s)", consumerId)
	} else if misbehaviour.ClientId != clientId {
		return fmt.Errorf("incorrect misbehaviour: expected client ID for consumer chain with id %s is %s got %s",
			consumerId,
			clientId,
			misbehaviour.ClientId,
		)
	}

	// Check that the headers are at the same height to ensure that
	// the misbehaviour is for a light client attack and not a time violation,
	// see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go
	if !misbehaviour.Header1.GetHeight().EQ(misbehaviour.Header2.GetHeight()) {
		return errorsmod.Wrap(ibcclienttypes.ErrInvalidMisbehaviour, "headers are not at same height")
	}

	// Check that the evidence is not too old
	minHeight := k.GetEquivocationEvidenceMinHeight(ctx, consumerId)
	evidenceHeight := misbehaviour.Header1.GetHeight().GetRevisionHeight()
	// Note that the revision number is not relevant for checking the age of evidence
	// as it's already part of the chain ID and the minimum height is mapped to chain IDs
	if evidenceHeight < minHeight {
		return errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"evidence for consumer chain %s is too old - evidence height (%d), min (%d)",
			consumerId,
			evidenceHeight,
			minHeight,
		)
	}

	lightClientModule := ibctmtypes.NewLightClientModule(k.cdc, k.clientKeeper.GetStoreProvider())

	// CheckForMisbehaviour verifies that the headers have different blockID hashes
	ok := lightClientModule.CheckForMisbehaviour(ctx, clientId, &misbehaviour)
	if !ok {
		return errorsmod.Wrapf(ibcclienttypes.ErrInvalidMisbehaviour, "invalid misbehaviour for client-id: %s", misbehaviour.ClientId)
	}

	// VerifyClientMessage calls verifyMisbehaviour which verifies that the headers in the misbehaviour
	// are valid against their respective trusted consensus states and that at least a TrustLevel of the validator set signed their commit,
	// see checkMisbehaviourHeader in ibc-go/blob/v7.3.0/modules/light-clients/07-tendermint/misbehaviour_handle.go#L126
	if err := lightClientModule.VerifyClientMessage(ctx, clientId, &misbehaviour); err != nil {
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
func (k Keeper) JailAndTombstoneValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress, jailingParams *types.SlashJailParameters) error {
	validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if err != nil && errors.Is(err, stakingtypes.ErrNoValidatorFound) {
		return errorsmod.Wrapf(slashingtypes.ErrNoValidatorForAddress, "provider consensus address: %s", providerAddr.String())
	} else if err != nil {
		return errorsmod.Wrapf(slashingtypes.ErrBadValidatorAddr, "unknown error looking for provider consensus address: %s", providerAddr.String())
	}

	if validator.IsUnbonded() {
		return fmt.Errorf("validator is unbonded. provider consensus address: %s", providerAddr.String())
	}

	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		return errorsmod.Wrapf(slashingtypes.ErrValidatorTombstoned, "provider consensus address: %s", providerAddr.String())
	}

	// jail validator if not already
	if !validator.IsJailed() {
		err := k.stakingKeeper.Jail(ctx, providerAddr.ToSdkConsAddr())
		if err != nil {
			return err
		}
	}

	jailEndTime := ctx.BlockTime().Add(jailingParams.JailDuration)
	err = k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), jailEndTime)
	if err != nil {
		return fmt.Errorf("fail to set jail duration for validator: %s: %s", providerAddr.String(), err)
	}

	if jailingParams.Tombstone {
		// Tombstone the validator so that we cannot slash the validator more than once
		// Note that we cannot simply use the fact that a validator is jailed to avoid slashing more than once
		// because then a validator could i) perform an equivocation, ii) get jailed (e.g., through downtime)
		// and in such a case the validator would not get slashed when we call `SlashValidator`.
		if err = k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr()); err != nil {
			return fmt.Errorf("fail to tombstone validator: %s: %s", providerAddr.String(), err)
		}
	}

	return nil
}

// ComputePowerToSlash computes the power to be slashed based on the tokens in non-matured `undelegations` and
// `redelegations`, as well as the current `power` of the validator.
// Note that this method does not perform any slashing.
func (k Keeper) ComputePowerToSlash(ctx sdk.Context, validator stakingtypes.Validator, undelegations []stakingtypes.UnbondingDelegation,
	redelegations []stakingtypes.Redelegation, power int64, powerReduction math.Int,
) int64 {
	// compute the total numbers of tokens currently being undelegated
	undelegationsInTokens := math.NewInt(0)

	// Note that we use a **cached** context to avoid any actual slashing of undelegations or redelegations.
	cachedCtx, _ := ctx.CacheContext()
	for _, u := range undelegations {
		// v50: errors are ignored
		amountSlashed, _ := k.stakingKeeper.SlashUnbondingDelegation(cachedCtx, u, 0, math.LegacyNewDec(1))
		undelegationsInTokens = undelegationsInTokens.Add(amountSlashed)
	}

	// compute the total numbers of tokens currently being redelegated
	redelegationsInTokens := math.NewInt(0)
	for _, r := range redelegations {
		// v50 errors are ignored
		amountSlashed, _ := k.stakingKeeper.SlashRedelegation(cachedCtx, validator, r, 0, math.LegacyNewDec(1))
		redelegationsInTokens = redelegationsInTokens.Add(amountSlashed)
	}

	// The power we pass to staking's keeper `Slash` method is the current power of the validator together with the total
	// power of all the currently undelegated and redelegated tokens (see docs/docs/adrs/adr-013-equivocation-slashing.md).
	undelegationsAndRedelegationsInPower := sdk.TokensToConsensusPower(
		undelegationsInTokens.Add(redelegationsInTokens), powerReduction)

	return power + undelegationsAndRedelegationsInPower
}

// SlashValidator slashes validator with given provider Address
func (k Keeper) SlashValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress, slashingParams *types.SlashJailParameters) error {
	validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if err != nil && errors.Is(err, stakingtypes.ErrNoValidatorFound) {
		return errorsmod.Wrapf(slashingtypes.ErrNoValidatorForAddress, "provider consensus address: %s", providerAddr.String())
	} else if err != nil {
		return errorsmod.Wrapf(slashingtypes.ErrBadValidatorAddr, "unknown error looking for provider consensus address: %s", providerAddr.String())
	}

	if validator.IsUnbonded() {
		return fmt.Errorf("validator is unbonded. provider consensus address: %s", providerAddr.String())
	}

	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		return fmt.Errorf("validator is tombstoned. provider consensus address: %s", providerAddr.String())
	}

	valAddr, err := k.ValidatorAddressCodec().StringToBytes(validator.GetOperator())
	if err != nil {
		return err
	}

	undelegations, err := k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, valAddr)
	if err != nil {
		return err
	}
	redelegations, err := k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, valAddr)
	if err != nil {
		return err
	}
	lastPower, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
	if err != nil {
		return err
	}

	powerReduction := k.stakingKeeper.PowerReduction(ctx)
	totalPower := k.ComputePowerToSlash(ctx, validator, undelegations, redelegations, lastPower, powerReduction)

	consAdrr, err := validator.GetConsAddr()
	if err != nil {
		return err
	}

	_, err = k.stakingKeeper.SlashWithInfractionReason(ctx, consAdrr, 0, totalPower, slashingParams.SlashFraction, stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN)
	return err
}

//
// CRUD section
//

// SetEquivocationEvidenceMinHeight sets the minimum height
// of a valid consumer equivocation evidence for a given consumer id
func (k Keeper) SetEquivocationEvidenceMinHeight(ctx sdk.Context, consumerId string, height uint64) {
	store := ctx.KVStore(k.storeKey)
	heightBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(heightBytes, height)

	store.Set(types.EquivocationEvidenceMinHeightKey(consumerId), heightBytes)
}

// GetEquivocationEvidenceMinHeight returns the minimum height
// of a valid consumer equivocation evidence for a given consumer id
func (k Keeper) GetEquivocationEvidenceMinHeight(ctx sdk.Context, consumerId string) uint64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.EquivocationEvidenceMinHeightKey(consumerId))
	if bz == nil {
		return 0
	}

	return binary.BigEndian.Uint64(bz)
}

// DeleteEquivocationEvidenceMinHeight deletes the minimum height
// of a valid consumer equivocation evidence for a given consumer id
func (k Keeper) DeleteEquivocationEvidenceMinHeight(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.EquivocationEvidenceMinHeightKey(consumerId))
}
