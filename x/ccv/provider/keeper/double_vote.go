package keeper

import (
	"bytes"
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// HandleConsumerDoubleVoting verifies a double voting evidence for a given a consumer chain and,
// if successful, executes the the jailing and the tombstoning of the malicious validator
func (k Keeper) HandleConsumerDoubleVoting(ctx sdk.Context, evidence *tmtypes.DuplicateVoteEvidence, h *ibctmtypes.Header) error {
	chainID := h.Header.ChainID

	if err := k.VerifyDoubleVoting(ctx, *evidence, chainID); err != nil {
		return err
	}

	// TODO optimize this to convert consumer address only once
	// but also remember that the jailing method is called in misbehaviour also
	consuAddress := types.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress))

	// catch errors
	if err := k.JailAndTombstoneByConsumerAddress(ctx, consuAddress, chainID); err != nil {
		return err
	}
	provAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consuAddress)

	logger := ctx.Logger()
	logger.Info(
		"confirmed equivocation",
		"byzantine validator address", provAddr,
	)

	return nil
}

// VerifyEquivocation verifies the equivocation for the given chain id
func (k Keeper) VerifyDoubleVoting(ctx sdk.Context, evidence tmtypes.DuplicateVoteEvidence, chainID string) error {
	// default evidence params in CometBFT see https://github.com/cometbft/cometbft/blob/main/types/params.go#L107
	MAX_AGE_NUM_BLOCKS := int64(1000000)
	MAX_AGE_DURATION := 48 * time.Hour

	height := ctx.BlockHeight()
	blockTime := ctx.BlockTime()
	ageNumBlocks := height - evidence.Height()

	// check that the evidence hasn't expired
	if ageNumBlocks > MAX_AGE_NUM_BLOCKS {
		return sdkerrors.Wrapf(
			ccvtypes.ErrInvalidEvidence,
			"evidence from height %d (created at: %v) is too old; min height is %d and evidence can not be older than %v",
			evidence.Height(),
			evidence.Time(),
			height-MAX_AGE_NUM_BLOCKS,
			blockTime.Add(MAX_AGE_DURATION),
		)
	}

	// H/R/S must be the same
	if evidence.VoteA.Height != evidence.VoteB.Height ||
		evidence.VoteA.Round != evidence.VoteB.Round ||
		evidence.VoteA.Type != evidence.VoteB.Type {
		return sdkerrors.Wrapf(
			ccvtypes.ErrInvalidEvidence,
			"h/r/s does not match: %d/%d/%v vs %d/%d/%v",
			evidence.VoteA.Height, evidence.VoteA.Round, evidence.VoteA.Type,
			evidence.VoteB.Height, evidence.VoteB.Round, evidence.VoteB.Type)
	}

	// Address must be the same
	if !bytes.Equal(evidence.VoteA.ValidatorAddress, evidence.VoteB.ValidatorAddress) {
		return sdkerrors.Wrapf(
			ccvtypes.ErrInvalidEvidence,
			"validator addresses do not match: %X vs %X",
			evidence.VoteA.ValidatorAddress,
			evidence.VoteB.ValidatorAddress,
		)
	}

	// BlockIDs must be different
	if evidence.VoteA.BlockID.Equals(evidence.VoteB.BlockID) {
		return sdkerrors.Wrapf(
			ccvtypes.ErrInvalidEvidence,
			"block IDs are the same (%v) - not a real duplicate vote",
			evidence.VoteA.BlockID,
		)
	}

	logger := k.Logger(ctx)

	// convert consumer validator address to provider adddress
	consumerAddr := types.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress.Bytes()))
	providerAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerAddr)
	val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())

	// why aren't we returning an error here ?
	if !ok || val.IsUnbonded() {
		logger.Error("validator not found or is unbonded", providerAddr.String())
		return nil
	}

	// use the validator consumer validator pubkeys to verify the signatures
	pubkey, err := val.ConsPubKey()
	if err != nil {
		logger.Error(err.Error()) // why aren't we returning an error here ? RETURN ERRORS
		return nil
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
