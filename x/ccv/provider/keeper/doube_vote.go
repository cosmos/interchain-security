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
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// header infraction heaader
func (k Keeper) HandleConsumerDoubleVoting(ctx sdk.Context, evidence *tmproto.DuplicateVoteEvidence, h *ibctmtypes.Header) error {
	h.Header.ChainID
	// TODO: check header against consumer chain client states

	// ev, err := tmtypes.DuplicateVoteEvidenceFromProto(evidence)
	// if err != nil {
	// 	return err
	// }

	// TODO: figure out if the evidence age must be checked
	// if err := tmev.VerifyDuplicateVote(ev, header.Header.ChainID, valset); err != nil {
	// 	return err
	// }

	// CONVERT CONSUMER ADDRESS TO PROVIDER ADDRESS

	// consuAddress := sdk.ConsAddress(evidence.VoteA.GetValidatorAddress())
	// chainID := header.Header.ChainID

	// k.JailConsumerValidator(ctx, chainID, consuAddress)

	// provAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consuAddress)

	// logger := ctx.Logger()
	// logger.Info(
	// 	"confirmed equivocation",
	// 	"byzantine validator address", provAddr,
	// )

	return nil
}

func (k Keeper) HandleConsensusEquivocation(ctx sdk.Context, evidence tmtypes.DuplicateVoteEvidence, chainID string) error {
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
			height,
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

	// convert consumer validator address to provider adddress
	consumerAddr := types.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress.Bytes()))
	providerAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerAddr)
	val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())

	logger := k.Logger(ctx)

	if !ok || val.IsUnbonded() {
		logger.Error("validator not found or is unbonded", providerAddr.String())
		return nil
	}

	pubkey, err := val.ConsPubKey()

	va := evidence.VoteA.ToProto()
	vb := evidence.VoteB.ToProto()
	// Signatures must be valid
	// RELAYER SEND EVIDENCE + CHAINID
	if !pubKey.VerifySignature(tmtypes.VoteSignBytes(chainID, va), evidence.VoteA.Signature) {
		return fmt.Errorf("verifying VoteA: %w", tmtypes.ErrVoteInvalidSignature)
	}
	if !pubKey.VerifySignature(tmtypes.VoteSignBytes(chainID, vb), evidence.VoteB.Signature) {
		return fmt.Errorf("verifying VoteB: %w", tmtypes.ErrVoteInvalidSignature)
	}

	return nil
}
