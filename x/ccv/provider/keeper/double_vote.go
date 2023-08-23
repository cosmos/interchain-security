package keeper

import (
	"bytes"
	"fmt"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
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

	providerAddr := k.GetProviderAddrFromConsumerAddr(
		ctx,
		chainID,
		types.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress.Bytes())),
	)

	if err := k.VerifyDoubleVoting(ctx, *evidence, chainID, providerAddr); err != nil {
		return err
	}

	k.JailAndTombstoneValidator(ctx, providerAddr, chainID)

	k.Logger(ctx).Info(
		"confirmed equivocation",
		"byzantine validator address", providerAddr,
	)

	return nil
}

// VerifyEquivocation verifies the equivocation for the given chain id and
// provider consensus address
func (k Keeper) VerifyDoubleVoting(
	ctx sdk.Context,
	evidence tmtypes.DuplicateVoteEvidence,
	chainID string,
	providerAddr types.ProviderConsAddress,
) error {

	// TODO: check the evidence age once we agreed on the infraction height mapping

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

	// get the consumer chain public key assigned to the validator
	tmpk, ok := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	if !ok {
		return fmt.Errorf("cannot find public key for validator %s and consumer chain %s", providerAddr.String(), chainID)
	}

	pubkey, err := cryptocodec.FromTmProtoPublicKey(tmpk)
	if err != nil {
		return err
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
