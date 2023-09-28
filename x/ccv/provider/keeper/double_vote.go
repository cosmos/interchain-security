package keeper

import (
	"bytes"
	"fmt"

	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"

	tmtypes "github.com/cometbft/cometbft/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// HandleConsumerDoubleVoting verifies a double voting evidence for a given a consumer chain ID
// and a public key and, if successful, executes the jailing of the malicious validator.
func (k Keeper) HandleConsumerDoubleVoting(
	ctx sdk.Context,
	evidence *tmtypes.DuplicateVoteEvidence,
	chainID string,
	pubkey cryptotypes.PubKey,
) error {
	// verifies the double voting evidence using the consumer chain public key
	if err := k.VerifyDoubleVotingEvidence(ctx, *evidence, chainID, pubkey); err != nil {
		return err
	}

	// get the validator's consensus address on the provider
	providerAddr := k.GetProviderAddrFromConsumerAddr(
		ctx,
		chainID,
		types.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress.Bytes())),
	)

	// execute the jailing
	k.JailValidator(ctx, providerAddr)

	k.Logger(ctx).Info(
		"confirmed equivocation",
		"byzantine validator address", providerAddr.String(),
	)

	return nil
}

// VerifyDoubleVotingEvidence verifies a double voting evidence
// for a given chain id and a validator public key
func (k Keeper) VerifyDoubleVotingEvidence(
	ctx sdk.Context,
	evidence tmtypes.DuplicateVoteEvidence,
	chainID string,
	pubkey cryptotypes.PubKey,
) error {
	if pubkey == nil {
		return fmt.Errorf("validator public key cannot be empty")
	}

	// Note that since we're only jailing validators for double voting on a consumer chain,
	// the age of the evidence is irrelevant and therefore isn't checked.

	// H/R/S must be the same
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
