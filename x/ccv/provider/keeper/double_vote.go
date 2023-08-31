package keeper

import (
	"bytes"
	"fmt"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// HandleConsumerDoubleVoting verifies a double voting evidence for a given a consumer chain and,
// if successful, executes the jailing of the malicious validator.
func (k Keeper) HandleConsumerDoubleVoting(ctx sdk.Context, evidence *tmtypes.DuplicateVoteEvidence, chainID string) error {

	k.Logger(ctx).Info("received double voting evidence", "chain: ", chainID, "evidence: ", evidence, "current block heigt",
		ctx.BlockHeight())

	// get the validator's consensus address on the provider
	providerAddr := k.GetProviderAddrFromConsumerAddr(
		ctx,
		chainID,
		types.NewConsumerConsAddress(sdk.ConsAddress(evidence.VoteA.ValidatorAddress.Bytes())),
	)

	// get the consumer chain public key assigned to the validator
	pubkey, err := k.getValidatorConsumerPubKey(ctx, chainID, providerAddr)
	if err != nil {
		// val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
		// if !ok {
		// 	return fmt.Errorf("cannot find validator %s", providerAddr.String())
		// }
		// pk, err := val.ConsPubKey()
		// if err != nil {
		// 	return fmt.Errorf("cannot find public key for validator %s", &providerAddr)
		// }

		// pubkey, err = cryptocodec.ToTmProtoPublicKey(pk)
		// if err != nil {
		// 	return fmt.Errorf("cannot convert public key for validator %s", &providerAddr)
		// }
		return fmt.Errorf("cannot find public key for validator %s and consumer chain %s", providerAddr.String(), chainID)
	}

	// verifies the double voting evidence using the consumer chain public key
	if err := k.VerifyDoubleVotingEvidence(ctx, *evidence, chainID, pubkey); err != nil {
		return err
	}

	// execute the jailing
	k.JailValidator(ctx, providerAddr)

	k.Logger(ctx).Info(
		"confirmed equivocation",
		"byzantine validator address", providerAddr,
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
	// Note that since we're only jailing validators for double voting on a consumer chain,
	// the age of the evidence is irrelevant and therefore isn't checked.

	// TODO: check the age of the evidence once we slash
	// validators for double voting on a consumer chain

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

// getValidatorConsumerPubKey returns the public key used by the given validator
// on a consumer chain
func (k Keeper) getValidatorConsumerPubKey(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) (pubkey cryptotypes.PubKey, err error) {
	// get the consumer chain public key assigned to the validator
	tmPK, ok := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	if ok {
		pubkey, err = cryptocodec.FromTmProtoPublicKey(tmPK)
		if err != nil {
			return
		}
	} else {
		val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
		if !ok {
			err = fmt.Errorf("cannot find validator %s", providerAddr.String())
			return
		}
		pubkey, err = val.ConsPubKey()
		if err != nil {
			return
		}
	}

	return
}
