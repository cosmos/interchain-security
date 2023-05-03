package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmev "github.com/tendermint/tendermint/evidence"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (k Keeper) HandleConsumerDoubleVoting(ctx sdk.Context, evidence *tmproto.DuplicateVoteEvidence, header *ibctmtypes.Header) error {

	// TODO check header against consumer chain client

	ev, err := tmtypes.DuplicateVoteEvidenceFromProto(evidence)
	if err != nil {
		return err
	}
	valset, err := tmtypes.ValidatorSetFromProto(header.TrustedValidators)
	if err != nil {
		return err
	}

	// TODO: figure out if the evidence age must also be checked
	if err := tmev.VerifyDuplicateVote(ev, header.Header.ChainID, valset); err != nil {
		return err
	}

	// TODO convert misbehaving validator consumer pubkey
	//TODO call k.evidenceKeeper.HandleEquivocationEvidence() using correct infraction height

	logger := ctx.Logger()
	logger.Info(
		"confirmed equivocation",
		"byzantine validator", sdk.ConsAddress(evidence.VoteA.GetValidatorAddress()),
	)

	return nil
}
