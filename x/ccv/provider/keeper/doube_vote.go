package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

// header infraction heaader
func (k Keeper) HandleConsumerDoubleVoting(ctx sdk.Context, evidence *tmproto.DuplicateVoteEvidence, _ *ibctmtypes.Header) error {
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
