package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/ibc-go/v4/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (k Keeper) CheckConsumerMisbehaviour(ctx sdk.Context, msg types.MsgSubmitConsumerMisbehaviour) error {

	clientID := msg.Misbehaviour.GetClientID()
	clientState, found := k.clientKeeper.GetClientState(ctx, clientID)
	if !found {
		return fmt.Errorf("types.ErrClientNotFound cannot check misbehaviour for client with ID %s", clientID)
	}

	clientStore := k.clientKeeper.ClientStore(ctx, msg.Misbehaviour.GetClientID())

	if status := clientState.Status(ctx, clientStore, k.cdc); status != exported.Active {
		return fmt.Errorf("types.ErrClientNotActive cannot process misbehaviour for client (%s) with status %s", clientID, status)
	}

	if err := msg.Misbehaviour.ValidateBasic(); err != nil {
		return err
	}

	clientState, err := clientState.CheckMisbehaviourAndUpdateState(ctx, k.cdc, clientStore, msg.Misbehaviour)
	if err != nil {
		return err
	}

	k.clientKeeper.SetClientState(ctx, clientID, clientState)
	k.Logger(ctx).Info("client frozen due to misbehaviour", "client-id", clientID)

	// get byzantine validators
	sh, err := tmtypes.SignedHeaderFromProto(msg.Misbehaviour.Header1.SignedHeader)
	if err != nil {
		return err
	}

	vs, err := tmtypes.ValidatorSetFromProto(msg.Misbehaviour.Header1.ValidatorSet)
	if err != nil {
		return err
	}
	ev := tmtypes.LightClientAttackEvidence{
		ConflictingBlock: &tmtypes.LightBlock{SignedHeader: sh, ValidatorSet: vs},
	}

	h2, err := tmtypes.HeaderFromProto(msg.Misbehaviour.Header2.Header)
	if err != nil {
		return err
	}

	// WIP: return byzantine validators according to the light client commited

	// if this is an equivocation or amnesia attack, i.e. the validator sets are the same, then we
	// return the height of the conflicting block else if it is a lunatic attack and the validator sets
	// are not the same then we send the height of the common header.
	if ev.ConflictingHeaderIsInvalid(&h2) {
		ev.CommonHeight = msg.Misbehaviour.Header2.Header.Height
		ev.Timestamp = msg.Misbehaviour.Header2.Header.Time
		ev.TotalVotingPower = msg.Misbehaviour.Header2.ValidatorSet.TotalVotingPower
	} else {
		ev.CommonHeight = msg.Misbehaviour.Header1.Header.Height
		ev.Timestamp = msg.Misbehaviour.Header1.Header.Time
		ev.TotalVotingPower = msg.Misbehaviour.Header1.ValidatorSet.TotalVotingPower
	}
	ev.ByzantineValidators = ev.GetByzantineValidators(vs, sh)

	logger := ctx.Logger()

	logger.Info(
		"confirmed equivocation",
		"byzantine validators", ev.ByzantineValidators,
	)

	// TBD
	// defer func() {
	// 	telemetry.IncrCounterWithLabels(
	// 		[]string{"ibc", "client", "misbehaviour"},
	// 		1,
	// 		[]metrics.Label{
	// 			telemetry.NewLabel(types.LabelClientType, misbehaviour.ClientType()),
	// 			telemetry.NewLabel(types.LabelClientID, misbehaviour.GetClientID()),
	// 		},
	// 	)
	// }()

	// EmitSubmitMisbehaviourEvent(ctx, clientID, clientState)

	return nil
}
