package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/ibc-go/v4/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
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
