package keeper

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/ibc-go/v4/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (k Keeper) CheckConsumerMisbehaviour(ctx sdk.Context, misbeaviour ibctmtypes.Misbehaviour) error {
	clientID := misbeaviour.GetClientID()
	clientState, found := k.clientKeeper.GetClientState(ctx, clientID)
	if !found {
		return fmt.Errorf("types.ErrClientNotFound cannot check misbehaviour for client with ID %s", clientID)
	}

	clientStore := k.clientKeeper.ClientStore(ctx, misbeaviour.GetClientID())

	if status := clientState.Status(ctx, clientStore, k.cdc); status != exported.Active {
		return fmt.Errorf("types.ErrClientNotActive cannot process misbehaviour for client (%s) with status %s", clientID, status)
	}

	if err := misbeaviour.ValidateBasic(); err != nil {
		return err
	}

	clientState, err := clientState.CheckMisbehaviourAndUpdateState(ctx, k.cdc, clientStore, &misbeaviour)
	if err != nil {
		return err
	}

	k.clientKeeper.SetClientState(ctx, clientID, clientState)
	k.Logger(ctx).Info("client frozen due to misbehaviour", "client-id", clientID)

	// get byzantine validators
	sh, err := tmtypes.SignedHeaderFromProto(misbeaviour.Header1.SignedHeader)
	if err != nil {
		return err
	}

	vs, err := tmtypes.ValidatorSetFromProto(misbeaviour.Header1.ValidatorSet)
	if err != nil {
		return err
	}
	ev := tmtypes.LightClientAttackEvidence{
		ConflictingBlock: &tmtypes.LightBlock{SignedHeader: sh, ValidatorSet: vs},
	}

	h2, err := tmtypes.HeaderFromProto(misbeaviour.Header2.Header)
	if err != nil {
		return err
	}

	// WIP: return byzantine validators according to the light client committed

	// if this is an equivocation or amnesia attack, i.e. the validator sets are the same, then we
	// return the height of the conflicting block else if it is a lunatic attack and the validator sets
	// are not the same then we send the height of the common header.
	if ev.ConflictingHeaderIsInvalid(&h2) {
		ev.CommonHeight = misbeaviour.Header2.Header.Height
		ev.Timestamp = misbeaviour.Header2.Header.Time
		ev.TotalVotingPower = misbeaviour.Header2.ValidatorSet.TotalVotingPower
	} else {
		ev.CommonHeight = misbeaviour.Header1.Header.Height
		ev.Timestamp = misbeaviour.Header1.Header.Time
		ev.TotalVotingPower = misbeaviour.Header1.ValidatorSet.TotalVotingPower
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

func (k Keeper) GetByzantineValidators(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) ([]*tmtypes.Validator, error) {
	trusted, err := HeaderToLightBlock(*misbehaviour.Header1)
	if err != nil {
		return nil, err
	}
	conflicted, err := HeaderToLightBlock(*misbehaviour.Header2)
	if err != nil {
		return nil, err
	}
	commonHeight, commonTs, commonValset, err := k.GetCommonFromMisbehaviour(ctx, misbehaviour)
	if err != nil {
		return nil, err
	}

	ev := tmtypes.LightClientAttackEvidence{
		ConflictingBlock: conflicted,
	}

	if ev.ConflictingHeaderIsInvalid(trusted.Header) {
		ev.CommonHeight = commonHeight
		ev.Timestamp = commonTs
		ev.TotalVotingPower = commonValset.TotalVotingPower()
	} else {
		ev.CommonHeight = trusted.Header.Height
		ev.Timestamp = trusted.Header.Time
		ev.TotalVotingPower = trusted.ValidatorSet.TotalVotingPower()
	}

	return ev.GetByzantineValidators(commonValset, trusted.SignedHeader), nil
}

func (k Keeper) GetCommonFromMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) (int64, time.Time, *tmtypes.ValidatorSet, error) {
	// A common trusted height is required
	commonHeight := misbehaviour.Header1.TrustedHeight
	if !commonHeight.EQ(misbehaviour.Header2.TrustedHeight) {
		return 0, time.Time{}, nil, fmt.Errorf("misbehaviour headers have different trusted height: %v , %v", commonHeight, misbehaviour.Header2.TrustedHeight)
	}

	cs, ok := k.clientKeeper.GetClientConsensusState(ctx, misbehaviour.GetClientID(), misbehaviour.Header1.TrustedHeight)
	if !ok {
		return 0, time.Time{}, nil, fmt.Errorf("cannot find consensus state at trusted height %d for client %s", commonHeight, misbehaviour.GetClientID())
	}

	vs, err := tmtypes.ValidatorSetFromProto(misbehaviour.Header1.ValidatorSet)
	if err != nil {
		return 0, time.Time{}, nil, err
	}

	return int64(commonHeight.RevisionHeight), time.Unix(0, int64(cs.GetTimestamp())), vs, nil
}

func HeaderToLightBlock(h ibctmtypes.Header) (*tmtypes.LightBlock, error) {
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
