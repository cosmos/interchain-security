package keeper

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	"github.com/cosmos/ibc-go/v4/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (k Keeper) HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	if err := k.CheckConsumerMisbehaviour(ctx, misbehaviour); err != nil {
		return err
	}

	byzantineValidators, err := k.GetByzantineValidators(ctx, misbehaviour)
	if err != nil {
		return err
	}

	// Since the misbehaviour packet was received within the trusting period
	// w.r.t to the last trusted consensus it entails that the infraction age
	// isn't too old. see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go
	for _, v := range byzantineValidators {
		k.JailConsumerValidator(ctx, misbehaviour.Header1.Header.ChainID, sdk.ConsAddress(v.Address.Bytes()))
		// store misbehaviour?
	}

	logger := ctx.Logger()
	logger.Info(
		"confirmed equivocation",
		"byzantine validators", byzantineValidators,
	)

	return nil
}

func (k Keeper) CheckConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {

	clientID := misbehaviour.GetClientID()

	clientState, found := k.clientKeeper.GetClientState(ctx, clientID)
	if !found {
		return fmt.Errorf("types.ErrClientNotFound cannot check misbehaviour for client with ID %s", clientID)
	}

	clientStore := k.clientKeeper.ClientStore(ctx, misbehaviour.GetClientID())

	if status := clientState.Status(ctx, clientStore, k.cdc); status != exported.Active {
		return fmt.Errorf("types.ErrClientNotActive cannot process misbehaviour for client (%s) with status %s", clientID, status)
	}

	if err := misbehaviour.ValidateBasic(); err != nil {
		return err
	}

	trusted, conflicted := misbehaviour.Header1, misbehaviour.Header2

	// A common trusted height is required to get the byzantine validators who signed both headers
	if !trusted.TrustedHeight.EQ(conflicted.TrustedHeight) {
		return fmt.Errorf("misbehaviour headers have different trusted height %d != %d", trusted.TrustedHeight, conflicted.TrustedHeight)
	}

	clientState, err := clientState.CheckMisbehaviourAndUpdateState(ctx, k.cdc, clientStore, &misbehaviour)
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
		ev.CommonHeight = int64(commonHeight)
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

// TODO: return bool and move logger to calling func
func (k Keeper) JailConsumerValidator(ctx sdk.Context, chainID string, consumerAddress sdk.ConsAddress) {
	// convert address to key assigned
	providerAddress := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerAddress)
	k.stakingKeeper.ValidatorByConsAddr(ctx, consumerAddress)
	val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddress)
	if !ok || val.IsUnbonded() {
		// Defensive: Simulation doesn't take unbonding periods into account, and
		// Tendermint might break this assumption at some point.
		k.Logger(ctx).Error("validator not found or is unbonded", providerAddress.String())
		return
	}
	// TODO: continue if validator is already tombstoned/jailed + log
	k.stakingKeeper.Jail(ctx, providerAddress)
	k.slashingKeeper.JailUntil(ctx, providerAddress, evidencetypes.DoubleSignJailEndTime)
	k.slashingKeeper.Tombstone(ctx, providerAddress)
}
