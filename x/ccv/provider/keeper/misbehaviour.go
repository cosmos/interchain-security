package keeper

import (
	"fmt"
	"time"

	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	ibcclienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	"github.com/cosmos/ibc-go/v4/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// HandleConsumerMisbehaviour checks whether the given IBC misbehaviour is valid and, if they are, the misbehaving
// CheckConsumerMisbehaviour check that the given IBC misbehaviour headers forms a valid light client attack evidence.
// proceed to the jailing and tombstoning of the bzyantine validators.
func (k Keeper) HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour exported.Misbehaviour) error {
	logger := ctx.Logger()

	// Check that the validity of the misbehaviour
	if err := k.clientKeeper.CheckMisbehaviourAndUpdateState(ctx, misbehaviour); err != nil {
		logger.Info("Misbehaviour rejected", err.Error())
		return err
	}

	// Assign the Tendermint client misbehaviour concrete type
	tmMisbehaviour := misbehaviour.(*ibctmtypes.Misbehaviour)

	// Since the misbehaviour packet was received within the trusting period
	// w.r.t to the last trusted consensus it entails that the infraction age
	// isn't too old. see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go

	// construct a light client attack evidence
	evidence, err := k.ConstructLightClientEvidence(ctx, *tmMisbehaviour)
	if err != nil {
		return err
	}

	logger.Info("ConstructLightClientEvidence", fmt.Sprintf("%#+v\n", evidence))

	// jail and tombstone the byzantine validators
	for _, v := range evidence.ByzantineValidators {
		// convert consumer consensus address
		consuAddr := sdk.ConsAddress(v.Address.Bytes())
		provAddr := k.GetProviderAddrFromConsumerAddr(ctx, tmMisbehaviour.Header1.Header.ChainID, types.NewConsumerConsAddress(consuAddr))
		k.stakingKeeper.ValidatorByConsAddr(ctx, consuAddr)
		val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, provAddr.Address)

		if !ok || val.IsUnbonded() {
			logger.Error("validator not found or is unbonded", provAddr.String())
			continue
		}

		// jail validator if not already
		if !val.IsJailed() {
			k.stakingKeeper.Jail(ctx, provAddr.Address)
		}

		// tombstone validator if not already
		if !k.slashingKeeper.IsTombstoned(ctx, provAddr.Address) {
			k.slashingKeeper.Tombstone(ctx, provAddr.Address)
		}

		// update jail time to end after double sign jail duration
		k.slashingKeeper.JailUntil(ctx, provAddr.Address, evidencetypes.DoubleSignJailEndTime)
	}

	logger.Info(
		"confirmed equivocation",
		"byzantine validators", evidence.ByzantineValidators,
	)

	return nil
}

// CheckMisbehaviourAndUpdateState checks for client misbehaviour and freeze the client if it's still active.
// Note that this method changes the original CheckMisbehaviourAndUpdateState method in ibc-go ibc-go/modules/core/02-client/keeper/client.go
func (k Keeper) CheckMisbehaviourAndUpdateState(ctx sdk.Context, misbehaviour exported.Misbehaviour) error {
	if err := misbehaviour.ValidateBasic(); err != nil {
		return err
	}

	// get client state
	clientState, found := k.clientKeeper.GetClientState(ctx, misbehaviour.GetClientID())
	if !found {
		return sdkerrors.Wrapf(ibcclienttypes.ErrClientNotFound, "cannot check misbehaviour for client with ID %s", misbehaviour.GetClientID())
	}

	clientStore := k.clientKeeper.ClientStore(ctx, misbehaviour.GetClientID())

	// check the IBC misbehaviour
	_, err := clientState.CheckMisbehaviourAndUpdateState(ctx, k.cdc, clientStore, misbehaviour)
	if err != nil {
		return err
	}

	// Check that the client's status isn't Expired
	consState, err := ibctmtypes.GetConsensusState(clientStore, k.cdc, clientState.GetLatestHeight())
	if err != nil {
		return err
	}

	if !clientState.(*ibctmtypes.ClientState).IsExpired(consState.Timestamp, ctx.BlockTime()) {
		k.Logger(ctx).Info("client frozen due to a consumer chain misbehaviour", "client-id", misbehaviour.GetClientID())
	}

	return nil
}

// ConstructLightClientEvidence constructs and returns a CometBFT Ligth Client Attack(LCA) evidence struct
// from the given misbehaviour
func (k Keeper) ConstructLightClientEvidence(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) (*tmtypes.LightClientAttackEvidence, error) {
	// construct the trusted and conflicetd ligth blocks
	trusted, err := headerToLightBlock(*misbehaviour.Header1)
	if err != nil {
		return nil, err
	}
	conflicted, err := headerToLightBlock(*misbehaviour.Header2)
	if err != nil {
		return nil, err
	}

	// get common header using the IBC misbehaviour
	commonHeight, commonTs, commonValset, err := k.GetTrustedInfoFromMisbehaviour(ctx, misbehaviour)
	if err != nil {
		return nil, err
	}

	// construct the LCA evidence by copying the CometBFT constructor
	// see newLightClientAttackEvidence() in tendermint/light/detector.go
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

	ev.ByzantineValidators = ev.GetByzantineValidators(commonValset, trusted.SignedHeader)

	return &ev, nil
}

// GetCommonFromMisbehaviour checks whether the given ibc misbehaviour's headers share common trusted height
// and that a consensus state exists for this height. In this case, it returns the associated trusted height, timestamp and valset.
func (k Keeper) GetTrustedInfoFromMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) (int64, time.Time, *tmtypes.ValidatorSet, error) {
	// a common trusted height is required
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

// headerToLightBlock returns a CometBFT ligth block from the given IBC header
func headerToLightBlock(h ibctmtypes.Header) (*tmtypes.LightBlock, error) {
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
