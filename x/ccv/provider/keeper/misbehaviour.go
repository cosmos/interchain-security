package keeper

import (
	"bytes"
	"sort"

	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	ibcclienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// HandleConsumerMisbehaviour checks if the given IBC misbehaviour corresponds to an equivocation light client attack,
// and in this case, jails and tombstones the Byzantine validators
func (k Keeper) HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	logger := k.Logger(ctx)

	// Check that the misbehaviour is valid and that the client isn't expired
	if err := k.CheckMisbehaviour(ctx, misbehaviour); err != nil {
		logger.Info("Misbehaviour rejected", err.Error())

		return err
	}

	// Since the misbehaviour packet was received within the trusting period
	// w.r.t to the last trusted consensus it entails that the infraction age
	// isn't too old. see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go

	// Get Byzantine validators from the conflicting headers
	// Note that it returns an error if the misbehaviour doesn't correspond to an equivocation
	byzantineValidators, err := k.GetByzantineValidators(ctx, misbehaviour)
	if err != nil {
		return err
	}

	// jail and tombstone the Byzantine validators
	for _, v := range byzantineValidators {
		// convert consumer consensus address
		consuAddr := sdk.ConsAddress(v.Address.Bytes())
		provAddr := k.GetProviderAddrFromConsumerAddr(ctx, misbehaviour.Header1.Header.ChainID, types.NewConsumerConsAddress(consuAddr))
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
		"byzantine validators", byzantineValidators,
	)

	return nil
}

// GetByzantineValidators returns the Byzantine validators from a given misbehaviour
// with the condition that it corresponds to an equivocation light client attack
func (k Keeper) GetByzantineValidators(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) ([]*tmtypes.Validator, error) {
	// construct the trusted and conflicted light blocks
	header1, err := headerToLightBlock(*misbehaviour.Header1)
	if err != nil {
		return nil, err
	}
	header2, err := headerToLightBlock(*misbehaviour.Header2)
	if err != nil {
		return nil, err
	}

	var validators []*tmtypes.Validator

	// compare the signatures of the headers
	// and return the intersection of validators who signed both

	// create a map with the validators' address that signed header1
	header1Signers := map[string]struct{}{}
	for _, sign := range header1.Commit.Signatures {
		if sign.Absent() {
			continue
		}
		header1Signers[sign.ValidatorAddress.String()] = struct{}{}
	}

	// iterate over the header2 signers
	// and check if they s signed header1
	for _, sign := range header2.Commit.Signatures {
		if sign.Absent() {
			continue
		}
		if _, ok := header1Signers[sign.ValidatorAddress.String()]; ok {
			_, val := header1.ValidatorSet.GetByAddress(sign.ValidatorAddress)
			validators = append(validators, val)
		}
	}

	sort.Sort(tmtypes.ValidatorsByVotingPower(validators))
	return validators, nil
}

// headerToLightBlock returns a CometBFT light block from the given IBC header
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

func headersStatesTransitionsAreEqual(header1, header2 *tmtypes.LightBlock) bool {
	return bytes.Equal(header1.ValidatorsHash, header2.ValidatorsHash) &&
		bytes.Equal(header1.NextValidatorsHash, header2.NextValidatorsHash) &&
		bytes.Equal(header1.ConsensusHash, header2.ConsensusHash) &&
		bytes.Equal(header1.AppHash, header2.AppHash) &&
		bytes.Equal(header1.LastResultsHash, header2.LastResultsHash)
}

// CheckMisbehaviourAndUpdateState checks that headers in the given misbehaviour forms
// a valid light client attack and that the corresponding light client isn't expired
func (k Keeper) CheckMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	if err := misbehaviour.ValidateBasic(); err != nil {
		return err
	}

	clientState, found := k.clientKeeper.GetClientState(ctx, misbehaviour.GetClientID())
	if !found {
		return sdkerrors.Wrapf(ibcclienttypes.ErrClientNotFound, "cannot check misbehaviour for client with ID %s", misbehaviour.GetClientID())
	}

	clientStore := k.clientKeeper.ClientStore(ctx, misbehaviour.GetClientID())

	// Check that the headers are at the same height to ensure that
	// the misbehaviour is for a light client attack and not a time violation,
	// see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go#L54
	if !misbehaviour.Header1.GetHeight().EQ(misbehaviour.Header2.GetHeight()) {
		return sdkerrors.Wrap(ibcclienttypes.ErrInvalidMisbehaviour, "headers are not at same height")
	}

	// CheckMisbehaviourAndUpdateState verifies the misbehaviour against the consensus states
	// but does NOT update the light client status.
	// Note CheckMisbehaviourAndUpdateState returns an error if the light client is expired
	_, err := clientState.CheckMisbehaviourAndUpdateState(ctx, k.cdc, clientStore, &misbehaviour)
	if err != nil {
		return err
	}

	return nil
}
