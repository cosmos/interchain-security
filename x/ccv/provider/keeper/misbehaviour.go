package keeper

import (
	"fmt"

	ibcclienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"

	tmtypes "github.com/cometbft/cometbft/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// HandleConsumerMisbehaviour checks if the given IBC misbehaviour corresponds to an equivocation light client attack,
// and in this case, slashes, jails, and tombstones
func (k Keeper) HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	logger := k.Logger(ctx)

	// Check that the misbehaviour is valid and that the client consensus states at trusted heights are within trusting period
	if err := k.CheckMisbehaviour(ctx, misbehaviour); err != nil {
		logger.Info("Misbehaviour rejected", err.Error())

		return err
	}

	// Since the misbehaviour packet was received within the trusting period
	// w.r.t to the trusted consensus states the infraction age
	// isn't too old. see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go

	// Get Byzantine validators from the conflicting headers
	byzantineValidators, err := k.GetByzantineValidators(ctx, misbehaviour)
	if err != nil {
		return err
	}

	provAddrs := make([]types.ProviderConsAddress, len(byzantineValidators))

	// slash, jail, and tombstone the Byzantine validators
	for _, v := range byzantineValidators {
		providerAddr := k.GetProviderAddrFromConsumerAddr(
			ctx,
			misbehaviour.Header1.Header.ChainID,
			types.NewConsumerConsAddress(sdk.ConsAddress(v.Address.Bytes())),
		)
		err := k.SlashValidator(ctx, providerAddr)
		if err != nil {
			logger.Error("failed to slash validator: %s", err)
			continue
		}
		err = k.JailAndTombstoneValidator(ctx, providerAddr)
		// JailAndTombstoneValidator should never return an error if
		// SlashValidator succeeded because both methods fail if the malicious
		// validator is either or both !found, unbonded and tombstoned.
		if err != nil {
			panic(err)
		}

		provAddrs = append(provAddrs, providerAddr)
	}

	// Return an error if no validators were punished
	if len(provAddrs) == 0 {
		return fmt.Errorf("failed to slash, jail, or tombstone all validators: %v", byzantineValidators)
	}

	logger.Info(
		"confirmed equivocation light client attack",
		"byzantine validators slashed, jailed and tombstoned", provAddrs,
	)

	return nil
}

// GetByzantineValidators returns the validators that signed both headers.
// If the misbehavior is an equivocation light client attack, then these
// validators are the Byzantine validators.
func (k Keeper) GetByzantineValidators(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) ([]*tmtypes.Validator, error) {
	// construct the trusted and conflicted light blocks
	lightBlock1, err := headerToLightBlock(*misbehaviour.Header1)
	if err != nil {
		return nil, err
	}
	lightBlock2, err := headerToLightBlock(*misbehaviour.Header2)
	if err != nil {
		return nil, err
	}

	var validators []*tmtypes.Validator

	// compare the signatures of the headers
	// and return the intersection of validators who signed both

	// create a map with the validators' address that signed header1
	header1Signers := map[string]struct{}{}
	for _, sign := range lightBlock1.Commit.Signatures {
		if sign.Absent() {
			continue
		}
		header1Signers[sign.ValidatorAddress.String()] = struct{}{}
	}

	// iterate over the header2 signers and check if they signed header1
	for _, sign := range lightBlock2.Commit.Signatures {
		if sign.Absent() {
			continue
		}
		if _, ok := header1Signers[sign.ValidatorAddress.String()]; ok {
			_, val := lightBlock1.ValidatorSet.GetByAddress(sign.ValidatorAddress)
			validators = append(validators, val)
		}
	}

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

// CheckMisbehaviour checks that headers in the given misbehaviour forms
// a valid light client attack and that the corresponding light client isn't expired
func (k Keeper) CheckMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	clientState, found := k.clientKeeper.GetClientState(ctx, misbehaviour.ClientId)
	if !found {
		return errorsmod.Wrapf(ibcclienttypes.ErrClientNotFound, "cannot check misbehaviour for client with ID %s", misbehaviour.ClientId)
	}

	clientStore := k.clientKeeper.ClientStore(ctx, misbehaviour.ClientId)

	// Check that the headers are at the same height to ensure that
	// the misbehaviour is for a light client attack and not a time violation,
	// see CheckForMisbehaviour in ibc-go/blob/v7.3.0/modules/light-clients/07-tendermint/misbehaviour_handle.go#L73
	if !misbehaviour.Header1.GetHeight().EQ(misbehaviour.Header2.GetHeight()) {
		return errorsmod.Wrap(ibcclienttypes.ErrInvalidMisbehaviour, "headers are not at same height")
	}

	// CheckMisbehaviour verifies that the headers have both he same block height and
	// different blockID hashes
	ok := clientState.CheckForMisbehaviour(ctx, k.cdc, clientStore, &misbehaviour)
	if !ok {
		return errorsmod.Wrapf(ibcclienttypes.ErrInvalidMisbehaviour, "invalid misbehaviour for client-id: %s", misbehaviour.ClientId)
	}

	// VerifyClientMessage calls verifyMisbehaviour which verifies that the headers in the misbehaviour
	// are valid against their respective trusted consensus states and  that trustLevel of the validator set signed their commit.
	// see checkMisbehaviourHeader in ibc-go/blob/v7.3.0/modules/light-clients/07-tendermint/misbehaviour_handle.go#L126
	if err := clientState.VerifyClientMessage(ctx, k.cdc, clientStore, &misbehaviour); err != nil {
		return err
	}

	return nil
}
