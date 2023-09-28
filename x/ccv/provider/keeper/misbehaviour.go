package keeper

import (
	tmtypes "github.com/cometbft/cometbft/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ibcclienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// HandleConsumerMisbehaviour checks if the given IBC misbehaviour corresponds to an equivocation light client attack,
// and in this case, jails the Byzantine validators
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

	// jail the Byzantine validators
	for _, v := range byzantineValidators {
		providerAddr := k.GetProviderAddrFromConsumerAddr(
			ctx,
			misbehaviour.Header1.Header.ChainID,
			types.NewConsumerConsAddress(sdk.ConsAddress(v.Address.Bytes())),
		)
		k.JailValidator(ctx, providerAddr)
		provAddrs = append(provAddrs, providerAddr)
	}

	logger.Info(
		"confirmed equivocation light client attack",
		"byzantine validators", provAddrs,
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
		return sdkerrors.Wrapf(ibcclienttypes.ErrClientNotFound, "cannot check misbehaviour for client with ID %s", misbehaviour.ClientId)
	}

	clientStore := k.clientKeeper.ClientStore(ctx, misbehaviour.ClientId)

	// Check that the headers are at the same height to ensure that
	// the misbehaviour is for a light client attack and not a time violation,
	// see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go
	if !misbehaviour.Header1.GetHeight().EQ(misbehaviour.Header2.GetHeight()) {
		return sdkerrors.Wrap(ibcclienttypes.ErrInvalidMisbehaviour, "headers are not at same height")
	}

	// CheckMisbehaviourAndUpdateState verifies the misbehaviour against the trusted consensus states
	// but does NOT update the light client state.
	// Note that the IBC CheckMisbehaviourAndUpdateState method returns an error if the trusted consensus states are expired,
	// see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go
	ok := clientState.CheckForMisbehaviour(ctx, k.cdc, clientStore, &misbehaviour)
	if !ok {
		return sdkerrors.Wrapf(ibcclienttypes.ErrInvalidMisbehaviour, "invalid misbehaviour for client-id: %s", misbehaviour.ClientId)
	}

	return nil
}
