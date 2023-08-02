package keeper

import (
	"bytes"
	"fmt"
	"sort"

	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// HandleConsumerMisbehaviour checks whether the given IBC misbehaviour is valid and, if they are, the misbehaving
// CheckConsumerMisbehaviour check that the given IBC misbehaviour headers forms a valid light client attack evidence.
// proceed to the jailing and tombstoning of the bzyantine validators.
func (k Keeper) HandleConsumerMisbehaviour(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) error {
	logger := k.Logger(ctx)

	if err := k.clientKeeper.CheckMisbehaviourAndUpdateState(ctx, &misbehaviour); err != nil {
		logger.Info("Misbehaviour rejected", err.Error())

		return err
	}
	// Since the misbehaviour packet was received within the trusting period
	// w.r.t to the last trusted consensus it entails that the infraction age
	// isn't too old. see ibc-go/modules/light-clients/07-tendermint/types/misbehaviour_handle.go

	// Get Byzantine validators from the conflicting headers
	// Note that it only handle equivocation light client attacks
	evidence, err := k.GetByzantineValidators(ctx, misbehaviour)
	if err != nil {
		return err
	}

	// jail and tombstone the byzantine validators
	for _, v := range evidence.ByzantineValidators {
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
		"byzantine validators", evidence.ByzantineValidators,
	)

	return nil
}

// GetByzantineValidators return the Byzantine validators from a given misbehaviour. Note that it only
// handles the equivocation light client attack and therefore will return an error an error the
// conflicting headers commit aren't for the same round.
func (k Keeper) GetByzantineValidators(ctx sdk.Context, misbehaviour ibctmtypes.Misbehaviour) (*tmtypes.LightClientAttackEvidence, error) {
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

	// Check if the light client attack correspond to a "equivocation"
	// in this case return the validators that signed both headers

	if headersHaveConflictingStatesTransitions(header1, header2) {
		return nil, fmt.Errorf("cannot get Byzantine validators; headers have conflicting states transitions; possible lunatic attack detected")
	} else if header1.Commit.Round == header2.Commit.Round {
		for i := 0; i < len(header2.Commit.Signatures); i++ {
			sigA := header2.Commit.Signatures[i]
			if sigA.Absent() {
				continue
			}

			sigB := header1.Commit.Signatures[i]
			if sigB.Absent() {
				continue
			}

			_, val := header2.ValidatorSet.GetByAddress(sigA.ValidatorAddress)
			validators = append(validators, val)
		}
		sort.Sort(tmtypes.ValidatorsByVotingPower(validators))
	} else {
		return nil, fmt.Errorf("cannot get Byzantine validators; misbehaviour is for an amnesia attack")
	}

	ev := tmtypes.LightClientAttackEvidence{
		ByzantineValidators: validators,
	}

	return &ev, nil
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

func headersHaveConflictingStatesTransitions(header1, header2 *tmtypes.LightBlock) bool {
	return !bytes.Equal(header1.ValidatorsHash, header2.ValidatorsHash) ||
		!bytes.Equal(header1.NextValidatorsHash, header2.NextValidatorsHash) ||
		!bytes.Equal(header1.ConsensusHash, header2.ConsensusHash) ||
		!bytes.Equal(header1.AppHash, header2.AppHash) ||
		!bytes.Equal(header1.LastResultsHash, header2.LastResultsHash)
}
