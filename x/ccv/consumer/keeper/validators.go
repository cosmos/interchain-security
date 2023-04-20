package keeper

import (
	"time"

	"cosmossdk.io/math"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

//
// TODO: make unit tests for all of: MVP consumer, democ consumer, and pre-ccv consumer
// for previously unimplemented methods, if they're implemented to solve the above issue.
//

// ApplyCCValidatorChanges applies the given changes to the cross-chain validators states
// and returns updates to forward to tendermint.
func (k Keeper) ApplyCCValidatorChanges(ctx sdk.Context, changes []abci.ValidatorUpdate) []abci.ValidatorUpdate {
	ret := []abci.ValidatorUpdate{}
	for _, change := range changes {
		// convert TM pubkey to SDK pubkey
		pubkey, err := cryptocodec.FromTmProtoPublicKey(change.GetPubKey())
		if err != nil {
			// An error here would indicate that the validator updates
			// received from the provider are invalid.
			panic(err)
		}
		addr := pubkey.Address()
		val, found := k.GetCCValidator(ctx, addr)

		if found {
			// update or delete an existing validator
			if change.Power < 1 {
				k.DeleteCCValidator(ctx, addr)
			} else {
				val.Power = change.Power
				k.SetCCValidator(ctx, val)
			}
		} else if 0 < change.Power {
			// create a new validator
			consAddr := sdk.ConsAddress(addr)

			ccVal, err := types.NewCCValidator(addr, change.Power, pubkey)
			if err != nil {
				// An error here would indicate that the validator updates
				// received from the provider are invalid.
				panic(err)
			}
			k.SetCCValidator(ctx, ccVal)
			k.AfterValidatorBonded(ctx, consAddr, nil)
		} else {
			// edge case: we received an update for 0 power
			// but the validator is already deleted. Do not forward
			// to tendermint.
			continue
		}
		ret = append(ret, change)
	}
	return ret
}

// IterateValidators - unimplemented on CCV keeper but perform a no-op in order to pass the slashing module InitGenesis.
// It is allowed since the condition verifying validator public keys in HandleValidatorSignature (x/slashing/keeper/infractions.go) is removed
// therefore it isn't required to store any validator public keys to the slashing states during genesis.
func (Keeper) IterateValidators(sdk.Context, func(index int64, validator stakingtypes.ValidatorI) (stop bool)) {
}

// Validator - unimplemented on CCV keeper
func (Keeper) Validator(_ sdk.Context, _ sdk.ValAddress) stakingtypes.ValidatorI {
	panic("unimplemented on CCV keeper")
}

// IsJailed returns the outstanding slashing flag for the given validator adddress
func (k Keeper) IsValidatorJailed(ctx sdk.Context, addr sdk.ConsAddress) bool {
	// if the changeover is not complete for prev standalone chain,
	// return the standalone staking keeper's jailed status
	if k.IsPrevStandaloneChain(ctx) && !k.ChangeoverIsComplete(ctx) {
		return k.standaloneStakingKeeper.IsValidatorJailed(ctx, addr)
	}
	// Otherwise, return the ccv consumer keeper's notion of a validator being jailed
	return k.OutstandingDowntime(ctx, addr)
}

// ValidatorByConsAddr returns an empty validator
func (Keeper) ValidatorByConsAddr(sdk.Context, sdk.ConsAddress) stakingtypes.ValidatorI {
	/*
		NOTE:

		The evidence module will call this function when it handles equivocation evidence.
		The returned value must not be nil and must not have an UNBONDED validator status,
		or evidence will reject it.

		Also, the slashing module will cal lthis function when it observes downtime. In that case
		the only requirement on the returned value is that it isn't null.
	*/
	return stakingtypes.Validator{}
}

// Slash queues a slashing request for the the provider chain
// All queued slashing requests will be cleared in EndBlock
func (k Keeper) SlashForked(
	ctx sdk.Context,
	addr sdk.ConsAddress,
	infractionHeight, power int64,
	slashFactor sdk.Dec,
	infraction stakingtypes.Infraction,
) {
	if infraction == stakingtypes.Infraction_INFRACTION_UNSPECIFIED {
		return
	}

	// If this is a previously standalone chain and infraction happened before the changeover was completed,
	// slash only on the standalone staking keeper.
	if k.IsPrevStandaloneChain(ctx) && infractionHeight < k.FirstConsumerHeight(ctx) {
		k.standaloneStakingKeeper.Slash(ctx, addr, infractionHeight, power, slashFactor) // @sontrinh16, @pysel: I think we need to review upstream changes, they may eliminate the need for SlashForked.  Also, I think that we should update godocs here, but I don't know what the difference between SlashForked and Slash is right now.  Thanks!
		return
	}

	// Otherwise infraction happened after the changeover was completed.

	// if this is a downtime infraction and the validator is allowed to
	// soft opt out, do not queue a slash packet
	if infraction == stakingtypes.Infraction_INFRACTION_DOWNTIME {
		if power < k.GetSmallestNonOptOutPower(ctx) {
			// soft opt out
			k.Logger(ctx).Debug("soft opt out",
				"validator", addr,
				"power", power,
			)
			return
		}
	}
	// get VSC ID for infraction height
	vscID := k.GetHeightValsetUpdateID(ctx, uint64(infractionHeight))

	k.Logger(ctx).Debug("vscID obtained from mapped infraction height",
		"infraction height", infractionHeight,
		"vscID", vscID,
	)

	k.QueueSlashPacket(
		ctx,
		abci.Validator{
			Address: addr.Bytes(),
			Power:   power,
		},
		vscID,
		infraction,
	)
}

func (k Keeper) Slash(
	ctx sdk.Context,
	addr sdk.ConsAddress,
	infractionHeight, power int64,
	_ sdk.Dec,
) math.Int {
	return math.Int{}
}

func (k Keeper) SlashWithInfractionReason(ctx sdk.Context, consAddr sdk.ConsAddress, infractionHeight, power int64, slashFactor sdk.Dec, _ stakingtypes.Infraction) math.Int {
	return k.Slash(ctx, consAddr, infractionHeight, power, slashFactor)
}

// Jail - unimplemented on CCV keeper
//
// This method should be a no-op even during a standalone to consumer changeover.
// Once the upgrade has happened as a part of the changeover,
// the provider validator set will soon be in effect, and jailing is n/a.
func (k Keeper) Jail(ctx sdk.Context, addr sdk.ConsAddress) {}

// Unjail - unimplemented on CCV keeper
//
// This method should be a no-op even during a standalone to consumer changeover.
// Once the upgrade has happened as a part of the changeover,
// the provider validator set will soon be in effect, and jailing is n/a.
func (k Keeper) Unjail(sdk.Context, sdk.ConsAddress) {}

// Delegation - unimplemented on CCV keeper
func (Keeper) Delegation(sdk.Context, sdk.AccAddress, sdk.ValAddress) stakingtypes.DelegationI {
	panic("unimplemented on CCV keeper")
}

// MaxValidators - unimplemented on CCV keeper
func (Keeper) MaxValidators(sdk.Context) uint32 {
	panic("unimplemented on CCV keeper")
}

// UnbondingTime returns consumer unbonding period, satisfying the staking keeper interface
func (k Keeper) UnbondingTime(ctx sdk.Context) time.Duration {
	return k.GetUnbondingPeriod(ctx)
}

// GetHistoricalInfo gets the historical info at a given height
func (k Keeper) GetHistoricalInfo(ctx sdk.Context, height int64) (stakingtypes.HistoricalInfo, bool) {
	store := ctx.KVStore(k.storeKey)
	key := types.HistoricalInfoKey(height)

	value := store.Get(key)
	if value == nil {
		return stakingtypes.HistoricalInfo{}, false
	}

	return stakingtypes.MustUnmarshalHistoricalInfo(k.cdc, value), true
}

// SetHistoricalInfo sets the historical info at a given height
func (k Keeper) SetHistoricalInfo(ctx sdk.Context, height int64, hi *stakingtypes.HistoricalInfo) {
	store := ctx.KVStore(k.storeKey)
	key := types.HistoricalInfoKey(height)
	value := k.cdc.MustMarshal(hi)

	store.Set(key, value)
}

// DeleteHistoricalInfo deletes the historical info at a given height
func (k Keeper) DeleteHistoricalInfo(ctx sdk.Context, height int64) {
	store := ctx.KVStore(k.storeKey)
	key := types.HistoricalInfoKey(height)

	store.Delete(key)
}

// TrackHistoricalInfo saves the latest historical-info and deletes the oldest
// heights that are below pruning height
func (k Keeper) TrackHistoricalInfo(ctx sdk.Context) {
	numHistoricalEntries := k.GetHistoricalEntries(ctx)

	// Prune store to ensure we only have parameter-defined historical entries.
	// In most cases, this will involve removing a single historical entry.
	// In the rare scenario when the historical entries gets reduced to a lower value k'
	// from the original value k. k - k' entries must be deleted from the store.
	// Since the entries to be deleted are always in a continuous range, we can iterate
	// over the historical entries starting from the most recent version to be pruned
	// and then return at the first empty entry.
	for i := ctx.BlockHeight() - numHistoricalEntries; i >= 0; i-- {
		_, found := k.GetHistoricalInfo(ctx, i)
		if found {
			k.DeleteHistoricalInfo(ctx, i)
		} else {
			break
		}
	}

	// if there is no need to persist historicalInfo, return
	if numHistoricalEntries == 0 {
		return
	}

	// Create HistoricalInfo struct
	lastVals := []stakingtypes.Validator{}
	for _, v := range k.GetAllCCValidator(ctx) {
		pk, err := v.ConsPubKey()
		if err != nil {
			// This should never happen as the pubkey is assumed
			// to be stored correctly in ApplyCCValidatorChanges.
			panic(err)
		}
		val, err := stakingtypes.NewValidator(nil, pk, stakingtypes.Description{})
		if err != nil {
			// This should never happen as the pubkey is assumed
			// to be stored correctly in ApplyCCValidatorChanges.
			panic(err)
		}

		// Set validator to bonded status
		val.Status = stakingtypes.Bonded
		// Compute tokens from voting power
		val.Tokens = sdk.TokensFromConsensusPower(v.Power, sdk.DefaultPowerReduction)
		lastVals = append(lastVals, val)
	}

	// Create historical info entry which sorts the validator set by voting power
	historicalEntry := stakingtypes.NewHistoricalInfo(ctx.BlockHeader(), lastVals, sdk.DefaultPowerReduction)

	// Set latest HistoricalInfo at current height
	k.SetHistoricalInfo(ctx, ctx.BlockHeight(), &historicalEntry)
}

// MustGetCurrentValidatorsAsABCIUpdates gets all cross-chain validators converted
// to the ABCI validator update type. It panics in case of failure.
func (k Keeper) MustGetCurrentValidatorsAsABCIUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
	vals := k.GetAllCCValidator(ctx)
	valUpdates := make([]abci.ValidatorUpdate, 0, len(vals))
	for _, v := range vals {
		pk, err := v.ConsPubKey()
		if err != nil {
			// This should never happen as the pubkey is assumed
			// to be stored correctly in ApplyCCValidatorChanges.
			panic(err)
		}
		tmPK, err := cryptocodec.ToTmProtoPublicKey(pk)
		if err != nil {
			// This should never happen as the pubkey is assumed
			// to be stored correctly in ApplyCCValidatorChanges.
			panic(err)
		}
		valUpdates = append(valUpdates, abci.ValidatorUpdate{PubKey: tmPK, Power: v.Power})
	}
	return valUpdates
}
