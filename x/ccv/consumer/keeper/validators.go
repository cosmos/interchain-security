package keeper

import (
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
)

// ApplyCCValidatorChanges applies the given changes to the cross-chain validators states
// and returns updates to forward to tendermint.
func (k Keeper) ApplyCCValidatorChanges(ctx sdk.Context, changes []abci.ValidatorUpdate) []abci.ValidatorUpdate {
	ret := []abci.ValidatorUpdate{}
	for _, change := range changes {
		addr := utils.GetChangePubKeyAddress(change)
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

			pubkey, err := cryptocodec.FromTmProtoPublicKey(change.GetPubKey())
			if err != nil {
				panic(err)
			}
			ccVal, err := types.NewCCValidator(addr, change.Power, pubkey)
			if err != nil {
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
func (k Keeper) IterateValidators(sdk.Context, func(index int64, validator stakingtypes.ValidatorI) (stop bool)) {
}

// Validator - unimplemented on CCV keeper
func (k Keeper) Validator(ctx sdk.Context, addr sdk.ValAddress) stakingtypes.ValidatorI {
	panic("unimplemented on CCV keeper")
}

// IsJailed returns the outstanding slashing flag for the given validator adddress
func (k Keeper) IsValidatorJailed(ctx sdk.Context, addr sdk.ConsAddress) bool {
	return k.OutstandingDowntime(ctx, addr)
}

// ValidatorByConsAddr returns an empty validator
func (k Keeper) ValidatorByConsAddr(sdk.Context, sdk.ConsAddress) stakingtypes.ValidatorI {
	return stakingtypes.Validator{}
}

// Slash sends a slashing request to the provider chain
func (k Keeper) Slash(ctx sdk.Context, addr sdk.ConsAddress, infractionHeight, power int64, _ sdk.Dec, infraction stakingtypes.InfractionType) {
	if infraction == stakingtypes.InfractionEmpty {
		return
	}

	k.SendSlashPacket(
		ctx,
		abci.Validator{
			Address: addr.Bytes(),
			Power:   power},
		// get VSC ID for infraction height
		k.GetHeightValsetUpdateID(ctx, uint64(infractionHeight)),
		infraction,
	)
}

// Jail - unimplemented on CCV keeper
func (k Keeper) Jail(ctx sdk.Context, addr sdk.ConsAddress) {}

// Unjail - unimplemented on CCV keeper
func (k Keeper) Unjail(sdk.Context, sdk.ConsAddress) {}

// Delegation - unimplemented on CCV keeper
func (k Keeper) Delegation(sdk.Context, sdk.AccAddress, sdk.ValAddress) stakingtypes.DelegationI {
	panic("unimplemented on CCV keeper")
}

// MaxValidators - unimplemented on CCV keeper
func (k Keeper) MaxValidators(sdk.Context) uint32 {
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
	for i := ctx.BlockHeight() - int64(numHistoricalEntries); i >= 0; i-- {
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
			panic(err)
		}
		val, err := stakingtypes.NewValidator(nil, pk, stakingtypes.Description{})
		if err != nil {
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

// ValidatorUpdates gets all cross-chain validators converted to the ABCI validator update type
func (k Keeper) GetValidatorUpdates(ctx sdk.Context) ([]abci.ValidatorUpdate, error) {
	vals := k.GetAllCCValidator(ctx)
	valUpdates := make([]abci.ValidatorUpdate, 0, len(vals))
	for _, v := range vals {
		pk, err := v.ConsPubKey()
		if err != nil {
			return nil, err
		}
		tmPK, err := cryptocodec.ToTmProtoPublicKey(pk)
		if err != nil {
			return nil, err
		}
		valUpdates = append(valUpdates, abci.ValidatorUpdate{PubKey: tmPK, Power: v.Power})
	}
	return valUpdates, nil
}
