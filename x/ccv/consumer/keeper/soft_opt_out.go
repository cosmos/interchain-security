package keeper

import (
	"encoding/binary"
	"errors"
	"fmt"
	"sort"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/consumer/types"
)

// BeginBlockSoftOptOut executes BeginBlock logic for the Soft Opt-Out sub-protocol
func (k Keeper) BeginBlockSoftOptOut(ctx sdk.Context) {
	// Update smallest validator power that cannot opt out.
	k.UpdateSmallestNonOptOutPower(ctx)

	// Update the SigningInfo structs of the Slashing module
	k.UpdateSlashingSigningInfo(ctx)
}

// SetSmallestNonOptOutPower sets the smallest validator power that cannot soft opt out.
func (k Keeper) SetSmallestNonOptOutPower(ctx sdk.Context, power uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.SmallestNonOptOutPowerKey(), sdk.Uint64ToBigEndian(power))
}

// UpdateSmallestNonOptOutPower updates the smallest validator power that cannot soft opt out.
// This is the smallest validator power such that the sum of the power of all validators with a lower power
// is less than [SoftOptOutThreshold] of the total power of all validators.
func (k Keeper) UpdateSmallestNonOptOutPower(ctx sdk.Context) {
	// get soft opt-out threshold
	optOutThreshold := math.LegacyMustNewDecFromStr(k.GetSoftOptOutThreshold(ctx))
	if optOutThreshold.IsZero() {
		// If the SoftOptOutThreshold is zero, then soft opt-out is disable.
		// Setting the smallest non-opt-out power to zero, fixes the diff-testing
		// when soft opt-out is disable.
		k.SetSmallestNonOptOutPower(ctx, uint64(0))
		return
	}

	// get all validators
	valset := k.GetAllCCValidator(ctx)

	// Valset should only be empty for hacky tests. Log error in case this ever happens in prod.
	if len(valset) == 0 {
		k.Logger(ctx).Error("UpdateSoftOptOutThresholdPower called with empty validator set")
		return
	}

	// sort validators by power ascending
	sort.SliceStable(valset, func(i, j int) bool {
		return valset[i].Power < valset[j].Power
	})

	// get total power in set
	totalPower := math.LegacyZeroDec()
	for _, val := range valset {
		totalPower = totalPower.Add(math.LegacyNewDecFromInt(math.NewInt(val.Power)))
	}

	// get power of the smallest validator that cannot soft opt out
	powerSum := math.LegacyZeroDec()
	for _, val := range valset {
		powerSum = powerSum.Add(math.LegacyNewDecFromInt(math.NewInt(val.Power)))
		// if powerSum / totalPower > SoftOptOutThreshold
		if powerSum.Quo(totalPower).GT(optOutThreshold) {
			// set smallest non opt out power
			k.SetSmallestNonOptOutPower(ctx, uint64(val.Power))
			k.Logger(ctx).Info("smallest non opt out power updated", "power", val.Power)
			return
		}
	}
	panic("UpdateSoftOptOutThresholdPower should not reach this point. Incorrect logic!")
}

// GetSmallestNonOptOutPower returns the smallest validator power that cannot soft opt out.
func (k Keeper) GetSmallestNonOptOutPower(ctx sdk.Context) int64 {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.SmallestNonOptOutPowerKey())
	if bz == nil {
		return 0
	}
	return int64(binary.BigEndian.Uint64(bz))
}

func (k Keeper) UpdateSlashingSigningInfo(ctx sdk.Context) {
	smallestNonOptOutPower := k.GetSmallestNonOptOutPower(ctx)

	// Update SigningInfo for opted out validators
	valset := k.GetAllCCValidator(ctx)
	// Note that we don't need to sort the valset as GetAllCCValidator
	// uses KVStorePrefixIterator that iterates over all the keys with
	// a certain prefix in ascending order
	for _, val := range valset {
		consAddr := sdk.ConsAddress(val.Address)
		signingInfo, err := k.slashingKeeper.GetValidatorSigningInfo(ctx, consAddr)
		if errors.Is(err, slashingtypes.ErrNoSigningInfoFound) {
			continue
		} else if err != nil {
			panic(fmt.Errorf("failed to get validator signing info for validator %s", consAddr))
		}
		if val.Power < smallestNonOptOutPower {
			// validator CAN opt-out from validating on consumer chains
			if !val.OptedOut {
				// previously the validator couldn't opt-out
				val.OptedOut = true
			}
		} else {
			// validator CANNOT opt-out from validating on consumer chains
			if val.OptedOut {
				// previously the validator could opt-out
				signingInfo.StartHeight = ctx.BlockHeight()
				val.OptedOut = false
			}
		}

		if err := k.slashingKeeper.SetValidatorSigningInfo(ctx, consAddr, signingInfo); err != nil {
			panic(fmt.Errorf("failed to update validator signing info for validator %s", consAddr))
		}
		k.SetCCValidator(ctx, val)
	}
}
