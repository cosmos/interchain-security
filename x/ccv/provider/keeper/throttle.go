package keeper

import (
	"fmt"
	"time"

	"cosmossdk.io/math"

	sdktypes "github.com/cosmos/cosmos-sdk/types"

	tmtypes "github.com/cometbft/cometbft/types"

	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// Obtains the effective validator power relevant to a validator consensus address.
func (k Keeper) GetEffectiveValPower(ctx sdktypes.Context,
	valConsAddr providertypes.ProviderConsAddress,
) math.Int {
	// Obtain staking module val object from the provider's consensus address.
	// Note: if validator is not found or unbonded, this will be handled appropriately in HandleSlashPacket
	val, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, valConsAddr.ToSdkConsAddr())

	if err != nil || val.IsJailed() {
		// If validator is not found, or found but jailed, it's power is 0. This path is explicitly defined since the
		// staking keeper's LastValidatorPower values are not updated till the staking keeper's endblocker.
		return math.ZeroInt()
	} else {
		// Otherwise, return the staking keeper's LastValidatorPower value.
		// NOTE: @MSalopek double check this conversion and see if it's necessary
		valAddrBech32, err := sdktypes.ValAddressFromHex(val.GetOperator())
		if err != nil {
			return math.ZeroInt()
		}

		power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddrBech32)
		if err != nil {
			return math.ZeroInt()
		}
		return math.NewInt(power)
	}
}

// InitializeSlashMeter initializes the slash meter to it's max value (also its allowance),
// and sets the replenish time candidate to one replenish period from current block time.
func (k Keeper) InitializeSlashMeter(ctx sdktypes.Context) {
	k.SetSlashMeter(ctx, k.GetSlashMeterAllowance(ctx))
	k.SetSlashMeterReplenishTimeCandidate(ctx)
}

// CheckForSlashMeterReplenishment checks if the slash meter should be replenished, and if so, replenishes it.
// Note: initial slash meter replenish time candidate is set in InitGenesis.
func (k Keeper) CheckForSlashMeterReplenishment(ctx sdktypes.Context) {
	// Replenish slash meter if current time is equal to or after the current replenish candidate time.
	if !ctx.BlockTime().UTC().Before(k.GetSlashMeterReplenishTimeCandidate(ctx)) {
		k.ReplenishSlashMeter(ctx)
		// Set replenish time candidate to one replenish period from now, since we just replenished.
		k.SetSlashMeterReplenishTimeCandidate(ctx)
	}

	// The following logic exists to ensure the slash meter is not greater than the allowance for this block,
	// in the event that the total voting power of the provider chain has decreased since previous blocks.

	// If slash meter is full, or more than full considering updated allowance/total power,
	allowance := k.GetSlashMeterAllowance(ctx)
	if k.GetSlashMeter(ctx).GTE(allowance) {

		// Update/set replenish time candidate to one replenish period from now.
		// This time candidate will be updated in every future block until the slash meter becomes NOT full.
		k.SetSlashMeterReplenishTimeCandidate(ctx)

		// Ensure the slash meter is not greater than allowance this block,
		// considering current total voting power.
		k.SetSlashMeter(ctx, allowance)
	}
}

func (k Keeper) ReplenishSlashMeter(ctx sdktypes.Context) {
	meter := k.GetSlashMeter(ctx)
	oldMeter := meter
	allowance := k.GetSlashMeterAllowance(ctx)

	// Replenish meter up to allowance for this block. That is, if meter was negative
	// before being replenished, it'll become more positive in value. However, if the meter
	// was 0 or positive in value, it'll be replenished only up to it's allowance
	// for the current block.
	meter = meter.Add(allowance)
	if meter.GT(allowance) {
		meter = allowance
	}

	k.SetSlashMeter(ctx, meter)

	k.Logger(ctx).Debug("slash meter replenished",
		"old meter value", oldMeter.Int64(),
		"new meter value", meter.Int64(),
	)
}

// GetSlashMeterAllowance returns the amount of voting power units (int)
// that would be added to the slash meter for a replenishment that would happen this block,
// this allowance value also serves as the max value for the meter for this block.
//
// Note: allowance can change between blocks, since it is directly correlated to total voting power.
// The slash meter must be less than or equal to the allowance for this block, before any slash
// packet handling logic can be executed.
func (k Keeper) GetSlashMeterAllowance(ctx sdktypes.Context) math.Int {
	strFrac := k.GetSlashMeterReplenishFraction(ctx)
	// MustNewDecFromStr should not panic, since the (string representation) of the slash meter replenish fraction
	// is validated in ValidateGenesis and anytime the param is mutated.
	decFrac := math.LegacyMustNewDecFromStr(strFrac)

	// Compute allowance in units of tendermint voting power (integer),
	// noting that total power changes over time
	// NOTE: ignoring err seems safe here, since the func returns a default math.ZeroInt()
	// and there are no concrete actions we can take if the err is not nil.
	totalPower, _ := k.stakingKeeper.GetLastTotalPower(ctx)

	roundedInt := math.NewInt(decFrac.MulInt(totalPower).RoundInt64())
	if roundedInt.IsZero() {
		k.Logger(ctx).Info("slash meter replenish fraction is too small " +
			"to add any allowance to the meter, considering bankers rounding")

		// Return non-zero allowance to guarantee some slash packets are eventually handled
		return math.NewInt(1)
	}
	return roundedInt
}

// GetSlashMeter returns a meter (persisted as a signed int) which stores an amount of voting power, corresponding
// to an allowance of validators that can be jailed/tombstoned over time.
//
// Note: the value of this int should always be in the range of tendermint's [-MaxVotingPower, MaxVotingPower]
func (k Keeper) GetSlashMeter(ctx sdktypes.Context) math.Int {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.SlashMeterKey())
	if bz == nil {
		// Slash meter should be set as a part of InitGenesis and periodically updated by throttle logic,
		// there is no deletion method exposed, so nil bytes would indicate something is very wrong.
		panic("slash meter not set")
	}
	value := math.ZeroInt()
	err := value.Unmarshal(bz)
	if err != nil {
		// We should have obtained value bytes that were serialized in SetSlashMeter,
		// so an error here would indicate something is very wrong.
		panic(fmt.Sprintf("failed to unmarshal slash meter: %v", err))
	}
	return value
}

// SetSlashMeter sets the slash meter to the given signed int value
//
// Note: the value of this int should always be in the range of tendermint's [-MaxTotalVotingPower, MaxTotalVotingPower]
func (k Keeper) SetSlashMeter(ctx sdktypes.Context, value math.Int) {
	// TODO: remove these invariant panics once https://github.com/cosmos/interchain-security/issues/534 is solved.

	// The following panics are included since they are invariants for slash meter value.
	//
	// Explanation: slash meter replenish fraction is validated to be in range of [0, 1],
	// and MaxMeterValue = MaxAllowance = MaxReplenishFrac * MaxTotalVotingPower = 1 * MaxTotalVotingPower.
	if value.GT(math.NewInt(tmtypes.MaxTotalVotingPower)) {
		panic("slash meter value cannot be greater than tendermint's MaxTotalVotingPower")
	}
	// Further, HandleThrottleQueues should never subtract more than MaxTotalVotingPower from the meter,
	// since we cannot slash more than an entire validator set. So MinMeterValue = -1 * MaxTotalVotingPower.
	if value.LT(math.NewInt(-tmtypes.MaxTotalVotingPower)) {
		panic("slash meter value cannot be less than negative tendermint's MaxTotalVotingPower")
	}
	store := ctx.KVStore(k.storeKey)
	bz, err := value.Marshal()
	if err != nil {
		// A returned error for marshaling an int would indicate something is very wrong.
		panic(fmt.Sprintf("failed to marshal slash meter: %v", err))
	}
	store.Set(providertypes.SlashMeterKey(), bz)
}

// GetSlashMeterReplenishTimeCandidate returns the next UTC time the slash meter could potentially be replenished.
//
// Note: this value is the next time the slash meter will be replenished IFF the slash meter is NOT full.
// Otherwise this value will be updated in every future block until the slash meter becomes NOT full.
func (k Keeper) GetSlashMeterReplenishTimeCandidate(ctx sdktypes.Context) time.Time {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.SlashMeterReplenishTimeCandidateKey())
	if bz == nil {
		// Slash meter replenish time candidate should be set as a part of InitGenesis and periodically updated by throttle logic,
		// there is no deletion method exposed, so nil bytes would indicate something is very wrong.
		panic("slash meter replenish time candidate not set")
	}
	time, err := sdktypes.ParseTimeBytes(bz)
	if err != nil {
		// We should have obtained value bytes that were serialized in SetSlashMeterReplenishTimeCandidate,
		// so an error here would indicate something is very wrong.
		panic(fmt.Sprintf("failed to parse slash meter replenish time candidate: %s", err))
	}
	return time.UTC()
}

// SetSlashMeterReplenishTimeCandidate sets the next time the slash meter may be replenished
// to the current block time + the configured slash meter replenish period.
//
// Note: this value is the next time the slash meter will be replenished IFF the slash meter is NOT full.
// Otherwise this value will be updated in every future block until the slash meter becomes NOT full.
func (k Keeper) SetSlashMeterReplenishTimeCandidate(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	timeToStore := ctx.BlockTime().UTC().Add(k.GetSlashMeterReplenishPeriod(ctx))
	store.Set(providertypes.SlashMeterReplenishTimeCandidateKey(), sdktypes.FormatTimeBytes(timeToStore))
}
