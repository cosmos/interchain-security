package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

var _ slashingtypes.SlashingHooks = Keeper{}

// AfterValidatorDowntime gets the given validator address jailing time
// in order either to add it the downtime jailing duration and initiated its slashing
// on the provider chain or perfom a no-op
func (k Keeper) AfterValidatorDowntime(ctx sdk.Context, consAddr sdk.ConsAddress, power int64) {

	// return if penalty already sent to the provider
	if k.IsPenaltySentToProvider(ctx, consAddr) {
		return
	}

	// get last the valset update id
	valsetUpdate, err := k.GetLastUnbondingPacketData(ctx)
	if err != nil {
		return
	}

	// send packet to initiate slashing on the provider chain
	k.SendPenalties(
		ctx,
		abci.Validator{
			Address: consAddr.Bytes(),
			Power:   power,
		},
		valsetUpdate.ValsetUpdateId,
		k.slashingKeeper.SlashFractionDowntime(ctx).TruncateInt64(),
		k.slashingKeeper.DowntimeJailDuration(ctx).Nanoseconds(),
	)

	// set penalty to validator address
	k.PenaltySentToProvider(ctx, consAddr)
}

// Hooks wrapper struct for ChildKeeper
type Hooks struct {
	k Keeper
}

// Return the wrapper struct
func (k Keeper) Hooks() Hooks {
	return Hooks{k}
}

// AfterValidatorDowntime implements the slashing hook interface
func (h Hooks) AfterValidatorDowntime(ctx sdk.Context, consAddr sdk.ConsAddress, power int64) {
	h.k.AfterValidatorDowntime(ctx, consAddr, power)
}
