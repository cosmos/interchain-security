package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

var _ ccv.SlashingHooks = Keeper{}

// AfterValidatorDowntime gets the given validator address jailing time
// in order either to add it the downtime jailing duration and initiated its slashing
// on the provider chain or perfom a no-op
func (k Keeper) AfterValidatorDowntime(ctx sdk.Context, consAddr sdk.ConsAddress, power int64) {

	// return if penalty already sent to the provider
	if k.IsPenaltySentToProvider(ctx, consAddr) {
		return
	}

	// get the previous block height valsetUpdateID when the infraction occured
	valsetUpdateID := k.HeightToValsetUpdateID(ctx, uint64(ctx.BlockHeight()-sdk.ValidatorUpdateDelay-1))
	if valsetUpdateID < 1 {
		return
	}

	// send packet to initiate slashing on the provider chain
	k.SendPenalties(
		ctx,
		abci.Validator{
			Address: consAddr.Bytes(),
			Power:   power,
		},
		int64(1),
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

func (k Keeper) AfterValidatorBonded(ctx sdk.Context, address sdk.ConsAddress, _ sdk.ValAddress) {
	if k.hooks == nil {
		panic("dd")
		fmt.Println("HOOK NIL")
	} else {
		fmt.Println("HOOK NOT NIL")

	}
	if k.hooks != nil {
		k.hooks.AfterValidatorBonded(ctx, address, nil)
	}
}

// AfterValidatorCreated adds the address-pubkey relation when a validator is created.
func (k Keeper) AfterValidatorCreated(ctx sdk.Context, valAddr sdk.ValAddress) {
	if k.hooks != nil {
		k.hooks.AfterValidatorCreated(ctx, valAddr)
	}
}

// AfterValidatorRemoved deletes the address-pubkey relation when a validator is removed,
func (k Keeper) AfterValidatorRemoved(ctx sdk.Context, address sdk.ConsAddress) {
	if k.hooks != nil {
		k.hooks.AfterValidatorRemoved(ctx, address, nil)
	}
}
