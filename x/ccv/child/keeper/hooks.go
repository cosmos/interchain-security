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
	// get validator signing info
	signInfo, _ := k.slashingKeeper.GetValidatorSigningInfo(ctx, consAddr)

	// do nothing if validator is jailed
	if ctx.BlockTime().UnixNano() < int64(signInfo.JailedUntil.UnixNano()) {
		return
	}

	// increase jail time
	signInfo.JailedUntil = ctx.BlockHeader().Time.Add(k.slashingKeeper.DowntimeJailDuration(ctx))

	// reset the missed block counters
	signInfo.MissedBlocksCounter = 0
	signInfo.IndexOffset = 0
	k.slashingKeeper.ClearValidatorMissedBlockBitArray(ctx, consAddr)

	// update signing info
	k.slashingKeeper.SetValidatorSigningInfo(ctx, consAddr, signInfo)

	// send packet to initiate slashing on the provider chain
	k.SendPacket(
		ctx,
		abci.Validator{
			Address: consAddr.Bytes(),
			Power:   power,
		},
		k.slashingKeeper.SlashFractionDowntime(ctx).TruncateInt64(),
		signInfo.JailedUntil.UnixNano(),
	)
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
