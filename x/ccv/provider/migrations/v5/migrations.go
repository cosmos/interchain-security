package v5

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
)

// This migration only takes already registered chains into account.
// If a chain is in voting while the upgrade happens, this is not sufficient,
// and a migration to rewrite the proposal is needed.
//
// TODO (PERMISSIONLESS): this migration needs to be fix or removed
func MigrateTopNForRegisteredChains(ctx sdk.Context, providerKeeper providerkeeper.Keeper) {
	// Set the topN of each chain to 95
	for _, consumerId := range providerKeeper.GetAllLaunchedConsumerIds(ctx) {
		// TODO (PERMISSIONLESS): this migration already took place and does not make much sense in the Permissionless world
		// living here for now and we should totally remove
		providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, types.PowerShapingParameters{
			Top_N: 95,
		})
	}
}

// // If there are consumer addition proposals in the voting period at the upgrade time, they may need the topN value updated.
// func MigrateTopNForVotingPeriodChains(ctx sdk.Context, govKeeper govkeeper.Keeper, providerKeeper providerkeeper.Keeper) {
// }
