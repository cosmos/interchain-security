package v3

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
)

// MigrateQueuedPackets processes all queued packet data for all consumer chains that were stored
// on the provider in the v2 consensus version (jail throttling v1).
func MigrateQueuedPackets(ctx sdk.Context, k providerkeeper.Keeper) error {
	for _, consumer := range k.GetAllConsumerChains(ctx) {
		slashData, vscmData := k.LegacyGetAllThrottledPacketData(ctx, consumer.ChainId)
		if len(slashData) > 0 {
			k.Logger(ctx).Error(fmt.Sprintf("slash data being dropped: %v", slashData))
		}
		for _, data := range vscmData {
			k.HandleVSCMaturedPacket(ctx, consumer.ChainId, data)
		}
		k.LegacyDeleteThrottledPacketDataForConsumer(ctx, consumer.ChainId)
	}
	return nil
}
