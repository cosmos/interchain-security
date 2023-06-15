package keeper

import (
	"fmt"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
)

// TODO: Adjust SendPackets in relay.go

func (k Keeper) GetPacketsToSend(ctx sdktypes.Context) ccvtypes.ConsumerPacketDataList {

	// Handle retries for bouncing slash packet if one exists
	bouncingSlashExists, bouncingSlashData := k.GetBouncingSlash(ctx)
	if bouncingSlashExists {
		// If retry of bouncing slash is allowed, return bouncing slash packet to be sent.
		// TODO: incorporate retry delay
		if k.IsSlashRetryAllowed(ctx) {
			return ccvtypes.ConsumerPacketDataList{List: []ccvtypes.ConsumerPacketData{bouncingSlashData}}
			// Otherwise, return empty list. Block sending of all other packets until bouncing slash is handled by provider.
		} else {
			return ccvtypes.ConsumerPacketDataList{}
		}
	}
	// If control flow reaches here, no bouncing slash packet exists.

	pending := k.GetPendingPackets(ctx)
	toSend := ccvtypes.ConsumerPacketDataList{}
	for _, packet := range pending.List {
		// switch over packet type, using if-statements to break out of loop in a readable way
		if packet.Type == ccvtypes.VscMaturedPacket {
			toSend.List = append(toSend.List, packet)

		} else if packet.Type == ccvtypes.SlashPacket {
			toSend.List = append(toSend.List, packet)
			k.SetBouncingSlash(ctx, packet)
			k.DeleteSlashRetryAllowed(ctx) // Retry not allowed until result is received from provider.

			// Break for-loop. No more packets are sent until the bouncing slash packet is handled by provider.
			// Once handled, BouncingSlash is deleted from state.
			break
		} else {
			panic("unknown packet type")
		}
	}
	return toSend
}

// TODO: will need good integration tests making sure this state is properly init, cleared, etc.

func (k Keeper) SetSlashRetryAllowed(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Set(consumertypes.RetryAllowedKey(), []byte{1})
}

func (k Keeper) DeleteSlashRetryAllowed(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(consumertypes.RetryAllowedKey())
}

func (k Keeper) IsSlashRetryAllowed(ctx sdktypes.Context) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Has(consumertypes.RetryAllowedKey())
}

// TODO: UTs

func (k Keeper) SetBouncingSlash(ctx sdktypes.Context, slashPacketData ccvtypes.ConsumerPacketData) {
	store := ctx.KVStore(k.storeKey)
	bz, err := slashPacketData.Marshal()
	if err != nil {
		// This should never happen
		panic(fmt.Errorf("failed to marshal bouncing slash: %w", err))
	}
	store.Set(consumertypes.BouncingSlashKey(), bz)
}

func (k Keeper) GetBouncingSlash(ctx sdktypes.Context) (found bool, packetData ccvtypes.ConsumerPacketData) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(consumertypes.BouncingSlashKey())
	if bz == nil {
		return false, packetData
	}
	err := packetData.Unmarshal(bz)
	if err != nil {
		// An error here would indicate something is very wrong,
		panic(fmt.Errorf("failed to unmarshal bouncing slash: %w", err))
	}
	return true, packetData
}

func (k Keeper) DeleteBouncingSlash(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(consumertypes.BouncingSlashKey())
}
