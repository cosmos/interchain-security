package keeper

import (
	"fmt"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
)

// TODO: Adjust SendPackets in relay.go

func (k Keeper) GetPacketsToSend(ctx sdktypes.Context) ccvtypes.ConsumerPacketDataList {

	// TODO: incorporate retry delay

	// Handle retries for bouncing slash packet if one exists
	bouncingSlashExists, bouncingSlash := k.GetBouncingSlash(ctx)
	if bouncingSlashExists {
		// Note if bouncing slash exists, return is always hit.
		// Ie. we block sending of all other packets until bouncing slash is handled by provider.

		// If retry of bouncing slash is allowed, return bouncing slash packet to be sent.
		if bouncingSlash.RetryAllowed {
			// Another retry will not be allowed until current retry result is received from provider.
			bouncingSlash.RetryAllowed = false
			k.SetBouncingSlash(ctx, bouncingSlash)
			return ccvtypes.ConsumerPacketDataList{List: []ccvtypes.ConsumerPacketData{*bouncingSlash.SlashPacketData}}
		} else {
			// If slash retry not allowed, return empty list. We still need to hear back from provider.
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
			bouncingSlash := consumertypes.BouncingSlash{
				SlashPacketData: &packet,
				// Retry not allowed until result is received from provider.
				RetryAllowed: false,
			}
			k.SetBouncingSlash(ctx, bouncingSlash)

			// Break for-loop. No more packets are sent until the bouncing slash packet is handled by provider.
			break
		} else {
			panic("unknown packet type")
		}
	}
	return toSend
}

// TODO: will need good integration tests making sure this state is properly init, cleared, etc.
// TODO: UTs

func (k Keeper) SetBouncingSlash(ctx sdktypes.Context, bouncingSlash consumertypes.BouncingSlash) {
	store := ctx.KVStore(k.storeKey)
	bz, err := bouncingSlash.Marshal()
	if err != nil {
		// This should never happen
		panic(fmt.Errorf("failed to marshal bouncing slash: %w", err))
	}
	store.Set(consumertypes.BouncingSlashKey(), bz)
}

func (k Keeper) GetBouncingSlash(ctx sdktypes.Context) (found bool, bouncingSlash consumertypes.BouncingSlash) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(consumertypes.BouncingSlashKey())
	if bz == nil {
		return false, bouncingSlash
	}
	err := bouncingSlash.Unmarshal(bz)
	if err != nil {
		// An error here would indicate something is very wrong,
		panic(fmt.Errorf("failed to unmarshal bouncing slash: %w", err))
	}
	return true, bouncingSlash
}

func (k Keeper) DeleteBouncingSlash(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(consumertypes.BouncingSlashKey())
}
