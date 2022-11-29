package v2

import (
	"github.com/cosmos/cosmos-sdk/codec"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	v1 "github.com/cosmos/interchain-security/x/ccv/consumer/migrations/v1"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

func MigrateStore(ctx sdk.Context, storeKey storetypes.StoreKey, cdc codec.BinaryCodec) error {
	store := ctx.KVStore(storeKey)

	if err := migrateSlashPackets(ctx, store); err != nil {
		return err
	}

	return nil
}

func migrateSlashPackets(ctx sdk.Context, store sdk.KVStore) error {
	slashingPackets, err := getPendingSlashPackets(ctx, store)
	if err != nil {
		return err
	}

	mappedConsumerPackets := make([]consumertypes.ConsumerPacket, 0)
	for _, slashPacketRequest := range slashingPackets.Requests {
		// construct slash packet data
		slashPacket := ccvtypes.SlashPacketData{
			Validator:      slashPacketRequest.Packet.Validator,
			ValsetUpdateId: slashPacketRequest.Packet.ValsetUpdateId,
			Infraction:     slashPacketRequest.Packet.Infraction}

		mappedConsumerPackets = append(mappedConsumerPackets, consumertypes.ConsumerPacket{
			Type: consumertypes.SlashPacket,
			Data: slashPacket.GetBytes(),
		})
	}

	consumerPackets := consumertypes.ConsumerPackets{List: mappedConsumerPackets}
	bz, err := consumerPackets.Marshal()
	if err != nil {
		return err
	}
	store.Set([]byte{consumertypes.PendingDataPacketsBytePrefix}, bz)

	return nil
}

// GetPendingPackets returns the pending CCV packets from the store
func getPendingSlashPackets(ctx sdk.Context, store sdk.KVStore) (v1.SlashRequests, error) {
	bz := store.Get([]byte{v1.PendingSlashRequestsBytePrefix})
	if bz == nil {
		return v1.SlashRequests{}, nil
	}

	var sr v1.SlashRequests
	err := sr.Unmarshal(bz)

	return sr, err
}
