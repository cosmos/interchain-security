package types

import ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"

func NewBouncingSlash(slashPacketData ccvtypes.ConsumerPacketData) (bouncingSlash BouncingSlash, ok bool) {
	if slashPacketData.Type != ccvtypes.SlashPacket {
		return BouncingSlash{}, false
	}
	_, ok = slashPacketData.Data.(*ccvtypes.ConsumerPacketData_SlashPacketData)
	if !ok {
		return BouncingSlash{}, false
	}
	return BouncingSlash{
		SlashPacketData: &slashPacketData,
		// Bouncing slash is initialized with retry not allowed.
		// We must hear back from provider before retry is allowed. See consumer's OnAcknowledgementPacket()
		RetryAllowed: false,
	}, true
}
