package simibc

import (
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"

	sdk "github.com/cosmos/cosmos-sdk/types"

	abci "github.com/cometbft/cometbft/abci/types"
)

// ParsePacketsFromEvents returns all packets found in events.
func ParsePacketsFromEvents(events []sdk.Event) (packets []channeltypes.Packet) {
	for i, ev := range events {
		if ev.Type == channeltypes.EventTypeSendPacket {
			packet, err := ibctesting.ParsePacketFromEvents(events[i:])
			if err != nil {
				panic(err)
			}
			packets = append(packets, packet)
		}
	}
	return
}

// ABCIToSDKEvents converts a list of ABCI events to Cosmos SDK events.
func ABCIToSDKEvents(abciEvents []abci.Event) sdk.Events {
	var events sdk.Events
	for _, evt := range abciEvents {
		var attributes []sdk.Attribute
		for _, attr := range evt.GetAttributes() {
			attributes = append(attributes, sdk.NewAttribute(attr.Key, attr.Value))
		}

		events = events.AppendEvent(sdk.NewEvent(evt.GetType(), attributes...))
	}

	return events
}
