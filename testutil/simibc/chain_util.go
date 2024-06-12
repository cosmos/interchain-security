package simibc

import (
	"time"

	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	abci "github.com/cometbft/cometbft/abci/types"
)

// FinalizeBlock calls app.FinalizeBlock and app.Commit.
// It sets the next block time to currentBlockTime + dt.
// This function returns the TMHeader of the block that was just ended,
//
// NOTE: this method may be used independently of the rest of simibc.
func FinalizeBlock(c *ibctesting.TestChain, dt time.Duration) (*ibctmtypes.Header, []channeltypes.Packet) {
	res, err := c.App.FinalizeBlock(&abci.RequestFinalizeBlock{
		Height:             c.CurrentHeader.Height,
		Time:               c.CurrentHeader.GetTime(),
		NextValidatorsHash: c.NextVals.Hash(),
	})
	require.NoError(c.TB, err)

	err = commitBlock(c, dt, res)
	require.NoError(c.TB, err)

	// handle packets
	packets := ParsePacketsFromEvents(res.Events)
	return c.LastHeader, packets
}

// ParsePacketsFromEvents returns all packets found in events.
func ParsePacketsFromEvents(events []abci.Event) (packets []channeltypes.Packet) {
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
