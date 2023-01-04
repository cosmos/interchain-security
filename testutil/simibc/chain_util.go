package simibc

import (
	"time"

	channelkeeper "github.com/cosmos/ibc-go/v3/modules/core/04-channel/keeper"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	abci "github.com/tendermint/tendermint/abci/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

// BeginBlock updates the current header and calls the app.BeginBlock() method.
// The new block height is the previous block height + 1.
// The new block time is the previous block time + dt.
func BeginBlock(c *ibctesting.TestChain, dt time.Duration) {

	c.CurrentHeader = tmproto.Header{
		ChainID:            c.ChainID,
		Height:             c.App.LastBlockHeight() + 1,
		AppHash:            c.App.LastCommitID().Hash,
		Time:               c.CurrentHeader.Time.Add(dt),
		ValidatorsHash:     c.Vals.Hash(),
		NextValidatorsHash: c.NextVals.Hash(),
	}

	_ = c.App.BeginBlock(abci.RequestBeginBlock{Header: c.CurrentHeader})
}

// EndBlock and calls the preCommitCallback before the app.Commit() is called.
func EndBlock(c *ibctesting.TestChain, preCommitCallback func()) (*ibctmtypes.Header, []channeltypes.Packet) {
	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})

	/*
		It is useful to call arbitrary code after ending the block but before
		committing the block because the sdk.Context is cleared after committing.
	*/
	preCommitCallback()

	c.App.Commit()

	c.Vals = c.NextVals

	c.NextVals = ibctesting.ApplyValSetChanges(c.T, c.Vals, ebRes.ValidatorUpdates)

	c.LastHeader = c.CurrentTMClientHeader()

	packets := []channeltypes.Packet{}

	for _, e := range ebRes.Events {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, _ := channelkeeper.ReconstructPacketFromEvent(e)
			packets = append(packets, packet)
		}
	}

	return c.LastHeader, packets
}
