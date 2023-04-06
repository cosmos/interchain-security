package simibc

import (
	"time"

	abci "github.com/cometbft/cometbft/abci/types"
	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	ibctestingcore "github.com/cosmos/interchain-security/v2/legacy_ibc_testing/core"
	ibctesting "github.com/cosmos/interchain-security/v2/legacy_ibc_testing/testing"
)

// BeginBlock updates the current header and calls the app.BeginBlock method.
// The new block height is the previous block height + 1.
// The new block time is the previous block time + dt.
//
// NOTE: this method may be used independently of the rest of simibc.
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

// EndBlock calls app.EndBlock and executes preCommitCallback BEFORE calling app.Commit
// The callback is useful for testing purposes to execute arbitrary code before the
// chain sdk context is cleared in .Commit().
// For example, app.EndBlock may lead to a new state, which you would like to query
// to check that it is correct. However, the sdk context is cleared after .Commit(),
// so you can query the state inside the callback.
//
// NOTE: this method may be used independently of the rest of simibc.
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
			packet, _ := ibctestingcore.ReconstructPacketFromEvent(e)
			packets = append(packets, packet)
		}
	}

	return c.LastHeader, packets
}
