package ibcsim

import (
	"time"

	"testing"

	channelkeeper "github.com/cosmos/ibc-go/v3/modules/core/04-channel/keeper"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	abci "github.com/tendermint/tendermint/abci/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

type Framework struct {
	T    *testing.T
	Link Link
	path *ibctesting.Path
	// chain -> array of headers for UpdateClient
	clientHeaders map[string][]*ibctmtypes.Header
	Chains        map[string]*ibctesting.TestChain // TODO: uncaps
}

func MakeFramework(t *testing.T, chains map[string]*ibctesting.TestChain, path *ibctesting.Path) Framework {
	trueTime := map[string]time.Time{}
	for id, c := range chains {
		trueTime[id] = c.CurrentHeader.Time
	}
	return Framework{
		T:             t,
		Link:          MakeLink(),
		Chains:        chains,
		clientHeaders: map[string][]*ibctmtypes.Header{},
		path:          path,
	}
}

// TODO: right now framework assumes exactly 2 chains
func (f *Framework) other(chainID string) string {
	for k := range f.Chains {
		if k != chainID {
			return k
		}
	}
	f.T.Fatal("other")
	return ""
}

func (f *Framework) endpoint(chainID string) *ibctesting.Endpoint {
	// TODO: this is hardcoded for interchain security use case!
	if chainID == ibctesting.GetChainID(0) {
		return f.path.EndpointB
	}
	if chainID == ibctesting.GetChainID(1) {
		return f.path.EndpointA
	}
	f.T.Fatal("endpoint")
	return nil
}

// UpdateClient will bring the client on chain
// up to date by delivering each header committed on the
// counterparty chain since the last idempotentUpdateClient
func (f *Framework) UpdateClient(chainID string) {
	for _, header := range f.clientHeaders[f.other(chainID)] {
		err := UpdateReceiverClient(f.endpoint(f.other(chainID)), f.endpoint(chainID), header)
		if err != nil {
			f.T.Fatal("UpdateClient")
		}
	}
	f.clientHeaders[f.other(chainID)] = []*ibctmtypes.Header{}
}

// deliver numPackets packets from the network to chain
func (f *Framework) DeliverPackets(chainID string, numPackets int64) {
	// Consume deliverable packets from the network
	packets := f.Link.ConsumePackets(f.other(chainID), numPackets)
	for _, p := range packets {
		receiver := f.endpoint(chainID)
		sender := receiver.Counterparty
		ack, err := TryRecvPacket(sender, receiver, p.Packet)
		if err != nil {
			f.T.Fatal("deliver")
		}
		f.Link.AddAck(chainID, ack, p.Packet)
	}
}

// DeliverAcks will deliver any acks available on the network
// which have been emitted by the counterparty chain since the last
// call to DeliverAcks
func (f *Framework) DeliverAcks(chainID string) {
	for _, ack := range f.Link.ConsumeAcks(f.other(chainID)) {
		f.UpdateClient(chainID) // TODO: remove!
		err := TryRecvAck(f.endpoint(f.other(chainID)), f.endpoint(chainID), ack.Packet, ack.Ack)
		if err != nil {
			f.T.Fatal("deliverAcks")
		}
	}
}

func (f *Framework) EndAndBeginBlock(chainID string, dt time.Duration, preCommitCallback func()) {
	c := f.Chains[chainID]

	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})

	preCommitCallback()

	c.App.Commit()

	c.Vals = c.NextVals

	c.NextVals = ibctesting.ApplyValSetChanges(c.T, c.Vals, ebRes.ValidatorUpdates)

	c.LastHeader = c.CurrentTMClientHeader()
	// Store header to be used in UpdateClient
	f.clientHeaders[chainID] = append(f.clientHeaders[chainID], c.LastHeader)

	for _, e := range ebRes.Events {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, _ := channelkeeper.ReconstructPacketFromEvent(e)
			// Collect packets
			f.Link.AddPacket(chainID, packet)
		}
	}

	// Commit packets emmitted up to this point
	f.Link.Commit(chainID)

	// increment the current header
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
