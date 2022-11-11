package simibc

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

// RelayedPath augments ibctesting.Path, giving fine-grained control
// over delivery of client updates, packet and ack delivery, and
// chain time and height progression.
type RelayedPath struct {
	t             *testing.T
	path          *ibctesting.Path
	clientHeaders map[string][]*ibctmtypes.Header
	Link          OrderedLink
}

// MakeRelayedPath returns an initialized RelayedPath
func MakeRelayedPath(t *testing.T, path *ibctesting.Path) RelayedPath {
	return RelayedPath{
		t:             t,
		clientHeaders: map[string][]*ibctmtypes.Header{},
		path:          path,
		Link:          MakeOrderedLink(),
	}
}

// Chain returns the chain with ChainID <chainID>
func (f *RelayedPath) Chain(chainID string) *ibctesting.TestChain {
	if f.path.EndpointA.Chain.ChainID == chainID {
		return f.path.EndpointA.Chain
	}
	if f.path.EndpointB.Chain.ChainID == chainID {
		return f.path.EndpointB.Chain
	}
	f.t.Fatal("chain")
	return nil
}

// UpdateClient will update the chain light client with
// each header added to the counterparty chain since the last
// call.
func (f *RelayedPath) UpdateClient(chainID string) {
	for _, header := range f.clientHeaders[f.other(chainID)] {
		err := UpdateReceiverClient(f.endpoint(f.other(chainID)), f.endpoint(chainID), header)
		if err != nil {
			f.t.Fatal("UpdateClient")
		}
	}
	f.clientHeaders[f.other(chainID)] = []*ibctmtypes.Header{}
}

// DeliverPackets delivers <num> packets to chain
// A real relayer will relay packets from one chain to another chain
// in two steps. First it will observe sufficiently committed outbound
// packets on the sender chain. Second, it will submit transactions
// containing those packets to the receiver chain.
// This method simulates the second step: sufficiently committed
// packets that have been already added to the OrderedLink will be
// delivered. It is necessary to add outbound packets to the link
// separately.
func (f *RelayedPath) DeliverPackets(chainID string, num int) {
	for _, p := range f.Link.ConsumePackets(f.other(chainID), num) {
		ack, err := TryRecvPacket(f.endpoint(f.other(chainID)), f.endpoint(chainID), p.Packet)
		if err != nil {
			f.t.Fatal("deliver")
		}
		f.Link.AddAck(chainID, ack, p.Packet)
	}
}

// DeliverAcks delivers <num> acks to chain
func (f *RelayedPath) DeliverAcks(chainID string, num int) {
	for _, ack := range f.Link.ConsumeAcks(f.other(chainID), num) {
		err := TryRecvAck(f.endpoint(f.other(chainID)), f.endpoint(chainID), ack.Packet, ack.Ack)
		if err != nil {
			f.t.Fatal("deliverAcks")
		}
	}
}

// EndAndBeginBlock calls EndBlock and commits block state, and then increments time and calls
// BeginBlock, for the chain. preCommitCallback is called after EndBlock and before Commit,
// allowing access to the sdk.Context after EndBlock.
func (f *RelayedPath) EndAndBeginBlock(chainID string, dt time.Duration, preCommitCallback func()) {
	c := f.Chain(chainID)

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

func (f *RelayedPath) other(chainID string) string {
	if f.path.EndpointA.Chain.ChainID == chainID {
		return f.path.EndpointB.Chain.ChainID
	}
	if f.path.EndpointB.Chain.ChainID == chainID {
		return f.path.EndpointA.Chain.ChainID
	}
	f.t.Fatal("other")
	return ""
}

func (f *RelayedPath) endpoint(chainID string) *ibctesting.Endpoint {
	if chainID == f.path.EndpointA.Chain.ChainID {
		return f.path.EndpointA
	}
	if chainID == f.path.EndpointB.Chain.ChainID {
		return f.path.EndpointB
	}
	f.t.Fatal("endpoint")
	return nil
}
