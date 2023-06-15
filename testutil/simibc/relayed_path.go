package simibc

import (
	"testing"
	"time"

	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"

	ibctesting "github.com/octopus-network/interchain-security/legacy_ibc_testing/testing"
)

// RelayedPath is a wrapper around ibctesting.Path gives fine-grained
// control over delivery packets and acks, and client updates. Specifically,
// the path represents a bidirectional ORDERED channel between two chains.
// It is possible to control the precise order that packets and acks are
// delivered, and the precise independent and relative order and timing of
// new blocks on each chain.
type RelayedPath struct {
	t    *testing.T
	path *ibctesting.Path
	// clientHeaders is a map from chainID to an ordered list of headers that
	// have been committed to that chain. The headers are used to update the
	// client of the counterparty chain.
	clientHeaders map[string][]*ibctmtypes.Header
	// TODO: Make this private and expose methods to add packets and acks.
	//       Currently, packets and acks are added directly to the outboxes,
	//       but we should hide this implementation detail.
	Outboxes OrderedOutbox
}

// MakeRelayedPath returns an initialized RelayedPath without any
// packets, acks or headers. Requires a fully initialised path where
// the connection and any channel handshakes have been COMPLETED.
func MakeRelayedPath(t *testing.T, path *ibctesting.Path) RelayedPath {
	t.Helper()
	return RelayedPath{
		t:             t,
		clientHeaders: map[string][]*ibctmtypes.Header{},
		path:          path,
		Outboxes:      MakeOrderedOutbox(),
	}
}

// Chain returns the chain with chainID
func (f *RelayedPath) Chain(chainID string) *ibctesting.TestChain {
	if f.path.EndpointA.Chain.ChainID == chainID {
		return f.path.EndpointA.Chain
	}
	if f.path.EndpointB.Chain.ChainID == chainID {
		return f.path.EndpointB.Chain
	}
	f.t.Fatal("no chain found in relayed path with chainID: ", chainID)
	return nil
}

// UpdateClient updates the chain with the latest sequence
// of available headers committed by the counterparty chain since
// the last call to UpdateClient (or all for the first call).
func (f *RelayedPath) UpdateClient(chainID string) {
	for _, header := range f.clientHeaders[f.counterparty(chainID)] {
		err := UpdateReceiverClient(f.endpoint(f.counterparty(chainID)), f.endpoint(chainID), header)
		if err != nil {
			f.t.Fatal("in relayed path could not update client of chain: ", chainID, " with header: ", header, " err: ", err)
		}
	}
	f.clientHeaders[f.counterparty(chainID)] = []*ibctmtypes.Header{}
}

// DeliverPackets delivers UP TO <num> packets to the chain which have been
// sent to it by the counterparty chain and are ready to be delivered.
//
// A packet is ready to be delivered if the sender chain has progressed
// a sufficient number of blocks since the packet was sent. This is because
// all sent packets must be committed to block state before they can be queried.
// Additionally, in practice, light clients require a header (h+1) to deliver a
// packet sent in header h.
//
// In order to deliver packets, the chain must have an up-to-date client
// of the counterparty chain. Ie. UpdateClient should be called before this.
func (f *RelayedPath) DeliverPackets(chainID string, num int) {
	for _, p := range f.Outboxes.ConsumePackets(f.counterparty(chainID), num) {
		ack, err := TryRecvPacket(f.endpoint(f.counterparty(chainID)), f.endpoint(chainID), p.Packet)
		if err != nil {
			f.t.Fatal("deliver")
		}
		f.Outboxes.AddAck(chainID, ack, p.Packet)
	}
}

// DeliverPackets delivers UP TO <num> acks to the chain which have been
// sent to it by the counterparty chain and are ready to be delivered.
//
// An ack is ready to be delivered if the sender chain has progressed
// a sufficient number of blocks since the ack was sent. This is because
// all sent acks must be committed to block state before they can be queried.
// Additionally, in practice, light clients require a header (h+1) to deliver
// an ack sent in header h.
//
// In order to deliver acks, the chain must have an up-to-date client
// of the counterparty chain. Ie. UpdateClient should be called before this.
func (f *RelayedPath) DeliverAcks(chainID string, num int) {
	for _, ack := range f.Outboxes.ConsumeAcks(f.counterparty(chainID), num) {
		err := TryRecvAck(f.endpoint(f.counterparty(chainID)), f.endpoint(chainID), ack.Packet, ack.Ack)
		if err != nil {
			f.t.Fatal("deliverAcks")
		}
	}
}

// EndAndBeginBlock calls EndBlock and commits block state, storing the header which can later
// be used to update the client on the counterparty chain. After committing, the chain local
// time progresses by dt, and BeginBlock is called with a header timestamped for the new time.
//
// preCommitCallback is called after EndBlock and before Commit, allowing arbitrary access to
// the sdk.Context after EndBlock. The callback is useful for testing purposes to execute
// arbitrary code before the chain sdk context is cleared in .Commit().
// For example, app.EndBlock may lead to a new state, which you would like to query
// to check that it is correct. However, the sdk context is cleared after .Commit(),
// so you can query the state inside the callback.
func (f *RelayedPath) EndAndBeginBlock(chainID string, dt time.Duration, preCommitCallback func()) {
	c := f.Chain(chainID)

	header, packets := EndBlock(c, preCommitCallback)
	f.clientHeaders[chainID] = append(f.clientHeaders[chainID], header)
	for _, p := range packets {
		f.Outboxes.AddPacket(chainID, p)
	}
	f.Outboxes.Commit(chainID)
	BeginBlock(c, dt)
}

// counterparty is a helper returning the counterparty chainID
func (f *RelayedPath) counterparty(chainID string) string {
	if f.path.EndpointA.Chain.ChainID == chainID {
		return f.path.EndpointB.Chain.ChainID
	}
	if f.path.EndpointB.Chain.ChainID == chainID {
		return f.path.EndpointA.Chain.ChainID
	}
	f.t.Fatal("no chain found in relayed path with chainID: ", chainID)
	return ""
}

// endpoint is a helper returning the endpoint for the chain
func (f *RelayedPath) endpoint(chainID string) *ibctesting.Endpoint {
	if chainID == f.path.EndpointA.Chain.ChainID {
		return f.path.EndpointA
	}
	if chainID == f.path.EndpointB.Chain.ChainID {
		return f.path.EndpointB
	}
	f.t.Fatal("no chain found in relayed path with chainID: ", chainID)
	return nil
}
