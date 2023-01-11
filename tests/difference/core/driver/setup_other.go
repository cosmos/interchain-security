package core

import (
	"time"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctestingcore "github.com/cosmos/interchain-security/legacy_ibc_testing/core"
	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"
	simibc "github.com/cosmos/interchain-security/testutil/simibc"
	abci "github.com/tendermint/tendermint/abci/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

type BHelper struct {
	link           simibc.OrderedLink
	clientHeaders  map[string][]*ibctmtypes.Header
	mustBeginBlock map[string]bool
}

func createLink(b *Builder) *BHelper {
	bh := &BHelper{}
	bh.link = simibc.MakeOrderedLink()
	// init utility data structures
	bh.mustBeginBlock = map[string]bool{P: true, C: true}
	bh.clientHeaders = map[string][]*ibctmtypes.Header{}
	for chainID := range b.coordinator.Chains {
		bh.clientHeaders[chainID] = []*ibctmtypes.Header{}
	}
	return bh
}

// idempotentBeginBlock begins a new block on chain
// if it is necessary to do so.
func (b *Builder) idempotentBeginBlock(bh *BHelper, chain string) {
	if bh.mustBeginBlock[chain] {
		bh.mustBeginBlock[chain] = false
		b.beginBlock(bh, b.chainID(chain))
		b.updateClient(bh, b.chainID(chain))
	}
}

func (b *Builder) beginBlock(bh *BHelper, chainID string) {
	c := b.coordinator.GetChain(chainID)
	c.CurrentHeader = tmproto.Header{
		ChainID:            c.ChainID,
		Height:             c.App.LastBlockHeight() + 1,
		AppHash:            c.App.LastCommitID().Hash,
		Time:               b.coordinator.CurrentTime,
		ValidatorsHash:     c.Vals.Hash(),
		NextValidatorsHash: c.NextVals.Hash(),
	}
	_ = c.App.BeginBlock(abci.RequestBeginBlock{Header: c.CurrentHeader})
}

func (b *Builder) updateClient(bh *BHelper, chainID string) {
	for _, header := range bh.clientHeaders[b.otherID(chainID)] {
		err := simibc.UpdateReceiverClient(b.endpointFromID(b.otherID(chainID)), b.endpointFromID(chainID), header)
		if err != nil {
			b.coordinator.Fatal("updateClient")
		}
	}
	bh.clientHeaders[b.otherID(chainID)] = []*ibctmtypes.Header{}
}

func (b *Builder) deliver(bh *BHelper, chainID string) {
	packets := bh.link.ConsumePackets(b.otherID(chainID), 1)
	for _, p := range packets {
		receiver := b.endpointFromID(chainID)
		sender := receiver.Counterparty
		ack, err := simibc.TryRecvPacket(sender, receiver, p.Packet)
		if err != nil {
			b.coordinator.Fatal("deliver")
		}
		bh.link.AddAck(chainID, ack, p.Packet)
	}
}

func (b *Builder) deliverAcks(bh *BHelper, chainID string) {
	for _, ack := range bh.link.ConsumeAcks(b.otherID(chainID), 999999) {
		err := simibc.TryRecvAck(b.endpointFromID(b.otherID(chainID)), b.endpointFromID(chainID), ack.Packet, ack.Ack)
		if err != nil {
			b.coordinator.Fatal("deliverAcks")
		}
	}
}

func (b *Builder) endBlock(bh *BHelper, chainID string) {
	c := b.coordinator.GetChain(chainID)

	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})

	c.App.Commit()

	c.Vals = c.NextVals

	c.NextVals = ibctesting.ApplyValSetChanges(c.T, c.Vals, ebRes.ValidatorUpdates)

	c.LastHeader = c.CurrentTMClientHeader()
	// Store header to be used in UpdateClient
	bh.clientHeaders[chainID] = append(bh.clientHeaders[chainID], c.LastHeader)

	for _, e := range ebRes.Events {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, _ := ibctestingcore.ReconstructPacketFromEvent(e)
			// Collect packets
			bh.link.AddPacket(chainID, packet)
		}
	}

	// Commit packets emmitted up to this point
	bh.link.Commit(chainID)

	newT := b.coordinator.CurrentTime.Add(b.initState.BlockInterval).UTC()

	// increment the current header
	c.CurrentHeader = tmproto.Header{
		ChainID:            c.ChainID,
		Height:             c.App.LastBlockHeight() + 1,
		AppHash:            c.App.LastCommitID().Hash,
		Time:               newT,
		ValidatorsHash:     c.Vals.Hash(),
		NextValidatorsHash: c.NextVals.Hash(),
	}

	c.App.BeginBlock(abci.RequestBeginBlock{Header: c.CurrentHeader})
}

func (b *Builder) runSomeProtocolSteps() {

	// Create a simulated network link link
	bh := createLink(b)

	b.endBlock(bh, b.consumer().ChainID)
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(time.Second * time.Duration(1)).UTC()
	bh.mustBeginBlock[C] = true

	// Progress chains in unison, allowing first VSC to mature.
	for i := 0; i < 11; i++ {
		b.idempotentBeginBlock(bh, P)
		b.endBlock(bh, b.provider().ChainID)
		b.idempotentBeginBlock(bh, C)
		b.endBlock(bh, b.consumer().ChainID)
		bh.mustBeginBlock = map[string]bool{P: true, C: true}
		b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockInterval).UTC()
	}

	b.idempotentBeginBlock(bh, P)
	// Deliver outstanding ack
	b.deliverAcks(bh, b.provider().ChainID)
	// Deliver the maturity from the first VSC (needed to complete handshake)
	b.deliver(bh, b.provider().ChainID)

	for i := 0; i < 2; i++ {
		b.idempotentBeginBlock(bh, P)
		b.endBlock(bh, b.provider().ChainID)
		b.idempotentBeginBlock(bh, C)
		b.deliverAcks(bh, b.consumer().ChainID)
		b.endBlock(bh, b.consumer().ChainID)
		bh.mustBeginBlock = map[string]bool{P: true, C: true}
		b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockInterval).UTC()
	}

	b.idempotentBeginBlock(bh, P)
	b.idempotentBeginBlock(bh, C)

	b.endBlock(bh, b.provider().ChainID)
	b.endBlock(bh, b.consumer().ChainID)
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockInterval).UTC()
	b.beginBlock(bh, b.provider().ChainID)
	b.beginBlock(bh, b.consumer().ChainID)
	b.updateClient(bh, b.provider().ChainID)
	b.updateClient(bh, b.consumer().ChainID)
}
