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

func (b *Builder) createLink() {
	b.link = simibc.MakeOrderedLink()
	// init utility data structures
	b.mustBeginBlock = map[string]bool{P: true, C: true}
	b.clientHeaders = map[string][]*ibctmtypes.Header{}
	for chainID := range b.coordinator.Chains {
		b.clientHeaders[chainID] = []*ibctmtypes.Header{}
	}
}

// idempotentBeginBlock begins a new block on chain
// if it is necessary to do so.
func (b *Builder) idempotentBeginBlock(chain string) {
	if b.mustBeginBlock[chain] {
		b.mustBeginBlock[chain] = false
		b.beginBlock(b.chainID(chain))
		b.updateClient(b.chainID(chain))
	}
}

func (b *Builder) beginBlock(chainID string) {
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

func (b *Builder) updateClient(chainID string) {
	for _, header := range b.clientHeaders[b.otherID(chainID)] {
		err := simibc.UpdateReceiverClient(b.endpointFromID(b.otherID(chainID)), b.endpointFromID(chainID), header)
		if err != nil {
			b.coordinator.Fatal("updateClient")
		}
	}
	b.clientHeaders[b.otherID(chainID)] = []*ibctmtypes.Header{}
}

func (b *Builder) deliver(chainID string) {
	packets := b.link.ConsumePackets(b.otherID(chainID), 1)
	for _, p := range packets {
		receiver := b.endpointFromID(chainID)
		sender := receiver.Counterparty
		ack, err := simibc.TryRecvPacket(sender, receiver, p.Packet)
		if err != nil {
			b.coordinator.Fatal("deliver")
		}
		b.link.AddAck(chainID, ack, p.Packet)
	}
}

func (b *Builder) deliverAcks(chainID string) {
	for _, ack := range b.link.ConsumeAcks(b.otherID(chainID), 999999) {
		err := simibc.TryRecvAck(b.endpointFromID(b.otherID(chainID)), b.endpointFromID(chainID), ack.Packet, ack.Ack)
		if err != nil {
			b.coordinator.Fatal("deliverAcks")
		}
	}
}

func (b *Builder) endBlock(chainID string) {
	c := b.coordinator.GetChain(chainID)

	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})

	c.App.Commit()

	c.Vals = c.NextVals

	c.NextVals = ibctesting.ApplyValSetChanges(c.T, c.Vals, ebRes.ValidatorUpdates)

	c.LastHeader = c.CurrentTMClientHeader()
	// Store header to be used in UpdateClient
	b.clientHeaders[chainID] = append(b.clientHeaders[chainID], c.LastHeader)

	for _, e := range ebRes.Events {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, _ := ibctestingcore.ReconstructPacketFromEvent(e)
			// Collect packets
			b.link.AddPacket(chainID, packet)
		}
	}

	// Commit packets emmitted up to this point
	b.link.Commit(chainID)

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

	b.endBlock(b.consumer().ChainID)
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(time.Second * time.Duration(1)).UTC()
	b.mustBeginBlock[C] = true

	// Progress chains in unison, allowing first VSC to mature.
	for i := 0; i < 11; i++ {
		b.idempotentBeginBlock(P)
		b.endBlock(b.provider().ChainID)
		b.idempotentBeginBlock(C)
		b.endBlock(b.consumer().ChainID)
		b.mustBeginBlock = map[string]bool{P: true, C: true}
		b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockInterval).UTC()
	}

	b.idempotentBeginBlock(P)
	// Deliver outstanding ack
	b.deliverAcks(b.provider().ChainID)
	// Deliver the maturity from the first VSC (needed to complete handshake)
	b.deliver(b.provider().ChainID)

	for i := 0; i < 2; i++ {
		b.idempotentBeginBlock(P)
		b.endBlock(b.provider().ChainID)
		b.idempotentBeginBlock(C)
		b.deliverAcks(b.consumer().ChainID)
		b.endBlock(b.consumer().ChainID)
		b.mustBeginBlock = map[string]bool{P: true, C: true}
		b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockInterval).UTC()
	}

	b.idempotentBeginBlock(P)
	b.idempotentBeginBlock(C)

	b.endBlock(b.provider().ChainID)
	b.endBlock(b.consumer().ChainID)
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockInterval).UTC()
	b.beginBlock(b.provider().ChainID)
	b.beginBlock(b.consumer().ChainID)
	b.updateClient(b.provider().ChainID)
	b.updateClient(b.consumer().ChainID)
}
