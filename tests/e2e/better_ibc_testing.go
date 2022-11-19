package e2e

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	channelkeeper "github.com/cosmos/ibc-go/v3/modules/core/04-channel/keeper"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	"github.com/cosmos/ibc-go/v3/testing/simapp"
	abci "github.com/tendermint/tendermint/abci/types"
)

// TODO: consolidate this stuff with /simibc directory. It's hacky as is

// This file contains hacky, more useful versions of specific ibc testing functions,
// which work for multiple consumers.

func GetSentPacketsFromEvents(suite *CCVTestSuite, events []abci.Event) []channeltypes.Packet {
	packets := []channeltypes.Packet{}
	for _, event := range events {
		if event.Type == channeltypes.EventTypeSendPacket {
			packet, err := channelkeeper.ReconstructPacketFromEvent(event)
			suite.Require().NoError(err)
			packets = append(packets, packet)
		}
	}
	return packets
}

func RecvPacketGetEvents(endpoint *ibctesting.Endpoint,
	packet channeltypes.Packet) ([]abci.Event, error) {

	// get proof of packet commitment on source
	packetKey := host.PacketCommitmentKey(packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())
	proof, proofHeight := endpoint.Counterparty.Chain.QueryProof(packetKey)

	recvMsg := channeltypes.NewMsgRecvPacket(packet, proof, proofHeight, endpoint.Chain.SenderAccount.GetAddress().String())

	// receive on counterparty and update source client
	events, err := SendMsgsGetEvents(endpoint.Chain, recvMsg)
	if err != nil {
		return []abci.Event{}, err
	}

	if err := endpoint.Counterparty.UpdateClient(); err != nil {
		return []abci.Event{}, err
	}

	return events, nil
}

func SendMsgsGetEvents(chain *ibctesting.TestChain, msgs ...sdk.Msg) ([]abci.Event, error) {
	// ensure the chain has the latest time
	chain.Coordinator.UpdateTimeForChain(chain)

	_, result, err := simapp.SignAndDeliver(
		chain.T,
		chain.TxConfig,
		chain.App.GetBaseApp(),
		chain.GetContext().BlockHeader(),
		msgs,
		chain.ChainID,
		[]uint64{chain.SenderAccount.GetAccountNumber()},
		[]uint64{chain.SenderAccount.GetSequence()},
		true, true, chain.SenderPrivKey,
	)
	if err != nil {
		return []abci.Event{}, err
	}

	// NextBlock calls app.Commit()
	ebRes, _, bbRes := chain.NextBlock()

	// Gather events
	events := append(ebRes.Events, bbRes.Events...)
	events = append(events, result.Events...)

	// increment sequence for successful transaction execution
	chain.SenderAccount.SetSequence(chain.SenderAccount.GetSequence() + 1)

	chain.Coordinator.IncrementTime()

	return events, nil
}
