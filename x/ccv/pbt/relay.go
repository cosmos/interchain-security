package pbt

import (
	"bytes"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	"github.com/cosmos/ibc-go/v3/modules/core/exported"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	"github.com/cosmos/ibc-go/v3/testing/simapp"
	"github.com/stretchr/testify/require"
)

// TODO: this is the original workings, delete when done with new version!
func tryRelayOriginalContent(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet) (bool, error) {

	receiver.UpdateClient()

	res, err := receiver.RecvPacketWithResult(packet)
	if err != nil {
		return false, err
	}

	ack, err := ibctesting.ParseAckFromEvents(res.GetEvents())
	if err != nil {
		return false, err
	}

	if err := sender.AcknowledgePacket(packet, ack); err != nil {
		return false, err
	}

	return true, nil
}

func tryRelay(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet) (succ bool, err error) {

	pc := sender.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(sender.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())

	if !bytes.Equal(pc, channeltypes.CommitPacket(sender.Chain.App.AppCodec(), packet)) {
		return false, nil
	}

	// return tryRelayOriginalContent(sender, receiver, packet)

	/*
		I think things can go like this
		ASSUMPTION: processing and UpdateClient Msg will not break anything if you do it
		as a 'middle' transaction in a block. I need this, because if I try...

		send an updateClient msg to receiver TODO: check what do with sequence numbers
		query packet proof on sender
		send a recvPacket msg to receiver and save the ack TODO: check what do with sequence numbers

		put the ack in a pendingAcks place
		when the receiver commits the next block make these acks 'visible' to the sender
		on the next opportunity in the sender, deliver any acknowledgements

	*/

	var header exported.Header

	switch receiver.ClientConfig.GetClientType() {
	case exported.Tendermint:
		header, err = receiver.Chain.ConstructUpdateTMClientHeader(receiver.Counterparty.Chain, receiver.ClientID)
	default:
		err = fmt.Errorf("client type %s is not supported", receiver.ClientConfig.GetClientType())
	}

	if err != nil {
		return false, err
	}

	UCmsg, err := clienttypes.NewMsgUpdateClient(
		receiver.ClientID, header,
		receiver.Chain.SenderAccount.GetAddress().String(),
	)
	require.NoError(receiver.Chain.T, err)

	_, _, err = simapp.SignAndDeliver(
		receiver.Chain.T,
		receiver.Chain.TxConfig,
		receiver.Chain.App.GetBaseApp(),
		receiver.Chain.GetContext().BlockHeader(),
		[]sdk.Msg{UCmsg},
		receiver.Chain.ChainID,
		[]uint64{receiver.Chain.SenderAccount.GetAccountNumber()},
		[]uint64{receiver.Chain.SenderAccount.GetSequence()},
		true, true, receiver.Chain.SenderPrivKey,
	)
	if err != nil {
		return false, err
	}

	// TODO: there used to be 'NextBlock' here...

	// increment sequence for successful transaction execution
	receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)

	packetKey := host.PacketCommitmentKey(packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())
	proof, proofHeight := sender.Chain.QueryProof(packetKey)

	RPmsg := channeltypes.NewMsgRecvPacket(packet, proof, proofHeight, receiver.Chain.SenderAccount.GetAddress().String())

	_, resWithAck, err := simapp.SignAndDeliver(
		receiver.Chain.T,
		receiver.Chain.TxConfig,
		receiver.Chain.App.GetBaseApp(),
		receiver.Chain.GetContext().BlockHeader(),
		[]sdk.Msg{RPmsg},
		receiver.Chain.ChainID,
		[]uint64{receiver.Chain.SenderAccount.GetAccountNumber()},
		[]uint64{receiver.Chain.SenderAccount.GetSequence()},
		true, true, receiver.Chain.SenderPrivKey,
	)

	if err != nil {
		return false, err
	}

	// TODO: there used to be 'NextBlock' here...

	// increment sequence for successful transaction execution
	receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)

	ack, err := ibctesting.ParseAckFromEvents(resWithAck.GetEvents())

	if err != nil {
		return false, err
	}

}

func RelayPacket(path *ibctesting.Path, packet channeltypes.Packet) error {
	sent, err := tryRelay(path.EndpointA, path.EndpointB, packet)
	if err != nil {
		return err
	}
	if sent {
		return nil
	}
	sent, err = tryRelay(path.EndpointB, path.EndpointA, packet)
	if err != nil {
		return err
	}
	if sent {
		return nil
	}
	return fmt.Errorf("packet commitment does not exist on either endpoint for provided packet")
}
