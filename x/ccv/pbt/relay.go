package pbt

import (
	"bytes"
	"fmt"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
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

func tryRelay(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet) (bool, error) {

	pc := sender.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(sender.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())

	if bytes.Equal(pc, channeltypes.CommitPacket(sender.Chain.App.AppCodec(), packet)) {

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

	}

	return false, nil

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
