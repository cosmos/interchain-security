package pbt

import (
	"bytes"
	"fmt"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
)

func tryRelay(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet) error {

	pc := sender.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(sender.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())

	if bytes.Equal(pc, channeltypes.CommitPacket(sender.Chain.App.AppCodec(), packet)) {

		receiver.UpdateClient()

		res, err := receiver.RecvPacketWithResult(packet)
		if err != nil {
			return err
		}

		ack, err := ibctesting.ParseAckFromEvents(res.GetEvents())
		if err != nil {
			return err
		}

		if err := sender.AcknowledgePacket(packet, ack); err != nil {
			return err
		}

	}

	return nil

}

func RelayPacket(path *ibctesting.Path, packet channeltypes.Packet) error {
	err := tryRelay(path.EndpointA, path.EndpointB, packet)
	if err != nil {
		return err
	}
	err = tryRelay(path.EndpointB, path.EndpointA, packet)
	if err != nil {
		return err
	}
	return fmt.Errorf("packet commitment does not exist on either endpoint for provided packet")
}
