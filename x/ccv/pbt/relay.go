package pbt

import (
	"bytes"
	"fmt"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
)

func RelayPacket(path *ibctesting.Path, packet channeltypes.Packet) error {
	pc := path.EndpointA.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(path.EndpointA.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())
	if bytes.Equal(pc, channeltypes.CommitPacket(path.EndpointA.Chain.App.AppCodec(), packet)) {

		// packet found, relay from A to B
		path.EndpointB.UpdateClient()

		res, err := path.EndpointB.RecvPacketWithResult(packet)
		if err != nil {
			return err
		}

		ack, err := ibctesting.ParseAckFromEvents(res.GetEvents())
		if err != nil {
			return err
		}

		if err := path.EndpointA.AcknowledgePacket(packet, ack); err != nil {
			return err
		}
		return nil

	}

	pc = path.EndpointB.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(path.EndpointB.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())
	if bytes.Equal(pc, channeltypes.CommitPacket(path.EndpointB.Chain.App.AppCodec(), packet)) {

		// packet found, relay B to A
		path.EndpointA.UpdateClient()

		res, err := path.EndpointA.RecvPacketWithResult(packet)
		if err != nil {
			return err
		}

		ack, err := ibctesting.ParseAckFromEvents(res.GetEvents())
		if err != nil {
			return err
		}

		if err := path.EndpointB.AcknowledgePacket(packet, ack); err != nil {
			return err
		}
		return nil
	}

	return fmt.Errorf("packet commitment does not exist on either endpoint for provided packet")
}
