package difftest

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

func updateReceiverClient(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint) (err error) {
	var header exported.Header

	switch receiver.ClientConfig.GetClientType() {
	case exported.Tendermint:
		header, err = receiver.Chain.ConstructUpdateTMClientHeader(sender.Chain, receiver.ClientID)
	default:
		err = fmt.Errorf("client type %s is not supported", receiver.ClientConfig.GetClientType())
	}

	if err != nil {
		return err
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
		return err
	}

	// TODO: there used to be 'receiver.NextBlock' here...

	// increment sequence for successful transaction execution
	receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)

	return nil
}

func deliverPacket(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet) (ack []byte, err error) {
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
		return nil, err
	}

	// TODO: there used to be 'NextBlock' here...

	// increment sequence for successful transaction execution
	receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)

	ack, err = ibctesting.ParseAckFromEvents(resWithAck.GetEvents())

	if err != nil {
		return nil, err
	}

	return ack, nil
}

func TryRelay(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet) (ack []byte, err error) {

	//~~~~~~~
	// TODO: I've added these lines here to help me debug
	// while using the extra BeginBlocker hack
	pc := sender.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(sender.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())

	if !bytes.Equal(pc, channeltypes.CommitPacket(sender.Chain.App.AppCodec(), packet)) {
		return nil, fmt.Errorf("packet committment bytes not equal")
	}
	//~~~~~~~

	err = updateReceiverClient(sender, receiver)

	if err != nil {
		return nil, err
	}

	ack, err = deliverPacket(sender, receiver, packet)

	if err != nil {
		return nil, err
	}

	return ack, nil

}
