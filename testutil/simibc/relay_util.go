package simibc

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	"github.com/cosmos/ibc-go/v3/testing/simapp"
	"github.com/stretchr/testify/require"
	tmtypes "github.com/tendermint/tendermint/types"
)

// UpdateReceiverClient is used to send a header to the receiving endpoint and update
// the client of the respective chain.
func UpdateReceiverClient(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, header *ibctmtypes.Header) (err error) {

	header, err = constructTMHeader(receiver.Chain, header, sender.Chain, receiver.ClientID, clienttypes.ZeroHeight())

	if err != nil {
		return err
	}

	msg, err := clienttypes.NewMsgUpdateClient(
		receiver.ClientID, header,
		receiver.Chain.SenderAccount.GetAddress().String(),
	)

	require.NoError(receiver.Chain.T, err)

	_, _, err = simapp.SignAndDeliver(
		receiver.Chain.T,
		receiver.Chain.TxConfig,
		receiver.Chain.App.GetBaseApp(),
		receiver.Chain.GetContext().BlockHeader(),
		[]sdk.Msg{msg},
		receiver.Chain.ChainID,
		[]uint64{receiver.Chain.SenderAccount.GetAccountNumber()},
		[]uint64{receiver.Chain.SenderAccount.GetSequence()},
		true, true, receiver.Chain.SenderPrivKey,
	)

	if err != nil {
		return err
	}

	err = receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)

	if err != nil {
		return err
	}

	return nil
}

// Try to receive a packet on receiver. Returns ack.
func TryRecvPacket(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet) (ack []byte, err error) {
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

	err = receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)

	if err != nil {
		return nil, err
	}

	ack, err = ibctesting.ParseAckFromEvents(resWithAck.GetEvents())

	if err != nil {
		return nil, err
	}

	return ack, nil
}

// Try to receive an ack on receiver.
func TryRecvAck(sender *ibctesting.Endpoint, receiver *ibctesting.Endpoint, packet channeltypes.Packet, ack []byte) (err error) {
	p := packet
	packetKey := host.PacketAcknowledgementKey(p.GetDestPort(), p.GetDestChannel(), p.GetSequence())
	proof, proofHeight := sender.Chain.QueryProof(packetKey)

	ackMsg := channeltypes.NewMsgAcknowledgement(p, ack, proof, proofHeight, receiver.Chain.SenderAccount.GetAddress().String())

	_, _, err = simapp.SignAndDeliver(
		receiver.Chain.T,
		receiver.Chain.TxConfig,
		receiver.Chain.App.GetBaseApp(),
		receiver.Chain.GetContext().BlockHeader(),
		[]sdk.Msg{ackMsg},
		receiver.Chain.ChainID,
		[]uint64{receiver.Chain.SenderAccount.GetAccountNumber()},
		[]uint64{receiver.Chain.SenderAccount.GetSequence()},
		true, true, receiver.Chain.SenderPrivKey,
	)

	if err != nil {
		return err
	}

	err = receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)

	if err != nil {
		return err
	}

	return nil
}

// constructTMHeader will augment a valid 07-tendermint Header with data needed to update
// light client.
func constructTMHeader(chain *ibctesting.TestChain, header *ibctmtypes.Header, counterparty *ibctesting.TestChain, clientID string, trustedHeight clienttypes.Height) (*ibctmtypes.Header, error) {
	// Relayer must query for LatestHeight on client to get TrustedHeight if the trusted height is not set
	if trustedHeight.IsZero() {
		trustedHeight = chain.GetClientState(clientID).GetLatestHeight().(clienttypes.Height)
	}
	var (
		tmTrustedVals *tmtypes.ValidatorSet
		ok            bool
	)
	// Once we get TrustedHeight from client, we must query the validators from the counterparty chain
	// If the LatestHeight == LastHeader.Height, then TrustedValidators are current validators
	// If LatestHeight < LastHeader.Height, we can query the historical validator set from HistoricalInfo
	if trustedHeight == counterparty.LastHeader.GetHeight() {
		tmTrustedVals = counterparty.Vals
	} else {
		// NOTE: We need to get validators from counterparty at height: trustedHeight+1
		// since the last trusted validators for a header at height h
		// is the NextValidators at h+1 committed to in header h by
		// NextValidatorsHash
		tmTrustedVals, ok = counterparty.GetValsAtHeight(int64(trustedHeight.RevisionHeight + 1))
		if !ok {
			return nil, sdkerrors.Wrapf(ibctmtypes.ErrInvalidHeaderHeight, "could not retrieve trusted validators at trustedHeight: %d", trustedHeight)
		}
	}
	// inject trusted fields into last header
	// for now assume revision number is 0
	header.TrustedHeight = trustedHeight

	trustedVals, err := tmTrustedVals.ToProto()
	if err != nil {
		return nil, err
	}
	header.TrustedValidators = trustedVals

	return header, nil
}
