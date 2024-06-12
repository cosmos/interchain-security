package simibc

import (
	"fmt"
	"time"

	cmtproto "github.com/cometbft/cometbft/proto/tendermint/types"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v8/modules/core/24-host"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	simapp "github.com/cosmos/ibc-go/v8/testing/simapp"

	abci "github.com/cometbft/cometbft/abci/types"
	cmttypes "github.com/cometbft/cometbft/types"
	ibctm "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	sdk "github.com/cosmos/cosmos-sdk/types"
)

// UpdateReceiverClient DELIVERs a header to the receiving endpoint
// and update the respective client of the receiving chain.
//
// The header is a header of the sender chain. The receiver chain
// must have a client of the sender chain that it can update.
//
// NOTE: this function MAY be used independently of the rest of simibc.
func UpdateReceiverClient(sender, receiver *ibctesting.Endpoint, header *ibctmtypes.Header, expectExpiration bool) (err error) {

	err = augmentHeader(sender.Chain, receiver.Chain, receiver.ClientID, header)
	if err != nil {
		return err
	}

	msg, err := clienttypes.NewMsgUpdateClient(
		receiver.ClientID, header,
		receiver.Chain.SenderAccount.GetAddress().String(),
	)
	if err != nil {
		return err
	}

	chain := receiver.Chain
	res, err := simapp.SignAndDeliver(
		chain.TB,
		chain.TxConfig,
		chain.App.GetBaseApp(),
		[]sdk.Msg{msg},
		chain.ChainID,
		[]uint64{chain.SenderAccount.GetAccountNumber()},
		[]uint64{chain.SenderAccount.GetSequence()},
		true,
		chain.CurrentHeader.GetTime(),
		chain.NextVals.Hash(),
		chain.SenderPrivKey,
	)
	if err != nil {
		return err
	}

	err = commitBlock(chain, 1*time.Nanosecond, res)
	if err != nil {
		return err
	}

	if len(res.TxResults) != 1 {
		return fmt.Errorf("expected a tx result")

	}

	txResult := res.TxResults[0]

	if txResult.Code != 0 {
		return fmt.Errorf("%s/%d: %q", txResult.Codespace, txResult.Code, txResult.Log)
	}

	setSequenceErr := receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)
	if setSequenceErr != nil {
		return setSequenceErr
	}

	return nil
}

// TryRecvPacket will try once to DELIVER a packet from sender to receiver. If successful,
// it will return the acknowledgement bytes.
//
// The packet must be sent from the sender chain to the receiver chain, and the
// receiver chain must have a client for the sender chain which has been updated
// to a recent height of the sender chain so that it can verify the packet.
func TryRecvPacket(sender, receiver *ibctesting.Endpoint, packet channeltypes.Packet, expectError bool) (ack []byte, err error) {
	packetKey := host.PacketCommitmentKey(packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())
	proof, proofHeight := sender.Chain.QueryProof(packetKey)

	RPmsg := channeltypes.NewMsgRecvPacket(packet, proof, proofHeight, receiver.Chain.SenderAccount.GetAddress().String())

	resWithAck, err := simapp.SignAndDeliver(
		receiver.Chain.TB,
		receiver.Chain.TxConfig,
		receiver.Chain.App.GetBaseApp(),
		[]sdk.Msg{RPmsg},
		receiver.Chain.ChainID,
		[]uint64{receiver.Chain.SenderAccount.GetAccountNumber()},
		[]uint64{receiver.Chain.SenderAccount.GetSequence()},
		!expectError,
		receiver.Chain.GetContext().BlockHeader().Time,
		receiver.Chain.GetContext().BlockHeader().NextValidatorsHash,
		receiver.Chain.SenderPrivKey,
	)
	if err != nil {
		return nil, err
	}

	// TODO: check if a commit is needed here

	for _, res := range resWithAck.TxResults {
		res := res
		if res.Code != 0 {
			return nil, fmt.Errorf("%s/%d: %q", res.Codespace, res.Code, res.Log)
		}
	}

	if len(resWithAck.TxResults) != 1 {
		return nil, fmt.Errorf("expected a tx result")
	}

	ack, err = ibctesting.ParseAckFromEvents(resWithAck.TxResults[0].GetEvents())
	if err != nil {
		return nil, err
	}

	// need to set the sequence even if there was an error in delivery
	setSequenceErr := receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)
	if setSequenceErr != nil {
		return nil, setSequenceErr
	}

	return ack, nil
}

// TryRecvAck will try once to DELIVER an ack from sender to receiver.
//
// The ack must have been sent from the sender to the receiver, in response
// to packet which was previously delivered from the receiver to the sender.
// The receiver chain must have a client for the sender chain which has been
// updated to a recent height of the sender chain so that it can verify the packet.
func TryRecvAck(sender, receiver *ibctesting.Endpoint, packet channeltypes.Packet, ack []byte) (err error) {
	p := packet
	packetKey := host.PacketAcknowledgementKey(p.GetDestPort(), p.GetDestChannel(), p.GetSequence())
	proof, proofHeight := sender.Chain.QueryProof(packetKey)

	ackMsg := channeltypes.NewMsgAcknowledgement(p, ack, proof, proofHeight, receiver.Chain.SenderAccount.GetAddress().String())

	chain := receiver.Chain
	res, err := simapp.SignAndDeliver(
		chain.TB,
		chain.TxConfig,
		chain.App.GetBaseApp(),
		[]sdk.Msg{ackMsg},
		chain.ChainID,
		[]uint64{chain.SenderAccount.GetAccountNumber()},
		[]uint64{chain.SenderAccount.GetSequence()},
		true,
		chain.GetContext().BlockHeader().Time,
		chain.GetContext().BlockHeader().NextValidatorsHash,
		chain.SenderPrivKey,
	)
	if err != nil {
		return err
	}

	// TODO: check if a commit is needed here

	if len(res.TxResults) != 1 {
		return fmt.Errorf("expected a tx result")
	}

	txResult := res.TxResults[0]

	if txResult.Code != 0 {
		return fmt.Errorf("%s/%d: %q", txResult.Codespace, txResult.Code, txResult.Log)
	}

	setSequenceErr := receiver.Chain.SenderAccount.SetSequence(receiver.Chain.SenderAccount.GetSequence() + 1)
	if err != nil {
		return err
	}

	if setSequenceErr != nil {
		return setSequenceErr
	}

	return nil
}

// augmentHeader is a helper that augments the header with the height and validators that are most recently trusted
// by the receiver chain. If there is an error, the header will not be modified.
// Note that its duplicates the ConstructUpdateTMClientHeaderWithTrustedHeight behaviour from ibc testing
func augmentHeader(sender, receiver *ibctesting.TestChain, clientID string, header *ibctmtypes.Header) error {
	trustedHeight := receiver.GetClientState(clientID).GetLatestHeight().(clienttypes.Height)

	// Relayer must query for LatestHeight on client to get TrustedHeight if the trusted height is not set
	if trustedHeight.IsZero() {
		trustedHeight = receiver.GetClientState(clientID).GetLatestHeight().(clienttypes.Height)
	}
	var (
		tmTrustedVals *cmttypes.ValidatorSet
		ok            bool
	)

	tmTrustedVals, ok = sender.GetValsAtHeight(int64(trustedHeight.RevisionHeight))
	if !ok {
		return fmt.Errorf("%s: could not retrieve trusted validators at trustedHeight: %d",
			ibctm.ErrInvalidHeaderHeight,
			trustedHeight)
	}

	// inject trusted fields into last header
	// for now assume revision number is 0
	header.TrustedHeight = trustedHeight

	trustedVals, err := tmTrustedVals.ToProto()
	if err != nil {
		return err
	}
	header.TrustedValidators = trustedVals

	return nil
}

func commitBlock(chain *ibctesting.TestChain, dt time.Duration, res *abci.ResponseFinalizeBlock) (err error) {
	_, err = chain.App.Commit()
	if err != nil {
		return err
	}

	// set the last header to the current header
	// use nil trusted fields
	chain.LastHeader = chain.CurrentTMClientHeader()

	// val set changes returned from previous block get applied to the next validators
	// of this block. See tendermint spec for details.
	chain.Vals = chain.NextVals
	chain.NextVals = ibctesting.ApplyValSetChanges(chain, chain.Vals, res.ValidatorUpdates)

	// increment the current header
	chain.CurrentHeader = cmtproto.Header{
		ChainID:            chain.ChainID,
		Height:             chain.App.LastBlockHeight() + 1,
		AppHash:            chain.App.LastCommitID().Hash,
		Time:               chain.CurrentHeader.Time.Add(dt),
		ValidatorsHash:     chain.Vals.Hash(),
		NextValidatorsHash: chain.NextVals.Hash(),
		ProposerAddress:    chain.CurrentHeader.ProposerAddress,
	}
	return nil
}
