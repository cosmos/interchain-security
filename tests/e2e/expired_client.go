package e2e

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	upgradetypes "github.com/cosmos/cosmos-sdk/x/upgrade/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctm "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
)

// TestVSCPacketSendWithExpiredClient tests the providers sending VSCPackets
// when the consumer client is expired
func (s *CCVTestSuite) TestVSCPacketSendExpiredClient() {
	providerKeeper := s.providerApp.GetProviderKeeper()

	s.SetupCCVChannel()
	s.SetupTransferChannel()

	// upgrade the trusting period of the client to the consumer;
	// as a result, we can expire this client w/o expiring the
	// counterparty client
	upgradeClient(s, Consumer, time.Hour)

	// increment time without updating the client;
	// this will result in the client to the consumer to expire
	s.coordinator.IncrementTimeBy(2 * time.Hour)

	// bond some tokens on provider to change validator powers
	bondAmt := sdk.NewInt(1000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)

	// try to send CCV packet to consumer
	s.providerChain.NextBlock()

	// check that the packet was added to the list of pending VSC packets
	packets, found := providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(found, "no pending VSC packets found")
	s.Require().Equal(1, len(packets), "unexpected number of pending VSC packets")

	// try again to send CCV packet to consumer
	s.providerChain.NextBlock()

	// check that the packet is still in the list of pending VSC packets
	packets, found = providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(found, "no pending VSC packets found")
	s.Require().Equal(1, len(packets), "unexpected number of pending VSC packets")

	// bond more tokens on provider to change validator powers
	delegate(s, delAddr, bondAmt)

	// try again to send CCV packets to consumer
	s.providerChain.NextBlock()

	// check that the packets are still in the list of pending VSC packets
	packets, found = providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(found, "no pending VSC packets found")
	s.Require().Equal(2, len(packets), "unexpected number of pending VSC packets")

	// TODO: upgrade expired client and check that the packets are sent
	// see https://github.com/cosmos/ibc-go/blob/46e020640e66f9043c14c53a4d215a5b457d6703/modules/core/02-client/proposal_handler_test.go#L14
}

func upgradeClient(s *CCVTestSuite, clientTo ChainType, trustingPeriod time.Duration) error {
	var hostEndpoint *ibctesting.Endpoint
	var hostChain *ibctesting.TestChain
	var targetChain *ibctesting.TestChain
	if clientTo == Consumer {
		hostEndpoint = s.path.EndpointB
		hostChain = s.providerChain
		targetChain = s.consumerChain
	} else {
		hostEndpoint = s.path.EndpointA
		hostChain = s.consumerChain
		targetChain = s.providerChain
	}
	clientState := hostEndpoint.GetClientState().(*ibctm.ClientState)
	newClientHeight := clienttypes.NewHeight(0, clientState.GetLatestHeight().GetRevisionHeight()+4)

	// new client state
	upgradedClient := ibctm.NewClientState(
		clientState.ChainId,
		ibctm.DefaultTrustLevel,
		trustingPeriod,
		ibctesting.UnbondingPeriod,
		ibctesting.MaxClockDrift,
		newClientHeight,
		commitmenttypes.GetSDKSpecs(),
		ibctesting.UpgradePath,
		false,
		false,
	)
	// new consensus state
	upgradedConsState := &ibctm.ConsensusState{
		NextValidatorsHash: targetChain.GetContext().BlockHeader().NextValidatorsHash,
	}

	upgradedClientBz, err := clienttypes.MarshalClientState(hostChain.App.AppCodec(), upgradedClient)
	s.Require().NoError(err)
	upgradedConsStateBz, err := clienttypes.MarshalConsensusState(hostChain.App.AppCodec(), upgradedConsState)
	s.Require().NoError(err)

	// zero custom fields and store in upgrade store
	lastHeight := clienttypes.NewHeight(0, uint64(targetChain.GetContext().BlockHeight()+1))
	s.consumerApp.GetUpgradeKeeper().SetUpgradedClient(
		targetChain.GetContext(),
		int64(lastHeight.GetRevisionHeight()),
		upgradedClientBz,
	)
	s.consumerApp.GetUpgradeKeeper().SetUpgradedConsensusState(
		targetChain.GetContext(),
		int64(lastHeight.GetRevisionHeight()),
		upgradedConsStateBz,
	)

	// commit upgrade store changes and update clients
	s.coordinator.CommitBlock(targetChain)
	err = hostEndpoint.UpdateClient()
	s.Require().NoError(err)

	cs, found := hostChain.App.GetIBCKeeper().ClientKeeper.GetClientState(hostChain.GetContext(), hostEndpoint.ClientID)
	s.Require().True(found)

	proofUpgradeClient, _ := targetChain.QueryUpgradeProof(
		upgradetypes.UpgradedClientKey(int64(lastHeight.GetRevisionHeight())),
		cs.GetLatestHeight().GetRevisionHeight(),
	)
	proofUpgradedConsState, _ := targetChain.QueryUpgradeProof(
		upgradetypes.UpgradedConsStateKey(int64(lastHeight.GetRevisionHeight())),
		cs.GetLatestHeight().GetRevisionHeight(),
	)

	msg, err := clienttypes.NewMsgUpgradeClient(
		hostEndpoint.ClientID,
		upgradedClient,
		upgradedConsState,
		proofUpgradeClient,
		proofUpgradedConsState,
		hostChain.SenderAccount.GetAddress().String(),
	)
	s.Require().NoError(err)

	_, err = hostChain.SendMsgs(msg)
	return err
}
