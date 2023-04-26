package integration

import (
	"time"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	ibcexported "github.com/cosmos/ibc-go/v4/modules/core/exported"
	ibctm "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/interchain-security/v2/legacy_ibc_testing/testing"
	ccv "github.com/cosmos/interchain-security/x/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// TestVSCPacketSendWithExpiredClient tests queueing of VSCPackets when the consumer client is expired.
// While the consumer client is expired (or inactive for some reason) all packets will be queued and
// and cleared once the consumer client is established.
func (s *CCVTestSuite) TestVSCPacketSendExpiredClient() {
	providerKeeper := s.providerApp.GetProviderKeeper()

	s.SetupCCVChannel(s.path)

	expireClient(s, Consumer)

	// bond some tokens on provider to change validator powers
	bondAmt := sdk.NewInt(1000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)

	// try to send CCV packet to consumer
	s.providerChain.NextBlock()

	// check that the packet was added to the list of pending VSC packets
	packets := providerKeeper.GetPendingVSCPackets(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().NotEmpty(packets, "no pending VSC packets found")
	s.Require().Equal(1, len(packets), "unexpected number of pending VSC packets")

	// try again to send CCV packet to consumer
	s.providerChain.NextBlock()

	// check that the packet is still in the list of pending VSC packets
	packets = providerKeeper.GetPendingVSCPackets(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().NotEmpty(packets, "no pending VSC packets found")
	s.Require().Equal(1, len(packets), "unexpected number of pending VSC packets")

	// bond more tokens on provider to change validator powers
	delegate(s, delAddr, bondAmt)

	// try again to send CCV packets to consumer
	s.providerChain.NextBlock()

	// check that the packets are still in the list of pending VSC packets
	packets = providerKeeper.GetPendingVSCPackets(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().NotEmpty(packets, "no pending VSC packets found")
	s.Require().Equal(2, len(packets), "unexpected number of pending VSC packets")

	// upgrade expired client to the consumer
	upgradeExpiredClient(s, Consumer)

	// go to next block
	s.providerChain.NextBlock()

	// check that the packets are not in the list of pending VSC packets
	packets = providerKeeper.GetPendingVSCPackets(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().Empty(packets, "unexpected pending VSC packets found")

	// check that validator updates work
	// - bond more tokens on provider to change validator powers
	delegate(s, delAddr, bondAmt)
	// - send CCV packet to consumer
	s.providerChain.NextBlock()
	// - relay all VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 3)
	// - increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)
	// - relay all VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 3)
}

// TestConsumerPacketSendExpiredClient tests the consumer sending packets when the provider client is expired.
// While the provider client is expired  all packets will be queued and and cleared once the provider client is upgraded.
func (s *CCVTestSuite) TestConsumerPacketSendExpiredClient() {
	providerKeeper := s.providerApp.GetProviderKeeper()
	consumerKeeper := s.consumerApp.GetConsumerKeeper()

	s.SetupCCVChannel(s.path)

	// bond some tokens on provider to change validator powers
	bondAmt := sdk.NewInt(1000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)

	// send CCV packet to consumer
	s.providerChain.NextBlock()

	// bond more tokens on provider to change validator powers
	delegate(s, delAddr, bondAmt)

	// send CCV packets to consumer
	s.providerChain.NextBlock()

	// check that the packets are not in the list of pending VSC packets
	providerPackets := providerKeeper.GetPendingVSCPackets(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().Empty(providerPackets, "pending VSC packets found")

	// relay all VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 2)

	// expire client to provider
	expireClient(s, Provider)

	// check that the client to the consumer is active
	checkClientExpired(s, Consumer, false)

	// increment time so that the unbonding period ends on the consumer;
	// do not try to update the client to the provider since it's expired
	consumerUnbondingPeriod := s.consumerApp.GetConsumerKeeper().GetUnbondingPeriod(s.consumerCtx())
	incrementTimeWithoutUpdate(s, consumerUnbondingPeriod+time.Hour, Provider)

	// check that the packets were added to the list of pending data packets
	consumerPackets := consumerKeeper.GetPendingPackets(s.consumerCtx())
	s.Require().NotEmpty(consumerPackets)
	s.Require().Equal(2, len(consumerPackets.GetList()), "unexpected number of pending data packets")

	// try to send slash packet for downtime infraction
	addr := ed25519.GenPrivKey().PubKey().Address()
	val := abci.Validator{Address: addr}
	consumerKeeper.QueueSlashPacket(s.consumerCtx(), val, 2, stakingtypes.Downtime)
	// try to send slash packet for the same downtime infraction
	consumerKeeper.QueueSlashPacket(s.consumerCtx(), val, 3, stakingtypes.Downtime)
	// try to send slash packet for the double-sign infraction
	consumerKeeper.QueueSlashPacket(s.consumerCtx(), val, 3, stakingtypes.DoubleSign)

	// check that the packets were added to the list of pending data packets
	consumerPackets = consumerKeeper.GetPendingPackets(s.consumerCtx())
	s.Require().NotEmpty(consumerPackets)
	s.Require().Equal(4, len(consumerPackets.GetList()), "unexpected number of pending data packets")

	// upgrade expired client to the consumer
	upgradeExpiredClient(s, Provider)

	// go to next block to trigger SendPendingDataPackets
	s.consumerChain.NextBlock()

	// check that the list of pending data packets is emptied
	consumerPackets = consumerKeeper.GetPendingPackets(s.consumerCtx())
	s.Require().Empty(consumerPackets)
	s.Require().Equal(0, len(consumerPackets.GetList()), "unexpected number of pending data packets")

	// relay all  packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 4)

	// check that everything works
	// - bond more tokens on provider to change validator powers
	delegate(s, delAddr, bondAmt)
	// - send CCV packet to consumer
	s.providerChain.NextBlock()
	// - relay 1 VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)
	// - increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Consumer)
	// - relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 1)
}

// expireClient expires the client to the `clientTo` chain
func expireClient(s *CCVTestSuite, clientTo ChainType) {
	var hostEndpoint *ibctesting.Endpoint
	var hostChain *ibctesting.TestChain
	if clientTo == Consumer {
		hostEndpoint = s.path.EndpointB
		hostChain = s.providerChain
	} else {
		hostEndpoint = s.path.EndpointA
		hostChain = s.consumerChain
	}
	cs, ok := hostChain.App.GetIBCKeeper().ClientKeeper.GetClientState(hostChain.GetContext(), hostEndpoint.ClientID)
	s.Require().True(ok)
	trustingPeriod := cs.(*ibctm.ClientState).TrustingPeriod

	// increment time without updating the `clientTo` client
	incrementTimeWithoutUpdate(s, trustingPeriod+time.Hour, clientTo)

	// check that the client is not active
	checkClientExpired(s, clientTo, true)
}

// checkClientIsExpired checks whether the client to `clientTo` is expired
func checkClientExpired(s *CCVTestSuite, clientTo ChainType, expectedExpired bool) {
	var hostEndpoint *ibctesting.Endpoint
	var hostChain *ibctesting.TestChain
	if clientTo == Consumer {
		hostEndpoint = s.path.EndpointB
		hostChain = s.providerChain
	} else {
		hostEndpoint = s.path.EndpointA
		hostChain = s.consumerChain
	}
	// check that the client to the consumer is not active
	cs, ok := hostChain.App.GetIBCKeeper().ClientKeeper.GetClientState(hostChain.GetContext(), hostEndpoint.ClientID)
	s.Require().True(ok)
	clientStore := hostChain.App.GetIBCKeeper().ClientKeeper.ClientStore(hostChain.GetContext(), hostEndpoint.ClientID)
	status := cs.Status(hostChain.GetContext(), clientStore, hostChain.App.AppCodec())
	if expectedExpired {
		s.Require().NotEqual(ibcexported.Active, status, "client is active")
	} else {
		s.Require().Equal(ibcexported.Active, status, "client is not active")
	}
}

// upgradeExpiredClient upgrades an expired client to `clientTo`
func upgradeExpiredClient(s *CCVTestSuite, clientTo ChainType) {
	subjectPath := s.path
	substitutePath := ibctesting.NewPath(s.consumerChain, s.providerChain)
	var subject, subjectCounterparty string
	var hostNewEndpoint, targetNewEndpoint *ibctesting.Endpoint
	var hostChain *ibctesting.TestChain
	var targetChain *ibctesting.TestChain
	if clientTo == Consumer {
		subject = subjectPath.EndpointB.ClientID             // provider endpoint client
		subjectCounterparty = subjectPath.EndpointA.ClientID // consumer endpoint client
		hostNewEndpoint = substitutePath.EndpointB
		targetNewEndpoint = substitutePath.EndpointA
		hostChain = s.providerChain
		targetChain = s.consumerChain
	} else {
		subject = subjectPath.EndpointA.ClientID             // consumer endpoint client
		subjectCounterparty = subjectPath.EndpointB.ClientID // provider endpoint client
		hostNewEndpoint = substitutePath.EndpointA
		targetNewEndpoint = substitutePath.EndpointB
		hostChain = s.consumerChain
		targetChain = s.providerChain
	}

	subjectClientState := hostChain.GetClientState(subject)

	// create substitute client with same unbonding period
	hostTmConfig, ok := hostNewEndpoint.ClientConfig.(*ibctesting.TendermintConfig)
	s.Require().True(ok)
	hostTmConfig.UnbondingPeriod = subjectClientState.(*ibctm.ClientState).UnbondingPeriod
	hostTmConfig.TrustingPeriod = subjectClientState.(*ibctm.ClientState).TrustingPeriod
	targetTmConfig, ok := targetNewEndpoint.ClientConfig.(*ibctesting.TendermintConfig)
	s.Require().True(ok)
	subjectCounterpartyCS := targetChain.GetClientState(subjectCounterparty)
	targetTmConfig.UnbondingPeriod = subjectCounterpartyCS.(*ibctm.ClientState).UnbondingPeriod
	targetTmConfig.TrustingPeriod = subjectCounterpartyCS.(*ibctm.ClientState).TrustingPeriod
	s.coordinator.SetupClients(substitutePath)
	substitute := hostNewEndpoint.ClientID

	// update substitute twice
	err := hostNewEndpoint.UpdateClient()
	s.Require().NoError(err)
	err = hostNewEndpoint.UpdateClient()
	s.Require().NoError(err)
	substituteClientState := hostChain.GetClientState(substitute)

	tmClientState, ok := subjectClientState.(*ibctm.ClientState)
	s.Require().True(ok)
	tmClientState.AllowUpdateAfterMisbehaviour = true
	tmClientState.AllowUpdateAfterExpiry = true
	tmClientState.FrozenHeight = tmClientState.LatestHeight
	hostChain.App.GetIBCKeeper().ClientKeeper.SetClientState(hostChain.GetContext(), subject, tmClientState)

	tmClientState, ok = substituteClientState.(*ibctm.ClientState)
	s.Require().True(ok)
	tmClientState.AllowUpdateAfterMisbehaviour = true
	tmClientState.AllowUpdateAfterExpiry = true
	hostChain.App.GetIBCKeeper().ClientKeeper.SetClientState(hostChain.GetContext(), substitute, tmClientState)

	content := clienttypes.NewClientUpdateProposal(ibctesting.Title, ibctesting.Description, subject, substitute)

	updateProp, ok := content.(*clienttypes.ClientUpdateProposal)
	s.Require().True(ok)
	err = hostChain.App.GetIBCKeeper().ClientKeeper.ClientUpdateProposal(hostChain.GetContext(), updateProp)
	s.Require().NoError(err)
}
