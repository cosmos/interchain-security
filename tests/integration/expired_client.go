package integration

import (
	"time"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	ibcexported "github.com/cosmos/ibc-go/v8/modules/core/exported"
	ibctm "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// TestVSCPacketSendWithExpiredClient tests queueing of VSCPackets when the consumer client is expired.
// While the consumer client is expired (or inactive for some reason) all packets will be queued and
// and cleared once the consumer client is established.
func (s *CCVTestSuite) TestVSCPacketSendExpiredClient() {
	providerKeeper := s.providerApp.GetProviderKeeper()

	s.SetupCCVChannel(s.path)

	expireClient(s, Consumer)

	// bond some tokens on provider to change validator powers
	bondAmt := math.NewInt(1000000)
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
	bondAmt := math.NewInt(1000000)
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
	s.Require().Len(consumerPackets, 2, "unexpected number of pending data packets")

	// try to send slash packet for downtime infraction
	addr := ed25519.GenPrivKey().PubKey().Address()
	val := abci.Validator{Address: addr, Power: 1}
	consumerKeeper.QueueSlashPacket(s.consumerCtx(), val, 2, stakingtypes.Infraction_INFRACTION_DOWNTIME)
	// try to send slash packet for the same downtime infraction
	consumerKeeper.QueueSlashPacket(s.consumerCtx(), val, 3, stakingtypes.Infraction_INFRACTION_DOWNTIME)
	// try to send slash packet for the double-sign infraction
	consumerKeeper.QueueSlashPacket(s.consumerCtx(), val, 3, stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN)

	// check that the packets were added to the list of pending data packets
	consumerPackets = consumerKeeper.GetPendingPackets(s.consumerCtx())
	s.Require().NotEmpty(consumerPackets)
	// At this point we expect 4 packets, two vsc matured packets and two trailing slash packets
	s.Require().Len(consumerPackets, 4, "unexpected number of pending data packets")

	// upgrade expired client to the consumer
	upgradeExpiredClient(s, Provider)

	// go to next block to trigger SendPendingPackets
	s.consumerChain.NextBlock()

	// Check that the leading vsc matured packets were sent and no longer pending
	consumerPackets = consumerKeeper.GetPendingPackets(s.consumerCtx())
	s.Require().Len(consumerPackets, 2, "unexpected number of pending data packets")

	// relay committed packets from consumer to provider, first slash packet should be committed
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 3) // two vsc matured + one slash

	// First slash has been acked, now only the second slash packet should remain as pending
	consumerPackets = consumerKeeper.GetPendingPackets(s.consumerCtx())
	s.Require().Len(consumerPackets, 1, "unexpected number of pending data packets")

	// go to next block to trigger SendPendingPackets
	s.consumerChain.NextBlock()

	// relay committed packets from consumer to provider, only second slash packet should be committed
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 1) // one slash

	consumerPackets = consumerKeeper.GetPendingPackets(s.consumerCtx())
	s.Require().Empty(consumerPackets, "pending data packets found")

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

	recoverMsg := clienttypes.NewMsgRecoverClient(hostChain.App.GetIBCKeeper().GetAuthority(), subject, substitute)
	err = recoverMsg.ValidateBasic()
	s.Require().NoError(err)

	res, err := hostChain.App.GetIBCKeeper().RecoverClient(hostChain.GetContext(), recoverMsg)
	s.Require().NoError(err)
	s.Require().NotNil(res)
}
