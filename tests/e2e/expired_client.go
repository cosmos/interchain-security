package e2e

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibcexported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	ibctm "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// TestVSCPacketSendWithExpiredClient tests the providers sending VSCPackets
// when the consumer client is expired
func (s *CCVTestSuite) TestVSCPacketSendExpiredClient() {
	providerKeeper := s.providerApp.GetProviderKeeper()

	s.SetupCCVChannel()
	s.SetupTransferChannel()

	cs, ok := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(), s.path.EndpointB.ClientID)
	s.Require().True(ok)
	trustingPeriod := cs.(*ibctm.ClientState).TrustingPeriod

	// increment time on consumer without updating the provider's client
	// this will result in the client to the consumer to expire
	incrementTimeWithoutUpdate(s, trustingPeriod+time.Hour, Consumer)

	// check that the client to the consumer is not active
	cs, ok = s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(), s.path.EndpointB.ClientID)
	s.Require().True(ok)
	clientStore := s.providerApp.GetIBCKeeper().ClientKeeper.ClientStore(s.providerCtx(), s.path.EndpointB.ClientID)
	status := cs.Status(s.providerCtx(), clientStore, s.providerChain.App.AppCodec())
	s.Require().NotEqual(ibcexported.Active, status, "")

	// bond some tokens on provider to change validator powers
	bondAmt := sdk.NewInt(1000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)

	// try to send CCV packet to consumer
	s.providerChain.NextBlock()

	// check that the packet was added to the list of pending VSC packets
	packets := providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().NotEmpty(packets, "no pending VSC packets found")
	s.Require().Equal(1, len(packets), "unexpected number of pending VSC packets")

	// try again to send CCV packet to consumer
	s.providerChain.NextBlock()

	// check that the packet is still in the list of pending VSC packets
	packets = providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().NotEmpty(packets, "no pending VSC packets found")
	s.Require().Equal(1, len(packets), "unexpected number of pending VSC packets")

	// bond more tokens on provider to change validator powers
	delegate(s, delAddr, bondAmt)

	// try again to send CCV packets to consumer
	s.providerChain.NextBlock()

	// check that the packets are still in the list of pending VSC packets
	packets = providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().NotEmpty(packets, "no pending VSC packets found")
	s.Require().Equal(2, len(packets), "unexpected number of pending VSC packets")

	// upgrade expired client to the consumer
	upgradeExpiredClient(s, Consumer)

	// go to next block
	s.providerChain.NextBlock()

	// check that the packets are not in the list of pending VSC packets
	packets = providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().Empty(packets, "unexpected pending VSC packets found")

	// bond more tokens on provider to change validator powers
	delegate(s, delAddr, bondAmt)

	// send CCV packet to consumer
	s.providerChain.NextBlock()

	// Relay 3 VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 3)

	// Increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// Relay 3 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 3)
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
