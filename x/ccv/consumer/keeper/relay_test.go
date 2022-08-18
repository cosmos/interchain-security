package keeper_test

import (
	"sort"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/bytes"
)

func TestOnRecvVSCPacket(t *testing.T) {
	channelID1 := "channel1"
	channelID2 := "channel2"

	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk3, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	changes1 := []abci.ValidatorUpdate{
		{
			PubKey: pk1,
			Power:  30,
		},
		{
			PubKey: pk2,
			Power:  20,
		},
	}

	changes2 := []abci.ValidatorUpdate{
		{
			PubKey: pk2,
			Power:  40,
		},
		{
			PubKey: pk3,
			Power:  10,
		},
	}

	pd := types.NewValidatorSetChangePacketData(
		changes1,
		1,
		nil,
	)

	pd2 := types.NewValidatorSetChangePacketData(
		changes2,
		2,
		nil,
	)

	testCases := []struct {
		name                   string
		packet                 channeltypes.Packet
		newChanges             types.ValidatorSetChangePacketData
		expectedPendingChanges types.ValidatorSetChangePacketData
		noAck                  bool
	}{
		{
			"success on first packet",
			channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, channelID1, consumertypes.PortID, channelID2,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			false,
		},
		{
			"success on subsequent packet",
			channeltypes.NewPacket(pd.GetBytes(), 2, providertypes.PortID, channelID1, consumertypes.PortID, channelID2,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			false,
		},
		{
			"success on packet with more changes",
			channeltypes.NewPacket(pd2.GetBytes(), 3, providertypes.PortID, channelID1, consumertypes.PortID, channelID2,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes2},
			types.ValidatorSetChangePacketData{ValidatorUpdates: []abci.ValidatorUpdate{
				{
					// this one is not included
					PubKey: pk1,
					Power:  30,
				},
				{
					PubKey: pk2,
					Power:  40,
				},
				{
					PubKey: pk3,
					Power:  10,
				},
			}},
			false,
		},
		{
			"invalid packet: different destination channel than provider channel",
			channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, channelID1, consumertypes.PortID, "InvalidChannel",
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: []abci.ValidatorUpdate{}},
			types.ValidatorSetChangePacketData{ValidatorUpdates: []abci.ValidatorUpdate{}},
			true,
		},
	}

	// Instantiate custom keeper with mocks
	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	cdc, storeKey, paramsSubspace, ctx := testkeeper.SetupInMemKeeper(t)

	mockScopedKeeper := testkeeper.NewMockScopedKeeper(ctrl)
	mockChannelKeeper := testkeeper.NewMockChannelKeeper(ctrl)

	// Setup expected mock calls for final test case

	dummyCap := &capabilitytypes.Capability{}
	gomock.InOrder(

		mockScopedKeeper.EXPECT().GetCapability(
			ctx, host.ChannelCapabilityPath(consumertypes.PortID, "InvalidChannel"),
		).Return(dummyCap, true).Times(1),

		mockChannelKeeper.EXPECT().ChanCloseInit(
			ctx, consumertypes.PortID, "InvalidChannel", dummyCap,
		).Return(nil).Times(1),
	)

	consumerKeeper := testkeeper.GetConsumerKeeperWithMocks(t,
		cdc,
		storeKey,
		paramsSubspace,
		mockScopedKeeper,
		mockChannelKeeper,
		testkeeper.NewMockPortKeeper(ctrl),
		testkeeper.NewMockConnectionKeeper(ctrl),
		testkeeper.NewMockClientKeeper(ctrl),
		testkeeper.NewMockSlashingKeeper(ctrl),
		testkeeper.NewMockBankKeeper(ctrl),
		testkeeper.NewMockAccountKeeper(ctrl),
		testkeeper.NewMockIBCTransferKeeper(ctrl),
		testkeeper.NewMockIBCCoreKeeper(ctrl),
	)

	consumerKeeper.SetProviderChannel(ctx, channelID2)
	consumerKeeper.SetUnbondingTime(ctx, 100*time.Hour)

	for _, tc := range testCases {
		ack := consumerKeeper.OnRecvVSCPacket(ctx, tc.packet, tc.newChanges)

		if tc.noAck {
			// if closing channel was successful, no acknowledgement returned, see OnRecvPacketOnUnknownChannel
			// TODO: Confirm this functionality
			require.Nil(t, ack, "invalid test case: %s ack returned ", tc.name)
		} else {
			require.NotNil(t, ack, "invalid test case: %s did not return ack", tc.name)
			require.True(t, ack.Success(), "invalid test case: %s did not return a Success Acknowledgment", tc.name)
			providerChannel, ok := consumerKeeper.GetProviderChannel(ctx)
			require.True(t, ok)
			require.Equal(t, tc.packet.DestinationChannel, providerChannel,
				"provider channel is not destination channel on successful receive for valid test case: %s", tc.name)

			// Check that pending changes are accumulated and stored correctly
			actualPendingChanges, ok := consumerKeeper.GetPendingChanges(ctx)
			require.True(t, ok)
			// Sort to avoid dumb inequalities
			sort.SliceStable(actualPendingChanges.ValidatorUpdates, func(i, j int) bool {
				return actualPendingChanges.ValidatorUpdates[i].PubKey.Compare(actualPendingChanges.ValidatorUpdates[j].PubKey) == -1
			})
			sort.SliceStable(tc.expectedPendingChanges.ValidatorUpdates, func(i, j int) bool {
				return tc.expectedPendingChanges.ValidatorUpdates[i].PubKey.Compare(tc.expectedPendingChanges.ValidatorUpdates[j].PubKey) == -1
			})
			require.Equal(t, tc.expectedPendingChanges, *actualPendingChanges, "pending changes not equal to expected changes after successful packet receive. case: %s", tc.name)

			unbondingPeriod, found := consumerKeeper.GetUnbondingTime(ctx)
			require.True(t, found)
			expectedTime := uint64(ctx.BlockTime().Add(unbondingPeriod).UnixNano())
			maturityTime := consumerKeeper.GetPacketMaturityTime(ctx, tc.newChanges.ValsetUpdateId)
			require.Equal(t, expectedTime, maturityTime, "packet maturity time has unexpected value for case: %s", tc.name)
		}
	}
}

func (suite *KeeperTestSuite) TestUnbondMaturePackets() {
	// setup CCV channel
	suite.SetupCCVChannel()

	// send 3 packets to consumer chain at different times
	pk, err := cryptocodec.FromTmPubKeyInterface(suite.providerChain.Vals.Validators[0].PubKey)
	suite.Require().NoError(err)
	pk1, err := cryptocodec.ToTmProtoPublicKey(pk)
	suite.Require().NoError(err)
	pk, err = cryptocodec.FromTmPubKeyInterface(suite.providerChain.Vals.Validators[1].PubKey)
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(pk)
	suite.Require().NoError(err)

	pd := types.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: pk1,
				Power:  30,
			},
			{
				PubKey: pk2,
				Power:  20,
			},
		},
		1,
		nil,
	)

	// send first packet
	packet := channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	ack := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time
	incrementTimeBy(suite, time.Hour)

	// update time and send second packet
	pd.ValidatorUpdates[0].Power = 15
	pd.ValsetUpdateId = 2
	packet.Data = pd.GetBytes()
	packet.Sequence = 2
	ack = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time
	incrementTimeBy(suite, 24*time.Hour)

	// update time and send third packet
	pd.ValidatorUpdates[1].Power = 40
	pd.ValsetUpdateId = 3
	packet.Data = pd.GetBytes()
	packet.Sequence = 3
	ack = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time such that first two packets are unbonded but third is not.
	unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.consumerChain.GetContext())
	suite.Require().True(found)
	// increase time
	incrementTimeBy(suite, unbondingPeriod-time.Hour)

	err = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.UnbondMaturePackets(suite.consumerChain.GetContext())
	suite.Require().NoError(err)

	// ensure first two packets are unbonded and VSCMatured packets are sent
	// unbonded time is deleted
	time1 := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 1)
	time2 := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 2)
	suite.Require().Equal(uint64(0), time1, "maturity time not deleted for mature packet 1")
	suite.Require().Equal(uint64(0), time2, "maturity time not deleted for mature packet 2")
	// ensure that third packet did not get unbonded and is still in store
	time3 := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 3)
	suite.Require().True(time3 > uint64(suite.consumerChain.GetContext().BlockTime().UnixNano()), "maturity time for packet 3 is not after current time")

	// check that the packets are committed in state
	commitments := suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(
		suite.consumerChain.GetContext(),
		consumertypes.PortID,
		suite.path.EndpointA.ChannelID,
	)
	suite.Require().Equal(2, len(commitments), "did not find packet commitments")
	suite.Require().Equal(uint64(1), commitments[0].Sequence, "did not send VSCMatured packet for VSC packet 1")
	suite.Require().Equal(uint64(2), commitments[1].Sequence, "did not send VSCMatured packet for VSC packet 2")
}

// incrementTimeByUnbondingPeriod increments the overall time by jumpPeriod
func incrementTimeBy(s *KeeperTestSuite, jumpPeriod time.Duration) {
	// Get unboding period from staking keeper
	consumerUnbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerChain.GetContext())
	s.Require().True(found)
	split := 1
	if jumpPeriod > consumerUnbondingPeriod/utils.TrustingPeriodFraction {
		// Make sure the clients do not expire
		split = 4
		jumpPeriod = jumpPeriod / 4
	}
	for i := 0; i < split; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		err := s.path.EndpointA.UpdateClient()
		s.Require().NoError(err)
		// Update the consumer client on the provider
		err = s.path.EndpointB.UpdateClient()
		s.Require().NoError(err)
	}
}

func TestOnAcknowledgement(t *testing.T) {

	// Channel ID to some dest chain that's not the established provider
	channelIDToDestChain := "channelIDToDestChain"

	// Channel ID to established provider
	channelIDToProvider := "channelIDToProvider"

	// Channel ID on destination (counter party) chain
	channelIDOnDest := "ChannelIDOnDest"

	// Instantiate custom keeper with mocks
	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	cdc, storeKey, paramsSubspace, ctx := testkeeper.SetupInMemKeeper(t)

	mockScopedKeeper := testkeeper.NewMockScopedKeeper(ctrl)
	mockChannelKeeper := testkeeper.NewMockChannelKeeper(ctrl)

	consumerKeeper := testkeeper.GetConsumerKeeperWithMocks(t,
		cdc,
		storeKey,
		paramsSubspace,
		mockScopedKeeper,
		mockChannelKeeper,
		testkeeper.NewMockPortKeeper(ctrl),
		testkeeper.NewMockConnectionKeeper(ctrl),
		testkeeper.NewMockClientKeeper(ctrl),
		testkeeper.NewMockSlashingKeeper(ctrl),
		testkeeper.NewMockBankKeeper(ctrl),
		testkeeper.NewMockAccountKeeper(ctrl),
		testkeeper.NewMockIBCTransferKeeper(ctrl),
		testkeeper.NewMockIBCCoreKeeper(ctrl),
	)

	// Set an established provider channel for later in test
	consumerKeeper.SetProviderChannel(ctx, channelIDToProvider)

	packetData := types.NewSlashPacketData(
		abci.Validator{Address: bytes.HexBytes{}, Power: int64(1)}, uint64(1), stakingtypes.Downtime,
	)

	// According to ICS 004: (https://github.com/cosmos/ibc/tree/main/spec/core/ics-004-channel-and-packet-semantics#processing-acknowledgements),
	// acknowledgedPacket is in reference to a packet originally sent from this (consumer) module.
	// TODO: Do we want to test weird edge cases like processing an ack where source port ID != consumer port ID?
	packet := channeltypes.NewPacket(
		packetData.GetBytes(),
		1,
		consumertypes.PortID, // Source port
		channelIDToDestChain, // Source channel
		providertypes.PortID, // Dest (counter party) port
		channelIDOnDest,      // Dest (counter party) channel
		clienttypes.Height{},
		uint64(time.Now().Add(60*time.Second).UnixNano()),
	)

	ack := channeltypes.NewResultAcknowledgement([]byte{1})

	// expect no error returned from OnAcknowledgementPacket, no input error with ack
	err := consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)

	// Still expect no error returned from OnAcknowledgementPacket,
	// but the input error ack will be handled with appropriate ChanCloseInit calls
	dummyCap := &capabilitytypes.Capability{}
	gomock.InOrder(

		mockScopedKeeper.EXPECT().GetCapability(
			ctx, host.ChannelCapabilityPath(consumertypes.PortID, channelIDToDestChain),
		).Return(dummyCap, true).Times(1),
		// Due to input error ack, ChanCloseInit is called on channel to destination chain
		mockChannelKeeper.EXPECT().ChanCloseInit(
			ctx, consumertypes.PortID, channelIDToDestChain, dummyCap,
		).Return(nil).Times(1),

		mockScopedKeeper.EXPECT().GetCapability(
			ctx, host.ChannelCapabilityPath(consumertypes.PortID, channelIDToProvider),
		).Return(dummyCap, true).Times(1),
		// Due to input error ack and existence of established channel to provider,
		// ChanCloseInit is called on channel to provider
		mockChannelKeeper.EXPECT().ChanCloseInit(
			ctx, consumertypes.PortID, channelIDToProvider, dummyCap,
		).Return(nil).Times(1),
	)

	ack = channeltypes.NewErrorAcknowledgement("error")
	err = consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)
}
