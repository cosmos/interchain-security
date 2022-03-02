package keeper_test

import (
	"fmt"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/testing"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/suite"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
	// 	slashing "github.com/cosmos/cosmos-sdk/x/slashing"
	// staking "github.com/cosmos/cosmos-sdk/x/staking"
)

func init() {
	ibctesting.DefaultTestingAppInit = simapp.SetupTestingApp
}

type KeeperTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	parentChain *ibctesting.TestChain
	childChain  *ibctesting.TestChain

	parentClient    *ibctmtypes.ClientState
	parentConsState *ibctmtypes.ConsensusState

	path *ibctesting.Path

	ctx sdk.Context
}

func (suite *KeeperTestSuite) SetupTest() {
	suite.coordinator = ibctesting.NewCoordinator(suite.T(), 2)
	suite.parentChain = suite.coordinator.GetChain(ibctesting.GetChainID(0))
	suite.childChain = suite.coordinator.GetChain(ibctesting.GetChainID(1))

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on parent chain before creating client
	suite.coordinator.CommitBlock(suite.parentChain)

	// create client and consensus state of parent chain to initialize child chain genesis.
	height := suite.parentChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	suite.parentClient = ibctmtypes.NewClientState(
		suite.parentChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	suite.parentConsState = suite.parentChain.LastHeader.ConsensusState()

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.parentChain.Vals)

	childGenesis := types.NewInitialGenesisState(suite.parentClient, suite.parentConsState, valUpdates)
	suite.childChain.App.(*app.App).ChildKeeper.InitGenesis(suite.childChain.GetContext(), childGenesis)

	suite.ctx = suite.childChain.GetContext()

	suite.path = ibctesting.NewPath(suite.childChain, suite.parentChain)
	suite.path.EndpointA.ChannelConfig.PortID = childtypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = parenttypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = ccv.Version
	suite.path.EndpointB.ChannelConfig.Version = ccv.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	parentClient, ok := suite.childChain.App.(*app.App).ChildKeeper.GetParentClient(suite.ctx)
	if !ok {
		panic("must already have parent client on child chain")
	}
	// set child endpoint's clientID
	suite.path.EndpointA.ClientID = parentClient

	// create child client on parent chain and set as child client for child chainID in parent keeper.
	suite.path.EndpointB.CreateClient()
	suite.parentChain.App.(*app.App).ParentKeeper.SetChildClient(suite.parentChain.GetContext(), suite.childChain.ChainID, suite.path.EndpointB.ClientID)
}

func (suite *KeeperTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)
	suite.coordinator.CreateChannels(suite.path)
}

func (suite *KeeperTestSuite) TestParentClient() {
	parentClient, ok := suite.childChain.App.(*app.App).ChildKeeper.GetParentClient(suite.ctx)
	suite.Require().True(ok)

	clientState, ok := suite.childChain.App.GetIBCKeeper().ClientKeeper.GetClientState(suite.ctx, parentClient)
	suite.Require().Equal(suite.parentClient, clientState, "stored client state does not match genesis parent client")
}

func (suite *KeeperTestSuite) TestParentChannel() {
	_, ok := suite.childChain.App.(*app.App).ChildKeeper.GetParentChannel(suite.ctx)
	suite.Require().False(ok)
	suite.childChain.App.(*app.App).ChildKeeper.SetParentChannel(suite.ctx, "channelID")
	channelID, ok := suite.childChain.App.(*app.App).ChildKeeper.GetParentChannel(suite.ctx)
	suite.Require().True(ok)
	suite.Require().Equal("channelID", channelID)
}

func (suite *KeeperTestSuite) TestPendingChanges() {
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)

	pd := ccv.NewValidatorSetChangePacketData(
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
	)

	suite.childChain.App.(*app.App).ChildKeeper.SetPendingChanges(suite.ctx, pd)
	gotPd, ok := suite.childChain.App.(*app.App).ChildKeeper.GetPendingChanges(suite.ctx)
	suite.Require().True(ok)
	suite.Require().Equal(&pd, gotPd, "packet data in store does not equal packet data set")
	suite.childChain.App.(*app.App).ChildKeeper.DeletePendingChanges(suite.ctx)
	gotPd, ok = suite.childChain.App.(*app.App).ChildKeeper.GetPendingChanges(suite.ctx)
	suite.Require().False(ok)
	suite.Require().Nil(gotPd, "got non-nil pending changes after Delete")
}

func (suite *KeeperTestSuite) TestUnbondingTime() {
	suite.childChain.App.(*app.App).ChildKeeper.SetUnbondingTime(suite.ctx, 1, 10)
	suite.childChain.App.(*app.App).ChildKeeper.SetUnbondingTime(suite.ctx, 2, 25)
	suite.childChain.App.(*app.App).ChildKeeper.SetUnbondingTime(suite.ctx, 5, 15)
	suite.childChain.App.(*app.App).ChildKeeper.SetUnbondingTime(suite.ctx, 6, 40)

	suite.childChain.App.(*app.App).ChildKeeper.DeleteUnbondingTime(suite.ctx, 6)

	suite.Require().Equal(uint64(10), suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingTime(suite.ctx, 1))
	suite.Require().Equal(uint64(25), suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingTime(suite.ctx, 2))
	suite.Require().Equal(uint64(15), suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingTime(suite.ctx, 5))
	suite.Require().Equal(uint64(0), suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingTime(suite.ctx, 3))
	suite.Require().Equal(uint64(0), suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingTime(suite.ctx, 6))

	orderedTimes := [][]uint64{{1, 10}, {2, 25}, {5, 15}}
	i := 0

	suite.childChain.App.(*app.App).ChildKeeper.IterateUnbondingTime(suite.ctx, func(seq, time uint64) bool {
		// require that we iterate through unbonding time in order of sequence
		suite.Require().Equal(orderedTimes[i][0], seq)
		suite.Require().Equal(orderedTimes[i][1], time)
		i++
		return false
	})
}

func (suite *KeeperTestSuite) TestUnbondingPacket() {
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)

	for i := 0; i < 5; i++ {
		pd := ccv.NewValidatorSetChangePacketData(
			[]abci.ValidatorUpdate{
				{
					PubKey: pk1,
					Power:  int64(i),
				},
				{
					PubKey: pk2,
					Power:  int64(i + 5),
				},
			},
			1,
		)
		packet := channeltypes.NewPacket(pd.GetBytes(), uint64(i), "parent", "channel-1", "child", "channel-1",
			clienttypes.NewHeight(1, 0), 0)
		suite.childChain.App.(*app.App).ChildKeeper.SetUnbondingPacket(suite.ctx, uint64(i), packet)
	}

	// ensure that packets are iterated by sequence
	i := 0
	suite.childChain.App.(*app.App).ChildKeeper.IterateUnbondingPacket(suite.ctx, func(seq uint64, packet channeltypes.Packet) bool {
		suite.Require().Equal(uint64(i), seq)
		gotPacket, err := suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingPacket(suite.ctx, seq)
		suite.Require().NoError(err)
		suite.Require().Equal(&packet, gotPacket, "packet from get and iteration do not match")
		i++
		return false
	})

	suite.childChain.App.(*app.App).ChildKeeper.DeleteUnbondingPacket(suite.ctx, 0)
	gotPacket, err := suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingPacket(suite.ctx, 0)
	suite.Require().Error(err)
	suite.Require().Nil(gotPacket, "packet is not nil after delete")
}

func (suite *KeeperTestSuite) TestVerifyParentChain() {
	channelID := "channel-1"
	testCases := []struct {
		name     string
		setup    func(suite *KeeperTestSuite)
		expError bool
	}{
		{
			name: "success",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// Set INIT channel on child chain
				suite.childChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, childtypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(parenttypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, suite.path.EndpointA.ChannelID, ccv.INITIALIZING)
			},
			expError: false,
		},
		{
			name: "not initializing status",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// Set INIT channel on child chain
				suite.childChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, childtypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(parenttypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID

				// set channel status to validating
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, suite.path.EndpointA.ChannelID, ccv.VALIDATING)
			},
			expError: true,
		},
		{
			name: "channel does not exist",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// set channelID without creating channel
				suite.path.EndpointA.ChannelID = "channel-1"
				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, suite.path.EndpointA.ChannelID, ccv.INITIALIZING)
			},
			expError: true,
		},
		{
			name: "connection hops is not length 1",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// Set INIT channel on child chain with multiple connection hops
				suite.childChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, childtypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(parenttypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID, "connection-2"}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID

				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, suite.path.EndpointA.ChannelID, ccv.INITIALIZING)
			},
			expError: true,
		},
		{
			name: "connection does not exist",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// Set INIT channel on child chain with nonexistent connection
				suite.childChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, childtypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(parenttypes.PortID, ""),
						[]string{"nonexistent-connection"}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID

				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, suite.path.EndpointA.ChannelID, ccv.INITIALIZING)
			},
			expError: true,
		},
		{
			name: "clientID does not match",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				// create a new parent client on child chain that is different from the one in genesis
				suite.path.EndpointA.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// Set INIT channel on child chain
				suite.childChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, childtypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(parenttypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID

				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, suite.path.EndpointA.ChannelID, ccv.INITIALIZING)
			},
			expError: true,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset suite

			tc.setup(suite)

			// Verify ParentChain on child chain using path returned by setup
			err := suite.childChain.App.(*app.App).ChildKeeper.VerifyParentChain(suite.ctx, suite.path.EndpointA.ChannelID)

			if tc.expError {
				suite.Require().Error(err, "invalid case did not return error")
			} else {
				suite.Require().NoError(err, "valid case returned error")
			}
		})
	}
}

func (suite *KeeperTestSuite) TestValidatorDowntime() {
	// initial setup
	suite.SendFirstCCVPacket()

	app, ctx := suite.childChain.App.(*app.App), suite.ctx
	channelID := suite.path.EndpointA.ChannelID

	// create a validator pubkey and address
	pubkey := ed25519.GenPrivKey().PubKey()
	consAddr := sdk.ConsAddress(pubkey.Address())

	// add the validator pubkey and signing info to the store
	app.SlashingKeeper.AddPubkey(ctx, pubkey)

	// set unbounding packet with valset update id
	vscPacket := ccv.ValidatorSetChangePacketData{ValsetUpdateId: uint64(3)}
	app.ChildKeeper.SetUnbondingPacket(ctx, uint64(0), channeltypes.Packet{Data: vscPacket.GetBytes()})

	valInfo := slashingtypes.NewValidatorSigningInfo(consAddr, ctx.BlockHeight(), ctx.BlockHeight()-1,
		time.Time{}.UTC(), false, int64(0))
	app.SlashingKeeper.SetValidatorSigningInfo(ctx, consAddr, valInfo)

	// save next sequence before sending slashing packet
	seq, ok := app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(ctx, types.PortID, channelID)
	suite.Require().True(ok)

	// Sign 1000 blocks
	valPower := int64(1)
	height := int64(0)
	for ; height < app.SlashingKeeper.SignedBlocksWindow(ctx); height++ {
		ctx = ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(ctx, pubkey.Address().Bytes(), valPower, true)
	}
	// Miss 500 blocks
	for ; height < app.SlashingKeeper.SignedBlocksWindow(ctx)+(app.SlashingKeeper.SignedBlocksWindow(ctx)-app.SlashingKeeper.MinSignedPerWindow(ctx))+1; height++ {
		ctx = ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(ctx, pubkey.Address().Bytes(), valPower, false)
	}

	// check that the validator signing info are correctly updated
	signInfo, found := app.SlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)
	suite.Require().True(found)
	suite.Require().NotZero(signInfo.JailedUntil, "did not update validator unjail until")
	suite.Require().Zero(signInfo.MissedBlocksCounter, "did not reset validator missed block counter")
	suite.Require().Zero(signInfo.IndexOffset)
	app.SlashingKeeper.IterateValidatorMissedBlockBitArray(ctx, consAddr, func(_ int64, missed bool) bool {
		suite.Require().False(missed)
		return false
	})

	// verify that the slashing packet was sent
	commit := app.IBCKeeper.ChannelKeeper.GetPacketCommitment(ctx, types.PortID, channelID, seq)
	suite.Require().NotNil(commit, "did not found slashing packet commitment")
}

// TestAfterValidatorDowntimeHook tests the slashing hook implementation logic
func (suite *KeeperTestSuite) TestAfterValidatorDowntimeHook() {
	// initial setup
	suite.SendFirstCCVPacket()

	app, ctx := suite.childChain.App.(*app.App), suite.ctx
	channelID := suite.path.EndpointA.ChannelID

	consAddr := sdk.ConsAddress(ed25519.GenPrivKey().PubKey().Bytes()).Bytes()

	// set initial validator signing info
	signInfo := slashingtypes.NewValidatorSigningInfo(consAddr, int64(1), int64(1),
		time.Time{}.UTC(), false, int64(0))
	app.SlashingKeeper.SetValidatorSigningInfo(ctx, consAddr, signInfo)

	// store sequence
	seq, ok := app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(ctx, types.PortID, channelID)
	suite.Require().True(ok)

	// expect no updates when no unbonding packets exist
	app.ChildKeeper.AfterValidatorDowntime(ctx, consAddr, int64(1))
	newSignInfo, _ := app.SlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)

	suite.Require().True(signInfo.JailedUntil.Equal(newSignInfo.JailedUntil), "updated signing info when no unbonding packets exist")

	// check that no slashing packet was sent
	commit := app.IBCKeeper.ChannelKeeper.GetPacketCommitment(ctx, types.PortID, channelID, seq)
	suite.Require().Nil(commit, "sent slashing packet when no unbonding packets exist")

	// set unbounding packet with valset update id
	vscPacket := ccv.ValidatorSetChangePacketData{ValsetUpdateId: uint64(3)}
	app.ChildKeeper.SetUnbondingPacket(ctx, uint64(0), channeltypes.Packet{Data: vscPacket.GetBytes()})

	blockTime := suite.childChain.GetContext().BlockTime()

	// test cases with jailing times being zero, elapsed and pending
	testcases := []struct {
		jailedUntil time.Time
		expUpdate   bool
	}{
		{
			jailedUntil: time.Time{},
			expUpdate:   true,
		}, {
			jailedUntil: blockTime.Add(-1 * time.Hour),
			expUpdate:   true,
		}, {
			jailedUntil: blockTime.Add(1 * time.Hour),
			expUpdate:   false,
		},
	}

	for _, tc := range testcases {
		// set test case signing info
		signInfo = slashingtypes.NewValidatorSigningInfo(consAddr, int64(1), int64(1), tc.jailedUntil, false, int64(0))
		app.SlashingKeeper.SetValidatorSigningInfo(ctx, consAddr, signInfo)
		// save current sequence
		seq, _ = app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(ctx, types.PortID, channelID)
		// execute hook logic
		app.ChildKeeper.AfterValidatorDowntime(ctx, consAddr, int64(1))
		// check signing info state
		newSignInfo, _ = app.SlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)
		suite.Require().True(tc.expUpdate == !(signInfo.JailedUntil.Equal(newSignInfo.JailedUntil)))

		// check that slashing packet was sent only if expected
		commit = app.IBCKeeper.ChannelKeeper.GetPacketCommitment(ctx, types.PortID, channelID, seq)
		suite.Require().Equal(tc.expUpdate, commit != nil)
	}
}

func (suite *KeeperTestSuite) SendFirstCCVPacket() {
	suite.SetupCCVChannel()

	oldBlockTime := suite.parentChain.GetContext().BlockTime()
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())

	packetData := ccv.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, uint64(1))
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, parenttypes.PortID, suite.path.EndpointB.ChannelID,
		childtypes.PortID, suite.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	suite.path.EndpointB.SendPacket(packet)

	err := suite.path.EndpointA.RecvPacket(packet)
	suite.Require().NoError(err)

	status := suite.childChain.App.(*app.App).ChildKeeper.GetChannelStatus(suite.childChain.GetContext(), suite.path.EndpointA.ChannelID)
	suite.Require().EqualValues(int32(2), status)
}

func (suite *KeeperTestSuite) TestGetLastBlockHeightValsetUpdateID() {
	app := suite.childChain.App.(*app.App)
	ctx := suite.childChain.GetContext()

	valUpdateID := app.ChildKeeper.GetHeightValsetUpdateID(ctx, 1)
	suite.Require().Zero(valUpdateID)
	for i := 0; i < 5; i++ {
		app.ChildKeeper.SetHeightValsetUpdateID(ctx, uint64(i), uint64(i))
	}

	valUpdateID = app.ChildKeeper.GetHeightValsetUpdateID(ctx, 0)
	suite.Require().Equal(uint64(0), valUpdateID)

	valUpdateID = app.ChildKeeper.GetHeightValsetUpdateID(ctx, 1)
	suite.Require().Equal(uint64(1), valUpdateID)

	valUpdateID = app.ChildKeeper.HeightToValsetUpdateID(ctx, uint64(2))
	suite.Require().Equal(uint64(2), valUpdateID)

	app.ChildKeeper.SetHeightValsetUpdateID(ctx, uint64(6), uint64(6))

	valUpdateID = app.ChildKeeper.HeightToValsetUpdateID(ctx, uint64(5))
	suite.Require().Equal(uint64(4), valUpdateID, "did not return the last valset update ID stored in or before block height 5")

}

func (suite *KeeperTestSuite) TestBlockHeightValsetUpdateID() {
	app := suite.childChain.App.(*app.App)
	ctx := suite.ctx

	valUpdateID := app.ChildKeeper.GetHeightValsetUpdateID(ctx, uint64(0))
	suite.Require().Zero(valUpdateID)

	app.ChildKeeper.SetHeightValsetUpdateID(ctx, uint64(1), uint64(2))
	valUpdateID = app.ChildKeeper.HeightToValsetUpdateID(ctx, uint64(1))
	suite.Require().Equal(valUpdateID, uint64(2))

	app.ChildKeeper.DeleteHeightValsetUpdateID(ctx, uint64(1))
	valUpdateID = app.ChildKeeper.GetHeightValsetUpdateID(ctx, uint64(1))
	suite.Require().Zero(valUpdateID)

	app.ChildKeeper.SetHeightValsetUpdateID(ctx, uint64(3), uint64(2))
	app.ChildKeeper.SetHeightValsetUpdateID(ctx, uint64(3), uint64(4))
	valUpdateID = app.ChildKeeper.GetHeightValsetUpdateID(ctx, uint64(3))
	suite.Require().Equal(valUpdateID, uint64(4))
}

func TestKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(KeeperTestSuite))
}
