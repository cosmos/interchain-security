package keeper_test

import (
	"fmt"
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/suite"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
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
	suite.parentChain = suite.coordinator.GetChain(ibctesting.GetChainID(1))
	suite.childChain = suite.coordinator.GetChain(ibctesting.GetChainID(2))

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

	params := childtypes.DefaultParams()
	params.Enabled = true
	childGenesis := types.NewInitialGenesisState(suite.parentClient, suite.parentConsState, valUpdates, params)
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

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

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
		nil,
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
			nil,
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
	var connectionHops []string
	channelID := "channel-0"
	testCases := []struct {
		name           string
		setup          func(suite *KeeperTestSuite)
		connectionHops []string
		expError       bool
	}{
		{
			name: "success",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, channelID, ccv.INITIALIZING)
				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID}
			},
			connectionHops: []string{suite.path.EndpointA.ConnectionID},
			expError:       false,
		},
		{
			name: "not initializing status",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// set channel status to validating
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, channelID, ccv.VALIDATING)
				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID}
			},
			expError: true,
		},
		{
			name: "connection hops is not length 1",
			setup: func(suite *KeeperTestSuite) {
				// create child client on parent chain
				suite.path.EndpointB.CreateClient()

				suite.coordinator.CreateConnections(suite.path)

				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, channelID, ccv.INITIALIZING)
				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID, "connection-2"}
			},
			expError: true,
		},
		{
			name: "connection does not exist",
			setup: func(suite *KeeperTestSuite) {
				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, channelID, ccv.INITIALIZING)
				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{"connection-dne"}
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

				// set channel status to INITIALIZING
				suite.childChain.App.(*app.App).ChildKeeper.SetChannelStatus(suite.ctx, channelID, ccv.INITIALIZING)
				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID}
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
			err := suite.childChain.App.(*app.App).ChildKeeper.VerifyParentChain(suite.ctx, channelID, connectionHops)

			if tc.expError {
				suite.Require().Error(err, "invalid case did not return error")
			} else {
				suite.Require().NoError(err, "valid case returned error")
			}
		})
	}
}

// TestValidatorDowntime tests if a slashing packet is sent
// and if the outstanding slashing flag is switched
// when a validator has downtime on the slashing module
func (suite *KeeperTestSuite) TestValidatorDowntime() {
	// initial setup
	suite.SetupCCVChannel()
	suite.SendEmptyVSCPacket()

	app, ctx := suite.childChain.App.(*app.App), suite.childChain.GetContext()
	channelID := suite.path.EndpointA.ChannelID

	// pick a cross-chain validator
	vals := app.ChildKeeper.GetAllCCValidator(ctx)
	consAddr := sdk.ConsAddress(vals[0].Address)

	// save sign info before slashing
	// signInfo, found := app.SlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)
	// suite.Require().True(found)

	// save next sequence before sending a slashing packet
	seq, ok := app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(ctx, types.PortID, channelID)
	suite.Require().True(ok)

	// Sign 1000 blocks
	valPower := int64(1)
	height := int64(0)
	for ; height < app.SlashingKeeper.SignedBlocksWindow(ctx); height++ {
		ctx = ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(ctx, vals[0].Address, valPower, true)
	}
	// Miss 500 blocks and expect a slashing packet to be sent
	for ; height < app.SlashingKeeper.SignedBlocksWindow(ctx)+(app.SlashingKeeper.SignedBlocksWindow(ctx)-app.SlashingKeeper.MinSignedPerWindow(ctx))+1; height++ {
		ctx = ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(ctx, vals[0].Address, valPower, false)
	}

	// check validator signing info
	res, _ := app.SlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)
	// expect increased jail time
	suite.Require().True(res.JailedUntil.Equal(ctx.BlockTime().Add(app.SlashingKeeper.DowntimeJailDuration(ctx))), "did not update validator jailed until signing info")
	// expect missed block counters reseted
	suite.Require().Zero(res.MissedBlocksCounter, "did not reset validator missed block counter")
	suite.Require().Zero(res.IndexOffset)
	app.SlashingKeeper.IterateValidatorMissedBlockBitArray(ctx, consAddr, func(_ int64, missed bool) bool {
		suite.Require().True(missed)
		return false
	})

	// verify that the slashing packet was sent
	commit := app.IBCKeeper.ChannelKeeper.GetPacketCommitment(ctx, types.PortID, channelID, seq)
	suite.Require().NotNil(commit, "did not found slashing packet commitment")

	// verify that the slashing packet was sent
	suite.Require().True(app.ChildKeeper.OutstandingDowntime(ctx, consAddr))

	// check that the outstanding slashing flag prevents
	// to update the jailed validator's missed block
	for ; height < app.SlashingKeeper.SignedBlocksWindow(ctx)+
		(2*(app.SlashingKeeper.SignedBlocksWindow(ctx)-app.SlashingKeeper.MinSignedPerWindow(ctx))+1); height++ {
		ctx = ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(ctx, vals[0].Address, valPower, false)
	}

	res, _ = app.SlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)

	suite.Require().Zero(res.MissedBlocksCounter, "did not reset validator missed block counter")
	suite.Require().Zero(res.IndexOffset)
	app.SlashingKeeper.IterateValidatorMissedBlockBitArray(ctx, consAddr, func(_ int64, missed bool) bool {
		suite.Require().True(missed, "did not reset validator missed block bit array")
		return false
	})
}

func (suite *KeeperTestSuite) TestPendingSlashRequestsLogic() {
	suite.SetupCCVChannel()

	app := suite.childChain.App.(*app.App)
	ctx := suite.childChain.GetContext()
	channelID := suite.path.EndpointA.ChannelID

	// check that CCV channel isn't established
	_, ok := app.ChildKeeper.GetParentChannel(ctx)
	suite.Require().False(ok)

	// expect to store 4 slash requests
	validators := []abci.Validator{}
	for i := 0; i < 4; i++ {
		addr := ed25519.GenPrivKey().PubKey().Address()
		val := abci.Validator{
			Address: addr}
		app.ChildKeeper.SendSlashPacket(ctx, val, 0, 0, 0)
		validators = append(validators, val)
	}

	// expect to store a duplicate for each slash request
	// in order to test the outstanding downtime logic
	for _, v := range validators {
		app.ChildKeeper.SendSlashPacket(ctx, v, 0, 0, 0)
	}

	// verify that all requests are stored
	requests := app.ChildKeeper.GetPendingSlashRequests(ctx)
	suite.Require().Len(requests, 8)

	// save child next sequence
	seq, _ := app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(ctx, types.PortID, channelID)

	// establish ccv channel by sending an empty VSC packet to child endpoint
	suite.SendEmptyVSCPacket()

	// check that each pending slash requests is sent once
	// and that the duplicates are skipped (due to the outstanding downtime flag)
	for i := 0; i < 7; i++ {
		commit := app.IBCKeeper.ChannelKeeper.GetPacketCommitment(ctx, types.PortID, channelID, seq+uint64(i))
		if i > 3 {
			suite.Require().Nil(commit)
			continue
		}
		suite.Require().NotNil(commit)
	}

	// check that outstanding downtime flags are all set to true
	for _, r := range requests {
		if r.Downtime {
			consAddr := sdk.ConsAddress(r.Packet.Validator.Address)
			suite.Require().True(app.ChildKeeper.OutstandingDowntime(ctx, consAddr))
		}
	}

	// check that pending slash requests get cleared after being sent
	requests = app.ChildKeeper.GetPendingSlashRequests(ctx)
	suite.Require().Len(requests, 0)

	// check that slash requests aren't stored when channel is established
	app.ChildKeeper.SendSlashPacket(ctx, abci.Validator{}, 0, 0, 0)

	requests = app.ChildKeeper.GetPendingSlashRequests(ctx)
	suite.Require().Len(requests, 0)
}

func (suite *KeeperTestSuite) TestCrossChainValidator() {
	app := suite.childChain.App.(*app.App)
	ctx := suite.childChain.GetContext()

	// should return false
	ccVal, foud := app.ChildKeeper.GetCCValidator(ctx, ed25519.GenPrivKey().PubKey().Address())
	suite.Require().False(foud)

	// get a validator from child chain
	val := suite.parentChain.Vals.Validators[0]

	// set cross chain validator
	ccVal = types.NewCCValidator(val.Address, 1000)

	app.ChildKeeper.SetCCValidator(ctx, ccVal)

	// should return true
	ccVal, foud = app.ChildKeeper.GetCCValidator(ctx, ccVal.Address)
	suite.Require().True(foud)

	app.ChildKeeper.DeleteCCValidator(ctx, ccVal.Address)

	// should return false
	ccVal, foud = app.ChildKeeper.GetCCValidator(ctx, ccVal.Address)
	suite.Require().False(foud)
}

func (suite *KeeperTestSuite) TestPendingSlashRequests() {
	childKeeper := suite.childChain.App.(*app.App).ChildKeeper
	ctx := suite.childChain.GetContext()

	// prepare test setup by storing 10 pending slash requests
	request := []types.SlashRequest{}
	for i := 0; i < 10; i++ {
		request = append(request, types.SlashRequest{})
		childKeeper.SetPendingSlashRequests(ctx, request)
	}

	// test set, append and clear operations
	testCases := []struct {
		operation func()
		expLen    int
	}{{
		operation: func() {},
		expLen:    10,
	}, {
		operation: func() { childKeeper.AppendPendingSlashRequests(ctx, types.SlashRequest{}) },
		expLen:    11,
	}, {
		operation: func() { childKeeper.ClearPendingSlashRequests(ctx) },
		expLen:    0,
	},
	}

	for _, t := range testCases {
		t.operation()
		requests := childKeeper.GetPendingSlashRequests(ctx)
		suite.Require().Len(requests, t.expLen)
	}
}

// SendEmptyVSCPacket sends a VSC packet without any changes
// to ensure that the channel gets established
func (suite *KeeperTestSuite) SendEmptyVSCPacket() {

	childKeeper := suite.childChain.App.(*app.App).ChildKeeper
	parentKeeper := suite.parentChain.App.(*app.App).ParentKeeper

	oldBlockTime := suite.parentChain.GetContext().BlockTime()
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())

	valUpdateID := parentKeeper.GetValidatorSetUpdateId(suite.parentChain.GetContext())

	pd := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{},
		valUpdateID,
		nil,
	)

	seq, ok := suite.parentChain.App.(*app.App).GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(
		suite.parentChain.GetContext(), parenttypes.PortID, suite.path.EndpointB.ChannelID)
	suite.Require().True(ok)

	packet := channeltypes.NewPacket(pd.GetBytes(), seq, parenttypes.PortID, suite.path.EndpointB.ChannelID,
		childtypes.PortID, suite.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	suite.path.EndpointB.SendPacket(packet)
	err := suite.path.EndpointA.RecvPacket(packet)
	suite.Require().NoError(err)

	// check that the channel is established
	status := childKeeper.GetChannelStatus(suite.childChain.GetContext(), suite.path.EndpointA.ChannelID)
	suite.Require().EqualValues(int32(2), status)
}

func TestKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(KeeperTestSuite))
}
