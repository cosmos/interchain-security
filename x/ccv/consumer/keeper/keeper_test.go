package keeper_test

import (
	"bytes"
	"fmt"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/ibc-go/modules/core/exported"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	"github.com/stretchr/testify/require"
	"github.com/stretchr/testify/suite"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

type KeeperTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState

	path *ibctesting.Path

	ctx sdk.Context
}

func (suite *KeeperTestSuite) SetupTest() {
	suite.coordinator, suite.providerChain, suite.consumerChain = simapp.NewProviderConsumerCoordinator(suite.T())

	// valsets must match
	providerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)
	consumerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.consumerChain.Vals)
	suite.Require().True(len(providerValUpdates) == len(consumerValUpdates), "initial valset not matching")
	for i := 0; i < len(providerValUpdates); i++ {
		addr1 := utils.GetChangePubKeyAddress(providerValUpdates[i])
		addr2 := utils.GetChangePubKeyAddress(consumerValUpdates[i])
		suite.Require().True(bytes.Equal(addr1, addr2), "validator mismatch")
	}

	// move both chains to the next block
	suite.providerChain.NextBlock()
	suite.consumerChain.NextBlock()

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.CreateConsumerClient(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	suite.Require().NoError(err)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), &consumerGenesis)
	suite.providerClient = consumerGenesis.ProviderClientState
	suite.providerConsState = consumerGenesis.ProviderConsensusState

	// create path for the CCV channel
	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer client not found")
	suite.path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	suite.Require().True(found, "provider client not found")
	suite.path.EndpointA.ClientID = providerClient
	// - client config
	providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
	// - channel config
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = ccv.Version
	suite.path.EndpointB.ChannelConfig.Version = ccv.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	err = suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.Require().NoError(err)
	err = suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)
	suite.Require().NoError(err)

	suite.ctx = suite.consumerChain.GetContext()
}

func (suite *KeeperTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)
	suite.coordinator.CreateChannels(suite.path)
}

func (suite *KeeperTestSuite) TestUnbondingTime() {
	// The unbonding time on the consumer was already set during InitGenesis()
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.DeleteUnbondingTime(suite.ctx)
	_, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.ctx)
	suite.Require().False(ok)
	unbondingPeriod := time.Hour * 24 * 7 * 3
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetUnbondingTime(suite.ctx, unbondingPeriod)
	storedUnbondingPeriod, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.ctx)
	suite.Require().True(ok)
	suite.Require().True(storedUnbondingPeriod == unbondingPeriod)

}

func (suite *KeeperTestSuite) TestProviderClient() {
	providerClient, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.ctx)
	suite.Require().True(ok)

	clientState, _ := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(suite.ctx, providerClient)
	suite.Require().Equal(suite.providerClient, clientState, "stored client state does not match genesis provider client")
}

func (suite *KeeperTestSuite) TestProviderChannel() {
	_, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderChannel(suite.ctx)
	suite.Require().False(ok)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channelID")
	channelID, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderChannel(suite.ctx)
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

	err = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPendingChanges(suite.ctx, pd)
	suite.Require().NoError(err)
	gotPd, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPendingChanges(suite.ctx)
	suite.Require().True(ok)
	suite.Require().Equal(&pd, gotPd, "packet data in store does not equal packet data set")
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.DeletePendingChanges(suite.ctx)
	gotPd, ok = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPendingChanges(suite.ctx)
	suite.Require().False(ok)
	suite.Require().Nil(gotPd, "got non-nil pending changes after Delete")
}

func (suite *KeeperTestSuite) TestPacketMaturityTime() {
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPacketMaturityTime(suite.ctx, 1, 10)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPacketMaturityTime(suite.ctx, 2, 25)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPacketMaturityTime(suite.ctx, 5, 15)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPacketMaturityTime(suite.ctx, 6, 40)

	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.DeletePacketMaturityTime(suite.ctx, 6)

	suite.Require().Equal(uint64(10), suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 1))
	suite.Require().Equal(uint64(25), suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 2))
	suite.Require().Equal(uint64(15), suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 5))
	suite.Require().Equal(uint64(0), suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 3))
	suite.Require().Equal(uint64(0), suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 6))

	orderedTimes := [][]uint64{{1, 10}, {2, 25}, {5, 15}}
	i := 0

	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.IteratePacketMaturityTime(suite.ctx, func(seq, time uint64) bool {
		// require that we iterate through unbonding time in order of sequence
		suite.Require().Equal(orderedTimes[i][0], seq)
		suite.Require().Equal(orderedTimes[i][1], time)
		i++
		return false
	})
}

func (suite *KeeperTestSuite) TestVerifyProviderChain() {
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
				// create consumer client on provider chain
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				suite.CreateCustomClient(suite.path.EndpointB, consumerUnbondingPeriod)
				err := suite.path.EndpointB.CreateClient()
				suite.Require().NoError(err)

				suite.coordinator.CreateConnections(suite.path)

				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID}
			},
			connectionHops: []string{suite.path.EndpointA.ConnectionID},
			expError:       false,
		},
		{
			name: "connection hops is not length 1",
			setup: func(suite *KeeperTestSuite) {
				// create consumer client on provider chain
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				suite.CreateCustomClient(suite.path.EndpointB, consumerUnbondingPeriod)

				suite.coordinator.CreateConnections(suite.path)

				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID, "connection-2"}
			},
			expError: true,
		},
		{
			name: "connection does not exist",
			setup: func(suite *KeeperTestSuite) {
				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{"connection-dne"}
			},
			expError: true,
		},
		{
			name: "clientID does not match",
			setup: func(suite *KeeperTestSuite) {
				// create consumer client on provider chain
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				suite.CreateCustomClient(suite.path.EndpointB, consumerUnbondingPeriod)

				// create a new provider client on consumer chain that is different from the one in genesis
				suite.CreateCustomClient(suite.path.EndpointA, providerUnbondingPeriod)

				suite.coordinator.CreateConnections(suite.path)

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

			// Verify ProviderChain on consumer chain using path returned by setup
			err := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.VerifyProviderChain(suite.ctx, channelID, connectionHops)

			if tc.expError {
				suite.Require().Error(err, "invalid case did not return error")
			} else {
				suite.Require().NoError(err, "valid case returned error")
			}
		})
	}
}

// CreateCustomClient creates an IBC client on the endpoint
// using the given unbonding period.
// It will update the clientID for the endpoint if the message
// is successfully executed.
func (suite *KeeperTestSuite) CreateCustomClient(endpoint *ibctesting.Endpoint, unbondingPeriod time.Duration) {
	// ensure counterparty has committed state
	endpoint.Chain.Coordinator.CommitBlock(endpoint.Counterparty.Chain)

	suite.Require().Equal(exported.Tendermint, endpoint.ClientConfig.GetClientType(), "only Tendermint client supported")

	tmConfig, ok := endpoint.ClientConfig.(*ibctesting.TendermintConfig)
	require.True(endpoint.Chain.T, ok)
	tmConfig.UnbondingPeriod = unbondingPeriod
	tmConfig.TrustingPeriod = unbondingPeriod / utils.TrustingPeriodFraction

	height := endpoint.Counterparty.Chain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}
	clientState := ibctmtypes.NewClientState(
		endpoint.Counterparty.Chain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	consensusState := endpoint.Counterparty.Chain.LastHeader.ConsensusState()

	msg, err := clienttypes.NewMsgCreateClient(
		clientState, consensusState, endpoint.Chain.SenderAccount.GetAddress().String(),
	)
	require.NoError(endpoint.Chain.T, err)

	res, err := endpoint.Chain.SendMsgs(msg)
	require.NoError(endpoint.Chain.T, err)

	endpoint.ClientID, err = ibctesting.ParseClientIDFromEvents(res.GetEvents())
	require.NoError(endpoint.Chain.T, err)
}

// TestValidatorDowntime tests if a slash packet is sent
// and if the outstanding slashing flag is switched
// when a validator has downtime on the slashing module
func (suite *KeeperTestSuite) TestValidatorDowntime() {
	// initial setup
	suite.SetupCCVChannel()
	suite.SendEmptyVSCPacket()

	// sync suite context after CCV channel is established
	suite.ctx = suite.consumerChain.GetContext()

	app := suite.consumerChain.App.(*appConsumer.App)
	channelID := suite.path.EndpointA.ChannelID

	// pick a cross-chain validator
	vals := app.ConsumerKeeper.GetAllCCValidator(suite.ctx)
	consAddr := sdk.ConsAddress(vals[0].Address)

	// save next sequence before sending a slash packet
	seq, ok := app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(suite.ctx, types.PortID, channelID)
	suite.Require().True(ok)

	// Sign 100 blocks
	valPower := int64(1)
	height, signedBlocksWindow := int64(0), app.SlashingKeeper.SignedBlocksWindow(suite.ctx)
	for ; height < signedBlocksWindow; height++ {
		suite.ctx = suite.ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(suite.ctx, vals[0].Address, valPower, true)
	}

	missedBlockThreshold := (2 * signedBlocksWindow) - app.SlashingKeeper.MinSignedPerWindow(suite.ctx)

	// construct slash packet to be sent and get its commit
	packetData := ccv.NewSlashPacketData(
		abci.Validator{Address: vals[0].Address, Power: valPower},
		// get the VSC ID mapping the infraction height
		app.ConsumerKeeper.GetHeightValsetUpdateID(suite.ctx, uint64(missedBlockThreshold-sdk.ValidatorUpdateDelay-1)),
		stakingtypes.Downtime,
	)
	expCommit := suite.commitSlashPacket(suite.ctx, packetData)

	// Miss 50 blocks and expect a slash packet to be sent
	for ; height <= missedBlockThreshold; height++ {
		suite.ctx = suite.ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(suite.ctx, vals[0].Address, valPower, false)
	}

	// check validator signing info
	res, _ := app.SlashingKeeper.GetValidatorSigningInfo(suite.ctx, consAddr)
	// expect increased jail time
	suite.Require().True(res.JailedUntil.Equal(suite.ctx.BlockTime().Add(app.SlashingKeeper.DowntimeJailDuration(suite.ctx))), "did not update validator jailed until signing info")
	// expect missed block counters reseted
	suite.Require().Zero(res.MissedBlocksCounter, "did not reset validator missed block counter")
	suite.Require().Zero(res.IndexOffset)
	app.SlashingKeeper.IterateValidatorMissedBlockBitArray(suite.ctx, consAddr, func(_ int64, missed bool) bool {
		suite.Require().True(missed)
		return false
	})

	// verify that the slash packet was sent
	gotCommit := app.IBCKeeper.ChannelKeeper.GetPacketCommitment(suite.ctx, types.PortID, channelID, seq)
	suite.Require().NotNil(gotCommit, "did not found slash packet commitment")
	suite.Require().EqualValues(expCommit, gotCommit, "invalid slash packet commitment")

	// verify that the slash packet was sent
	suite.Require().True(app.ConsumerKeeper.OutstandingDowntime(suite.ctx, consAddr))

	// check that the outstanding slashing flag prevents the jailed validator to keep missing block
	for ; height < missedBlockThreshold+signedBlocksWindow; height++ {
		suite.ctx = suite.ctx.WithBlockHeight(height)
		app.SlashingKeeper.HandleValidatorSignature(suite.ctx, vals[0].Address, valPower, false)
	}

	res, _ = app.SlashingKeeper.GetValidatorSigningInfo(suite.ctx, consAddr)

	suite.Require().Zero(res.MissedBlocksCounter, "did not reset validator missed block counter")
	suite.Require().Zero(res.IndexOffset)
	app.SlashingKeeper.IterateValidatorMissedBlockBitArray(suite.ctx, consAddr, func(_ int64, missed bool) bool {
		suite.Require().True(missed, "did not reset validator missed block bit array")
		return false
	})
}

// TestValidatorDoubleSigning tests if a slash packet is sent
// when a double-signing evidence is handled by the evidence module
func (suite *KeeperTestSuite) TestValidatorDoubleSigning() {
	// initial setup
	suite.SetupCCVChannel()
	suite.SendEmptyVSCPacket()

	// sync suite context after CCV channel is established
	suite.ctx = suite.consumerChain.GetContext()

	app := suite.consumerChain.App.(*appConsumer.App)
	channelID := suite.path.EndpointA.ChannelID

	// create a validator pubkey and address
	// note that the validator wont't necessarily be in valset to due the TM delay
	pubkey := ed25519.GenPrivKey().PubKey()
	consAddr := sdk.ConsAddress(pubkey.Address())

	// set an arbitrary infraction height
	infractionHeight := suite.ctx.BlockHeight() - 1
	power := int64(100)

	// create evidence
	e := &evidencetypes.Equivocation{
		Height:           infractionHeight,
		Power:            power,
		Time:             time.Now().UTC(),
		ConsensusAddress: consAddr.String(),
	}

	// add validator signing-info to the store
	app.SlashingKeeper.SetValidatorSigningInfo(suite.ctx, consAddr, slashingtypes.ValidatorSigningInfo{
		Address:    consAddr.String(),
		Tombstoned: false,
	})

	// save next sequence before sending a slash packet
	seq, ok := app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(suite.ctx, types.PortID, channelID)
	suite.Require().True(ok)

	// construct slash packet data and get the expcted commit hash
	packetData := ccv.NewSlashPacketData(
		abci.Validator{Address: consAddr.Bytes(), Power: power},
		// get VSC ID mapping to the infraction height with the TM delay substracted
		app.ConsumerKeeper.GetHeightValsetUpdateID(suite.ctx, uint64(infractionHeight-sdk.ValidatorUpdateDelay)),
		stakingtypes.DoubleSign,
	)
	expCommit := suite.commitSlashPacket(suite.ctx, packetData)

	// expect to send slash packet when handling double-sign evidence
	app.EvidenceKeeper.HandleEquivocationEvidence(suite.ctx, e)

	// check that slash packet is sent
	gotCommit := app.IBCKeeper.ChannelKeeper.GetPacketCommitment(suite.ctx, types.PortID, channelID, seq)
	suite.NotNil(gotCommit)

	suite.Require().EqualValues(expCommit, gotCommit)
}

func (suite *KeeperTestSuite) TestSendSlashPacket() {
	suite.SetupCCVChannel()

	app := suite.consumerChain.App.(*appConsumer.App)
	ctx := suite.consumerChain.GetContext()
	channelID := suite.path.EndpointA.ChannelID

	// check that CCV channel isn't established
	_, ok := app.ConsumerKeeper.GetProviderChannel(ctx)
	suite.Require().False(ok)

	// expect to store 4 slash requests for downtime
	// and 4 slash request for double-signing
	type slashedVal struct {
		validator  abci.Validator
		infraction stakingtypes.InfractionType
	}
	slashedVals := []slashedVal{}

	infraction := stakingtypes.Downtime
	for j := 0; j < 2; j++ {
		for i := 0; i < 4; i++ {
			addr := ed25519.GenPrivKey().PubKey().Address()
			val := abci.Validator{
				Address: addr}
			app.ConsumerKeeper.SendSlashPacket(ctx, val, 0, infraction)
			slashedVals = append(slashedVals, slashedVal{validator: val, infraction: infraction})
		}
		infraction = stakingtypes.DoubleSign
	}

	// expect to store a duplicate for each slash request
	// in order to test the outstanding downtime logic
	for _, sv := range slashedVals {
		app.ConsumerKeeper.SendSlashPacket(ctx, sv.validator, 0, sv.infraction)
	}

	// verify that all requests are stored
	requests := app.ConsumerKeeper.GetPendingSlashRequests(ctx)
	suite.Require().Len(requests, 16)

	// save consumer next sequence
	seq, _ := app.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(ctx, types.PortID, channelID)

	// establish ccv channel by sending an empty VSC packet to consumer endpoint
	suite.SendEmptyVSCPacket()

	// check that each pending slash requests is sent once
	// and that the downtime slash request duplicates are skipped (due to the outstanding downtime flag)
	for i := 0; i < 16; i++ {
		commit := app.IBCKeeper.ChannelKeeper.GetPacketCommitment(ctx, types.PortID, channelID, seq+uint64(i))
		if i > 11 {
			suite.Require().Nil(commit)
			continue
		}
		suite.Require().NotNil(commit)
	}

	// check that outstanding downtime flags
	// are all set to true for validators slashed for downtime requests
	for _, r := range requests {
		downtime := r.Infraction == stakingtypes.Downtime
		if downtime {
			consAddr := sdk.ConsAddress(r.Packet.Validator.Address)
			suite.Require().True(app.ConsumerKeeper.OutstandingDowntime(ctx, consAddr))
		}
	}

	// check that pending slash requests get cleared after being sent
	requests = app.ConsumerKeeper.GetPendingSlashRequests(ctx)
	suite.Require().Len(requests, 0)

	// check that slash requests aren't stored when channel is established
	app.ConsumerKeeper.SendSlashPacket(ctx, abci.Validator{}, 0, stakingtypes.Downtime)
	app.ConsumerKeeper.SendSlashPacket(ctx, abci.Validator{}, 0, stakingtypes.DoubleSign)

	requests = app.ConsumerKeeper.GetPendingSlashRequests(ctx)
	suite.Require().Len(requests, 0)
}

func (suite *KeeperTestSuite) TestCrossChainValidator() {
	app := suite.consumerChain.App.(*appConsumer.App)
	ctx := suite.consumerChain.GetContext()

	// should return false
	_, foud := app.ConsumerKeeper.GetCCValidator(ctx, ed25519.GenPrivKey().PubKey().Address())
	suite.Require().False(foud)

	// get a validator from consumer chain
	val := suite.providerChain.Vals.Validators[0]

	// convert validator publick key
	pubkey, err := cryptocodec.FromTmPubKeyInterface(val.PubKey)
	suite.Require().NoError(err)

	// set cross chain validator
	ccVal, err := types.NewCCValidator(val.Address, 1000, pubkey)
	suite.Require().NoError(err)

	app.ConsumerKeeper.SetCCValidator(ctx, ccVal)

	// should return true
	gotCCVal, found := app.ConsumerKeeper.GetCCValidator(ctx, ccVal.Address)
	suite.Require().True(found)

	// verify the returned validator values
	suite.Require().EqualValues(ccVal, gotCCVal)

	// expect to return the same consensus pubkey
	pk, err := gotCCVal.ConsPubKey()
	suite.Require().NoError(err)
	gotPK, err := gotCCVal.ConsPubKey()
	suite.Require().NoError(err)

	suite.Require().True(pk.Equals(gotPK))

	// delete validator
	app.ConsumerKeeper.DeleteCCValidator(ctx, ccVal.Address)

	// should return false
	_, foud = app.ConsumerKeeper.GetCCValidator(ctx, ccVal.Address)
	suite.Require().False(foud)
}

func (suite *KeeperTestSuite) TestPendingSlashRequests() {
	consumerKeeper := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	ctx := suite.consumerChain.GetContext()

	// prepare test setup by storing 10 pending slash requests
	request := []types.SlashRequest{}
	for i := 0; i < 10; i++ {
		request = append(request, types.SlashRequest{})
		consumerKeeper.SetPendingSlashRequests(ctx, request)
	}

	// test set, append and clear operations
	testCases := []struct {
		operation func()
		expLen    int
	}{{
		operation: func() {},
		expLen:    10,
	}, {
		operation: func() { consumerKeeper.AppendPendingSlashRequests(ctx, types.SlashRequest{}) },
		expLen:    11,
	}, {
		operation: func() { consumerKeeper.ClearPendingSlashRequests(ctx) },
		expLen:    0,
	},
	}

	for _, t := range testCases {
		t.operation()
		requests := consumerKeeper.GetPendingSlashRequests(ctx)
		suite.Require().Len(requests, t.expLen)
	}
}

// SendEmptyVSCPacket sends a VSC packet without any changes
// to ensure that the channel gets established
func (suite *KeeperTestSuite) SendEmptyVSCPacket() {
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper

	oldBlockTime := suite.providerChain.GetContext().BlockTime()
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())

	valUpdateID := providerKeeper.GetValidatorSetUpdateId(suite.providerChain.GetContext())

	pd := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{},
		valUpdateID,
		nil,
	)

	seq, ok := suite.providerChain.App.(*appProvider.App).GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(
		suite.providerChain.GetContext(), providertypes.PortID, suite.path.EndpointB.ChannelID)
	suite.Require().True(ok)

	packet := channeltypes.NewPacket(pd.GetBytes(), seq, providertypes.PortID, suite.path.EndpointB.ChannelID,
		consumertypes.PortID, suite.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	err := suite.path.EndpointB.SendPacket(packet)
	suite.Require().NoError(err)
	err = suite.path.EndpointA.RecvPacket(packet)
	suite.Require().NoError(err)
}

func TestKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(KeeperTestSuite))
}

// commitSlashPacket returns a commit hash for the given slash packet data
// Note that it must be called before sending the embedding IBC packet.
func (suite *KeeperTestSuite) commitSlashPacket(ctx sdk.Context, packetData ccv.SlashPacketData) []byte {
	oldBlockTime := ctx.BlockTime()
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())

	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, consumertypes.PortID, suite.path.EndpointA.ChannelID,
		providertypes.PortID, suite.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	return channeltypes.CommitPacket(suite.consumerChain.App.AppCodec(), packet)
}

func (suite *KeeperTestSuite) TestProviderChannelClosed() {
	// Init consumer states and provider channel
	suite.SetupCCVChannel()
	suite.SendEmptyVSCPacket()
	channelID, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderChannel(suite.consumerChain.GetContext())
	suite.Require().True(found)

	// Close provider channel
	err := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.ChanCloseInit(suite.consumerChain.GetContext(), types.PortID, channelID)
	suite.Require().NoError(err)
	suite.Require().True(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.IsChannelClosed(suite.consumerChain.GetContext(), channelID))

	// Init all consumer states left
	consAddr := sdk.ConsAddress(ed25519.GenPrivKey().PubKey().Address().Bytes())
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetOutstandingDowntime(suite.consumerChain.GetContext(), consAddr)
	err = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPendingChanges(
		suite.consumerChain.GetContext(),
		ccv.ValidatorSetChangePacketData{ValsetUpdateId: 1},
	)
	suite.Require().NoError(err)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPendingSlashRequests(
		suite.consumerChain.GetContext(),
		[]types.SlashRequest{{Infraction: stakingtypes.Downtime}, {Infraction: stakingtypes.DoubleSign}},
	)

	// check that begin blocker panics when the channel is closed
	// and that the provider states are cleaned up
	defer func() {
		if r := recover(); r != nil {
			_, found = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderChannel(suite.consumerChain.GetContext())
			suite.Require().False(found)

			_, found = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderChannel(suite.consumerChain.GetContext())
			suite.Require().False(found)

			_, found = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
			suite.Require().False(found)

			p := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPort(suite.consumerChain.GetContext())
			suite.Require().Zero(p)

			vals := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetAllCCValidator(suite.consumerChain.GetContext())
			suite.Require().Zero(vals)

			_, found = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPendingChanges(suite.consumerChain.GetContext())
			suite.Require().False(found)

			_, found = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.consumerChain.GetContext())
			suite.Require().False(found)

			suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.IteratePacketMaturityTime(suite.consumerChain.GetContext(), func(vscId, timeNs uint64) bool {
				suite.Require().Fail("packet maturity time is not empty")
				return true
			})

			suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.IterateOutstandingDowntime(suite.consumerChain.GetContext(), func(_ sdk.ConsAddress) bool {
				suite.Require().Fail("outstanding downtime is not empty")
				return true
			})

			suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.IterateHistoricalInfo(suite.consumerChain.GetContext(), func(_ uint64) bool {
				suite.Require().Fail("historical info is not empty")
				return true
			})

			suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.IterateHeightValsetUpdateID(suite.consumerChain.GetContext(), func(height uint64) bool {
				suite.Require().Fail("height to valset update ID mapping is not empty")
				return true
			})

			reqs := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPendingSlashRequests(suite.consumerChain.GetContext())
			suite.Require().Zero(reqs)

			suite.Require().Zero(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetParams(suite.consumerChain.GetContext()))

			return
		}
		suite.Require().Fail("Begin blocker did not panic with a closed channel")

	}()
	suite.consumerChain.App.(*appConsumer.App).BeginBlocker(suite.consumerChain.GetContext(), abci.RequestBeginBlock{})

}
