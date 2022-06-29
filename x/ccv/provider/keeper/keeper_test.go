package keeper_test

import (
	"bytes"
	"fmt"
	"testing"
	"time"

	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	ibcsimapp "github.com/cosmos/ibc-go/v3/testing/simapp"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type KeeperTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

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
		suite.Require().True(bytes.Compare(addr1, addr2) == 0, "validator mismatch")
	}

	// move both chains to the next block
	suite.providerChain.NextBlock()
	suite.consumerChain.NextBlock()

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	suite.providerChain.App.(*appProvider.App).ProviderKeeper.CreateConsumerClient(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), &consumerGenesis)

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
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)

	suite.ctx = suite.providerChain.GetContext()
}

func TestKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(KeeperTestSuite))
}

func (suite *KeeperTestSuite) TestValsetUpdateBlockHeight() {
	app := suite.providerChain.App.(*appProvider.App)
	ctx := suite.ctx

	blockHeight := app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(0))
	suite.Require().Zero(blockHeight)

	app.ProviderKeeper.SetValsetUpdateBlockHeight(ctx, uint64(1), uint64(2))
	blockHeight = app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(1))
	suite.Require().Equal(blockHeight, uint64(2))

	app.ProviderKeeper.DeleteValsetUpdateBlockHeight(ctx, uint64(1))
	blockHeight = app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(1))
	suite.Require().Zero(blockHeight)

	app.ProviderKeeper.SetValsetUpdateBlockHeight(ctx, uint64(1), uint64(2))
	app.ProviderKeeper.SetValsetUpdateBlockHeight(ctx, uint64(3), uint64(4))
	blockHeight = app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(3))
	suite.Require().Equal(blockHeight, uint64(4))
}

func (suite *KeeperTestSuite) TestSlashAcks() {
	app := suite.providerChain.App.(*appProvider.App)
	ctx := suite.ctx

	var chainsAcks [][]string

	penaltiesfN := func() (penalties []string) {
		app.ProviderKeeper.IterateSlashAcks(ctx, func(id string, acks []string) bool {
			chainsAcks = append(chainsAcks, acks)
			return true
		})
		return
	}

	chainID := "consumer"

	acks := app.ProviderKeeper.GetSlashAcks(ctx, chainID)
	suite.Require().Nil(acks)

	p := []string{"alice", "bob", "charlie"}
	app.ProviderKeeper.SetSlashAcks(ctx, chainID, p)

	acks = app.ProviderKeeper.GetSlashAcks(ctx, chainID)
	suite.Require().NotNil(acks)

	suite.Require().Len(acks, 3)
	emptied := app.ProviderKeeper.EmptySlashAcks(ctx, chainID)
	suite.Require().Len(emptied, 3)

	acks = app.ProviderKeeper.GetSlashAcks(ctx, chainID)
	suite.Require().Nil(acks)

	chains := []string{"c1", "c2", "c3"}

	for _, c := range chains {
		app.ProviderKeeper.SetSlashAcks(ctx, c, p)
	}

	penaltiesfN()
	suite.Require().Len(chainsAcks, len(chains))
}

func (suite *KeeperTestSuite) TestAppendSlashAck() {
	app := suite.providerChain.App.(*appProvider.App)
	ctx := suite.ctx

	p := []string{"alice", "bob", "charlie"}
	chains := []string{"c1", "c2"}
	app.ProviderKeeper.SetSlashAcks(ctx, chains[0], p)

	app.ProviderKeeper.AppendSlashAck(ctx, chains[0], p[0])
	acks := app.ProviderKeeper.GetSlashAcks(ctx, chains[0])
	suite.Require().NotNil(acks)
	suite.Require().Len(acks, len(p)+1)

	app.ProviderKeeper.AppendSlashAck(ctx, chains[1], p[0])
	acks = app.ProviderKeeper.GetSlashAcks(ctx, chains[1])
	suite.Require().NotNil(acks)
	suite.Require().Len(acks, 1)
}

func (suite *KeeperTestSuite) TestPendingVSCs() {
	app := suite.providerChain.App.(*appProvider.App)
	ctx := suite.ctx

	chainID := "consumer"

	_, found := app.ProviderKeeper.GetPendingVSCs(ctx, chainID)
	suite.Require().False(found)

	pks := ibcsimapp.CreateTestPubKeys(4)
	var ppks [4]tmprotocrypto.PublicKey
	for i, pk := range pks {
		ppks[i], _ = cryptocodec.ToTmProtoPublicKey(pk)
	}

	packetList := []ccv.ValidatorSetChangePacketData{
		{
			ValidatorUpdates: []abci.ValidatorUpdate{
				{PubKey: ppks[0], Power: 1},
				{PubKey: ppks[1], Power: 2},
			},
			ValsetUpdateId: 1,
		},
		{
			ValidatorUpdates: []abci.ValidatorUpdate{
				{PubKey: ppks[2], Power: 3},
			},
			ValsetUpdateId: 2,
		},
	}
	for _, packet := range packetList {
		app.ProviderKeeper.AppendPendingVSC(ctx, chainID, packet)
	}

	packets, found := app.ProviderKeeper.GetPendingVSCs(ctx, chainID)
	suite.Require().True(found)
	suite.Require().Len(packets, 2)

	newPacket := ccv.ValidatorSetChangePacketData{
		ValidatorUpdates: []abci.ValidatorUpdate{
			{PubKey: ppks[3], Power: 4},
		},
		ValsetUpdateId: 3,
	}
	app.ProviderKeeper.AppendPendingVSC(ctx, chainID, newPacket)
	emptied := app.ProviderKeeper.EmptyPendingVSC(ctx, chainID)
	suite.Require().Len(emptied, 3)
	suite.Require().True(emptied[len(emptied)-1].ValsetUpdateId == 3)
	suite.Require().True(emptied[len(emptied)-1].GetValidatorUpdates()[0].PubKey.String() == ppks[3].String())

	_, found = app.ProviderKeeper.GetPendingVSCs(ctx, chainID)
	suite.Require().False(found)
}

func (suite *KeeperTestSuite) TestInitHeight() {
	app := suite.providerChain.App.(*appProvider.App)
	ctx := suite.ctx

	tc := []struct {
		chainID  string
		expected uint64
	}{
		{expected: 0, chainID: "chain"},
		{expected: 10, chainID: "chain1"},
		{expected: 12, chainID: "chain2"},
	}

	app.ProviderKeeper.SetInitChainHeight(ctx, tc[1].chainID, tc[1].expected)
	app.ProviderKeeper.SetInitChainHeight(ctx, tc[2].chainID, tc[2].expected)

	for _, t := range tc {
		height := app.ProviderKeeper.GetInitChainHeight(ctx, t.chainID)
		suite.Require().EqualValues(t.expected, height)
	}
}

func (suite *KeeperTestSuite) TestHandleSlashPacketDoubleSigning() {
	ProviderKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	providerSlashingKeeper := suite.providerChain.App.(*appProvider.App).SlashingKeeper
	providerStakingKeeper := suite.providerChain.App.(*appProvider.App).StakingKeeper

	tmVal := suite.providerChain.Vals.Validators[0]
	consAddr := sdk.ConsAddress(tmVal.Address)

	// check that validator bonded status
	validator, found := providerStakingKeeper.GetValidatorByConsAddr(suite.ctx, consAddr)
	suite.Require().True(found)
	suite.Require().Equal(stakingtypes.Bonded, validator.GetStatus())

	// set init VSC id for chain0
	ProviderKeeper.SetInitChainHeight(suite.ctx, suite.consumerChain.ChainID, uint64(suite.ctx.BlockHeight()))

	// set validator signing-info
	providerSlashingKeeper.SetValidatorSigningInfo(
		suite.ctx,
		consAddr,
		slashingtypes.ValidatorSigningInfo{Address: consAddr.String()},
	)

	err := ProviderKeeper.HandleSlashPacket(suite.ctx, suite.consumerChain.ChainID,
		ccv.NewSlashPacketData(
			abci.Validator{Address: tmVal.Address, Power: 0},
			uint64(0),
			stakingtypes.DoubleSign,
		),
	)
	suite.NoError(err)

	// verify that validator is jailed in the staking and slashing mdodules' states
	suite.Require().True(providerStakingKeeper.IsValidatorJailed(suite.ctx, consAddr))

	signingInfo, _ := providerSlashingKeeper.GetValidatorSigningInfo(suite.ctx, consAddr)
	suite.Require().True(signingInfo.JailedUntil.Equal(evidencetypes.DoubleSignJailEndTime))
	suite.Require().True(signingInfo.Tombstoned)
}

func (suite *KeeperTestSuite) TestHandleSlashPacketErrors() {
	providerStakingKeeper := suite.providerChain.App.(*appProvider.App).StakingKeeper
	ProviderKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	providerSlashingKeeper := suite.providerChain.App.(*appProvider.App).SlashingKeeper
	consumerChainID := suite.consumerChain.ChainID

	// sync contexts block height
	suite.ctx = suite.providerChain.GetContext()

	// expect an error if initial block height isn't set for consumer chain
	err := ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, ccv.SlashPacketData{})
	suite.Require().Error(err, "slash validator with invalid infraction")

	// save VSC ID
	vID := ProviderKeeper.GetValidatorSetUpdateId(suite.ctx)

	// set faulty block height for current VSC ID
	ProviderKeeper.SetValsetUpdateBlockHeight(suite.ctx, vID, 0)

	// expect an error if block height mapping VSC ID is zero
	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, ccv.SlashPacketData{ValsetUpdateId: vID})
	suite.Require().Error(err, "did slash unknown validator")

	// construct slashing packet with non existing validator
	slashingPkt := ccv.NewSlashPacketData(
		abci.Validator{Address: ed25519.GenPrivKey().PubKey().Address(),
			Power: int64(0)}, uint64(0), stakingtypes.Downtime,
	)

	// Set initial block height for consumer chain
	ProviderKeeper.SetInitChainHeight(suite.ctx, consumerChainID, uint64(suite.ctx.BlockHeight()))

	//expect an error if validator doesn't exist
	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().Error(err, "did slash unknown validator")

	// jail an existing validator
	val := suite.providerChain.Vals.Validators[0]
	consAddr := sdk.ConsAddress(val.Address)
	providerStakingKeeper.Jail(suite.ctx, consAddr)
	// commit block to set VSC ID
	suite.coordinator.CommitBlock(suite.providerChain)
	// Update suite.ctx bc CommitBlock updates only providerChain's current header block height
	suite.ctx = suite.providerChain.GetContext()
	suite.Require().NotZero(ProviderKeeper.GetValsetUpdateBlockHeight(suite.ctx, vID))

	// create validator signing info
	valInfo := slashingtypes.NewValidatorSigningInfo(sdk.ConsAddress(val.Address), suite.ctx.BlockHeight(),
		suite.ctx.BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	providerSlashingKeeper.SetValidatorSigningInfo(suite.ctx, sdk.ConsAddress(val.Address), valInfo)

	// update validator address and VSC ID
	slashingPkt.Validator.Address = val.Address
	slashingPkt.ValsetUpdateId = vID

	// expect to slash and jail validator
	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().NoError(err, "did slash jail validator")

	// expect error when infraction type in unspecified
	tmAddr := suite.providerChain.Vals.Validators[1].Address
	slashingPkt.Validator.Address = tmAddr
	slashingPkt.Infraction = stakingtypes.InfractionEmpty

	valInfo.Address = sdk.ConsAddress(tmAddr).String()
	providerSlashingKeeper.SetValidatorSigningInfo(suite.ctx, sdk.ConsAddress(tmAddr), valInfo)

	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().EqualError(err, fmt.Sprintf("invalid infraction type: %v", stakingtypes.InfractionEmpty))

	// expect to slash jail and tombstone validator
	slashingPkt.Infraction = stakingtypes.DoubleSign
	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().NoError(err)

	// expect error when validator is tombstoned
	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().Error(err)
}

// TestHandleSlashPacketDistribution tests the slashing of an undelegation balance
// by varying the slash packet VSC ID mapping to infraction heights
// lesser, equal or greater than the undelegation entry creation height
func (suite *KeeperTestSuite) TestHandleSlashPacketDistribution() {
	providerStakingKeeper := suite.providerChain.App.(*appProvider.App).StakingKeeper
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper

	// choose a validator
	tmValidator := suite.providerChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	suite.Require().NoError(err)

	validator, found := providerStakingKeeper.GetValidator(suite.providerChain.GetContext(), valAddr)
	suite.Require().True(found)

	// unbonding operations parameters
	delAddr := suite.providerChain.SenderAccount.GetAddress()
	bondAmt := sdk.NewInt(1000000)

	// new delegator shares used
	testShares := sdk.Dec{}

	// setup the test with a delegation, a no-op and an undelegation
	setupOperations := []struct {
		fn func(suite *KeeperTestSuite) error
	}{
		{
			func(suite *KeeperTestSuite) error {
				testShares, err = providerStakingKeeper.Delegate(suite.providerChain.GetContext(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
				return err
			},
		}, {
			func(suite *KeeperTestSuite) error {
				return nil
			},
		}, {
			// undelegate a quarter of the new shares created
			func(suite *KeeperTestSuite) error {
				_, err = providerStakingKeeper.Undelegate(suite.providerChain.GetContext(), delAddr, valAddr, testShares.QuoInt64(4))
				return err
			},
		},
	}

	// execute the setup operations, distributed uniformly in three blocks.
	// For each of them, save their current VSC Id value which map correspond respectively
	// to the block heights lesser, equal and greater than the undelegation creation height.
	vscIDs := make([]uint64, 0, 3)
	for _, so := range setupOperations {
		err := so.fn(suite)
		suite.Require().NoError(err)

		vscIDs = append(vscIDs, providerKeeper.GetValidatorSetUpdateId(suite.providerChain.GetContext()))
		suite.providerChain.NextBlock()
	}

	// create validator signing info to test slashing
	suite.providerChain.App.(*appProvider.App).SlashingKeeper.SetValidatorSigningInfo(
		suite.providerChain.GetContext(),
		sdk.ConsAddress(tmValidator.Address),
		slashingtypes.ValidatorSigningInfo{Address: tmValidator.Address.String()},
	)

	// the test cases verify that only the unbonding tokens get slashed for the VSC ids
	// mapping to the block heights before and during the undelegation otherwise not.
	testCases := []struct {
		expSlash bool
		vscID    uint64
	}{
		{expSlash: true, vscID: vscIDs[0]},
		{expSlash: true, vscID: vscIDs[1]},
		{expSlash: false, vscID: vscIDs[2]},
	}

	// save unbonding balance before slashing tests
	ubd, found := providerStakingKeeper.GetUnbondingDelegation(suite.providerChain.GetContext(), delAddr, valAddr)
	suite.Require().True(found)
	ubdBalance := ubd.Entries[0].Balance

	for _, tc := range testCases {
		slashPacket := ccv.NewSlashPacketData(
			abci.Validator{Address: tmValidator.Address, Power: tmValidator.VotingPower},
			tc.vscID,
			stakingtypes.Downtime,
		)

		// slash
		err := providerKeeper.HandleSlashPacket(suite.providerChain.GetContext(), suite.consumerChain.ChainID, slashPacket)
		suite.Require().NoError(err)

		ubd, found := providerStakingKeeper.GetUnbondingDelegation(suite.providerChain.GetContext(), delAddr, valAddr)
		suite.Require().True(found)

		isUbdSlashed := ubdBalance.GT(ubd.Entries[0].Balance)
		suite.Require().True(tc.expSlash == isUbdSlashed)

		// update balance
		ubdBalance = ubd.Entries[0].Balance
	}
}

func (suite *KeeperTestSuite) TestIterateOverUnbondingOpIndex() {
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	chainID := suite.consumerChain.ChainID

	// mock an unbonding index
	unbondingOpIndex := []uint64{0, 1, 2, 3, 4, 5, 6}

	// set ubd ops by varying vsc ids and index slices
	for i := 1; i < len(unbondingOpIndex); i++ {
		providerKeeper.SetUnbondingOpIndex(suite.providerChain.GetContext(), chainID, uint64(i), unbondingOpIndex[:i])
	}

	// check iterator returns expected entries
	i := 1
	providerKeeper.IterateOverUnbondingOpIndex(suite.providerChain.GetContext(), chainID, func(vscID uint64, ubdIndex []uint64) bool {
		suite.Require().Equal(uint64(i), vscID)
		suite.Require().EqualValues(unbondingOpIndex[:i], ubdIndex)
		i++
		return true
	})
	suite.Require().Equal(len(unbondingOpIndex), i)
}
