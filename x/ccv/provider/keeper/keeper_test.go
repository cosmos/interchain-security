package keeper_test

import (
	"testing"
	"time"

	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

func init() {
	ibctesting.DefaultTestingAppInit = simapp.SetupTestingApp
}

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
	suite.coordinator = ibctesting.NewCoordinator(suite.T(), 2)
	suite.providerChain = suite.coordinator.GetChain(ibctesting.GetChainID(1))
	suite.consumerChain = suite.coordinator.GetChain(ibctesting.GetChainID(2))

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on provider chain before creating client
	suite.coordinator.CommitBlock(suite.providerChain)

	// create client and consensus state of provider chain to initialize consumer chain genesis.
	height := suite.providerChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	suite.providerClient = ibctmtypes.NewClientState(
		suite.providerChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	suite.providerConsState = suite.providerChain.LastHeader.ConsensusState()

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	params := consumertypes.DefaultParams()
	params.Enabled = true
	consumerGenesis := consumertypes.NewInitialGenesisState(suite.providerClient, suite.providerConsState, valUpdates, params)
	suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), consumerGenesis)

	suite.ctx = suite.providerChain.GetContext()

	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	providerClient, ok := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	// set consumer endpoint's clientID
	suite.path.EndpointA.ClientID = providerClient

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	suite.path.EndpointB.CreateClient()
	suite.providerChain.App.(*app.App).ProviderKeeper.SetConsumerClient(suite.providerChain.GetContext(), suite.consumerChain.ChainID, suite.path.EndpointB.ClientID)
}

func TestKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(KeeperTestSuite))
}

func (suite *KeeperTestSuite) TestValsetUpdateBlockHeight() {
	app := suite.providerChain.App.(*app.App)
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
	app := suite.providerChain.App.(*app.App)
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

func (suite *KeeperTestSuite) TestAppendSlashgAck() {
	app := suite.providerChain.App.(*app.App)
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

func (suite *KeeperTestSuite) TestInitHeight() {
	app := suite.providerChain.App.(*app.App)
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

func (suite *KeeperTestSuite) TestHandleSlashPacketDistribution() {
	providerStakingKeeper := suite.providerChain.App.GetStakingKeeper()
	providerSlashingKeeper := suite.providerChain.App.(*app.App).SlashingKeeper
	ProviderKeeper := suite.providerChain.App.(*app.App).ProviderKeeper

	// bonded amount
	bondAmt := sdk.NewInt(1000000)
	delAddr := suite.providerChain.SenderAccount.GetAddress()

	// choose a validator and get its delegations
	consAddr := sdk.ConsAddress(suite.providerChain.Vals.Validators[0].Address)
	val, _ := providerStakingKeeper.GetValidatorByConsAddr(suite.providerChain.GetContext(), consAddr)
	valAddr, _ := sdk.ValAddressFromBech32(val.OperatorAddress)
	del, found := providerStakingKeeper.GetDelegation(suite.providerChain.GetContext(), delAddr, valAddr)
	suite.Require().True(found)
	validator, found := providerStakingKeeper.GetValidator(suite.providerChain.GetContext(), valAddr)
	suite.Require().True(found)

	consAdrr, err := validator.GetConsAddr()
	suite.Require().NoError(err)

	ubdAmount := del.Shares.QuoInt64(2)
	undel := func() stakingtypes.UnbondingDelegation {
		ubd, found := providerStakingKeeper.GetUnbondingDelegation(suite.providerChain.GetContext(), delAddr, valAddr)
		suite.Require().True(found)
		return ubd
	}
	// undelegate half of the tokens
	unboundHalf := func() stakingtypes.UnbondingDelegation {
		_, err := providerStakingKeeper.Undelegate(suite.providerChain.GetContext(), delAddr, valAddr, ubdAmount)
		suite.Require().NoError(err)
		return undel()
	}

	// save valset update ID mapping the next block height
	valseUpdateID1 := ProviderKeeper.GetValidatorSetUpdateId(suite.providerChain.GetContext())

	// get valset update ID mapping the current block height
	valseUpdateID0 := valseUpdateID1 - 1

	// create first undelegation entry
	ubdBalance := ubdAmount.Mul(bondAmt.ToDec()).TruncateInt()
	ubd := unboundHalf()
	suite.Require().Len(ubd.Entries, 1)
	suite.Require().Equal(ubdBalance, ubd.Entries[0].Balance)

	// check valset update ID height mapping
	suite.coordinator.CommitBlock(suite.providerChain)
	// suite context isn't updated in CommitBlock
	valsetUpdateIDHeight := ProviderKeeper.GetValsetUpdateBlockHeight(suite.providerChain.GetContext(), valseUpdateID1)

	suite.Require().EqualValues(valsetUpdateIDHeight, ubd.Entries[0].CreationHeight+1)

	// create second undelegation entry
	ubd = unboundHalf()
	suite.Require().Len(ubd.Entries, 2)
	suite.Require().Equal(ubdBalance, ubd.Entries[1].Balance)
	valseUpdateID2 := ProviderKeeper.GetValidatorSetUpdateId(suite.providerChain.GetContext())

	suite.coordinator.CommitBlock(suite.providerChain)
	valsetUpdateIDHeight = ProviderKeeper.GetValsetUpdateBlockHeight(suite.providerChain.GetContext(), valseUpdateID2)

	suite.Require().EqualValues(valsetUpdateIDHeight, ubd.Entries[1].CreationHeight+1)

	// create validator signing info
	valInfo := slashingtypes.NewValidatorSigningInfo(consAdrr, suite.ctx.BlockHeight(),
		suite.ctx.BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	providerSlashingKeeper.SetValidatorSigningInfo(suite.providerChain.GetContext(), consAdrr, valInfo)

	// resulting balance after slashing
	ubdBalanceSlashed := ubdBalance.Sub(ubdBalance.Quo(sdk.NewInt(100)))
	// ubdBalanceSlashed2 := ubdBalanceSlashed.Sub(ubdBalance.Quo(sdk.NewInt(100)))

	// test slashing using the valset update IDs
	tests := []struct {
		expBalances    []sdk.Int
		valsetUpdateID uint64
	}{
		{ // both undelegations slashed: valseUpdateID0  maps to 1st undelegation height
			expBalances:    []sdk.Int{ubdBalanceSlashed, ubdBalanceSlashed},
			valsetUpdateID: valseUpdateID0,
		},
		// TODO SIMON: unjail validators after each test case to slash a validator more than once
		// { // second undelegation is slashed again: valseUpdateID1 maps to 2nd undelegation height
		// 	expBalances:    []sdk.Int{ubdBalanceSlashed, ubdBalanceSlashed2},
		// 	valsetUpdateID: valseUpdateID1,
		// },
		// { // no slashing: valseUpdateID2 maps to 2nd undelegation height + 1
		// 	expBalances:    []sdk.Int{ubdBalanceSlashed, ubdBalanceSlashed2},
		// 	valsetUpdateID: valseUpdateID2,
		// },
	}

	slashingPkt := ccv.SlashPacketData{Validator: abci.Validator{
		Address: consAdrr.Bytes(),
		Power:   int64(1),
	},
		Infraction: stakingtypes.Downtime,
	}

	for _, t := range tests {
		// set test case parameters
		slashingPkt.ValsetUpdateId = t.valsetUpdateID

		// slash
		err := ProviderKeeper.HandleSlashPacket(suite.providerChain.GetContext(), suite.consumerChain.ChainID, slashingPkt)
		suite.Require().NoError(err)

		// check that second undelegation was slashed
		ubd = undel()

		suite.Require().EqualValues(t.expBalances[0], ubd.Entries[0].Balance)
		suite.Require().EqualValues(t.expBalances[1], ubd.Entries[1].Balance)
	}
}

func (suite *KeeperTestSuite) TestHandleSlashPacketDoubleSigning() {
	ProviderKeeper := suite.providerChain.App.(*app.App).ProviderKeeper
	providerSlashingKeeper := suite.providerChain.App.(*app.App).SlashingKeeper

	val := suite.providerChain.Vals.Validators
	consAddr := sdk.ConsAddress(val[0].Address)

	// set init VSC id for chain0
	ProviderKeeper.SetInitChainHeight(suite.ctx, suite.consumerChain.ChainID, uint64(suite.ctx.BlockHeight()))

	// set validator signing info
	valInfo := slashingtypes.NewValidatorSigningInfo(consAddr, suite.ctx.BlockHeight(),
		suite.ctx.BlockHeight()-1, time.Time{}.UTC(), false, int64(0))

	providerSlashingKeeper.SetValidatorSigningInfo(suite.ctx, consAddr, valInfo)

	err := ProviderKeeper.HandleSlashPacket(suite.ctx, suite.consumerChain.ChainID,
		ccv.NewSlashPacketData(
			abci.Validator{Address: val[0].Address, Power: 0},
			uint64(0),
			stakingtypes.DoubleSign,
		),
	)
	suite.NoError(err)

	valInfo, _ = providerSlashingKeeper.GetValidatorSigningInfo(suite.ctx, consAddr)

	suite.Require().True(valInfo.JailedUntil.Equal(evidencetypes.DoubleSignJailEndTime))
	suite.Require().True(valInfo.Tombstoned)
}

func (suite *KeeperTestSuite) TestHandleSlashPacketErrors() {
	providerStakingKeeper := suite.providerChain.App.GetStakingKeeper()
	ProviderKeeper := suite.providerChain.App.(*app.App).ProviderKeeper
	providerSlashingKeeper := suite.providerChain.App.(*app.App).SlashingKeeper
	consumerChainID := suite.consumerChain.ChainID

	// sync context
	suite.ctx = suite.providerChain.GetContext()

	// expect an error if initial block height isn't set for consumer chain
	err := ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, ccv.SlashPacketData{})
	suite.Require().Error(err, "did slash unknown validator")

	// suite.SetupCCVChannel()
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
	//expect an error if validator doesn't exist
	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().Error(err, "did slash unknown validator")

	// jail an existing validator
	val := suite.providerChain.Vals.Validators[0]
	consAddr := sdk.ConsAddress(val.Address)
	// origTime := suite.ctx.BlockTime()
	providerStakingKeeper.Jail(suite.ctx, consAddr)
	// commit block to set VSC ID
	suite.coordinator.CommitBlock(suite.providerChain)
	// Update suite.ctx bc CommitBlock updates only providerChain's current header block height
	suite.ctx = suite.providerChain.GetContext()
	//suite.Require().NotZero(ProviderKeeper.GetValsetUpdateBlockHeight(suite.ctx, vID))

	// fmt.Println(suite.providerChain.GetContext().BlockHeight())
	// fmt.Println(suite.ctx.BlockHeight())
	// validator, f := providerStakingKeeper.GetValidatorByConsAddr(suite.providerChain.GetContext(), consAddr)
	// suite.Require().True(f)
	// fmt.Printf(validator.String())

	// replace validator address
	slashingPkt.Validator.Address = val.Address
	slashingPkt.ValsetUpdateId = vID

	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().Error(err, "did slash jail validator")

	// end validator unbonding period
	// suite.ctx = suite.ctx.WithBlockTime(origTime.Add(10 * consumertypes.UnbondingTime).Add(3 * time.Hour))
	// // suite.providerChain.App.EndBlock(abci.RequestEndBlock{})
	// suite.providerChain.App.GetStakingKeeper().BlockValidatorUpdates(suite.ctx)

	// validator, f := providerStakingKeeper.GetValidatorByConsAddr(suite.providerChain.GetContext(), consAddr)
	// suite.Require().True(f)
	// valAddr, err := sdk.ValAddressFromBech32(validator.OperatorAddress)
	// suite.Require().NoError(err)
	// err = providerSlashingKeeper.Unjail(suite.ctx, valAddr)
	// suite.Require().NoError(err)

	// // validator, f := providerStakingKeeper.GetValidatorByConsAddr(suite.ctx, consAddr)
	// // suite.Require().True(f)
	// // fmt.Printf(validator.String())
	// // expect no-error
	// err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	// suite.Require().NoError(err)

	// replace validator address
	val = suite.providerChain.Vals.Validators[1]
	slashingPkt.Validator.Address = val.Address

	// set VSC ID
	slashingPkt.ValsetUpdateId = vID
	slashingPkt.Infraction = stakingtypes.DoubleSign

	// // set current valset update ID
	valInfo := slashingtypes.NewValidatorSigningInfo(sdk.ConsAddress(val.Address), suite.ctx.BlockHeight(),
		suite.ctx.BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	providerSlashingKeeper.SetValidatorSigningInfo(suite.ctx, sdk.ConsAddress(val.Address), valInfo)

	// expect no error
	err = ProviderKeeper.HandleSlashPacket(suite.ctx, consumerChainID, slashingPkt)
	suite.Require().NoError(err)
}
