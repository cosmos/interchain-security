package parent_test

import (
	"fmt"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"

	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/testing"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/bytes"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

func init() {
	ibctesting.DefaultTestingAppInit = simapp.SetupTestingApp
}

type ParentTestSuite struct {
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

func (suite *ParentTestSuite) SetupTest() {
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

	childGenesis := childtypes.NewInitialGenesisState(suite.parentClient, suite.parentConsState, valUpdates)
	suite.childChain.App.(*app.App).ChildKeeper.InitGenesis(suite.childChain.GetContext(), childGenesis)

	suite.ctx = suite.parentChain.GetContext()

	suite.path = ibctesting.NewPath(suite.childChain, suite.parentChain)
	suite.path.EndpointA.ChannelConfig.PortID = childtypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = parenttypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	parentClient, ok := suite.childChain.App.(*app.App).ChildKeeper.GetParentClient(suite.childChain.GetContext())
	if !ok {
		panic("must already have parent client on child chain")
	}
	// set child endpoint's clientID
	suite.path.EndpointA.ClientID = parentClient

	// create child client on parent chain and set as child client for child chainID in parent keeper.
	suite.path.EndpointB.CreateClient()
	suite.parentChain.App.(*app.App).ParentKeeper.SetChildClient(suite.parentChain.GetContext(), suite.childChain.ChainID, suite.path.EndpointB.ClientID)
}

func (suite *ParentTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)
	suite.coordinator.CreateChannels(suite.path)
}

func TestParentTestSuite(t *testing.T) {
	suite.Run(t, new(ParentTestSuite))
}

func (s *ParentTestSuite) TestPacketRoundtrip() {
	s.SetupCCVChannel()
	parentCtx := s.parentChain.GetContext()
	parentStakingKeeper := s.parentChain.App.GetStakingKeeper()

	origTime := s.ctx.BlockTime()
	bondAmt := sdk.NewInt(1000000)

	delAddr := s.parentChain.SenderAccount.GetAddress()

	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.parentChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := parentStakingKeeper.GetValidator(s.parentCtx(), valAddr)
	s.Require().True(found)

	// Bond some tokens on provider to change validator powers
	_, err = parentStakingKeeper.Delegate(s.parentCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	s.Require().NoError(err)

	// Save valset update ID to reconstruct packet
	valUpdateID := s.parentChain.App.(*app.App).ParentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	// Send CCV packet to consumer
	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := parentStakingKeeper.GetValidatorUpdates(s.parentCtx())

	// commit block on parent chain and update child chain's client
	oldBlockTime := s.parentCtx().BlockTime()
	s.coordinator.CommitBlock(s.parentChain)
	s.path.EndpointA.UpdateClient()

	// Reconstruct packet
	packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateID)
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, parenttypes.PortID, s.path.EndpointB.ChannelID,
		childtypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// Receive CCV packet on consumer chain
	err = s.path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)

	// - End provider unbonding period
	parentCtx = parentCtx.WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// - End consumer unbonding period
	childCtx := s.childCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	// TODO: why doesn't this work: s.childChain.App.EndBlock(abci.RequestEndBlock{})
	err = s.childChain.App.(*app.App).ChildKeeper.UnbondMaturePackets(childCtx)
	s.Require().NoError(err)

	// commit child chain and update parent chain client
	s.coordinator.CommitBlock(s.childChain)
	err = s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})

	err = s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	s.Require().NoError(err)
}

func (s *ParentTestSuite) parentCtx() sdk.Context {
	return s.parentChain.GetContext()
}

func (s *ParentTestSuite) childCtx() sdk.Context {
	return s.childChain.GetContext()
}

func (s *ParentTestSuite) parentBondDenom() string {
	return s.parentChain.App.(*app.App).StakingKeeper.BondDenom(s.parentCtx())
}

func (s *ParentTestSuite) getVal(index int) (validator stakingtypes.Validator, valAddr sdk.ValAddress) {
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.parentChain.Vals.Validators[index]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := s.parentChain.App.GetStakingKeeper().GetValidator(s.parentCtx(), valAddr)
	s.Require().True(found)

	return validator, valAddr
}

func (s *ParentTestSuite) TestStakingHooks() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.parentChain.SenderAccount.GetAddress()

	origTime := s.ctx.BlockTime()

	// Choose a validator, and get its address and data structure into the correct types
	validator, valAddr := s.getVal(0)

	delBalance := func() sdk.Int {
		return s.parentChain.App.(*app.App).BankKeeper.GetBalance(s.parentCtx(), delAddr, s.parentBondDenom()).Amount
	}

	checkStakingUBDE := func(id uint64, found bool, onHold bool) {
		stakingUBDE, wasFound := GetStakingUbde(s.parentCtx(), s.parentChain.App.GetStakingKeeper(), id)
		s.Require().True(found == wasFound)
		s.Require().True(onHold == stakingUBDE.OnHold)
	}

	checkCCVUBDE := func(chainID string, valUpdateID uint64, found bool) {
		_, wasFound := s.parentChain.App.(*app.App).ParentKeeper.GetUBDEsFromIndex(s.parentCtx(), chainID, valUpdateID)
		s.Require().True(found == wasFound)
	}

	sendValUpdatePacket := func(valUpdates []abci.ValidatorUpdate, valUpdateId uint64, blockTime time.Time, packetSequence uint64) channeltypes.Packet {
		packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateId)
		timeout := uint64(ccv.GetTimeoutTimestamp(blockTime).UnixNano())
		packet := channeltypes.NewPacket(packetData.GetBytes(), packetSequence, parenttypes.PortID, s.path.EndpointB.ChannelID,
			childtypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

		// Receive CCV packet on consumer chain
		err := s.path.EndpointA.RecvPacket(packet)
		s.Require().NoError(err)

		return packet
	}

	commitParentBlock := func() {
		s.coordinator.CommitBlock(s.parentChain)
		s.path.EndpointA.UpdateClient()
	}

	initBalance := delBalance()

	// INITIAL BOND

	// Bond some tokens on provider to change validator powers
	shares, err := s.parentChain.App.GetStakingKeeper().Delegate(s.parentCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	s.Require().NoError(err)

	afterbondBalance := delBalance()

	// Check that the correct number of tokens were taken
	s.Require().True(initBalance.Sub(afterbondBalance).Equal(bondAmt))

	// UNDELEGATE

	// Undelegate half
	_, err = s.parentChain.App.GetStakingKeeper().Undelegate(s.parentCtx(), delAddr, valAddr, shares.QuoInt64(2))
	s.Require().NoError(err)

	// Check that the tokens have not been returned yet
	s.Require().True(afterbondBalance.Equal(delBalance()))

	// save the current valset update ID
	valUpdateID := s.parentChain.App.(*app.App).ParentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	// check that staking ubde was created and onHold is false
	checkStakingUBDE(1, true, false)

	// check that CCV ubde was created
	checkCCVUBDE(s.childChain.ChainID, valUpdateID, true)

	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// SEND PACKET

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.parentChain.App.GetStakingKeeper().GetValidatorUpdates(s.parentCtx())

	// Get current blocktime
	oldBlockTime := s.parentCtx().BlockTime()

	// commit block on parent chain and update consumer chain's client
	commitParentBlock()
	// Relay actual packet content to consumer chain
	packet := sendValUpdatePacket(valUpdates, valUpdateID, oldBlockTime, 1)

	// ACKNOWLEDGE PACKET

	// Some time passes
	// s.coordinator.IncrementTimeBy(childtypes.UnbondingTime + (3 * time.Hour))

	// - End provider unbonding period
	parentCtx := s.parentCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	// s.parentChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	s.parentChain.App.GetStakingKeeper().BlockValidatorUpdates(parentCtx)

	// check that onHold is true
	checkStakingUBDE(1, true, true)

	// Check that unbonding has not yet completed
	s.Require().True(delBalance().Equal(initBalance.Sub(bondAmt)))

	// - End consumer unbonding period
	childCtx := s.childCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	// s.childChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	err = s.childChain.App.(*app.App).ChildKeeper.UnbondMaturePackets(childCtx)
	s.Require().NoError(err)

	// commit child chain and update parent chain client
	s.coordinator.CommitBlock(s.childChain)
	err = s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})

	err = s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	s.Require().NoError(err)

	// Check that ccv ubde has been deleted
	checkCCVUBDE(s.childChain.ChainID, valUpdateID, false)

	// Check that staking UBDE has been deleted
	checkStakingUBDE(valUpdateID, false, false)

	// Check that unbonding has completed
	s.Require().True(delBalance().Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

func GetStakingUbde(ctx sdk.Context, k stakingkeeper.Keeper, id uint64) (stakingUbde stakingtypes.UnbondingDelegationEntry, found bool) {
	stakingUbd, found := k.GetUnbondingDelegationByEntry(ctx, id)

	for _, entry := range stakingUbd.Entries {
		if entry.Id == id {
			stakingUbde = entry
			found = true
			break
		}
	}

	return stakingUbde, found
}

// TestSendDowntimePacket tests to the consumer initiated slashing and jailing
//  on the provider chain by the consumer chain
func (s *ParentTestSuite) TestSendDowntimePacket() {
	// set two validators per chain
	ibctesting.ValidatorsPerChain = 2
	s.SetupTest()
	s.SetupCCVChannel()
	s.Require().Len(s.parentChain.Vals.Validators, ibctesting.ValidatorsPerChain)

	parentStakingKeeper := s.parentChain.App.GetStakingKeeper()
	parentSlashingKeeper := s.parentChain.App.(*app.App).SlashingKeeper

	// get a parent chain validator address and balance
	tmVals := s.parentChain.Vals.Validators
	tmVal := tmVals[0]

	val, err := tmVal.ToProto()
	s.Require().NoError(err)
	pubkey, err := cryptocodec.FromTmProtoPublicKey(val.GetPubKey())
	s.Require().Nil(err)
	consAddr := sdk.GetConsAddress(pubkey)
	valData, found := parentStakingKeeper.GetValidatorByConsAddr(s.parentCtx(), consAddr)
	s.Require().True(found)
	valOldBalance := valData.Tokens

	// create the validator's signing info record to allow jailing
	valInfo := slashingtypes.NewValidatorSigningInfo(consAddr, s.parentCtx().BlockHeight(),
		s.parentCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	parentSlashingKeeper.SetValidatorSigningInfo(s.parentCtx(), consAddr, valInfo)

	// create a valseUpdateId that allows to retrieve the infraction block height on the provider
	valsetUpdateId := uint64(1)

	// save the current block height for the last valsetUpdateId
	s.parentChain.App.(*app.App).ParentKeeper.SetValsetUpdateBlockHeight(s.parentCtx(), valsetUpdateId,
		uint64(s.parentCtx().BlockHeight()))
	validator := abci.Validator{
		Address: tmVal.Address,
		Power:   int64(1),
	}

	// construct the downtime packet with the validator address and power along
	// with the slashing and jailing parameters
	oldBlockTime := s.childCtx().BlockTime()
	slashFraction := int64(100)
	packetData := types.NewValidatorDowntimePacketData(validator, valsetUpdateId, slashFraction,
		int64(slashingtypes.DefaultDowntimeJailDuration))
	timeout := uint64(types.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, childtypes.PortID, s.path.EndpointA.ChannelID,
		parenttypes.PortID, s.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	// Send the downtime packet through CCV
	err = s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)

	// receive the downtime packet on the provider chain;
	// tell the parentchain to slash and jail the validator
	s.path.EndpointB.RecvPacket(packet)

	// check that the validator was removed from the chain validator set
	s.Require().Len(s.parentChain.Vals.Validators, ibctesting.ValidatorsPerChain-1)

	// check that the validator is successfully jailed
	valAddr, err := sdk.ValAddressFromHex(tmVal.Address.String())
	s.Require().NoError(err)
	validatorJailed, ok := s.parentChain.App.GetStakingKeeper().GetValidator(s.parentCtx(), valAddr)
	s.Require().True(ok)
	s.Require().True(validatorJailed.Jailed)
	s.Require().Equal(validatorJailed.Status, stakingtypes.Unbonding)

	// check that the validator's token was slashed
	slashedAmout := sdk.NewDec(1).QuoInt64(slashFraction).Mul(valOldBalance.ToDec())
	resultingTokens := valOldBalance.Sub(slashedAmout.TruncateInt())
	s.Require().Equal(resultingTokens, validatorJailed.GetTokens())

	// check that the validator's unjailing time is updated
	valSignInfo, found := parentSlashingKeeper.GetValidatorSigningInfo(s.parentCtx(), consAddr)
	s.Require().True(found)
	s.Require().True(valSignInfo.JailedUntil.After(s.parentCtx().BlockHeader().Time))

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	err = s.path.EndpointA.AcknowledgePacket(packet, ack.Acknowledgement())
	s.Require().NoError(err)
}

// TestHandleConsumerDowntime tests the slashing and jailing on the provider
// by varying the downtime infraction block height
func (s *ParentTestSuite) TestHandleConsumerDowntime() {
	s.SetupCCVChannel()

	parentStakingKeeper := s.parentChain.App.GetStakingKeeper()
	parentSlashingKeeper := s.parentChain.App.(*app.App).SlashingKeeper

	delAddr := s.parentChain.SenderAccount.GetAddress()

	// Should return an error when the validator doesn't exists
	err := s.parentChain.App.(*app.App).ParentKeeper.HandleConsumerDowntime(
		s.parentCtx(),
		types.NewValidatorDowntimePacketData(
			abci.Validator{Address: bytes.HexBytes{}, Power: int64(1)}, uint64(1), int64(4), int64(1),
		),
	)
	s.Require().Error(err)

	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.parentChain.Vals.Validators[0]
	valAddr := sdk.ValAddress(tmValidator.Address)

	// Create a signing info to jail the validator for downtime
	valInfo := slashingtypes.NewValidatorSigningInfo(sdk.ConsAddress(tmValidator.Address), s.parentCtx().BlockHeight(),
		s.parentCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	parentSlashingKeeper.SetValidatorSigningInfo(s.parentCtx(), sdk.ConsAddress(tmValidator.Address), valInfo)

	// Undelegate the shares from the validator
	ubdTime := time.Now()
	parentCtx := s.parentCtx().WithBlockTime(ubdTime)
	parentStakingKeeper.Undelegate(parentCtx, delAddr, valAddr, sdk.NewDec(1))

	// Save valset update ID
	valUpdateID := s.parentChain.App.(*app.App).ParentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	// save the current block height for the last valsetUpdateId
	s.parentChain.App.(*app.App).ParentKeeper.SetValsetUpdateBlockHeight(s.parentCtx(), valUpdateID,
		uint64(s.parentCtx().BlockHeight()))

	// Save unbonding balance before slashing
	ubd, found := parentStakingKeeper.GetUnbondingDelegation(parentCtx, delAddr, valAddr)
	s.Require().Len(ubd.Entries, 1)
	s.Require().True(found)
	ubdBalance := ubd.Entries[0].Balance

	// test the slashing at different block time and height
	testCases := []struct {
		blockHeight    int64
		currentTime    time.Time
		expSlashAmount sdk.Int
	}{{
		blockHeight:    s.parentCtx().BlockHeight(),
		currentTime:    ubdTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour),
		expSlashAmount: sdk.NewInt(0),
	},
		{
			blockHeight:    s.parentCtx().BlockHeight() + 1,
			currentTime:    ubdTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour),
			expSlashAmount: sdk.NewInt(0),
		},
		{
			blockHeight:    s.parentCtx().BlockHeight() + 1,
			currentTime:    ubdTime.Add(3 * time.Hour),
			expSlashAmount: ubdBalance.ToDec().Mul(sdk.NewDec(1).QuoInt64(4)).TruncateInt(),
		},
	}

	for _, tc := range testCases {
		parentCtx = s.parentCtx().WithBlockHeight(tc.blockHeight).WithBlockTime(tc.currentTime)
		// Slash 1/4 of the validator tokens
		err := s.parentChain.App.(*app.App).ParentKeeper.HandleConsumerDowntime(
			parentCtx,
			types.NewValidatorDowntimePacketData(
				abci.Validator{
					Address: tmValidator.Address,
					Power:   int64(1),
				},
				valUpdateID,
				int64(4),
				int64(1),
			),
		)
		s.Require().NoError(err)

		newUbdBalance, found := parentStakingKeeper.GetUnbondingDelegation(parentCtx, delAddr, valAddr)
		s.Require().Len(newUbdBalance.Entries, 1)
		s.Require().True(found)
		s.Require().True(tc.expSlashAmount.Abs().Equal(ubdBalance.Sub(newUbdBalance.Entries[0].Balance)))
	}
}
