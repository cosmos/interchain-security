package parent_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/testing"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"

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

	childGenesis := childtypes.NewInitialGenesisState(suite.parentClient, suite.parentConsState)
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

	// Send CCV packet to consumer
	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := parentStakingKeeper.GetValidatorUpdates(s.parentCtx())

	// commit block on parent chain and update child chain's client
	oldBlockTime := s.parentCtx().BlockTime()
	s.coordinator.CommitBlock(s.parentChain)
	s.path.EndpointA.UpdateClient()

	// Reconstruct packet
	packetData := types.NewValidatorSetChangePacketData(valUpdates, 1)
	timeout := uint64(parenttypes.GetTimeoutTimestamp(oldBlockTime).UnixNano())
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
		timeout := uint64(parenttypes.GetTimeoutTimestamp(blockTime).UnixNano())
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

	// check that staking ubde was created and onHold is false
	checkStakingUBDE(1, true, false)

	// check that CCV ubde was created
	checkCCVUBDE(s.childChain.ChainID, 1, true)

	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// SEND PACKET

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.parentChain.App.GetStakingKeeper().GetValidatorUpdates(s.parentCtx())

	// Get current blocktime
	oldBlockTime := s.parentCtx().BlockTime()

	// commit block on parent chain and update consumer chain's client
	commitParentBlock()
	// Relay actual packet content to consumer chain
	packet := sendValUpdatePacket(valUpdates, 1, oldBlockTime, 1)

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
	// _, found = s.parentChain.App.(*app.App).ParentKeeper.GetUBDEsFromIndex(s.parentCtx(), s.childChain.ChainID, 1)
	// s.Require().False(found)
	checkCCVUBDE(s.childChain.ChainID, 1, false)

	// Check that staking UBDE has been deleted
	checkStakingUBDE(1, false, false)

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
