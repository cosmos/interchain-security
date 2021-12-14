package parent_test

import (
	"fmt"
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

func (s *ParentTestSuite) TestStakingHooks() {
	s.SetupCCVChannel()
	// bondAmt := sdk.NewInt(1000000)

	delAddr := s.parentChain.SenderAccount.GetAddress()
	origTime := s.ctx.BlockTime()
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.parentChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := s.parentChain.App.GetStakingKeeper().GetValidator(s.parentCtx(), valAddr)
	s.Require().True(found)

	delBalance := func() sdk.Int {
		return s.parentChain.App.(*app.App).BankKeeper.GetBalance(s.parentCtx(), delAddr, s.parentBondDenom()).Amount
	}

	// INITIAL BOND

	// Bond some tokens on provider to change validator powers
	shares, err := s.parentChain.App.GetStakingKeeper().Delegate(s.parentCtx(), delAddr, sdk.NewInt(10000000), stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	s.Require().NoError(err)

	// UNDELEGATE

	// Undelegate half
	_, err = s.parentChain.App.GetStakingKeeper().Undelegate(s.parentCtx(), delAddr, valAddr, shares.QuoInt64(2))
	s.Require().NoError(err)

	// check that staking ubde was created
	_, found = GetStakingUbde(s.parentCtx(), s.parentChain.App.GetStakingKeeper(), 1)
	s.Require().True(found)

	// check that CCV ubde was created
	_, found = s.parentChain.App.(*app.App).ParentKeeper.GetUBDEsFromIndex(s.parentCtx(), s.childChain.ChainID, 1)
	s.Require().True(found)

	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// SEND PACKET

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.parentChain.App.GetStakingKeeper().GetValidatorUpdates(s.parentCtx())

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

	// ACKNOWLEDGE PACKET

	// - End provider unbonding period
	parentCtx := s.parentCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	// s.parentChain.App.EndBlock(abci.RequestEndBlock{}) <- this doesn't work because we can't modify the ctx
	s.parentChain.App.GetStakingKeeper().BlockValidatorUpdates(parentCtx)

	// - End consumer unbonding period
	childCtx := s.childCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	// s.childChain.App.EndBlock(abci.RequestEndBlock{})  <- this doesn't work because we can't modify the ctx
	err = s.childChain.App.(*app.App).ChildKeeper.UnbondMaturePackets(childCtx)
	s.Require().NoError(err)

	// commit child chain and update parent chain client
	s.coordinator.CommitBlock(s.childChain)
	err = s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})

	err = s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	s.Require().NoError(err)

	endBalance := delBalance()
	fmt.Printf("END BOND BALANCE %#v\n", endBalance.Int64())
}

// func (suite *ParentTestSuite) TestStakingHooks() {
// 	fmt.Println("START TEST")

// 	suite.SetupCCVChannel()
// 	parentCtx := suite.parentChain.GetContext()
// 	parentStakingKeeper := suite.parentChain.App.GetStakingKeeper()

// 	origTime := suite.ctx.BlockTime()
// 	// var valsetUpdateId uint64
// 	// valsetUpdateId = 9
// 	bondAmt := sdk.NewInt(1000000)

// 	delAddr := suite.parentChain.SenderAccount.GetAddress()

// 	// Choose a validator, and get its address and data structure into the correct types
// 	tmValidator := suite.parentChain.Vals.Validators[0]
// 	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
// 	suite.Require().NoError(err)
// 	validator, found := parentStakingKeeper.GetValidator(parentCtx, valAddr)
// 	suite.Require().True(found)

// 	// // - Check if Staking UBD is created
// 	// stakingUbde, found := GetStakingUbde(parentCtx, parentStakingKeeper, 0)
// 	// suite.Require().True(found)

// 	// suite.parentChain.App.EndBlock(abci.RequestEndBlock{})
// 	// suite.parentChain.NextBlock()

// 	// - Bond and unbond some tokens on provider
// 	println("\n- Bond and unbond some tokens on provider")
// 	shares, err := parentStakingKeeper.Delegate(parentCtx, delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
// 	suite.Require().NoError(err)

// 	// Unbond half the tokens
// 	_, err = parentStakingKeeper.Undelegate(parentCtx, delAddr, valAddr, shares.QuoInt64(2))
// 	suite.Require().NoError(err)

// 	// - Check if Staking UBD is created
// 	// println("\n- Check if Staking UBD is created")
// 	// stakingUbde, found := GetStakingUbde(parentCtx, parentStakingKeeper, 1)
// 	// suite.Require().True(found)
// 	// fmt.Printf("stakingUbde %#v\n", stakingUbde)
// 	// suite.Require().True(false)

// 	// // - Check if CCV UBDE is created
// 	// println("\n- Check if CCV UBDE is created")
// 	// ccvUbdes, found := suite.parentChain.App.(*app.App).ParentKeeper.d(parentCtx, fmt.Sprintf("%s%s", "chaintochannel/",
// 	// 	suite.childChain.ChainID), valsetUpdateId)
// 	// suite.Require().True(found)
// 	// ccvUbde := ccvUbdes[0]

// 	// - Send CCV packet to consumer
// 	println("\n- Send CCV packet to consumer")
// 	// suite.parentChain.App.(*app.App).ParentKeeper.EndBlockCallback(parentCtx)
// 	suite.parentChain.App.EndBlock(abci.RequestEndBlock{})

// 	// get validator update created in Endblock
// 	valUpdates := parentStakingKeeper.GetValidatorUpdates(parentCtx)

// 	// commit block on parent chain and update child chain's client
// 	suite.coordinator.CommitBlock(suite.parentChain)
// 	suite.path.EndpointA.UpdateClient()
// 	println("END CALLBACK")

// 	// Receive CCV packet on consumer chain
// 	// reconstruct packet
// 	packetData := types.NewValidatorSetChangePacketData(valUpdates, 1)
// 	timeout := uint64(parenttypes.GetTimeoutTimestamp(parentCtx.BlockTime()).UnixNano())
// 	fmt.Printf("Reconstructed Packet Data: %#v\n", packetData)
// 	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, parenttypes.PortID, suite.path.EndpointB.ChannelID,
// 		childtypes.PortID, suite.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

// 	fmt.Printf("RECONSTRUCTED PACKET: %#v\n", packet)
// 	suite.path.EndpointA.RecvPacket(packet)

// 	// - End provider unbonding period
// 	println("\n- End provider unbonding period")
// 	parentCtx = parentCtx.WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
// 	parentStakingKeeper.BlockValidatorUpdates(parentCtx)

// 	// - Check if hook was called and that unbonding did not succeed
// 	// println("\n- Check if hook was called and that unbonding did not succeed")
// 	// stakingUbde, found = GetStakingUbde(parentCtx, parentStakingKeeper, ccvUbde.UnbondingDelegationEntryId)
// 	// suite.Require().True(found)
// 	// suite.Require().True(stakingUbde.OnHold) // Should equal true
// 	// // stakingUbde.Balance // Should probably check some other properties too

// 	// - End consumer unbonding period
// 	println("\n- End consumer unbonding period")
// 	childCtx := suite.childChain.GetContext().WithBlockTime(origTime.Add(3 * childtypes.UnbondingTime).Add(3 * time.Hour))
// 	err = suite.childChain.App.(*app.App).ChildKeeper.UnbondMaturePackets(childCtx)
// 	suite.Require().NoError(err)

// 	// commit child chain and update parent chain client
// 	suite.coordinator.CommitBlock(suite.childChain)
// 	suite.path.EndpointB.UpdateClient()

// 	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
// 	fmt.Printf("RECONSTRUCTED ACK: %#v\n", ack)
// 	fmt.Printf("RECONSTRUCTED acknowledgement: %X\n", ack.Acknowledgement())

// 	suite.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())

// 	// - Check if unbonding succeeded in CCV
// 	// println("\n- Check if unbonding succeeded in CCV")
// 	// ccvUbdes, found = suite.parentChain.App.(*app.App).ParentKeeper.d(parentCtx, fmt.Sprintf("%s%s", "chaintochannel/",
// 	// 	suite.childChain.ChainID), valsetUpdateId)
// 	// fmt.Printf("ccvUbdes %#v\n", ccvUbdes)
// 	// suite.Require().False(found)
// 	// ccvUbde = ccvUbdes[0]
// 	// stakingUbde, found = GetStakingUbde(parentCtx, parentStakingKeeper, ccvUbde.UnbondingDelegationEntryId)
// 	// suite.Require().False(found)
// }

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
