package parent_test

import (
	"strconv"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"

	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
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
	suite.coordinator = ibctesting.NewCoordinator(suite.T(), 1)
	suite.parentChain = suite.coordinator.GetChain(ibctesting.GetChainID(1))
	// create child chain with parent chain valset
	suite.CreateChildChain()
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

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create child client on parent chain and set as child client for child chainID in parent keeper.
	suite.path.EndpointB.CreateClient()
	suite.parentChain.App.(*app.App).ParentKeeper.SetChildClient(suite.parentChain.GetContext(), suite.childChain.ChainID, suite.path.EndpointB.ClientID)
}

func (suite *ParentTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)
	suite.coordinator.CreateChannels(suite.path)
}

func (s *ParentTestSuite) CreateChildChain() {
	parent := s.parentChain
	chainID := ibctesting.ChainIDPrefix + strconv.Itoa(len(s.coordinator.Chains)+1)
	child := ibctesting.NewTestChainWithValSet(s.T(), s.coordinator, chainID, parent.Vals, parent.Signers)
	s.coordinator.Chains[child.ChainID] = child
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
	packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateID, nil)
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, parenttypes.PortID, s.path.EndpointB.ChannelID,
		childtypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// Receive CCV packet on consumer chain
	err = s.path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)

	// Update chilchain hist info for the current block
	s.UpdateChildHistInfo(packetData.ValidatorUpdates)

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
		s.Require().True(onHold == stakingUBDE.UnbondingOnHold)
	}

	checkCCVUBDE := func(chainID string, valUpdateID uint64, found bool) {
		_, wasFound := s.parentChain.App.(*app.App).ParentKeeper.GetUBDEsFromIndex(s.parentCtx(), chainID, valUpdateID)
		s.Require().True(found == wasFound)
	}

	sendValUpdatePacket := func(valUpdates []abci.ValidatorUpdate, valUpdateId uint64, blockTime time.Time, packetSequence uint64) channeltypes.Packet {
		packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateId, nil)
		timeout := uint64(ccv.GetTimeoutTimestamp(blockTime).UnixNano())
		packet := channeltypes.NewPacket(packetData.GetBytes(), packetSequence, parenttypes.PortID, s.path.EndpointB.ChannelID,
			childtypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

		// Receive CCV packet on consumer chain
		err := s.path.EndpointA.RecvPacket(packet)
		s.Require().NoError(err)

		// update child chain hist info
		s.UpdateChildHistInfo(valUpdates)

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
	stakingUbd, found := k.GetUnbondingDelegationByUnbondingOpId(ctx, id)

	for _, entry := range stakingUbd.Entries {
		if entry.UnbondingOpId == id {
			stakingUbde = entry
			found = true
			break
		}
	}

	return stakingUbde, found
}

// TestSendDowntimePacket tests consumer initiated slashing
func (s *ParentTestSuite) TestSendDowntimePacket() {
	s.SetupCCVChannel()
	validatorsPerChain := len(s.childChain.Vals.Validators)

	parentStakingKeeper := s.parentChain.App.GetStakingKeeper()
	parentSlashingKeeper := s.parentChain.App.(*app.App).SlashingKeeper

	childKeeper := s.childChain.App.(*app.App).ChildKeeper

	// get a cross-chain validator address, pubkey and balance
	tmVals := s.childChain.Vals.Validators
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

	// get valseUpdateId for current block height
	valsetUpdateId := childKeeper.GetHeightValsetUpdateID(s.childCtx(), uint64(s.childCtx().BlockHeight()))

	// construct the downtime packet with the validator address and power along
	// with the slashing and jailing parameters
	validator := abci.Validator{
		Address: tmVal.Address,
		Power:   tmVal.VotingPower,
	}

	oldBlockTime := s.childCtx().BlockTime()
	slashFraction := int64(100)
	packetData := types.NewSlashPacketData(validator, valsetUpdateId, slashFraction,
		int64(slashingtypes.DefaultDowntimeJailDuration))
	timeout := uint64(types.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, childtypes.PortID, s.path.EndpointA.ChannelID,
		parenttypes.PortID, s.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	// Send the downtime packet through CCV
	err = s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)

	// Set outstanding slashing flag
	s.childChain.App.(*app.App).ChildKeeper.SetOutstandingDowntime(s.childCtx(), consAddr)

	// save next VSC packet info
	oldBlockTime = s.parentCtx().BlockTime()
	timeout = uint64(types.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	valsetUpdateID := s.parentChain.App.(*app.App).ParentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	// receive the downtime packet on the parent chain;
	// RecvPacket() calls the parent endblocker thus sends a VSC packet to the consumer
	err = s.path.EndpointB.RecvPacket(packet)
	s.Require().NoError(err)

	// check that the validator was removed from the parent validator set
	s.Require().Len(s.parentChain.Vals.Validators, validatorsPerChain-1)
	// check that the VSC ID is updated on the child chain

	// update child client on the VSC packet sent from parent
	err = s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)

	// reconstruct VSC packet
	valUpdates := []abci.ValidatorUpdate{
		{
			PubKey: val.GetPubKey(),
			Power:  int64(0),
		},
	}
	packetData2 := ccv.NewValidatorSetChangePacketData(valUpdates, valsetUpdateID, []string{consAddr.String()})
	packet2 := channeltypes.NewPacket(packetData2.GetBytes(), 1, parenttypes.PortID, s.path.EndpointB.ChannelID,
		childtypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// receive VSC packet about jailing on the child chain
	err = s.path.EndpointA.RecvPacket(packet2)
	s.Require().NoError(err)

	// check that the child update its VSC ID for the subsequent block
	s.Require().Equal(childKeeper.GetHeightValsetUpdateID(s.childCtx(), uint64(s.childCtx().BlockHeight())+1), valsetUpdateID)

	// update child chain hist info
	s.UpdateChildHistInfo(packetData2.ValidatorUpdates)

	// check that the validator was removed from the child validator set
	s.Require().Len(s.childChain.Vals.Validators, validatorsPerChain-1)

	err = s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	// check that the validator is successfully jailed on parent
	validatorJailed, ok := s.parentChain.App.GetStakingKeeper().GetValidatorByConsAddr(s.parentCtx(), consAddr)
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

	// check that the outstanding slashing flag is reset on the child
	pFlag := s.childChain.App.(*app.App).ChildKeeper.OutstandingDowntime(s.childCtx(), consAddr)
	s.Require().False(pFlag)

	// check that slashing packet gets acknowledged
	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	err = s.path.EndpointA.AcknowledgePacket(packet, ack.Acknowledgement())
	s.Require().NoError(err)
}

// TestHandleConsumerDowntime tests the slashing distribution
func (s *ParentTestSuite) TestHandleConsumerDowntime() {
	s.SetupCCVChannel()
	parentStakingKeeper := s.parentChain.App.GetStakingKeeper()
	parentSlashingKeeper := s.parentChain.App.(*app.App).SlashingKeeper
	parentKeeper := s.parentChain.App.(*app.App).ParentKeeper

	// bonded amount
	bondAmt := sdk.NewInt(1000000)
	delAddr := s.parentChain.SenderAccount.GetAddress()

	// choose a validator and get its delegations
	_, valAddr := s.getVal(0)
	del, found := parentStakingKeeper.GetDelegation(s.parentCtx(), delAddr, valAddr)
	s.Require().True(found)
	validator, found := parentStakingKeeper.GetValidator(s.parentCtx(), valAddr)
	s.Require().True(found)

	consAdrr, err := validator.GetConsAddr()
	s.Require().NoError(err)

	ubdAmount := del.Shares.QuoInt64(2)
	undel := func() stakingtypes.UnbondingDelegation {
		ubd, found := parentStakingKeeper.GetUnbondingDelegation(s.parentCtx(), delAddr, valAddr)
		s.Require().True(found)
		return ubd
	}
	// undelegate half of the tokens
	unboundHalf := func() stakingtypes.UnbondingDelegation {
		_, err := parentStakingKeeper.Undelegate(s.parentCtx(), delAddr, valAddr, ubdAmount)
		s.Require().NoError(err)
		return undel()
	}

	// save valset update ID mapping the next block height
	valseUpdateID1 := parentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	// get valset update ID mapping the current block height
	valseUpdateID0 := valseUpdateID1 - 1

	// create first undelegation entry
	ubdBalance := ubdAmount.Mul(bondAmt.ToDec()).TruncateInt()
	ubd := unboundHalf()
	s.Require().Len(ubd.Entries, 1)
	s.Require().Equal(ubdBalance, ubd.Entries[0].Balance)

	// check valset update ID height mapping
	s.coordinator.CommitBlock(s.parentChain)
	valsetUpdateIDHeight := parentKeeper.GetValsetUpdateBlockHeight(s.parentCtx(), valseUpdateID1)

	s.Require().EqualValues(valsetUpdateIDHeight, ubd.Entries[0].CreationHeight+1)

	// create second undelegation entry
	ubd = unboundHalf()
	s.Require().Len(ubd.Entries, 2)
	s.Require().Equal(ubdBalance, ubd.Entries[1].Balance)
	valseUpdateID2 := parentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	s.coordinator.CommitBlock(s.parentChain)
	valsetUpdateIDHeight = parentKeeper.GetValsetUpdateBlockHeight(s.parentCtx(), valseUpdateID2)

	s.Require().EqualValues(valsetUpdateIDHeight, ubd.Entries[1].CreationHeight+1)

	// create validator signing info
	valInfo := slashingtypes.NewValidatorSigningInfo(consAdrr, s.parentCtx().BlockHeight(),
		s.parentCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	parentSlashingKeeper.SetValidatorSigningInfo(s.parentCtx(), consAdrr, valInfo)

	// resulting balance after slashing
	ubdBalanceSlashed := ubdBalance.Sub(ubdBalance.Quo(sdk.NewInt(4)))
	ubdBalanceSlashed2 := ubdBalanceSlashed.Sub(ubdBalance.Quo(sdk.NewInt(4)))

	// test slashing using the valset update IDs
	tests := []struct {
		expBalances    []sdk.Int
		valsetUpdateID uint64
	}{{ // both undelegations slashed: valseUpdateID0  maps to 1st undelegation height
		expBalances:    []sdk.Int{ubdBalanceSlashed, ubdBalanceSlashed},
		valsetUpdateID: valseUpdateID0,
	}, { // second undelegation is slashed again: valseUpdateID1 maps to 2nd undelegation height
		expBalances:    []sdk.Int{ubdBalanceSlashed, ubdBalanceSlashed2},
		valsetUpdateID: valseUpdateID1,
	}, { // no slashing: valseUpdateID2 maps to 2nd undelegation height + 1
		expBalances:    []sdk.Int{ubdBalanceSlashed, ubdBalanceSlashed2},
		valsetUpdateID: valseUpdateID2,
	},
	}

	slashingPkt := ccv.SlashPacketData{Validator: abci.Validator{
		Address: consAdrr.Bytes(),
		Power:   int64(1),
	},
		SlashFraction: int64(4),
	}

	for _, t := range tests {
		// set test case parameters
		slashingPkt.ValsetUpdateId = t.valsetUpdateID

		// slash
		err := parentKeeper.HandleConsumerDowntime(s.parentCtx(), s.childChain.ChainID, slashingPkt)
		s.Require().NoError(err)

		// check that second undelegation was slashed
		ubd = undel()

		s.Require().EqualValues(t.expBalances[0], ubd.Entries[0].Balance)
		s.Require().EqualValues(t.expBalances[1], ubd.Entries[1].Balance)
	}
}

func (s *ParentTestSuite) TestHandleConsumerDowntimeErrors() {
	parentStakingKeeper := s.parentChain.App.GetStakingKeeper()
	parentKeeper := s.parentChain.App.(*app.App).ParentKeeper
	parentSlashingKeeper := s.parentChain.App.(*app.App).SlashingKeeper
	childChainID := s.childChain.ChainID

	// expect an error if initial block height isn't set for child chain
	err := parentKeeper.HandleConsumerDowntime(s.parentCtx(), childChainID, types.SlashPacketData{})
	s.Require().Error(err, "did slash unknown validator")

	s.SetupCCVChannel()
	// save VSC ID
	vID := parentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	// set faulty block height for current VSC ID
	parentKeeper.SetValsetUpdateBlockHeight(s.parentCtx(), vID, 0)

	// expect an error if block height mapping VSC ID is zero
	err = parentKeeper.HandleConsumerDowntime(s.parentCtx(), childChainID, types.SlashPacketData{ValsetUpdateId: vID})
	s.Require().Error(err, "did slash unknown validator")

	// construct slashing packet with non existing validator
	slashingPkt := ccv.NewSlashPacketData(
		abci.Validator{Address: ed25519.GenPrivKey().PubKey().Address(),
			Power: int64(0)}, uint64(0), int64(1), int64(0),
	)
	//expect an error if validator doesn't exist
	err = parentKeeper.HandleConsumerDowntime(s.parentCtx(), childChainID, slashingPkt)
	s.Require().Error(err, "did slash unknown validator")

	// jail an existing validator
	val := s.parentChain.Vals.Validators[0]
	consAddr := sdk.ConsAddress(val.Address)
	origTime := s.parentCtx().BlockTime()
	parentStakingKeeper.Jail(s.parentCtx(), consAddr)
	// commit block to set VSC ID
	s.coordinator.CommitBlock(s.parentChain)
	s.Require().NotZero(parentKeeper.GetValsetUpdateBlockHeight(s.parentCtx(), vID))

	// end validator unbonding period
	parentCtx := s.parentCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	s.parentChain.App.GetStakingKeeper().BlockValidatorUpdates(parentCtx)

	// replace validator address
	slashingPkt.Validator.Address = val.Address
	// expect an error since the validator is already jailed
	err = parentKeeper.HandleConsumerDowntime(s.parentCtx(), childChainID, slashingPkt)
	s.Require().Error(err, "did slash unbonded validator")

	// replace validator address
	val = s.parentChain.Vals.Validators[1]
	slashingPkt.Validator.Address = val.Address

	// set VSC ID
	slashingPkt.ValsetUpdateId = vID

	// // set current valset update ID
	valInfo := slashingtypes.NewValidatorSigningInfo(sdk.ConsAddress(val.Address), s.parentCtx().BlockHeight(),
		s.parentCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	parentSlashingKeeper.SetValidatorSigningInfo(s.parentCtx(), sdk.ConsAddress(val.Address), valInfo)

	// expect no error
	err = parentKeeper.HandleConsumerDowntime(s.parentCtx(), childChainID, slashingPkt)
	s.Require().NoError(err)
}

func (s *ParentTestSuite) TestslashingPacketAcknowldgement() {
	parentKeeper := s.parentChain.App.(*app.App).ParentKeeper
	childKeeper := s.childChain.App.(*app.App).ChildKeeper

	packet := channeltypes.NewPacket([]byte{}, 1, childtypes.PortID, s.path.EndpointA.ChannelID,
		parenttypes.PortID, "wrongchannel", clienttypes.Height{}, 0)

	ack := parentKeeper.OnRecvPacket(s.parentCtx(), packet, ccv.SlashPacketData{})
	s.Require().NotNil(ack)

	err := childKeeper.OnAcknowledgementPacket(s.childCtx(), packet, ccv.SlashPacketData{}, channeltypes.NewResultAcknowledgement(ack.Acknowledgement()))
	s.Require().NoError(err)

	err = childKeeper.OnAcknowledgementPacket(s.childCtx(), packet, ccv.SlashPacketData{}, channeltypes.NewErrorAcknowledgement("another error"))
	s.Require().Error(err)
}

// UpdateChildHistInfo updates child chains historical info manually since
// the staking keeper is disabled. Provider chains need this to update their client trusted validators
// in IBC-GO testing (see ConstructUpdateTMClientHeaderWithTrustedHeight in chain.go)
func (s *ParentTestSuite) UpdateChildHistInfo(changes []abci.ValidatorUpdate) {
	// map changes per pubkey
	changesPower := make(map[string]int64)
	for _, c := range changes {
		pk, err := cryptocodec.FromTmProtoPublicKey(c.PubKey)
		s.Require().NoError(err)
		changesPower[pk.String()] = c.Power
	}

	// update validators power
	var validators stakingtypes.Validators
	for _, v := range s.childChain.Vals.Validators {
		pk, err := cryptocodec.FromTmPubKeyInterface(v.PubKey)
		s.Require().NoError(err)
		val, err := stakingtypes.NewValidator(nil, pk, stakingtypes.Description{})
		s.Require().NoError(err)

		if p, ok := changesPower[pk.String()]; ok {
			val.Tokens = sdk.TokensFromConsensusPower(p, sdk.DefaultPowerReduction)
		} else {
			val.Tokens = sdk.TokensFromConsensusPower(v.VotingPower, sdk.DefaultPowerReduction)
		}

		if val.Tokens.IsZero() {
			val.Status = stakingtypes.Unbonding
			val.Jailed = true
		} else {
			val.Status = stakingtypes.Bonded
		}
		validators = append(validators, val)
	}

	// update chain historical info
	hi := stakingtypes.NewHistoricalInfo(s.ctx.BlockHeader(), validators, sdk.DefaultPowerReduction)
	s.childChain.App.GetStakingKeeper().SetHistoricalInfo(s.childCtx(), s.childCtx().BlockHeight(), &hi)
}
