package parent_test

import (
	"fmt"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channelkeeper "github.com/cosmos/ibc-go/v3/modules/core/04-channel/keeper"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type ParentTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	parentChain *ibctesting.TestChain
	childChain  *ibctesting.TestChain

	parentClient    *ibctmtypes.ClientState
	parentConsState *ibctmtypes.ConsensusState

	path         *ibctesting.Path
	transferPath *ibctesting.Path

	providerDistrIndex int

	ctx sdk.Context
}

func (suite *ParentTestSuite) SetupTest() {

	suite.coordinator, suite.parentChain, suite.childChain = simapp.NewParentChildCoordinator(suite.T())

	suite.DisableConsumerDistribution()

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

	params := childtypes.NewParams(
		true,
		1000, // about 2 hr at 7.6 seconds per blocks
		"",
		"",
		"0.5", // 50%
	)
	childGenesis := childtypes.NewInitialGenesisState(suite.parentClient, suite.parentConsState, valUpdates, params)
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

	suite.transferPath = ibctesting.NewPath(suite.childChain, suite.parentChain)
	suite.transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	suite.transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version
}

func (suite *ParentTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CreateChannels for ccv path returns.
	suite.coordinator.CreateChannels(suite.path)

	// transfer path will use the same connection as ccv path

	suite.transferPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.transferPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.transferPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.transferPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// INIT step for transfer path has already been called during CCV channel setup
	suite.transferPath.EndpointA.ChannelID = suite.childChain.App.(*app.App).
		ChildKeeper.GetDistributionTransmissionChannel(suite.childChain.GetContext())

	// Complete TRY, ACK, CONFIRM for transfer path
	err := suite.transferPath.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	suite.transferPath.EndpointA.UpdateClient()
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

func (s *ParentTestSuite) getVal(index int) (validator stakingtypes.Validator, valAddr sdk.ValAddress) {
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.parentChain.Vals.Validators[index]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := s.parentChain.App.GetStakingKeeper().GetValidator(s.parentCtx(), valAddr)
	s.Require().True(found)

	return validator, valAddr
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

	// set manually validator status from unbonding to unbonded
	err = s.parentChain.App.GetStakingKeeper().UnbondingOpCanComplete(parentCtx, uint64(1))
	s.Require().NoError(err)

	// replace validator address
	slashingPkt.Validator.Address = val.Address

	// expect an error since the validator is already unbonded
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

func (s *ParentTestSuite) DisableConsumerDistribution() {
	cChain := s.childChain
	cApp := cChain.App.(*app.App)
	for i, moduleName := range cApp.MM.OrderBeginBlockers {
		if moduleName == distrtypes.ModuleName {
			cApp.MM.OrderBeginBlockers = append(cApp.MM.OrderBeginBlockers[:i], cApp.MM.OrderBeginBlockers[i+1:]...)
			return
		}
	}
}

func (s *ParentTestSuite) DisableProviderDistribution() {
	pChain := s.parentChain
	pApp := pChain.App.(*app.App)
	for i, moduleName := range pApp.MM.OrderBeginBlockers {
		if moduleName == distrtypes.ModuleName {
			s.providerDistrIndex = i
			pApp.MM.OrderBeginBlockers = append(pApp.MM.OrderBeginBlockers[:i], pApp.MM.OrderBeginBlockers[i+1:]...)
			return
		}
	}
}

func (s *ParentTestSuite) ReenableProviderDistribution() {
	pChain := s.parentChain
	pApp := pChain.App.(*app.App)
	i := s.providerDistrIndex
	pApp.MM.OrderBeginBlockers = append(
		pApp.MM.OrderBeginBlockers[:i+1], pApp.MM.OrderBeginBlockers[i:]...) // make space
	pApp.MM.OrderBeginBlockers[i] = distrtypes.ModuleName // set value
}

// TestDistribution tests that tokens are distributed to the
// provider chain from the consumer chain appropriately
func (s *ParentTestSuite) TestDistribution() {
	s.SetupCCVChannel() // also sets up transfer channels
	// NOTE s.transferPath.EndpointA == Consumer Chain
	//      s.transferPath.EndpointB == Provider Chain

	pChain, cChain := s.parentChain, s.childChain
	pApp, cApp := pChain.App.(*app.App), cChain.App.(*app.App)
	cKeep := cApp.ChildKeeper

	// Get the receiving fee pool on the provider chain
	fcAddr := pApp.ParentKeeper.GetFeeCollectorAddressStr(pChain.GetContext())

	// Ensure that the provider fee pool address stored on the consumer chain
	// is the correct address
	fcAddr2 := cApp.ChildKeeper.GetProviderFeePoolAddrStr(cChain.GetContext())
	s.Require().Equal(fcAddr, fcAddr2)

	// make sure we're starting at consumer height 21 (some blocks commited during setup)
	s.Require().Equal(int64(21), cChain.GetContext().BlockHeight())

	// get last consumer transmission
	ltbh, err := cKeep.GetLastTransmissionBlockHeight(cChain.GetContext())
	s.Require().NoError(err)
	s.Require().Equal(int64(0), ltbh.Height)

	bpdt := cKeep.GetBlocksPerDistributionTransmission(cChain.GetContext())
	s.Require().Equal(int64(1000), bpdt)

	// check the consumer chain fee pool
	consumerFeePoolAddr := cApp.AccountKeeper.GetModuleAccount(
		cChain.GetContext(), authtypes.FeeCollectorName).GetAddress()
	providerFeePoolAddr := pApp.AccountKeeper.GetModuleAccount(
		pChain.GetContext(), authtypes.FeeCollectorName).GetAddress()
	balance := cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerFeePoolAddr, "stake")
	s.Assert().Equal(balance.Amount.Int64(), int64(140062235461521))

	// Commit some new blocks (commit blocks less than the distribution event blocks)
	s.coordinator.CommitNBlocks(cChain, (1000-1)-21)
	err = s.path.EndpointB.UpdateClient()
	s.Require().Equal(int64(1000), cChain.GetContext().BlockHeight())

	// check the consumer chain fee pool (should have increased
	balance = cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerFeePoolAddr, "stake")
	expFeePoolAtDistr := int64(4175822659438993)
	s.Assert().Equal(balance.Amount.Int64(), expFeePoolAtDistr)

	// Verify that the destinationChannel exists
	// if this doesn't exist then the transfer logic will fail when
	// a the distribution transfer is invoked in the next block.
	ctx := cChain.GetContext()
	sourcePort := transfertypes.PortID
	sourceChannel := cKeep.GetDistributionTransmissionChannel(ctx)
	sourceChannelEnd, found := cApp.IBCKeeper.ChannelKeeper.GetChannel(ctx, sourcePort, sourceChannel)
	s.Require().True(found)
	destinationChannel := sourceChannelEnd.GetCounterparty().GetChannelID()
	s.Require().True(len(destinationChannel) > 0)

	// commit 1 more block (which should invoke a distribution event)
	rspEB, _, _ := s.coordinator.CommitBlockGetResponses(cChain)

	// get the packet from the endblock events
	var packet channeltypes.Packet
	var ftpd transfertypes.FungibleTokenPacketData
	found = false
	for _, evnt := range rspEB.Events {
		if evnt.Type == channeltypes.EventTypeSendPacket {
			found = true
			packet, err = channelkeeper.ReconstructPacketFromEvent(evnt)
			s.Require().NoError(err)
			cApp.AppCodec().MustUnmarshalJSON(packet.GetData(), &ftpd)
		}
	}
	s.Require().True(found)

	// ensure the correct amount is being transmitted within the packet
	expConsRedistrAmt := expFeePoolAtDistr / 2 // because of default 50% redistribute fraction (will truc decimal)
	expProviderAmt := expFeePoolAtDistr - expConsRedistrAmt
	s.Assert().Equal(ftpd.Amount, fmt.Sprintf("%v", expProviderAmt))

	// halt provider distribution (for testing purposes to be able to review the
	// provider fee pool)
	s.DisableProviderDistribution()

	// relay the packet
	err = s.transferPath.RelayPacket(packet)
	s.Require().NoError(err)

	// check the consumer chain fee pool which should be now emptied (besides
	// new minted tokens since the transfer)
	balance = cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerFeePoolAddr, "stake")
	s.Assert().Equal(balance.Amount.Int64(), int64(26786189989304)) // this is "small"

	// check the provider chain fee pool which should now have
	// the consumer chain tokens
	balance = pApp.BankKeeper.GetBalance(pChain.GetContext(), providerFeePoolAddr,
		"ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9")
	s.Assert().Equal(balance.Amount.Int64(), expProviderAmt)

	// check the consumer redistribution amount arrives in the module account
	consumerRedistrAddr := cApp.AccountKeeper.GetModuleAccount(ctx,
		childtypes.ConsumerRedistributeName).GetAddress()
	balance = cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerRedistrAddr, "stake")
	s.Assert().Equal(balance.Amount.Int64(), expConsRedistrAmt)

	// Ensure provider pool emptied and that allocation was called normally
	// allocation would result in validator rewards, but due to limitations in
	// the testing framework (where validators do not actually sign votes and
	// therefor do not produce abci.VoteInfo) the expected behaviour of
	// allocation is to send all rewards to the community pool
	s.ReenableProviderDistribution()
	s.coordinator.CommitNBlocks(pChain, 1)
	balance = pApp.BankKeeper.GetBalance(pChain.GetContext(), providerFeePoolAddr,
		"ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9")
	s.Assert().Equal(balance.Amount.Int64(), int64(0))
	communityPool := pApp.DistrKeeper.GetFeePool(pChain.GetContext()).CommunityPool
	balanceI64 := communityPool.AmountOf(
		"ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9").RoundInt64()
	s.Assert().Equal(balanceI64, expProviderAmt)
}
