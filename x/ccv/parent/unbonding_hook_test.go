package parent_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	childApp "github.com/cosmos/interchain-security/app_child"
	parentApp "github.com/cosmos/interchain-security/app_parent"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
)

// PROVIDER FINISHES FIRST
// Bond some tokens on provider
// Unbond them to create unbonding op
// Check unbonding ops on both sides
// Advance time so that provider's unbonding op completes
// Check that unbonding on staking is not allowed to complete
// Relay valset update to consumer
// Advance time so that consumer's unbonding op completes
// Relay ack to provider
// Check that unbonding has finally completed in provider staking
func (s *ParentTestSuite) TestStakingHooks2() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.parentChain.SenderAccount.GetAddress()

	origTime := s.ctx.BlockTime()

	initBalance, valsetUpdateID := doUnbonding(s, delAddr, bondAmt)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.parentCtx(), s.childChain.ChainID, valsetUpdateID, true)

	// SEND PACKET
	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.parentChain.App.GetStakingKeeper().GetValidatorUpdates(s.parentCtx())

	// Get current blocktime
	oldBlockTime := s.parentCtx().BlockTime()

	// commit block on parent chain and update consumer chain's client
	commitParentBlock(s)
	// Relay packet to consumer chain
	packet, packetData := sendValUpdatePacket(s, valUpdates, valsetUpdateID, oldBlockTime, 1)

	// ACKNOWLEDGE PACKET
	newParentCtx := endParentUnbondingPeriod(s, origTime)
	// check that onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, newParentCtx, delAddr).Equal(initBalance.Sub(bondAmt)))

	// end child's unbonding period by advancing time and calling UnbondMaturePackets
	endChildUnbondingPeriod(s, origTime)

	// commit block on child and update parent client
	commitChildBlock(s)

	// send acknowledgement to parent
	sendValUpdateAck(s, newParentCtx, packet, packetData)

	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, newParentCtx, s.childChain.ChainID, valsetUpdateID, false)

	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that unbonding has completed
	// Check that half the coins have been returned
	s.Require().True(getBalance(s, newParentCtx, delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

// CONSUMER FINISHES FIRST
// Bond some tokens on provider
// Unbond them to create unbonding op
// Check unbonding ops on both sides
// Relay valset update to consumer
// Advance time so that consumer's unbonding op completes
// Relay ack to provider
// Check that unbonding on staking is not allowed to complete
// Advance time so that provider's unbonding op completes
// Check that unbonding has finally completed in provider staking

func (s *ParentTestSuite) TestStakingHooks1() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.parentChain.SenderAccount.GetAddress()

	origTime := s.ctx.BlockTime()

	initBalance, valsetUpdateID := doUnbonding(s, delAddr, bondAmt)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.parentCtx(), s.childChain.ChainID, valsetUpdateID, true)

	// SEND PACKET
	s.parentChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.parentChain.App.GetStakingKeeper().GetValidatorUpdates(s.parentCtx())

	// Get current blocktime
	oldBlockTime := s.parentCtx().BlockTime()

	// commit block on parent chain and update consumer chain's client
	commitParentBlock(s)
	// Relay packet to consumer chain
	packet, packetData := sendValUpdatePacket(s, valUpdates, valsetUpdateID, oldBlockTime, 1)

	// END CONSUMER UNBONDING
	// end child's unbonding period by advancing time and calling UnbondMaturePackets
	endChildUnbondingPeriod(s, origTime)

	// commit block on child and update parent client
	commitChildBlock(s)

	// send acknowledgement to parent
	sendValUpdateAck(s, s.parentCtx(), packet, packetData)

	// CHECK THAT UNBONDING IS NOT COMPLETE
	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, s.parentCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// END PROVIDER UNBONDING
	newParentCtx := endParentUnbondingPeriod(s, origTime)

	// CHECK THAT UNBONDING IS COMPLETE
	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, newParentCtx, s.childChain.ChainID, valsetUpdateID, false)

	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that unbonding has completed
	// Check that half the coins have been returned
	s.Require().True(getBalance(s, newParentCtx, delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

func getBalance(s *ParentTestSuite, parentCtx sdk.Context, delAddr sdk.AccAddress) sdk.Int {
	return s.parentChain.App.(*parentApp.App).BankKeeper.GetBalance(parentCtx, delAddr, s.parentBondDenom()).Amount
}

func doUnbonding(s *ParentTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int) (initBalance sdk.Int, valsetUpdateId uint64) {
	initBalance = getBalance(s, s.parentCtx(), delAddr)

	// Choose a validator, and get its address and data structure into the correct types
	validator, valAddr := s.getVal(0)

	// INITIAL BOND
	// Bond some tokens on provider to change validator powers
	shares, err := s.parentChain.App.GetStakingKeeper().Delegate(s.parentCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	s.Require().NoError(err)

	// Check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.parentCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// UNDELEGATE
	// Undelegate half
	_, err = s.parentChain.App.GetStakingKeeper().Undelegate(s.parentCtx(), delAddr, valAddr, shares.QuoInt64(2))
	s.Require().NoError(err)

	// Check that the tokens have not been returned yet
	s.Require().True(getBalance(s, s.parentCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// save the current valset update ID
	valsetUpdateID := s.parentChain.App.(*parentApp.App).ParentKeeper.GetValidatorSetUpdateId(s.parentCtx())

	return initBalance, valsetUpdateID
}

func endParentUnbondingPeriod(s *ParentTestSuite, origTime time.Time) sdk.Context {
	// - End provider unbonding period
	parentCtx := s.parentCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	// s.parentChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	s.parentChain.App.GetStakingKeeper().BlockValidatorUpdates(parentCtx)

	return parentCtx
}

func endChildUnbondingPeriod(s *ParentTestSuite, origTime time.Time) {
	// - End consumer unbonding period
	childCtx := s.childCtx().WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))
	// s.childChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	err := s.childChain.App.(*childApp.App).ChildKeeper.UnbondMaturePackets(childCtx)
	s.Require().NoError(err)
}

func checkStakingUnbondingOps(s *ParentTestSuite, id uint64, found bool, onHold bool) {
	stakingUnbondingOp, wasFound := GetStakingUnbondingDelegationEntry(s.parentCtx(), s.parentChain.App.GetStakingKeeper(), id)
	s.Require().True(found == wasFound)
	s.Require().True(onHold == stakingUnbondingOp.UnbondingOnHold)
}

func checkCCVUnbondingOp(s *ParentTestSuite, parentCtx sdk.Context, chainID string, valUpdateID uint64, found bool) {
	_, wasFound := s.parentChain.App.(*parentApp.App).ParentKeeper.GetUnbondingOpsFromIndex(parentCtx, chainID, valUpdateID)
	s.Require().True(found == wasFound)
}

func sendValUpdatePacket(s *ParentTestSuite, valUpdates []abci.ValidatorUpdate, valUpdateId uint64, blockTime time.Time, packetSequence uint64) (channeltypes.Packet, types.ValidatorSetChangePacketData) {
	packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateId, nil)
	timeout := uint64(ccv.GetTimeoutTimestamp(blockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), packetSequence, parenttypes.PortID, s.path.EndpointB.ChannelID,
		childtypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// Receive CCV packet on consumer chain
	err := s.path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)

	// update child chain hist info
	s.UpdateChildHistInfo(valUpdates)

	return packet, packetData
}

func commitParentBlock(s *ParentTestSuite) {
	s.coordinator.CommitBlock(s.parentChain)
	err := s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)
}

func commitChildBlock(s *ParentTestSuite) {
	// commit child chain and update parent chain client
	s.coordinator.CommitBlock(s.childChain)
	err := s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)
}

func sendValUpdateAck(s *ParentTestSuite, parentCtx sdk.Context, packet channeltypes.Packet, packetData types.ValidatorSetChangePacketData) {
	// TODO: I have commented out the below code because i do not know how to
	// get s.path.EndpointB.AcknowledgePacket to see the correct time. Instead, I am calling the
	// CCV module's keeper function directly. This is not as complete of a test.
	// If we have a more robust time system at some point, use s.path.EndpointB.AcknowledgePacket again.

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	// err := s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	// s.Require().NoError(err)

	err := s.parentChain.App.(*parentApp.App).ParentKeeper.OnAcknowledgementPacket(parentCtx, packet, packetData, ack)
	s.Require().NoError(err)
}

func GetStakingUnbondingDelegationEntry(ctx sdk.Context, k stakingkeeper.Keeper, id uint64) (stakingUnbondingOp stakingtypes.UnbondingDelegationEntry, found bool) {
	stakingUbd, found := k.GetUnbondingDelegationByUnbondingOpId(ctx, id)

	for _, entry := range stakingUbd.Entries {
		if entry.UnbondingOpId == id {
			stakingUnbondingOp = entry
			found = true
			break
		}
	}

	return stakingUnbondingOp, found
}
