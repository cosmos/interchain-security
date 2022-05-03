package provider_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	"github.com/cosmos/interchain-security/app"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
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
func (s *ProviderTestSuite) TestStakingHooks2() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.providerChain.SenderAccount.GetAddress()

	origTime := s.ctx.BlockTime()

	initBalance, valsetUpdateID := doUnbonding(s, delAddr, bondAmt)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// SEND PACKET
	s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.providerChain.App.GetStakingKeeper().GetValidatorUpdates(s.providerCtx())

	// Get current blocktime
	oldBlockTime := s.providerCtx().BlockTime()

	// commit block on provider chain and update consumer chain's client
	commitProviderBlock(s)
	// Relay packet to consumer chain
	packet, packetData := sendValUpdatePacket(s, valUpdates, valsetUpdateID, oldBlockTime, 1)

	// ACKNOWLEDGE PACKET
	newProviderCtx := endProviderUnbondingPeriod(s, origTime)
	// check that onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance.Sub(bondAmt)))

	// end consumer's unbonding period by advancing time and calling UnbondMaturePackets
	endConsumerUnbondingPeriod(s, origTime)

	// commit block on consumer and update provider client
	commitConsumerBlock(s)

	// send acknowledgement to provider
	sendValUpdateAck(s, newProviderCtx, packet, packetData)

	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, newProviderCtx, s.consumerChain.ChainID, valsetUpdateID, false)

	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that unbonding has completed
	// Check that half the coins have been returned
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
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

func (s *ProviderTestSuite) TestStakingHooks1() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.providerChain.SenderAccount.GetAddress()

	origTime := s.ctx.BlockTime()

	initBalance, valsetUpdateID := doUnbonding(s, delAddr, bondAmt)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// SEND PACKET
	s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.providerChain.App.GetStakingKeeper().GetValidatorUpdates(s.providerCtx())

	// Get current blocktime
	oldBlockTime := s.providerCtx().BlockTime()

	// commit block on provider chain and update consumer chain's client
	commitProviderBlock(s)
	// Relay packet to consumer chain
	packet, packetData := sendValUpdatePacket(s, valUpdates, valsetUpdateID, oldBlockTime, 1)

	// END CONSUMER UNBONDING
	// end consumer's unbonding period by advancing time and calling UnbondMaturePackets
	endConsumerUnbondingPeriod(s, origTime)

	// commit block on consumer and update provider client
	commitConsumerBlock(s)

	// send acknowledgement to provider
	sendValUpdateAck(s, s.providerCtx(), packet, packetData)

	// CHECK THAT UNBONDING IS NOT COMPLETE
	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// END PROVIDER UNBONDING
	newProviderCtx := endProviderUnbondingPeriod(s, origTime)

	// CHECK THAT UNBONDING IS COMPLETE
	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, newProviderCtx, s.consumerChain.ChainID, valsetUpdateID, false)

	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that unbonding has completed
	// Check that half the coins have been returned
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

func getBalance(s *ProviderTestSuite, providerCtx sdk.Context, delAddr sdk.AccAddress) sdk.Int {
	return s.providerChain.App.(*app.App).BankKeeper.GetBalance(providerCtx, delAddr, s.providerBondDenom()).Amount
}

func doUnbonding(s *ProviderTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int) (initBalance sdk.Int, valsetUpdateId uint64) {
	initBalance = getBalance(s, s.providerCtx(), delAddr)

	// Choose a validator, and get its address and data structure into the correct types
	validator, valAddr := s.getVal(0)

	// INITIAL BOND
	// Bond some tokens on provider to change validator powers
	shares, err := s.providerChain.App.GetStakingKeeper().Delegate(s.providerCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	s.Require().NoError(err)

	// Check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// UNDELEGATE
	// Undelegate half
	_, err = s.providerChain.App.GetStakingKeeper().Undelegate(s.providerCtx(), delAddr, valAddr, shares.QuoInt64(2))
	s.Require().NoError(err)

	// Check that the tokens have not been returned yet
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// save the current valset update ID
	valsetUpdateID := s.providerChain.App.(*app.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	return initBalance, valsetUpdateID
}

func endProviderUnbondingPeriod(s *ProviderTestSuite, origTime time.Time) sdk.Context {
	// - End provider unbonding period
	providerCtx := s.providerCtx().WithBlockTime(origTime.Add(consumertypes.UnbondingTime).Add(3 * time.Hour))
	// s.providerChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	s.providerChain.App.GetStakingKeeper().BlockValidatorUpdates(providerCtx)

	return providerCtx
}

func endConsumerUnbondingPeriod(s *ProviderTestSuite, origTime time.Time) {
	// - End consumer unbonding period
	consumerCtx := s.consumerCtx().WithBlockTime(origTime.Add(consumertypes.UnbondingTime).Add(3 * time.Hour))
	// s.consumerChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	err := s.consumerChain.App.(*app.App).ConsumerKeeper.UnbondMaturePackets(consumerCtx)
	s.Require().NoError(err)
}

func checkStakingUnbondingOps(s *ProviderTestSuite, id uint64, found bool, onHold bool) {
	stakingUnbondingOp, wasFound := GetStakingUnbondingDelegationEntry(s.providerCtx(), s.providerChain.App.GetStakingKeeper(), id)
	s.Require().True(found == wasFound)
	s.Require().True(onHold == stakingUnbondingOp.UnbondingOnHold)
}

func checkCCVUnbondingOp(s *ProviderTestSuite, providerCtx sdk.Context, chainID string, valUpdateID uint64, found bool) {
	_, wasFound := s.providerChain.App.(*app.App).ProviderKeeper.GetUnbondingOpsFromIndex(providerCtx, chainID, valUpdateID)
	s.Require().True(found == wasFound)
}

func sendValUpdatePacket(s *ProviderTestSuite, valUpdates []abci.ValidatorUpdate, valUpdateId uint64, blockTime time.Time, packetSequence uint64) (channeltypes.Packet, types.ValidatorSetChangePacketData) {
	packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateId, nil)
	timeout := uint64(ccv.GetTimeoutTimestamp(blockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), packetSequence, providertypes.PortID, s.path.EndpointB.ChannelID,
		consumertypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// Receive CCV packet on consumer chain
	err := s.path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)

	// update consumer chain hist info
	s.UpdateConsumerHistInfo(valUpdates)

	return packet, packetData
}

func commitProviderBlock(s *ProviderTestSuite) {
	s.coordinator.CommitBlock(s.providerChain)
	err := s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)
}

func commitConsumerBlock(s *ProviderTestSuite) {
	// commit consumer chain and update provider chain client
	s.coordinator.CommitBlock(s.consumerChain)
	err := s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)
}

func sendValUpdateAck(s *ProviderTestSuite, providerCtx sdk.Context, packet channeltypes.Packet, packetData types.ValidatorSetChangePacketData) {
	// TODO: I have commented out the below code because i do not know how to
	// get s.path.EndpointB.AcknowledgePacket to see the correct time. Instead, I am calling the
	// CCV module's keeper function directly. This is not as complete of a test.
	// If we have a more robust time system at some point, use s.path.EndpointB.AcknowledgePacket again.

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	// err := s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	// s.Require().NoError(err)

	err := s.providerChain.App.(*app.App).ProviderKeeper.OnAcknowledgementPacket(providerCtx, packet, packetData, ack)
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
