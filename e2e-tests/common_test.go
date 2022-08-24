package e2e_test

import (
	"strings"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	"github.com/stretchr/testify/suite"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

// ChainType defines the type of chain (either provider or consumer)
type ChainType int

const (
	Provider ChainType = iota
	Consumer
)

func TestProviderTestSuite(t *testing.T) {
	suite.Run(t, new(ProviderTestSuite))
}

func (s *ProviderTestSuite) providerCtx() sdk.Context {
	return s.providerChain.GetContext()
}

func (s *ProviderTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}

func (s *ProviderTestSuite) providerBondDenom() string {
	return s.providerChain.App.(*appProvider.App).StakingKeeper.BondDenom(s.providerCtx())
}

func (s *ProviderTestSuite) getVal(index int) (validator stakingtypes.Validator, valAddr sdk.ValAddress) {
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.providerChain.Vals.Validators[index]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidator(s.providerCtx(), valAddr)
	s.Require().True(found)

	return validator, valAddr
}

func getBalance(s *ProviderTestSuite, providerCtx sdk.Context, delAddr sdk.AccAddress) sdk.Int {
	return s.providerChain.App.(*appProvider.App).BankKeeper.GetBalance(providerCtx, delAddr, s.providerBondDenom()).Amount
}

// delegateAndUndelegate delegates bondAmt from delAddr to the first validator
// and then immediately undelegates 1/shareDiv of that delegation
func delegateAndUndelegate(s *ProviderTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int, shareDiv int64) (initBalance sdk.Int, valsetUpdateId uint64) {
	// delegate
	initBalance, shares, valAddr := delegate(s, delAddr, bondAmt)

	// check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// undelegate 1/shareDiv
	valsetUpdateId = undelegate(s, delAddr, valAddr, shares.QuoInt64(shareDiv))

	// check that the tokens have not been returned yet
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	return initBalance, valsetUpdateId
}

// delegate delegates bondAmt to the first validator
func delegate(s *ProviderTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int) (initBalance sdk.Int, shares sdk.Dec, valAddr sdk.ValAddress) {
	initBalance = getBalance(s, s.providerCtx(), delAddr)
	// choose a validator
	validator, valAddr := s.getVal(0)
	// delegate bondAmt tokens on provider to change validator powers
	shares, err := s.providerChain.App.(*appProvider.App).StakingKeeper.Delegate(
		s.providerCtx(),
		delAddr,
		bondAmt,
		stakingtypes.Unbonded,
		stakingtypes.Validator(validator),
		true,
	)
	s.Require().NoError(err)
	// check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))
	return initBalance, shares, valAddr
}

// undelegate unbonds an amount of delegator shares from a given validator
func undelegate(s *ProviderTestSuite, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount sdk.Dec) (valsetUpdateId uint64) {
	_, err := s.providerChain.App.(*appProvider.App).StakingKeeper.Undelegate(s.providerCtx(), delAddr, valAddr, sharesAmount)
	s.Require().NoError(err)

	// save the current valset update ID
	valsetUpdateID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	return valsetUpdateID
}

// relayAllCommittedPackets relays all committed packets from `srcChain` on `path`
func relayAllCommittedPackets(
	s *ProviderTestSuite,
	srcChain *ibctesting.TestChain,
	path *ibctesting.Path,
	portID string,
	channelID string,
	expectedPackets int,
) {
	// check that the packets are committed in  state
	commitments := srcChain.App.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(
		srcChain.GetContext(),
		portID,
		channelID,
	)
	s.Require().Equal(expectedPackets, len(commitments), "did not find packet commitments")

	// relay all packets from srcChain to counterparty
	for _, commitment := range commitments {
		// - get packets
		packet, found := srcChain.GetSentPacket(commitment.Sequence)
		s.Require().True(found, "did not find sent packet")
		// - relay the packet
		err := path.RelayPacket(packet)
		s.Require().NoError(err)
	}
}

// incrementTimeByUnbondingPeriod increments the overall time by
//   - if provider == true, the unbonding period on the provider;
//   - otherwise, the unbonding period on the consumer.
//
// Note that it is expected for the provider unbonding period
// to be one day larger than the consumer unbonding period.
func incrementTimeByUnbondingPeriod(s *ProviderTestSuite, chainType ChainType) {
	// Get unboding period from staking keeper
	providerUnbondingPeriod := s.providerChain.App.GetStakingKeeper().UnbondingTime(s.providerCtx())
	consumerUnbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	s.Require().True(found)
	expectedUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	s.Require().Equal(expectedUnbondingPeriod+24*time.Hour, providerUnbondingPeriod, "unexpected provider unbonding period")
	s.Require().Equal(expectedUnbondingPeriod, consumerUnbondingPeriod, "unexpected consumer unbonding period")
	var jumpPeriod time.Duration
	if chainType == Provider {
		jumpPeriod = providerUnbondingPeriod
	} else {
		jumpPeriod = consumerUnbondingPeriod
	}
	// Make sure the clients do not expire
	jumpPeriod = jumpPeriod/4 + time.Hour
	for i := 0; i < 4; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		err := s.path.EndpointA.UpdateClient()
		s.Require().NoError(err)
		// Update the consumer client on the provider
		err = s.path.EndpointB.UpdateClient()
		s.Require().NoError(err)
	}
}

func checkStakingUnbondingOps(s *ProviderTestSuite, id uint64, found bool, onHold bool) {
	stakingUnbondingOp, wasFound := getStakingUnbondingDelegationEntry(s.providerCtx(), s.providerChain.App.(*appProvider.App).StakingKeeper, id)
	s.Require().True(found == wasFound)
	s.Require().True(onHold == (0 < stakingUnbondingOp.UnbondingOnHoldRefCount))
}

func checkCCVUnbondingOp(s *ProviderTestSuite, providerCtx sdk.Context, chainID string, valUpdateID uint64, found bool) {
	entries, wasFound := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetUnbondingOpsFromIndex(providerCtx, chainID, valUpdateID)
	s.Require().True(found == wasFound)
	if found {
		s.Require().True(len(entries) > 0, "No unbonding ops found")
		s.Require().True(len(entries[0].UnbondingConsumerChains) > 0, "Unbonding op with no consumer chains")
		s.Require().True(strings.Compare(entries[0].UnbondingConsumerChains[0], "testchain2") == 0, "Unbonding op with unexpected consumer chain")
	}
}

func getStakingUnbondingDelegationEntry(ctx sdk.Context, k stakingkeeper.Keeper, id uint64) (stakingUnbondingOp stakingtypes.UnbondingDelegationEntry, found bool) {
	stakingUbd, found := k.GetUnbondingDelegationByUnbondingId(ctx, id)

	for _, entry := range stakingUbd.Entries {
		if entry.UnbondingId == id {
			stakingUnbondingOp = entry
			found = true
			break
		}
	}

	return stakingUnbondingOp, found
}
