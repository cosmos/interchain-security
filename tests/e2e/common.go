package e2e

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/testutil/e2e"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	"github.com/cosmos/ibc-go/v3/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
)

// ChainType defines the type of chain (either provider or consumer)
type ChainType int

const (
	Provider ChainType = iota
	Consumer
)

func (s *CCVTestSuite) providerCtx() sdk.Context {
	return s.providerChain.GetContext()
}

func (s *CCVTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}

func (s *CCVTestSuite) providerBondDenom() string {
	return s.providerApp.GetE2eStakingKeeper().BondDenom(s.providerCtx())
}

func (s *CCVTestSuite) getValByIdx(index int) (validator stakingtypes.Validator, valAddr sdk.ValAddress) {
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.providerChain.Vals.Validators[index]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	return s.getVal(s.providerCtx(), valAddr), valAddr
}

func (s *CCVTestSuite) getVal(ctx sdk.Context, valAddr sdk.ValAddress) stakingtypes.Validator {
	validator, found := s.providerApp.GetE2eStakingKeeper().GetValidator(s.providerCtx(), valAddr)
	s.Require().True(found)
	return validator
}

func getBalance(s *CCVTestSuite, providerCtx sdk.Context, delAddr sdk.AccAddress) sdk.Int {
	return s.providerApp.GetE2eBankKeeper().GetBalance(providerCtx, delAddr, s.providerBondDenom()).Amount
}

// delegateAndUndelegate delegates bondAmt from delAddr to the first validator
// and then immediately undelegates 1/shareDiv of that delegation
func delegateAndUndelegate(s *CCVTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int, shareDiv int64) (initBalance sdk.Int, valsetUpdateId uint64) {
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

// Delegates "amount" to a source validator, then redelegates that same amount to a dest validator,
// with related state assertions along the way.
//
// Note: This function advances blocks in-between operations, where validator powers are
// not checked, since they are checked in integration tests.
func delegateAndRedelegate(s *CCVTestSuite, delAddr sdk.AccAddress,
	srcValAddr sdk.ValAddress, dstValAddr sdk.ValAddress, amount sdk.Int) {

	// Delegate to src validator
	srcValTokensBefore := s.getVal(s.providerCtx(), srcValAddr).GetBondedTokens()
	_, sharesDelegated, _ := delegate(s, delAddr, amount)

	// Assert expected amount was bonded to src validator
	srcValTokensAfter := s.getVal(s.providerCtx(), srcValAddr).GetBondedTokens()
	s.Require().Equal(srcValTokensAfter.Sub(srcValTokensBefore), amount)

	s.providerChain.NextBlock()

	dstValTokensBefore := s.getVal(s.providerCtx(), dstValAddr).GetBondedTokens()

	// redelegate shares from src to dst validators
	redelegate(s, delAddr,
		srcValAddr,
		dstValAddr,
		sharesDelegated,
	)

	// Assert expected amount was delegated to dst val
	dstValTokensAfter := s.getVal(s.providerCtx(), dstValAddr).GetBondedTokens()
	s.Require().Equal(dstValTokensAfter.Sub(dstValTokensBefore), amount)

	// Assert delegated tokens amount returned to original value for src validator
	s.Require().Equal(srcValTokensBefore, s.getVal(s.providerCtx(), srcValAddr).GetBondedTokens())
}

// delegate delegates bondAmt to the first validator
func delegate(s *CCVTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int) (initBalance sdk.Int, shares sdk.Dec, valAddr sdk.ValAddress) {
	initBalance = getBalance(s, s.providerCtx(), delAddr)
	// choose a validator
	validator, valAddr := s.getValByIdx(0)
	// delegate bondAmt tokens on provider to change validator powers
	shares, err := s.providerApp.GetE2eStakingKeeper().Delegate(
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
func undelegate(s *CCVTestSuite, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount sdk.Dec) (valsetUpdateId uint64) {
	_, err := s.providerApp.GetE2eStakingKeeper().Undelegate(s.providerCtx(), delAddr, valAddr, sharesAmount)
	s.Require().NoError(err)

	// save the current valset update ID
	valsetUpdateID := s.providerApp.GetProviderKeeper().GetValidatorSetUpdateId(s.providerCtx())

	return valsetUpdateID
}

// Executes a BeginRedelegation (unbonding and redelegation) operation
// on the provider chain using delegated funds from delAddr
func redelegate(s *CCVTestSuite, delAddr sdk.AccAddress, valSrcAddr sdk.ValAddress,
	ValDstAddr sdk.ValAddress, sharesAmount sdk.Dec) {

	stakingKeeper := s.providerApp.GetE2eStakingKeeper()
	ctx := s.providerCtx()

	// delegate bondAmt tokens on provider to change validator powers
	completionTime, err := stakingKeeper.BeginRedelegation(
		ctx,
		delAddr,
		valSrcAddr,
		ValDstAddr,
		sharesAmount,
	)
	s.Require().NoError(err)

	providerUnbondingPeriod := stakingKeeper.UnbondingTime(ctx)

	valSrc, found := stakingKeeper.GetValidator(ctx, valSrcAddr)
	s.Require().True(found)

	// Completion time of redelegation operation will be after unbonding period if source val is bonded
	if valSrc.IsBonded() {
		s.Require().Equal(ctx.BlockHeader().Time.Add(providerUnbondingPeriod), completionTime)
	}
	// Completion time of redelegation operation will be at unbonding time of validator if it's unbonding
	if valSrc.IsUnbonding() {
		s.Require().Equal(valSrc.UnbondingTime, completionTime)
	}
}

// relayAllCommittedPackets relays all committed packets from `srcChain` on `path`
func relayAllCommittedPackets(
	s *CCVTestSuite,
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
	s.Require().Equal(expectedPackets, len(commitments),
		"actual number of packet commitments does not match expectation")

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
//   - if chainType == Provider, the unbonding period on the provider.
//   - otherwise, the unbonding period on the consumer.
//
// Note that it is expected for the provider unbonding period
// to be one day larger than the consumer unbonding period.
func incrementTimeByUnbondingPeriod(s *CCVTestSuite, chainType ChainType) {
	// Get unboding period from staking keeper
	providerUnbondingPeriod := s.providerApp.GetStakingKeeper().UnbondingTime(s.providerCtx())
	consumerUnbondingPeriod := s.consumerApp.GetConsumerKeeper().GetUnbondingPeriod(s.consumerCtx())
	// Note: the assertions below are not strictly necessary, and rely on default values
	s.Require().Equal(consumertypes.DefaultConsumerUnbondingPeriod+24*time.Hour, providerUnbondingPeriod, "unexpected provider unbonding period")
	s.Require().Equal(consumertypes.DefaultConsumerUnbondingPeriod, consumerUnbondingPeriod, "unexpected consumer unbonding period")
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

func checkStakingUnbondingOps(s *CCVTestSuite, id uint64, found bool, onHold bool, msgAndArgs ...interface{}) {
	stakingUnbondingOp, wasFound := getStakingUnbondingDelegationEntry(s.providerCtx(), s.providerApp.GetE2eStakingKeeper(), id)
	s.Require().Equal(
		found,
		wasFound,
		fmt.Sprintf("checkStakingUnbondingOps failed - getStakingUnbondingDelegationEntry; %s", msgAndArgs...),
	)
	if wasFound {
		s.Require().True(
			onHold == (0 < stakingUnbondingOp.UnbondingOnHoldRefCount),
			fmt.Sprintf("checkStakingUnbondingOps failed - onHold; %s", msgAndArgs...),
		)
	}
}

func checkCCVUnbondingOp(s *CCVTestSuite, providerCtx sdk.Context, chainID string, valUpdateID uint64, found bool, msgAndArgs ...interface{}) {
	entries, wasFound := s.providerApp.GetProviderKeeper().GetUnbondingOpsFromIndex(providerCtx, chainID, valUpdateID)
	s.Require().Equal(
		found,
		wasFound,
		fmt.Sprintf("checkCCVUnbondingOp failed - GetUnbondingOpsFromIndex; %s", msgAndArgs...),
	)
	if found {
		s.Require().Greater(
			len(entries),
			0,
			fmt.Sprintf("checkCCVUnbondingOp failed - no unbonding ops found; %s", msgAndArgs...),
		)
		s.Require().Greater(
			len(entries[0].UnbondingConsumerChains),
			0,
			fmt.Sprintf("checkCCVUnbondingOp failed - unbonding op with no consumer chains; %s", msgAndArgs...),
		)
		s.Require().Equal(
			"testchain2",
			entries[0].UnbondingConsumerChains[0],
			fmt.Sprintf("checkCCVUnbondingOp failed - unbonding op with unexpected consumer chain; %s", msgAndArgs...),
		)
	}
}

// Checks that an expected amount of redelegations exist for a delegator
// via the staking keeper, then returns those redelegations.
func checkRedelegations(s *CCVTestSuite, delAddr sdk.AccAddress,
	expect uint16) []stakingtypes.Redelegation {

	redelegations := s.providerApp.GetE2eStakingKeeper().GetRedelegations(s.providerCtx(), delAddr, 2)

	s.Require().Len(redelegations, int(expect))
	return redelegations
}

// Checks that a redelegation entry has a completion time equal to an expected time
func checkRedelegationEntryCompletionTime(
	s *CCVTestSuite, entry stakingtypes.RedelegationEntry, expectedCompletion time.Time) {
	s.Require().Equal(expectedCompletion, entry.CompletionTime)
}

func getStakingUnbondingDelegationEntry(ctx sdk.Context, k e2e.E2eStakingKeeper, id uint64) (stakingUnbondingOp stakingtypes.UnbondingDelegationEntry, found bool) {
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

// SendEmptyVSCPacket sends a VSC packet without any changes
// to ensure that the channel gets established
func (suite *CCVTestSuite) SendEmptyVSCPacket() {
	providerKeeper := suite.providerApp.GetProviderKeeper()

	oldBlockTime := suite.providerChain.GetContext().BlockTime()
	timeout := uint64(oldBlockTime.Add(ccv.DefaultCCVTimeoutPeriod).UnixNano())

	valUpdateID := providerKeeper.GetValidatorSetUpdateId(suite.providerChain.GetContext())

	pd := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{},
		valUpdateID,
		nil,
	)

	seq, ok := suite.providerApp.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(
		suite.providerChain.GetContext(), ccv.ProviderPortID, suite.path.EndpointB.ChannelID)
	suite.Require().True(ok)

	packet := channeltypes.NewPacket(pd.GetBytes(), seq, ccv.ProviderPortID, suite.path.EndpointB.ChannelID,
		ccv.ConsumerPortID, suite.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	err := suite.path.EndpointB.SendPacket(packet)
	suite.Require().NoError(err)
	err = suite.path.EndpointA.RecvPacket(packet)
	suite.Require().NoError(err)
}

// commitSlashPacket returns a commit hash for the given slash packet data
// Note that it must be called before sending the embedding IBC packet.
func (suite *CCVTestSuite) commitSlashPacket(ctx sdk.Context, packetData ccv.SlashPacketData) []byte {
	oldBlockTime := ctx.BlockTime()
	timeout := uint64(oldBlockTime.Add(ccv.DefaultCCVTimeoutPeriod).UnixNano())

	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, ccv.ConsumerPortID, suite.path.EndpointA.ChannelID,
		ccv.ProviderPortID, suite.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	return channeltypes.CommitPacket(suite.consumerChain.App.AppCodec(), packet)
}

// incrementTimeBy increments the overall time by jumpPeriod
func incrementTimeBy(s *CCVTestSuite, jumpPeriod time.Duration) {
	// Get unboding period from staking keeper
	consumerUnbondingPeriod := s.consumerApp.GetConsumerKeeper().GetUnbondingPeriod(s.consumerChain.GetContext())
	split := 1
	trustingPeriodFraction := s.providerApp.GetProviderKeeper().GetTrustingPeriodFraction(s.providerCtx())
	if jumpPeriod > consumerUnbondingPeriod/time.Duration(trustingPeriodFraction) {
		// Make sure the clients do not expire
		split = 4
		jumpPeriod = jumpPeriod / 4
	}
	for i := 0; i < split; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		err := s.path.EndpointA.UpdateClient()
		s.Require().NoError(err)
		// Update the consumer client on the provider
		err = s.path.EndpointB.UpdateClient()
		s.Require().NoError(err)
	}
}

// CreateCustomClient creates an IBC client on the endpoint
// using the given unbonding period.
// It will update the clientID for the endpoint if the message
// is successfully executed.
func (suite *CCVTestSuite) CreateCustomClient(endpoint *ibctesting.Endpoint, unbondingPeriod time.Duration) {
	// ensure counterparty has committed state
	endpoint.Chain.Coordinator.CommitBlock(endpoint.Counterparty.Chain)

	suite.Require().Equal(exported.Tendermint, endpoint.ClientConfig.GetClientType(), "only Tendermint client supported")

	tmConfig, ok := endpoint.ClientConfig.(*ibctesting.TendermintConfig)
	require.True(endpoint.Chain.T, ok)
	tmConfig.UnbondingPeriod = unbondingPeriod
	tmConfig.TrustingPeriod = unbondingPeriod / providertypes.DefaultTrustingPeriodFraction

	height := endpoint.Counterparty.Chain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}
	clientState := ibctmtypes.NewClientState(
		endpoint.Counterparty.Chain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	consensusState := endpoint.Counterparty.Chain.LastHeader.ConsensusState()

	msg, err := clienttypes.NewMsgCreateClient(
		clientState, consensusState, endpoint.Chain.SenderAccount.GetAddress().String(),
	)
	require.NoError(endpoint.Chain.T, err)

	res, err := endpoint.Chain.SendMsgs(msg)
	require.NoError(endpoint.Chain.T, err)

	endpoint.ClientID, err = ibctesting.ParseClientIDFromEvents(res.GetEvents())
	require.NoError(endpoint.Chain.T, err)
}

func (suite *CCVTestSuite) GetConsumerEndpointClientAndConsState() (exported.ClientState, exported.ConsensusState) {

	clientID, found := suite.consumerApp.GetConsumerKeeper().GetProviderClientID(suite.consumerCtx())
	suite.Require().True(found)

	clientState, found := suite.consumerApp.GetIBCKeeper().ClientKeeper.GetClientState(
		suite.consumerCtx(), clientID)
	suite.Require().True(found)

	consState, found := suite.consumerApp.GetIBCKeeper().ClientKeeper.GetClientConsensusState(
		suite.consumerCtx(), clientID, clientState.GetLatestHeight())
	suite.Require().True(found)

	return clientState, consState
}
