package integration

import (
	"fmt"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v8/modules/core/23-commitment/types"
	"github.com/cosmos/ibc-go/v8/modules/core/exported"
	ibctm "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"
	tmtypes "github.com/cometbft/cometbft/types"

	icstestingutils "github.com/cosmos/interchain-security/v5/testutil/ibc_testing"
	testutil "github.com/cosmos/interchain-security/v5/testutil/integration"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// ChainType defines the type of chain (either provider or consumer)
type ChainType int

const (
	Provider ChainType = iota
	Consumer
)

// firstConsumerBundle returns the bundle of the first consumer chain
func (s *CCVTestSuite) getFirstBundle() icstestingutils.ConsumerBundle {
	return s.getBundleByIdx(0)
}

func (s *CCVTestSuite) getBundleByIdx(index int) icstestingutils.ConsumerBundle {
	return *s.consumerBundles[ibctesting.GetChainID(2+index)]
}

func (s *CCVTestSuite) providerCtx() sdk.Context {
	return s.providerChain.GetContext()
}

// consumerCtx returns the context of only the FIRST consumer chain
func (s *CCVTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}

func (s *CCVTestSuite) providerBondDenom() (string, error) {
	return s.providerApp.GetTestStakingKeeper().BondDenom(s.providerCtx())
}

func (s *CCVTestSuite) getValByIdx(index int) (validator stakingtypes.Validator, valAddr sdk.ValAddress) {
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.providerChain.Vals.Validators[index]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	return s.getVal(s.providerCtx(), valAddr), valAddr
}

func (s *CCVTestSuite) getVal(ctx sdk.Context, valAddr sdk.ValAddress) stakingtypes.Validator {
	validator, err := s.providerApp.GetTestStakingKeeper().GetValidator(s.providerCtx(), valAddr)
	s.Require().NoError(err)
	return validator
}

func (s *CCVTestSuite) getValConsAddr(tmVal tmtypes.Validator) sdk.ConsAddress {
	val, err := tmVal.ToProto()
	s.Require().NoError(err)
	pubkey, err := cryptocodec.FromTmProtoPublicKey(val.GetPubKey())
	s.Require().Nil(err)
	return sdk.GetConsAddress(pubkey)
}

// setDefaultValSigningInfo sets the singing info on provider for tmVal,
// some slashing tests set signing info in different ways than this method.
func (s *CCVTestSuite) setDefaultValSigningInfo(tmVal tmtypes.Validator) {
	consAddr := s.getValConsAddr(tmVal)
	valInfo := slashingtypes.NewValidatorSigningInfo(consAddr, s.providerCtx().BlockHeight(),
		s.providerCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	s.providerApp.GetTestSlashingKeeper().SetValidatorSigningInfo(s.providerCtx(), consAddr, valInfo)
}

func getBalance(s *CCVTestSuite, providerCtx sdk.Context, delAddr sdk.AccAddress) math.Int {
	denom, err := s.providerBondDenom()
	s.Require().NoError(err)
	return s.providerApp.GetTestBankKeeper().GetBalance(providerCtx, delAddr, denom).Amount
}

// delegateAndUndelegate delegates bondAmt from delAddr to the first validator
// and then immediately undelegates 1/shareDiv of that delegation
func delegateAndUndelegate(s *CCVTestSuite, delAddr sdk.AccAddress, bondAmt math.Int, shareDiv int64) (initBalance math.Int, valsetUpdateId uint64) {
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
	srcValAddr, dstValAddr sdk.ValAddress, amount math.Int,
) {
	// Delegate to src validator
	srcValTokensBefore := s.getVal(s.providerCtx(), srcValAddr).GetBondedTokens()
	_, sharesDelegated, _ := delegate(s, delAddr, amount)

	// Assert expected amount was bonded to src validator
	srcValTokensAfter := s.getVal(s.providerCtx(), srcValAddr).GetBondedTokens()
	s.Require().Equal(srcValTokensAfter.Sub(srcValTokensBefore), amount)

	s.nextEpoch()

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
func delegate(s *CCVTestSuite, delAddr sdk.AccAddress, bondAmt math.Int) (initBalance math.Int, shares math.LegacyDec, valAddr sdk.ValAddress) {
	return delegateByIdx(s, delAddr, bondAmt, 0)
}

// delegateByIdx delegates bondAmt to the validator at specified index in provider val set
func delegateByIdx(s *CCVTestSuite, delAddr sdk.AccAddress, bondAmt math.Int, idx int) (initBalance math.Int, shares math.LegacyDec, valAddr sdk.ValAddress) {
	initBalance = getBalance(s, s.providerCtx(), delAddr)
	// choose a validator
	validator, valAddr := s.getValByIdx(idx)
	// delegate bondAmt tokens on provider to change validator powers
	shares, err := s.providerApp.GetTestStakingKeeper().Delegate(
		s.providerCtx(),
		delAddr,
		bondAmt,
		stakingtypes.Unbonded,
		validator,
		true,
	)
	s.Require().NoError(err)
	// check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))
	return initBalance, shares, valAddr
}

// undelegate unbonds an amount of delegator shares from a given validator
func undelegate(s *CCVTestSuite, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount math.LegacyDec) (valsetUpdateId uint64) {
	_, _, err := s.providerApp.GetTestStakingKeeper().Undelegate(s.providerCtx(), delAddr, valAddr, sharesAmount)
	s.Require().NoError(err)

	// save the current valset update ID
	valsetUpdateID := s.providerApp.GetProviderKeeper().GetValidatorSetUpdateId(s.providerCtx())

	return valsetUpdateID
}

// Executes a BeginRedelegation (unbonding and redelegation) operation
// on the provider chain using delegated funds from delAddr
func redelegate(s *CCVTestSuite, delAddr sdk.AccAddress, valSrcAddr sdk.ValAddress,
	valDstAddr sdk.ValAddress, sharesAmount math.LegacyDec,
) {
	stakingKeeper := s.providerApp.GetTestStakingKeeper()
	ctx := s.providerCtx()

	// delegate bondAmt tokens on provider to change validator powers
	completionTime, err := stakingKeeper.BeginRedelegation(
		ctx,
		delAddr,
		valSrcAddr,
		valDstAddr,
		sharesAmount,
	)
	s.Require().NoError(err)

	providerUnbondingPeriod, err := stakingKeeper.UnbondingTime(ctx)
	s.Require().NoError(err)

	valSrc, err := stakingKeeper.GetValidator(ctx, valSrcAddr)
	s.Require().NoError(err)

	// Completion time of redelegation operation will be after unbonding period if source val is bonded
	if valSrc.IsBonded() {
		s.Require().Equal(ctx.BlockHeader().Time.Add(providerUnbondingPeriod), completionTime)
	}
	// Completion time of redelegation operation will be at unbonding time of validator if it's unbonding
	if valSrc.IsUnbonding() {
		s.Require().Equal(valSrc.UnbondingTime, completionTime)
	}
}

func (s *CCVTestSuite) newPacketFromProvider(data []byte, sequence uint64, path *ibctesting.Path, timeoutHeight clienttypes.Height, timeoutTimestamp uint64) channeltypes.Packet {
	return channeltypes.NewPacket(data, sequence,
		path.EndpointB.ChannelConfig.PortID, path.EndpointB.ChannelID,
		path.EndpointA.ChannelConfig.PortID, path.EndpointA.ChannelID,
		timeoutHeight, timeoutTimestamp)
}

func (s *CCVTestSuite) newPacketFromConsumer(data []byte, sequence uint64, path *ibctesting.Path, timeoutHeight clienttypes.Height, timeoutTimestamp uint64) channeltypes.Packet {
	return channeltypes.NewPacket(data, sequence,
		path.EndpointA.ChannelConfig.PortID, path.EndpointA.ChannelID,
		path.EndpointB.ChannelConfig.PortID, path.EndpointB.ChannelID,
		timeoutHeight, timeoutTimestamp)
}

// sendOnProviderRecvOnConsumer sends a packet from the provider chain and receives it on the consumer chain
func sendOnProviderRecvOnConsumer(s *CCVTestSuite, path *ibctesting.Path, timeoutHeight clienttypes.Height, timeoutTimestamp uint64, data []byte) channeltypes.Packet {
	sequence, err := path.EndpointB.SendPacket(timeoutHeight, timeoutTimestamp, data)
	s.Require().NoError(err)

	packet := s.newPacketFromProvider(data, sequence, path, timeoutHeight, timeoutTimestamp)

	err = path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)
	return packet
}

// sendOnConsumerRecvOnProvider sends a packet from the consumer chain and receives it on the provider chain
func sendOnConsumerRecvOnProvider(s *CCVTestSuite, path *ibctesting.Path, timeoutHeight clienttypes.Height, timeoutTimestamp uint64, data []byte) channeltypes.Packet {
	sequence, err := path.EndpointA.SendPacket(timeoutHeight, timeoutTimestamp, data)
	s.Require().NoError(err)

	packet := s.newPacketFromConsumer(data, sequence, path, timeoutHeight, timeoutTimestamp)

	err = path.EndpointB.RecvPacket(packet)
	s.Require().NoError(err)
	return packet
}

// relayAllCommittedPackets relays all committed packets from `srcChain` on `path`
func relayAllCommittedPackets(
	s *CCVTestSuite,
	srcChain *ibctesting.TestChain,
	path *ibctesting.Path,
	srcPortID string,
	srcChannelID string,
	expectedPackets int,
	msgAndArgs ...interface{},
) {
	// check that the packets are committed in  state
	commitments := srcChain.App.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(
		srcChain.GetContext(),
		srcPortID,
		srcChannelID,
	)
	s.Require().Equal(
		expectedPackets,
		len(commitments),
		fmt.Sprintf("actual number of packet commitments does not match expectation; expected: %d - got: %d", expectedPackets, len(commitments)),
	)

	// relay all packets from srcChain to counterparty
	for _, commitment := range commitments {
		// - get packets
		packet, found := s.getSentPacket(srcChain, commitment.Sequence, srcChannelID)
		s.Require().True(
			found,
			fmt.Sprintf("did not find sent packet; %s", msgAndArgs...),
		)
		// - relay the packet
		err := path.RelayPacket(packet)
		s.Require().NoError(
			err,
			fmt.Sprintf("error while relaying packets; %v", err),
		)
	}
}

// incrementTimeByUnbondingPeriod increments the overall time by
//   - if chainType == Provider, the unbonding period on the provider.
//   - otherwise, the unbonding period on the consumer.
//
// Note that it is expected for the provider unbonding period
// to be one day larger than the consumer unbonding period.
func incrementTimeByUnbondingPeriod(s *CCVTestSuite, chainType ChainType) {
	// Get unboding periods
	providerUnbondingPeriod, err := s.providerApp.GetTestStakingKeeper().UnbondingTime(s.providerCtx())
	s.Require().NoError(err)
	consumerUnbondingPeriod := s.consumerApp.GetConsumerKeeper().GetUnbondingPeriod(s.consumerCtx())
	var jumpPeriod time.Duration
	if chainType == Provider {
		jumpPeriod = providerUnbondingPeriod
	} else {
		jumpPeriod = consumerUnbondingPeriod
	}
	incrementTime(s, jumpPeriod)
}

func checkStakingUnbondingOps(s *CCVTestSuite, id uint64, found, onHold bool, msgAndArgs ...interface{}) {
	stakingUnbondingOp, wasFound := getStakingUnbondingDelegationEntry(s.providerCtx(), s.providerApp.GetTestStakingKeeper(), id)
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
	entries := s.providerApp.GetProviderKeeper().GetUnbondingOpsFromIndex(providerCtx, chainID, valUpdateID)
	if found {
		s.Require().NotEmpty(entries, fmt.Sprintf("checkCCVUnbondingOp failed - should not be empty; %s", msgAndArgs...))
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
	expect uint16,
) []stakingtypes.Redelegation {
	redelegations, err := s.providerApp.GetTestStakingKeeper().GetRedelegations(s.providerCtx(), delAddr, 2)
	s.Require().NoError(err)
	s.Require().Len(redelegations, int(expect))
	return redelegations
}

// Checks that a redelegation entry has a completion time equal to an expected time
func checkRedelegationEntryCompletionTime(
	s *CCVTestSuite, entry stakingtypes.RedelegationEntry, expectedCompletion time.Time,
) {
	s.Require().Equal(expectedCompletion, entry.CompletionTime)
}

func getStakingUnbondingDelegationEntry(ctx sdk.Context, k testutil.TestStakingKeeper, id uint64) (stakingUnbondingOp stakingtypes.UnbondingDelegationEntry, found bool) {
	stakingUbd, err := k.GetUnbondingDelegationByUnbondingID(ctx, id)
	if err != nil {
		return
	}

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

	sendOnProviderRecvOnConsumer(suite, suite.getFirstBundle().Path, clienttypes.Height{}, timeout, pd.GetBytes())
}

// commitSlashPacket returns a commit hash for the given slash packet data
// Note that it must be called before sending the embedding IBC packet.
func (suite *CCVTestSuite) commitSlashPacket(ctx sdk.Context, packetData ccv.SlashPacketData) []byte {
	consumerPacket := ccv.ConsumerPacketData{
		Type: ccv.SlashPacket,
		Data: &ccv.ConsumerPacketData_SlashPacketData{
			SlashPacketData: &packetData,
		},
	}

	return suite.commitConsumerPacket(ctx, consumerPacket)
}

// commitConsumerPacket returns a commit hash for the given consumer packet data
// Note that it must be called before sending the embedding IBC packet.
func (suite *CCVTestSuite) commitConsumerPacket(ctx sdk.Context, packetData ccv.ConsumerPacketData) []byte {
	oldBlockTime := ctx.BlockTime()
	timeout := uint64(oldBlockTime.Add(ccv.DefaultCCVTimeoutPeriod).UnixNano())

	packet := suite.newPacketFromConsumer(packetData.GetBytes(), 1, suite.path, clienttypes.Height{}, timeout)

	return channeltypes.CommitPacket(suite.consumerChain.App.AppCodec(), packet)
}

// constructSlashPacketFromConsumer constructs an IBC packet embedding
// slash packet data to be sent from consumer to provider
func (s *CCVTestSuite) constructSlashPacketFromConsumer(bundle icstestingutils.ConsumerBundle,
	tmVal tmtypes.Validator, infractionType stakingtypes.Infraction, ibcSeqNum uint64,
) channeltypes.Packet {
	packet, _ := s.constructSlashPacketFromConsumerWithData(bundle, tmVal, infractionType, ibcSeqNum)
	return packet
}

func (s *CCVTestSuite) constructSlashPacketFromConsumerWithData(bundle icstestingutils.ConsumerBundle,
	tmVal tmtypes.Validator, infractionType stakingtypes.Infraction, ibcSeqNum uint64,
) (channeltypes.Packet, ccv.SlashPacketData) {
	valsetUpdateId := bundle.GetKeeper().GetHeightValsetUpdateID(
		bundle.GetCtx(), uint64(bundle.GetCtx().BlockHeight()))

	spdData := ccv.SlashPacketData{
		Validator: abci.Validator{
			Address: tmVal.Address,
			Power:   tmVal.VotingPower,
		},
		ValsetUpdateId: valsetUpdateId,
		Infraction:     infractionType,
	}

	cpdData := ccv.ConsumerPacketData{
		Type: ccv.SlashPacket,
		Data: &ccv.ConsumerPacketData_SlashPacketData{
			SlashPacketData: &spdData,
		},
	}

	return channeltypes.NewPacket(cpdData.GetBytes(),
		ibcSeqNum,
		ccv.ConsumerPortID,              // Src port
		bundle.Path.EndpointA.ChannelID, // Src channel
		ccv.ProviderPortID,              // Dst port
		bundle.Path.EndpointB.ChannelID, // Dst channel
		clienttypes.Height{},
		uint64(bundle.GetCtx().BlockTime().Add(ccv.DefaultCCVTimeoutPeriod).UnixNano()),
	), spdData
}

// incrementTime increments the overall time by jumpPeriod
// while updating to not expire the clients
func incrementTime(s *CCVTestSuite, jumpPeriod time.Duration) {
	// get trusting period of client on provider endpoint
	cs, ok := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(), s.path.EndpointB.ClientID)
	s.Require().True(ok)
	providerEndpointTP := cs.(*ibctm.ClientState).TrustingPeriod
	// get trusting period of client on consumer endpoint
	cs, ok = s.consumerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.consumerCtx(), s.path.EndpointA.ClientID)
	s.Require().True(ok)
	consumerEndpointTP := cs.(*ibctm.ClientState).TrustingPeriod
	// find the minimum trusting period
	var minTP time.Duration
	if providerEndpointTP < consumerEndpointTP {
		minTP = providerEndpointTP
	} else {
		minTP = consumerEndpointTP
	}
	// jumpStep is the maximum interval at which both clients are updated
	jumpStep := minTP / 2
	for jumpPeriod > 0 {
		var step time.Duration
		if jumpPeriod < jumpStep {
			step = jumpPeriod
		} else {
			step = jumpStep
		}
		s.coordinator.IncrementTimeBy(step)
		// update the provider client on the consumer
		err := s.path.EndpointA.UpdateClient()
		s.Require().NoError(err)
		// update the consumer client on the provider
		err = s.path.EndpointB.UpdateClient()
		s.Require().NoError(err)
		jumpPeriod -= step
	}
}

// incrementTimeWithoutUpdate increments the overall time by jumpPeriod
// without updating the client to the `noUpdate` chain
func incrementTimeWithoutUpdate(s *CCVTestSuite, jumpPeriod time.Duration, noUpdate ChainType) {
	var trustingPeriod time.Duration
	var endpointToUpdate *ibctesting.Endpoint
	if noUpdate == Consumer {
		cs, ok := s.consumerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.consumerCtx(), s.path.EndpointA.ClientID)
		s.Require().True(ok)
		trustingPeriod = cs.(*ibctm.ClientState).TrustingPeriod
		endpointToUpdate = s.path.EndpointA
	} else {
		cs, ok := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(), s.path.EndpointB.ClientID)
		s.Require().True(ok)
		trustingPeriod = cs.(*ibctm.ClientState).TrustingPeriod
		endpointToUpdate = s.path.EndpointB
	}
	// jumpStep is the maximum interval at which the client on endpointToUpdate is updated
	jumpStep := trustingPeriod / 2
	for jumpPeriod > 0 {
		var step time.Duration
		if jumpPeriod < jumpStep {
			step = jumpPeriod
		} else {
			step = jumpStep
		}
		s.coordinator.IncrementTimeBy(step)
		// update the client
		err := endpointToUpdate.UpdateClient()
		s.Require().NoError(err)
		jumpPeriod -= step
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
	require.True(endpoint.Chain.TB, ok)
	tmConfig.UnbondingPeriod = unbondingPeriod

	trustPeriod, err := ccv.CalculateTrustPeriod(unbondingPeriod, providertypes.DefaultTrustingPeriodFraction)
	require.NoError(endpoint.Chain.TB, err)
	tmConfig.TrustingPeriod = trustPeriod

	height := endpoint.Counterparty.Chain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}
	clientState := ibctm.NewClientState(
		endpoint.Counterparty.Chain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath,
	)
	consensusState := endpoint.Counterparty.Chain.LastHeader.ConsensusState()

	msg, err := clienttypes.NewMsgCreateClient(
		clientState, consensusState, endpoint.Chain.SenderAccount.GetAddress().String(),
	)
	require.NoError(endpoint.Chain.TB, err)

	res, err := endpoint.Chain.SendMsgs(msg)
	require.NoError(endpoint.Chain.TB, err)

	endpoint.ClientID, err = ibctesting.ParseClientIDFromEvents(res.GetEvents())
	require.NoError(endpoint.Chain.TB, err)
}

// GetConsumerEndpointClientAndConsState returns the client and consensus state
// for a particular consumer endpoint, as specified by the consumer's bundle.
func (suite *CCVTestSuite) GetConsumerEndpointClientAndConsState(
	consumerBundle icstestingutils.ConsumerBundle,
) (exported.ClientState, exported.ConsensusState) {
	ctx := consumerBundle.GetCtx()
	consumerKeeper := consumerBundle.GetKeeper()

	clientID, found := consumerKeeper.GetProviderClientID(ctx)
	suite.Require().True(found)

	clientState, found := consumerBundle.App.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientID)
	suite.Require().True(found)

	consState, found := consumerBundle.App.GetIBCKeeper().ClientKeeper.GetClientConsensusState(
		ctx, clientID, clientState.GetLatestHeight())
	suite.Require().True(found)

	return clientState, consState
}

// setupValidatorPowers delegates from the sender account to give all
// validators on the provider chain the given voting powers.
func (s *CCVTestSuite) setupValidatorPowers(powers []int64) {
	delAddr := s.providerChain.SenderAccount.GetAddress()
	s.Require().Equal(len(powers), len(s.providerChain.Vals.Validators))
	for idx := range s.providerChain.Vals.Validators {
		bondAmt := math.NewInt(powers[idx]).Mul(sdk.DefaultPowerReduction)
		bondAmt = bondAmt.Sub(math.NewInt(1)) // 1 token is bonded during the initial setup
		delegateByIdx(s, delAddr, bondAmt, idx)
	}

	s.providerChain.NextBlock()

	stakingKeeper := s.providerApp.GetTestStakingKeeper()
	expectedTotalPower := int64(0)
	for idx, val := range s.providerChain.Vals.Validators {
		actualPower, err := stakingKeeper.GetLastValidatorPower(s.providerCtx(), sdk.ValAddress(val.Address))
		s.Require().NoError(err)
		s.Require().Equal(powers[idx], actualPower)
		expectedTotalPower += powers[idx]
	}

	totalPower, err := stakingKeeper.GetLastTotalPower(s.providerCtx())
	s.Require().NoError(err)
	s.Require().Equal(expectedTotalPower, totalPower.Int64())
}

// mustGetStakingValFromTmVal returns the staking validator from the current state of the staking keeper,
// corresponding to a given tendermint validator. Note this func will fail the test if the validator is not found.
func (s *CCVTestSuite) mustGetStakingValFromTmVal(tmVal tmtypes.Validator) (stakingVal stakingtypes.Validator) {
	stakingVal, err := s.providerApp.GetTestStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), sdk.ConsAddress(tmVal.Address))
	s.Require().NoError(err)
	return stakingVal
}

// nextEpoch moves `chain` forward by an epoch
func (s *CCVTestSuite) nextEpoch() {
	blocksPerEpoch := s.providerApp.GetProviderKeeper().GetParams(s.providerCtx()).BlocksPerEpoch

	for i := int64(0); i < blocksPerEpoch; i++ {
		s.providerChain.NextBlock()
	}
}
