// Contains native golang tests relevant to individual integration tests,
// enabling easier debugging of individual integration tests in VSCode.
package integration_test

import (
	"reflect"
	"testing"

	appConsumer "github.com/cosmos/interchain-security/v6/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/v6/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/v6/app/provider"
	integr "github.com/cosmos/interchain-security/v6/tests/integration"
	icstestingutils "github.com/cosmos/interchain-security/v6/testutil/ibc_testing"
)

// runCCVTestByName runs a single CCV integration test by name, using a CCVTestSuite
// initialized with the dummy provider and consumer defined in this repo.
func runCCVTestByName(t *testing.T, methodName string) {
	t.Helper()
	suite := integr.NewCCVTestSuite[*appProvider.App, *appConsumer.App](
		icstestingutils.ProviderAppIniter, icstestingutils.ConsumerAppIniter, []string{})
	suite.SetT(t)
	suite.SetupTest()

	findAndCallMethod(t, suite, methodName)
}

// runConsumerDemocracyTestByName runs a single consumer democracy integration test by name,
// using a ConsumerDemocracyTestSuite initialized with the dummy
// democracy consumer defined in this repo.
func runConsumerDemocracyTestByName(t *testing.T, methodName string) {
	t.Helper()
	suite := integr.NewConsumerDemocracyTestSuite[*appConsumerDemocracy.App](
		icstestingutils.DemocracyConsumerAppIniter)
	suite.SetT(t)
	suite.SetupTest()

	findAndCallMethod(t, suite, methodName)
}

func findAndCallMethod(t *testing.T, suite any, methodName string) {
	t.Helper()
	methodFinder := reflect.TypeOf(suite)
	method, found := methodFinder.MethodByName(methodName)
	if !found {
		t.Errorf("Method %s is not defined for suite type", methodName)
	}

	method.Func.Call([]reflect.Value{reflect.ValueOf(suite)})
}

//
// Consumer democracy tests
//

func TestDemocracyRewardsDistribution(t *testing.T) {
	runConsumerDemocracyTestByName(t, "TestDemocracyRewardsDistribution")
}

func TestDemocracyGovernanceWhitelisting(t *testing.T) {
	runConsumerDemocracyTestByName(t, "TestDemocracyGovernanceWhitelisting")
}

func TestDemocracyMsgUpdateParams(t *testing.T) {
	runConsumerDemocracyTestByName(t, "TestDemocracyMsgUpdateParams")
}

//
// Distribution tests
//

func TestSendRewardsRetries(t *testing.T) {
	runCCVTestByName(t, "TestSendRewardsRetries")
}

func TestRewardsDistribution(t *testing.T) {
	runCCVTestByName(t, "TestRewardsDistribution")
}

func TestEndBlockRD(t *testing.T) {
	runCCVTestByName(t, "TestEndBlockRD")
}

func TestSendRewardsToProvider(t *testing.T) {
	runCCVTestByName(t, "TestSendRewardsToProvider")
}

//
// Expired client tests
//

func TestVSCPacketSendExpiredClient(t *testing.T) {
	runCCVTestByName(t, "TestVSCPacketSendExpiredClient")
}

func TestConsumerPacketSendExpiredClient(t *testing.T) {
	runCCVTestByName(t, "TestConsumerPacketSendExpiredClient")
}

//
// Normal operations tests
//

func TestHistoricalInfo(t *testing.T) {
	runCCVTestByName(t, "TestHistoricalInfo")
}

//
// Slashing tests
//

func TestRelayAndApplyDowntimePacket(t *testing.T) {
	runCCVTestByName(t, "TestRelayAndApplyDowntimePacket")
}

func TestRelayAndApplyDoubleSignPacket(t *testing.T) {
	runCCVTestByName(t, "TestRelayAndApplyDoubleSignPacket")
}

func TestSlashPacketAcknowledgement(t *testing.T) {
	runCCVTestByName(t, "TestSlashPacketAcknowledgement")
}

func TestHandleSlashPacketDowntime(t *testing.T) {
	runCCVTestByName(t, "TestHandleSlashPacketDowntime")
}

func TestOnRecvSlashPacketErrors(t *testing.T) {
	runCCVTestByName(t, "TestOnRecvSlashPacketErrors")
}

func TestValidatorDowntime(t *testing.T) {
	runCCVTestByName(t, "TestValidatorDowntime")
}

func TestValidatorDoubleSigning(t *testing.T) {
	runCCVTestByName(t, "TestValidatorDoubleSigning")
}

func TestQueueAndSendSlashPacket(t *testing.T) {
	runCCVTestByName(t, "TestQueueAndSendSlashPacket")
}

func TestCISBeforeCCVEstablished(t *testing.T) {
	runCCVTestByName(t, "TestCISBeforeCCVEstablished")
}

//
// Stop consumer tests
//

func TestStopConsumerChain(t *testing.T) {
	runCCVTestByName(t, "TestStopConsumerChain")
}

func TestStopConsumerOnChannelClosed(t *testing.T) {
	runCCVTestByName(t, "TestStopConsumerOnChannelClosed")
}

//
// Throttle tests
//

func TestBasicSlashPacketThrottling(t *testing.T) {
	runCCVTestByName(t, "TestBasicSlashPacketThrottling")
}

func TestMultiConsumerSlashPacketThrottling(t *testing.T) {
	runCCVTestByName(t, "TestMultiConsumerSlashPacketThrottling")
}

func TestPacketSpam(t *testing.T) {
	runCCVTestByName(t, "TestPacketSpam")
}

func TestDoubleSignDoesNotAffectThrottling(t *testing.T) {
	runCCVTestByName(t, "TestDoubleSignDoesNotAffectThrottling")
}

func TestSlashingSmallValidators(t *testing.T) {
	runCCVTestByName(t, "TestSlashingSmallValidators")
}

func TestSlashMeterAllowanceChanges(t *testing.T) {
	runCCVTestByName(t, "TestSlashMeterAllowanceChanges")
}

func TestSlashAllValidators(t *testing.T) {
	runCCVTestByName(t, "TestSlashAllValidators")
}

//
// Unbonding tests
//

func TestUndelegationCompletion(t *testing.T) {
	runCCVTestByName(t, "TestUndelegationCompletion")
}

//
// Val set update tests
//

func TestPacketRoundtrip(t *testing.T) {
	runCCVTestByName(t, "TestPacketRoundtrip")
}

func TestQueueAndSendVSCMaturedPackets(t *testing.T) {
	runCCVTestByName(t, "TestQueueAndSendVSCMaturedPackets")
}

//
// Changeover tests
//

func TestRecycleTransferChannel(t *testing.T) {
	runCCVTestByName(t, "TestRecycleTransferChannel")
}

//
// Misbehaviour tests
//

func TestHandleConsumerMisbehaviour(t *testing.T) {
	runCCVTestByName(t, "TestHandleConsumerMisbehaviour")
}

func TestGetByzantineValidators(t *testing.T) {
	runCCVTestByName(t, "TestGetByzantineValidators")
}

func TestCheckMisbehaviour(t *testing.T) {
	runCCVTestByName(t, "TestCheckMisbehaviour")
}

//
// Consumer Equivocation test
//

func TestHandleConsumerDoubleVoting(t *testing.T) {
	runCCVTestByName(t, "TestHandleConsumerDoubleVoting")
}

func TestHandleConsumerDoubleVotingSlashesUndelegationsAndRelegations(t *testing.T) {
	runCCVTestByName(t, "TestHandleConsumerDoubleVotingSlashesUndelegationsAndRelegations")
}

//
// Throttle retry tests
//

func TestSlashRetries(t *testing.T) {
	runCCVTestByName(t, "TestSlashRetries")
}

func TestKeyAssignment(t *testing.T) {
	runCCVTestByName(t, "TestKeyAssignment")
}

//
// Provider gov hooks test
//

func TestAfterPropSubmissionAndVotingPeriodEnded(t *testing.T) {
	runCCVTestByName(t, "TestAfterPropSubmissionAndVotingPeriodEnded")
}

func TestGetConsumerAdditionFromProp(t *testing.T) {
	runCCVTestByName(t, "TestGetConsumerAdditionFromProp")
}

func TestIBCTransferMiddleware(t *testing.T) {
	runCCVTestByName(t, "TestIBCTransferMiddleware")
}

func TestAllocateTokens(t *testing.T) {
	runCCVTestByName(t, "TestAllocateTokens")
}

func TestMultiConsumerRewardsDistribution(t *testing.T) {
	runCCVTestByName(t, "TestMultiConsumerRewardsDistribution")
}

func TestTooManyLastValidators(t *testing.T) {
	runCCVTestByName(t, "TestTooManyLastValidators")
}
