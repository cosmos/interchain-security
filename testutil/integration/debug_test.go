// Contains native golang tests relevant to individual integration tests,
// enabling easier debugging of individual integration tests in VSCode.
package integration_test

import (
	"reflect"
	"testing"

	appConsumer "github.com/cosmos/interchain-security/v5/app/consumer"
	appConsumerDemocracy "github.com/cosmos/interchain-security/v5/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/v5/app/provider"
	integr "github.com/cosmos/interchain-security/v5/tests/integration"
	icstestingutils "github.com/cosmos/interchain-security/v5/testutil/ibc_testing"
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
// Channel init tests
//

func TestInitTimeout(t *testing.T) {
	runCCVTestByName(t, "TestInitTimeout")
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

// TODO: fix panics -> possible app wiring issue -> seems that evidence router is nil
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
// Soft opt out tests
//

func TestSoftOptOut(t *testing.T) {
	runCCVTestByName(t, "TestSoftOptOut")
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

func TestUndelegationNormalOperation(t *testing.T) {
	runCCVTestByName(t, "TestUndelegationNormalOperation")
}

func TestUndelegationVscTimeout(t *testing.T) {
	runCCVTestByName(t, "TestUndelegationVscTimeout")
}

func TestUndelegationDuringInit(t *testing.T) {
	runCCVTestByName(t, "TestUndelegationDuringInit")
}

func TestUnbondingNoConsumer(t *testing.T) {
	runCCVTestByName(t, "TestUnbondingNoConsumer")
}

func TestRedelegationNoConsumer(t *testing.T) {
	runCCVTestByName(t, "TestRedelegationNoConsumer")
}

func TestRedelegationProviderFirst(t *testing.T) {
	runCCVTestByName(t, "TestRedelegationProviderFirst")
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

// Throttle retry tests
//

func TestSlashRetries(t *testing.T) {
	runCCVTestByName(t, "TestSlashRetries")
}
