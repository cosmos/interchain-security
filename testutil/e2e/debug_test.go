// Contains native golang tests relevant to individual CCVTestSuite tests,
// enabling easier debugging of individual e2e tests in VSCode.
package e2e_test

import (
	"os"
	"reflect"
	"strings"
	"testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/tests/e2e"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
)

// runE2eTestByName runs a single e2e test by name, using a CCVTestSuite
// initialized with the dummy provider and consumer defined in this repo.
func runE2eTestByName(t *testing.T, testName string) {

	if strings.Contains(os.Args[0], "/_test/") {
		t.Skip("Skipping e2e test in test binary")
	}

	s := e2e.NewCCVTestSuite[*appProvider.App, *appConsumer.App](
		icstestingutils.ProviderAppIniter, icstestingutils.ConsumerAppIniter)
	s.SetT(t)

	methodFinder := reflect.TypeOf(s)
	method, found := methodFinder.MethodByName(testName)
	if !found {
		t.Errorf("Method %s is not defined for CCVTestSuite", testName)
	}

	s.SetupTest()
	method.Func.Call([]reflect.Value{reflect.ValueOf(s)})
}

//
// Channel init tests
//

func TestConsumerGenesis(t *testing.T) {
	runE2eTestByName(t, "TestConsumerGenesis")
}

func TestInitTimeout(t *testing.T) {
	runE2eTestByName(t, "TestInitTimeout")
}

//
// Distribution tests
//

func TestRewardsDistribution(t *testing.T) {
	runE2eTestByName(t, "TestRewardsDistribution")
}

//
// Normal operations tests
//
func TestHistoricalInfo(t *testing.T) {
	runE2eTestByName(t, "TestHistoricalInfo")
}

//
// Slashing tests
//

func TestRelayAndApplySlashPacket(t *testing.T) {
	runE2eTestByName(t, "TestRelayAndApplySlashPacket")
}

func TestSlashPacketAcknowledgement(t *testing.T) {
	runE2eTestByName(t, "TestSlashPacketAcknowledgement")
}

func TestHandleSlashPacketDoubleSigning(t *testing.T) {
	runE2eTestByName(t, "TestHandleSlashPacketDoubleSigning")
}

func TestHandleSlashPacketErrors(t *testing.T) {
	runE2eTestByName(t, "TestHandleSlashPacketErrors")
}

func TestHandleSlashPacketDistribution(t *testing.T) {
	runE2eTestByName(t, "TestHandleSlashPacketDistribution")
}

func TestValidatorDowntime(t *testing.T) {
	runE2eTestByName(t, "TestValidatorDowntime")
}

func TestValidatorDoubleSigning(t *testing.T) {
	runE2eTestByName(t, "TestValidatorDoubleSigning")
}

func TestSendSlashPacket(t *testing.T) {
	runE2eTestByName(t, "TestSendSlashPacket")
}

//
// Stop consumer tests
//

func TestStopConsumerChain(t *testing.T) {
	runE2eTestByName(t, "TestStopConsumerChain")
}

func TestStopConsumerOnChannelClosed(t *testing.T) {
	runE2eTestByName(t, "TestStopConsumerOnChannelClosed")
}

func TestProviderChannelClosed(t *testing.T) {
	runE2eTestByName(t, "TestProviderChannelClosed")
}

//
// Unbonding tests
//

func TestUndelegationNormalOperation(t *testing.T) {
	runE2eTestByName(t, "TestUndelegationNormalOperation")
}

func TestUndelegationVscTimeout(t *testing.T) {
	runE2eTestByName(t, "TestUndelegationVscTimeout")
}

func TestUndelegationDuringInit(t *testing.T) {
	runE2eTestByName(t, "TestUndelegationDuringInit")
}

func TestUnbondingNoConsumer(t *testing.T) {
	runE2eTestByName(t, "TestUnbondingNoConsumer")
}

func TestRedelegationNoConsumer(t *testing.T) {
	runE2eTestByName(t, "TestRedelegationNoConsumer")
}

func TestRedelegationProviderFirst(t *testing.T) {
	runE2eTestByName(t, "TestRedelegationProviderFirst")
}

//
// Val set update tests
//

func TestPacketRoundtrip(t *testing.T) {
	runE2eTestByName(t, "TestPacketRoundtrip")
}

func TestSendVSCMaturedPackets(t *testing.T) {
	runE2eTestByName(t, "TestSendVSCMaturedPackets")
}
