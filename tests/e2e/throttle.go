package e2e

import (
	"fmt"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
)

// TODO: PR for multiple consumers?
func (s *CCVTestSuite) TestSlashPacketThrottling() {
	// TODO

	testCases := []struct {
		name    string
		packets []channeltypes.Packet
	}{
		{
			"no packets to receive",
			[]channeltypes.Packet{},
		},
		// mas
	}

	s.SetupCCVChannel(s.path)
	// s.SetupTransferChannel()

	providerStakingKeeper := s.providerApp.GetE2eStakingKeeper()
	providerSlashingKeeper := s.providerApp.GetE2eSlashingKeeper()
	providerKeeper := s.providerApp.GetProviderKeeper()
	consumerKeeper := s.consumerApp.GetConsumerKeeper()
	fmt.Println("provider keeper", providerKeeper.GetCCVTimeoutPeriod(s.providerCtx()))
	fmt.Println("consumer keeper", consumerKeeper.UnbondingTime(s.consumerCtx()))
	fmt.Println("provider staking keeper", providerStakingKeeper.UnbondingTime(s.providerCtx()))
	fmt.Println("provider slashing keeper", providerSlashingKeeper.SlashFractionDoubleSign(s.providerCtx()))

	for _, tc := range testCases {
		fmt.Println("test case", tc.name)

	}

}
