package app_test

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v7/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer-democracy"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	testutil "github.com/cosmos/interchain-security/testutil/integration"
	"github.com/stretchr/testify/require"
)

func TestDemocracyGovernanceWhitelistingKeys(t *testing.T) {
	_, valUpdates, _ := testutil.CreateValidators(t, 4)
	ibctesting.DefaultTestingAppInit = icstestingutils.DemocracyConsumerAppIniter(valUpdates)
	chain := ibctesting.NewTestChain(t, ibctesting.NewCoordinator(t, 0), "test")
	paramKeeper := chain.App.(*appConsumer.App).ParamsKeeper
	for paramKey := range appConsumer.LegacyWhitelistedParams {
		ss, ok := paramKeeper.GetSubspace(paramKey.Subspace)
		require.True(t, ok, "Unknown subspace %s", paramKey.Subspace)
		hasKey := ss.Has(chain.GetContext(), []byte(paramKey.Key))
		require.True(t, hasKey, "Invalid key %s for subspace %s", paramKey.Key, paramKey.Subspace)
	}
}
