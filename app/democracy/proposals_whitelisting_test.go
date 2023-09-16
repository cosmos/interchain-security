package app_test

import (
	"testing"

	ibctesting "github.com/cosmos/ibc-go/v7/testing"
	"github.com/stretchr/testify/require"

	appConsumer "github.com/cosmos/interchain-security/v3/app/democracy"
	icstestingutils "github.com/cosmos/interchain-security/v3/testutil/ibc_testing"
	testutil "github.com/cosmos/interchain-security/v3/testutil/integration"
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
