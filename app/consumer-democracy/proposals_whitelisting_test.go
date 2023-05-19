package app_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	appConsumer "github.com/octopus-network/interchain-security/app/consumer-democracy"
	ibctesting "github.com/octopus-network/interchain-security/legacy_ibc_testing/testing"
	icstestingutils "github.com/octopus-network/interchain-security/testutil/ibc_testing"
)

func TestDemocracyGovernanceWhitelistingKeys(t *testing.T) {
	chain := ibctesting.NewTestChain(t, ibctesting.NewCoordinator(t, 0),
		icstestingutils.DemocracyConsumerAppIniter, "test")
	paramKeeper := chain.App.(*appConsumer.App).ParamsKeeper
	for paramKey := range appConsumer.WhitelistedParams {
		ss, ok := paramKeeper.GetSubspace(paramKey.Subspace)
		require.True(t, ok, "Unknown subspace %s", paramKey.Subspace)
		hasKey := ss.Has(chain.GetContext(), []byte(paramKey.Key))
		require.True(t, hasKey, "Invalid key %s for subspace %s", paramKey.Key, paramKey.Subspace)
	}
}
