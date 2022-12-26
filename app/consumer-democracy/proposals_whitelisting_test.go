package app_test

import (
	"testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer-democracy"
	// TODO: Remove ibc ref
	//ibctesting "github.com/cosmos/ibc-go/v3/testing"
	ibctesting "github.com/cosmos/interchain-security/ibc/testing"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	"github.com/stretchr/testify/require"
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
