package v7

import (
	"testing"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v6/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

func TestMigrateParams(t *testing.T) {
	t.Helper()
	inMemParams := testutil.NewInMemKeeperParams(t)
	k, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	if !inMemParams.ParamsSubspace.HasKeyTable() {
		inMemParams.ParamsSubspace.WithKeyTable(providertypes.ParamKeyTable())
	}

	defaultParams := providertypes.DefaultParams()
	inMemParams.ParamsSubspace.Set(ctx, providertypes.KeyTemplateClient, defaultParams.TemplateClient)
	inMemParams.ParamsSubspace.Set(ctx, providertypes.KeyTrustingPeriodFraction, defaultParams.TrustingPeriodFraction)
	inMemParams.ParamsSubspace.Set(ctx, ccvtypes.KeyCCVTimeoutPeriod, defaultParams.CcvTimeoutPeriod)
	inMemParams.ParamsSubspace.Set(ctx, providertypes.KeySlashMeterReplenishPeriod, defaultParams.SlashMeterReplenishPeriod)
	inMemParams.ParamsSubspace.Set(ctx, providertypes.KeySlashMeterReplenishFraction, defaultParams.SlashMeterReplenishFraction)
	inMemParams.ParamsSubspace.Set(ctx, providertypes.KeyConsumerRewardDenomRegistrationFee, defaultParams.ConsumerRewardDenomRegistrationFee)
	inMemParams.ParamsSubspace.Set(ctx, providertypes.KeyBlocksPerEpoch, defaultParams.BlocksPerEpoch)
	inMemParams.ParamsSubspace.Set(ctx, providertypes.KeyNumberOfEpochsToStartReceivingRewards, defaultParams.NumberOfEpochsToStartReceivingRewards)

	// confirms that inMemParams.ParamsSubspace works as expected
	require.NotPanics(t, func() {
		GetParamsLegacy(ctx, inMemParams.ParamsSubspace)
	})

	// no "new" params should be available before migration
	// "new" params are stored under providertypes.ParametersKey()
	emptyParams := k.GetParams(ctx)
	require.Empty(t, emptyParams)

	// make sure that the legacy params are equal to the default params (they were set using inMemParams.ParamsSubspace.Set())
	legacyParams := GetParamsLegacy(ctx, inMemParams.ParamsSubspace)
	require.NotNil(t, legacyParams)
	require.Equal(t, defaultParams, legacyParams)

	err := MigrateLegacyParams(ctx, k, inMemParams.ParamsSubspace)
	require.NoError(t, err)

	// check that "new" params are available after migration and equal to defaults
	migratedParams := k.GetParams(ctx)
	require.NotEmpty(t, migratedParams)
	require.Equal(t, defaultParams, migratedParams)
}
