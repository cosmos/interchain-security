package v3

import (
	"fmt"
	"testing"
	"time"

	storetypes "cosmossdk.io/store/types"
	"github.com/cosmos/cosmos-sdk/testutil"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v5/app/encoding"
	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"

	"github.com/stretchr/testify/require"
)

type testLegacyParamSubspace struct {
	*ccvtypes.ConsumerParams
}

func newTestLegacyParamsSubspace(p ccvtypes.ConsumerParams) testLegacyParamSubspace {
	return testLegacyParamSubspace{
		&p,
	}
}

func (ps testLegacyParamSubspace) Get(ctx sdk.Context, key []byte, ptr interface{}) {
	switch string(key) {
	case string(ccvtypes.KeyEnabled):
		*ptr.(*bool) = ps.Enabled
	case string(ccvtypes.KeyBlocksPerDistributionTransmission):
		*ptr.(*int64) = ps.BlocksPerDistributionTransmission
	case string(ccvtypes.KeyDistributionTransmissionChannel):
		*ptr.(*string) = ps.DistributionTransmissionChannel
	case string(ccvtypes.KeyProviderFeePoolAddrStr):
		*ptr.(*string) = ps.ProviderFeePoolAddrStr
	case string(ccvtypes.KeyCCVTimeoutPeriod):
		*ptr.(*time.Duration) = ps.CcvTimeoutPeriod
	case string(ccvtypes.KeyTransferTimeoutPeriod):
		*ptr.(*time.Duration) = ps.TransferTimeoutPeriod
	case string(ccvtypes.KeyConsumerRedistributionFrac):
		*ptr.(*string) = ps.ConsumerRedistributionFraction
	case string(ccvtypes.KeyHistoricalEntries):
		*ptr.(*int64) = ps.HistoricalEntries
	case string(ccvtypes.KeyConsumerUnbondingPeriod):
		*ptr.(*time.Duration) = ps.UnbondingPeriod
	case string(ccvtypes.KeySoftOptOutThreshold):
		*ptr.(*string) = ps.SoftOptOutThreshold
	case string(ccvtypes.KeyRewardDenoms):
		*ptr.(*[]string) = ps.RewardDenoms
	case string(ccvtypes.KeyProviderRewardDenoms):
		*ptr.(*[]string) = ps.ProviderRewardDenoms
	case string(ccvtypes.KeyRetryDelayPeriod):
		*ptr.(*time.Duration) = ps.RetryDelayPeriod
	default:
		panic(fmt.Sprintf("invalid paramspace key: %s", string(key)))

	}
}

func TestMigrateParams(t *testing.T) {
	cdc := encoding.MakeTestEncodingConfig().Codec
	storeKey := storetypes.NewKVStoreKey("ccvconsumer")
	ctx := testutil.DefaultContext(storeKey, storetypes.NewTransientStoreKey("transient_test"))
	store := ctx.KVStore(storeKey)

	defaultParams := ccvtypes.DefaultParams()
	legacyParamSubspace := newTestLegacyParamsSubspace(defaultParams)
	// confirms that testLegacyParamSubspace works as expected
	require.NotPanics(t, func() {
		GetConsumerParamsLegacy(ctx, legacyParamSubspace)
	})

	emptyParams := ccvtypes.ConsumerParams{}
	bz := store.Get(consumertypes.ParametersKey())
	require.NoError(t, cdc.Unmarshal(bz, &emptyParams))
	require.NotNil(t, emptyParams)
	require.Empty(t, emptyParams)
	require.NotEqual(t, defaultParams, emptyParams)

	err := MigrateLegacyParams(ctx, cdc, store, legacyParamSubspace)
	require.NoError(t, err)

	// check that new params are available after migration and equal to defaults
	// legacyParamSubspace was set to match defaultParams
	migratedParams := ccvtypes.ConsumerParams{}
	paramsBz := store.Get(consumertypes.ParametersKey())
	require.NotEqual(t, bz, paramsBz)
	require.NoError(t, cdc.Unmarshal(paramsBz, &migratedParams))

	require.Equal(t, defaultParams, migratedParams)
	require.NotEqual(t, emptyParams, migratedParams)
}
