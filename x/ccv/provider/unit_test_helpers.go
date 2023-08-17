package provider

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/types"
	ututil "github.com/cosmos/interchain-security/v3/x/ccv/types/unit_test_util"
)

//
// Unit test helpers specific to the provider module.
//

// NewInMemProviderKeeper instantiates an in-mem provider keeper from params and mocked keepers
func NewInMemProviderKeeper(params ututil.InMemKeeperParams, mocks ututil.MockedKeepers) providerkeeper.Keeper {
	return providerkeeper.NewKeeper(
		params.Cdc,
		params.StoreKey,
		*params.ParamsSubspace,
		mocks.MockScopedKeeper,
		mocks.MockChannelKeeper,
		mocks.MockPortKeeper,
		mocks.MockConnectionKeeper,
		mocks.MockClientKeeper,
		mocks.MockStakingKeeper,
		mocks.MockSlashingKeeper,
		mocks.MockAccountKeeper,
		mocks.MockEvidenceKeeper,
		mocks.MockDistributionKeeper,
		mocks.MockBankKeeper,
		authtypes.FeeCollectorName,
	)
}

// Returns an in-memory provider keeper, context, controller, and mocks, given a test instance and parameters.
//
// Note: Calling ctrl.Finish() at the end of a test function ensures that
// no unexpected calls to external keepers are made.
func GetProviderKeeperAndCtx(t *testing.T, params ututil.InMemKeeperParams) (
	providerkeeper.Keeper, sdk.Context, *gomock.Controller, ututil.MockedKeepers,
) {
	t.Helper()
	ctrl := gomock.NewController(t)
	mocks := ututil.NewMockedKeepers(ctrl)
	return NewInMemProviderKeeper(params, mocks), params.Ctx, ctrl, mocks
}

// SetupForStoppingConsumerChain registers expected mock calls and corresponding state setup
// which asserts that a consumer chain was properly stopped from StopConsumerChain().
func SetupForStoppingConsumerChain(t *testing.T, ctx sdk.Context,
	providerKeeper *providerkeeper.Keeper, mocks ututil.MockedKeepers,
) {
	t.Helper()
	expectations := ututil.GetMocksForCreateConsumerClient(ctx, &mocks,
		"chainID", clienttypes.NewHeight(4, 5))
	expectations = append(expectations, ututil.GetMocksForSetConsumerChain(ctx, &mocks, "chainID")...)
	expectations = append(expectations, ututil.GetMocksForStopConsumerChain(ctx, &mocks)...)

	gomock.InOrder(expectations...)

	prop := GetTestConsumerAdditionProp()
	err := providerKeeper.CreateConsumerClient(ctx, prop)
	require.NoError(t, err)
	err = providerKeeper.SetConsumerChain(ctx, "channelID")
	require.NoError(t, err)
}

func GetTestConsumerAdditionProp() *providertypes.ConsumerAdditionProposal {
	prop := providertypes.NewConsumerAdditionProposal(
		"chainID",
		"description",
		"chainID",
		clienttypes.NewHeight(4, 5),
		[]byte("gen_hash"),
		[]byte("bin_hash"),
		time.Now(),
		types.DefaultConsumerRedistributeFrac,
		types.DefaultBlocksPerDistributionTransmission,
		"",
		types.DefaultHistoricalEntries,
		types.DefaultCCVTimeoutPeriod,
		types.DefaultTransferTimeoutPeriod,
		types.DefaultConsumerUnbondingPeriod,
	).(*providertypes.ConsumerAdditionProposal)

	return prop
}
