package distribution

import (
	"context"
	"time"

	"cosmossdk.io/core/appmodule"
	"cosmossdk.io/math"
	"github.com/cosmos/cosmos-sdk/codec"
	"github.com/cosmos/cosmos-sdk/telemetry"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"
	distr "github.com/cosmos/cosmos-sdk/x/distribution"
	"github.com/cosmos/cosmos-sdk/x/distribution/exported"
	"github.com/cosmos/cosmos-sdk/x/distribution/keeper"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
)

var (
	_ module.AppModule           = AppModule{}
	_ module.AppModuleBasic      = AppModuleBasic{}
	_ module.AppModuleSimulation = AppModule{}

	_ appmodule.AppModule       = AppModule{}
	_ appmodule.HasBeginBlocker = AppModule{}
)

// AppModule embeds the Cosmos SDK's x/distribution AppModuleBasic.
type AppModuleBasic struct {
	distr.AppModuleBasic
}

// AppModule embeds the Cosmos SDK's x/distribution AppModule
type AppModule struct {
	// embed the Cosmos SDK's x/distribution AppModule
	distr.AppModule

	keeper        keeper.Keeper
	accountKeeper distrtypes.AccountKeeper
	bankKeeper    distrtypes.BankKeeper
	stakingKeeper stakingkeeper.Keeper

	feeCollectorName string
}

// NewAppModule creates a new AppModule object using the native x/distribution module
// AppModule constructor.
func NewAppModule(
	cdc codec.Codec, keeper keeper.Keeper, ak distrtypes.AccountKeeper,
	bk distrtypes.BankKeeper, sk stakingkeeper.Keeper, feeCollectorName string, subspace exported.Subspace,
) AppModule {
	distrAppMod := distr.NewAppModule(cdc, keeper, ak, bk, sk, subspace)
	return AppModule{
		AppModule:        distrAppMod,
		keeper:           keeper,
		accountKeeper:    ak,
		bankKeeper:       bk,
		stakingKeeper:    sk,
		feeCollectorName: feeCollectorName,
	}
}

// BeginBlock implements HasBeginBlocker interface
// The cosmos-sdk/distribution BeginBlocker functionality is replicated here,
// however no proposer awards are allocated.
func (am AppModule) BeginBlock(goCtx context.Context) error {
	ctx := sdk.UnwrapSDKContext(goCtx)
	defer telemetry.ModuleMeasureSince(distrtypes.ModuleName, time.Now(), telemetry.MetricKeyBeginBlocker)

	// TODO this is Tendermint-dependent
	// ref https://github.com/cosmos/cosmos-sdk/issues/3095
	if ctx.BlockHeight() > 1 {
		return am.AllocateTokens(ctx)
	}

	return nil
}

// AllocateTokens handles distribution of the collected fees
// NOTE: refactored to use collections (FeePool.Get instead of GetFeePool) for v47 -> v50 migration
func (am AppModule) AllocateTokens(
	ctx sdk.Context,
) error {
	// fetch and clear the collected fees for distribution, since this is
	// called in BeginBlock, collected fees will be from the previous block
	// (and distributed to the current representatives)
	feeCollector := am.accountKeeper.GetModuleAccount(ctx, consumertypes.ConsumerRedistributeName)
	feesCollectedInt := am.bankKeeper.GetAllBalances(ctx, feeCollector.GetAddress())
	feesCollected := sdk.NewDecCoinsFromCoins(feesCollectedInt...)

	// transfer collected fees to the distribution module account
	err := am.bankKeeper.SendCoinsFromModuleToModule(ctx, consumertypes.ConsumerRedistributeName, distrtypes.ModuleName, feesCollectedInt)
	if err != nil {
		return err
	}

	// temporary workaround to keep CanWithdrawInvariant happy
	// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
	feePool, err := am.keeper.FeePool.Get(ctx)
	if err != nil {
		return err
	}
	vs := am.stakingKeeper.GetValidatorSet()
	totalBondedTokens, err := vs.TotalBondedTokens(ctx)
	if err != nil {
		return err
	}
	if totalBondedTokens.IsZero() {
		feePool.CommunityPool = feePool.CommunityPool.Add(feesCollected...)
		if err := am.keeper.FeePool.Set(ctx, feePool); err != nil {
			return err
		}
		return nil
	}

	// calculate the fraction allocated to representatives by subtracting the community tax.
	// e.g. if community tax is 0.02, representatives fraction will be 0.98 (2% goes to the community pool and the rest to the representatives)
	remaining := feesCollected
	communityTax, err := am.keeper.GetCommunityTax(ctx)
	if err != nil {
		return err
	}
	representativesFraction := math.LegacyOneDec().Sub(communityTax)

	// allocate tokens proportionally to representatives voting power
	_ = vs.IterateBondedValidatorsByPower(ctx, func(_ int64, validator stakingtypes.ValidatorI) bool {
		// we get this validator's percentage of the total power by dividing their tokens by the total bonded tokens
		powerFraction := math.LegacyNewDecFromInt(validator.GetTokens()).QuoTruncate(math.LegacyNewDecFromInt(totalBondedTokens))
		// we truncate here again, which means that the reward will be slightly lower than it should be
		reward := feesCollected.MulDecTruncate(representativesFraction).MulDecTruncate(powerFraction)
		_ = am.keeper.AllocateTokensToValidator(ctx, validator, reward)
		remaining = remaining.Sub(reward)

		return false
	})

	// allocate community funding
	// due to the 3 truncations above, remaining sent to the community pool will be slightly more than it should be. This is OK
	feePool.CommunityPool = feePool.CommunityPool.Add(remaining...)
	if err := am.keeper.FeePool.Set(ctx, feePool); err != nil {
		return err
	}

	return nil
}
