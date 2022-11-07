package distribution

import (
	"time"

	"github.com/cosmos/cosmos-sdk/codec"
	"github.com/cosmos/cosmos-sdk/types/module"

	"github.com/cosmos/cosmos-sdk/telemetry"
	sdk "github.com/cosmos/cosmos-sdk/types"
	distr "github.com/cosmos/cosmos-sdk/x/distribution"
	"github.com/cosmos/cosmos-sdk/x/distribution/keeper"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"

	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

var (
	_ module.AppModule           = AppModule{}
	_ module.AppModuleBasic      = AppModuleBasic{}
	_ module.AppModuleSimulation = AppModule{}
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
	bk distrtypes.BankKeeper, sk stakingkeeper.Keeper, feeCollectorName string,
) AppModule {
	distrAppMod := distr.NewAppModule(cdc, keeper, ak, bk, sk)
	return AppModule{
		AppModule:        distrAppMod,
		keeper:           keeper,
		accountKeeper:    ak,
		bankKeeper:       bk,
		stakingKeeper:    sk,
		feeCollectorName: feeCollectorName,
	}
}

// BeginBlocker mirror functionality of cosmos-sdk/distribution BeginBlocker
// however it allocates no proposer reward
func (am AppModule) BeginBlock(ctx sdk.Context, req abci.RequestBeginBlock) {
	defer telemetry.ModuleMeasureSince(distrtypes.ModuleName, time.Now(), telemetry.MetricKeyBeginBlocker)

	// TODO this is Tendermint-dependent
	// ref https://github.com/cosmos/cosmos-sdk/issues/3095
	if ctx.BlockHeight() > 1 {
		am.AllocateTokens(ctx)
	}
}

// AllocateTokens handles distribution of the collected fees
func (am AppModule) AllocateTokens(
	ctx sdk.Context,
) {

	// fetch and clear the collected fees for distribution, since this is
	// called in BeginBlock, collected fees will be from the previous block
	// (and distributed to the current representatives)
	feeCollector := am.accountKeeper.GetModuleAccount(ctx, consumertypes.ConsumerRedistributeName)
	feesCollectedInt := am.bankKeeper.GetAllBalances(ctx, feeCollector.GetAddress())
	feesCollected := sdk.NewDecCoinsFromCoins(feesCollectedInt...)

	// transfer collected fees to the distribution module account
	err := am.bankKeeper.SendCoinsFromModuleToModule(ctx, consumertypes.ConsumerRedistributeName, distrtypes.ModuleName, feesCollectedInt)
	if err != nil {
		panic(err)
	}

	// temporary workaround to keep CanWithdrawInvariant happy
	// general discussions here: https://github.com/cosmos/cosmos-sdk/issues/2906#issuecomment-441867634
	feePool := am.keeper.GetFeePool(ctx)
	vs := am.stakingKeeper.GetValidatorSet()
	totalBondedTokens := vs.TotalBondedTokens(ctx)
	if totalBondedTokens.IsZero() {
		feePool.CommunityPool = feePool.CommunityPool.Add(feesCollected...)
		am.keeper.SetFeePool(ctx, feePool)
		return
	}

	// calculate the fraction allocated to representatives by subtracting the community tax.
	// e.g. if community tax is 0.02, representatives fraction will be 0.98 (2% goes to the community pool and the rest to the representatives)
	remaining := feesCollected
	communityTax := am.keeper.GetCommunityTax(ctx)
	representativesFraction := sdk.OneDec().Sub(communityTax)

	// allocate tokens proportionally to representatives voting power
	vs.IterateBondedValidatorsByPower(ctx, func(_ int64, validator stakingtypes.ValidatorI) bool {
		//we get this validator's percentage of the total power by dividing their tokens by the total bonded tokens
		powerFraction := sdk.NewDecFromInt(validator.GetTokens()).QuoTruncate(sdk.NewDecFromInt(totalBondedTokens))
		//we truncate here again, which means that the reward will be slightly lower than it should be
		reward := feesCollected.MulDecTruncate(representativesFraction).MulDecTruncate(powerFraction)
		am.keeper.AllocateTokensToValidator(ctx, validator, reward)
		remaining = remaining.Sub(reward)

		return false
	})

	// allocate community funding
	//due to the 3 truncations above, remaining sent to the community pool will be slightly more than it should be. This is OK
	feePool.CommunityPool = feePool.CommunityPool.Add(remaining...)
	am.keeper.SetFeePool(ctx, feePool)
}
