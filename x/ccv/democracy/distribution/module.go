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

// AppModule embeds the Cosmos SDK's x/staking AppModuleBasic.
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

	// record the proposer for when we payout on the next block
	consAddr := sdk.ConsAddress(req.Header.ProposerAddress)
	am.keeper.SetPreviousProposerConsAddr(ctx, consAddr)
}

// AllocateTokens handles distribution of the collected fees
// bondedVotes is a list of (validator address, validator voted on last block flag) for all
// validators in the bonded set.
func (am AppModule) AllocateTokens(
	ctx sdk.Context,
) {

	// fetch and clear the collected fees for distribution, since this is
	// called in BeginBlock, collected fees will be from the previous block
	// (and distributed to the previous proposer)
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
	totalPower := vs.TotalBondedTokens(ctx)
	if totalPower.IsZero() {
		feePool.CommunityPool = feePool.CommunityPool.Add(feesCollected...)
		am.keeper.SetFeePool(ctx, feePool)
		return
	}

	// calculate fraction allocated to validators
	remaining := feesCollected
	communityTax := am.keeper.GetCommunityTax(ctx)
	voteMultiplier := sdk.OneDec().Sub(communityTax)

	// allocate tokens proportionally to voting power
	// TODO consider parallelizing later, ref https://github.com/cosmos/cosmos-sdk/pull/3099#discussion_r246276376

	vs.IterateBondedValidatorsByPower(ctx, func(_ int64, validator stakingtypes.ValidatorI) bool {

		// TODO consider microslashing for missing votes.
		// ref https://github.com/cosmos/cosmos-sdk/issues/2525#issuecomment-430838701
		powerFraction := sdk.NewDecFromInt(validator.GetTokens()).QuoTruncate(sdk.NewDecFromInt(totalPower))
		reward := feesCollected.MulDecTruncate(voteMultiplier).MulDecTruncate(powerFraction)
		am.keeper.AllocateTokensToValidator(ctx, validator, reward)
		remaining = remaining.Sub(reward)

		return false
	})

	// allocate community funding
	feePool.CommunityPool = feePool.CommunityPool.Add(remaining...)
	am.keeper.SetFeePool(ctx, feePool)
}
