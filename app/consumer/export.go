package app

import (
	"encoding/json"
	"log"

	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	servertypes "github.com/cosmos/cosmos-sdk/server/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	ibcconsumer "github.com/cosmos/interchain-security/x/ccv/consumer"
)

// ExportAppStateAndValidators exports the state of the application for a genesis
// file.
func (app *App) ExportAppStateAndValidators(
	forZeroHeight bool, jailAllowedAddrs []string,
) (servertypes.ExportedApp, error) {

	// as if they could withdraw from the start of the next block
	ctx := app.NewContext(true, tmproto.Header{Height: app.LastBlockHeight()})

	// We export at last height + 1, because that's the height at which
	// Tendermint will start InitChain.
	height := app.LastBlockHeight() + 1
	if forZeroHeight {
		height = 0
		app.prepForZeroHeightGenesis(ctx, jailAllowedAddrs)
	}

	genState := app.MM.ExportGenesis(ctx, app.appCodec)
	appState, err := json.MarshalIndent(genState, "", "  ")
	if err != nil {
		return servertypes.ExportedApp{}, err
	}

	validators, err := ibcconsumer.WriteValidators(ctx, app.ConsumerKeeper)
	if err != nil {
		return servertypes.ExportedApp{}, err
	}
	return servertypes.ExportedApp{
		AppState:        appState,
		Validators:      validators,
		Height:          height,
		ConsensusParams: app.BaseApp.GetConsensusParams(ctx),
	}, nil
}

// prepare for fresh start at zero height
// NOTE zero height genesis is a temporary feature which will be deprecated
//      in favour of export at a block height
func (app *App) prepForZeroHeightGenesis(ctx sdk.Context, jailAllowedAddrs []string) {
	// TODO: decide whether this can be removed permanentely
	// applyAllowedAddrs := false

	// // check if there is a allowed address list
	// if len(jailAllowedAddrs) > 0 {
	// 	applyAllowedAddrs = true
	// }

	allowedAddrsMap := make(map[string]bool)

	for _, addr := range jailAllowedAddrs {
		_, err := sdk.ValAddressFromBech32(addr)
		if err != nil {
			log.Fatal(err)
		}
		allowedAddrsMap[addr] = true
	}

	/* Just to be safe, assert the invariants on current state. */
	app.CrisisKeeper.AssertInvariants(ctx)

	/* Handle fee distribution state. */

	// withdraw all validator commission
	// TODO: add back with gov-staking
	// app.ConsumerKeeper.IterateValidators(ctx, func(_ int64, val stakingtypes.ValidatorI) (stop bool) {
	// _, err := app.DistrKeeper.WithdrawValidatorCommission(ctx, val.GetOperator())
	// if err != nil {
	// 	panic(err)
	// }
	// 	return false
	// })

	// withdraw all delegator rewards
	// TODO: add back with gov-staking
	// dels := app.ConsumerKeeper.GetAllDelegations(ctx)
	// for _, delegation := range dels {
	// 	_, err := app.DistrKeeper.WithdrawDelegationRewards(ctx, delegation.GetDelegatorAddr(), delegation.GetValidatorAddr())
	// 	if err != nil {
	// 		panic(err)
	// 	}
	// }

	// TODO: add back with gov-staking
	// clear validator slash events
	// app.DistrKeeper.DeleteAllValidatorSlashEvents(ctx)

	// TODO: add back with gov-staking
	// clear validator historical rewards
	// app.DistrKeeper.DeleteAllValidatorHistoricalRewards(ctx)

	// set context height to zero
	height := ctx.BlockHeight()
	ctx = ctx.WithBlockHeight(0)

	// reinitialize all validators
	// TODO: add back with gov-staking
	// app.ConsumerKeeper.IterateValidators(ctx, func(_ int64, val stakingtypes.ValidatorI) (stop bool) {
	// 	// donate any unwithdrawn outstanding reward fraction tokens to the community pool
	// 	scraps := app.DistrKeeper.GetValidatorOutstandingRewardsCoins(ctx, val.GetOperator())
	// 	feePool := app.DistrKeeper.GetFeePool(ctx)
	// 	feePool.CommunityPool = feePool.CommunityPool.Add(scraps...)
	// 	app.DistrKeeper.SetFeePool(ctx, feePool)

	// 	app.DistrKeeper.Hooks().AfterValidatorCreated(ctx, val.GetOperator())
	// 	return false
	// })

	// reinitialize all delegations
	// for _, del := range dels {
	// 	app.DistrKeeper.Hooks().BeforeDelegationCreated(ctx, del.GetDelegatorAddr(), del.GetValidatorAddr())
	// 	app.DistrKeeper.Hooks().AfterDelegationModified(ctx, del.GetDelegatorAddr(), del.GetValidatorAddr())
	// }

	// reset context height
	ctx = ctx.WithBlockHeight(height)

	/* Handle staking state. */

	// TODO: decide whether this can be removed permanentely
	// // iterate through redelegations, reset creation height
	// app.ConsumerKeeper.IterateRedelegations(ctx, func(_ int64, red stakingtypes.Redelegation) (stop bool) {
	// 	for i := range red.Entries {
	// 		red.Entries[i].CreationHeight = 0
	// 	}
	// 	app.ConsumerKeeper.SetRedelegation(ctx, red)
	// 	return false
	// })

	// TODO: decide whether this can be removed permanentely
	// // iterate through unbonding delegations, reset creation height
	// app.ConsumerKeeper.IterateUnbondingDelegations(ctx, func(_ int64, ubd stakingtypes.UnbondingDelegation) (stop bool) {
	// 	for i := range ubd.Entries {
	// 		ubd.Entries[i].CreationHeight = 0
	// 	}
	// 	app.ConsumerKeeper.SetUnbondingDelegation(ctx, ubd)
	// 	return false
	// })

	// TODO: decide whether this can be removed permanentely
	// // Iterate through validators by power descending, reset bond heights, and
	// // update bond intra-tx counters.
	// store := ctx.KVStore(app.keys[stakingtypes.StoreKey])
	// iter := sdk.KVStoreReversePrefixIterator(store, stakingtypes.ValidatorsKey)
	// counter := int16(0)

	// for ; iter.Valid(); iter.Next() {
	// 	addr := sdk.ValAddress(iter.Key()[1:])
	// 	validator, found := app.ConsumerKeeper.GetValidator(ctx, addr)
	// 	if !found {
	// 		panic("expected validator, not found")
	// 	}

	// 	validator.UnbondingHeight = 0
	// 	if applyAllowedAddrs && !allowedAddrsMap[addr.String()] {
	// 		validator.Jailed = true
	// 	}

	// 	app.ConsumerKeeper.SetValidator(ctx, validator)
	// 	counter++
	// }

	// iter.Close()

	// if _, err := app.ConsumerKeeper.ApplyAndReturnValidatorSetUpdates(ctx); err != nil {
	// 	panic(err)
	// }

	/* Handle slashing state. */

	// reset start height on signing infos
	app.SlashingKeeper.IterateValidatorSigningInfos(
		ctx,
		func(addr sdk.ConsAddress, info slashingtypes.ValidatorSigningInfo) (stop bool) {
			info.StartHeight = 0
			app.SlashingKeeper.SetValidatorSigningInfo(ctx, addr, info)
			return false
		},
	)
}
