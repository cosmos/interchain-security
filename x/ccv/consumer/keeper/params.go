package keeper

import (
	"context"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// GetParams returns the params for the consumer ccv module
// NOTE: it is different from the GetParams method which is required to implement StakingKeeper interface
func (k Keeper) GetConsumerParams(ctx sdk.Context) (ccvtypes.Params, error) {
	store := k.storeService.OpenKVStore(ctx)
	bz, err := store.Get(types.ParametersKey())
	if err != nil {
		return ccvtypes.Params{}, err //TODO @bermuell: check if default arguments or error handling should be done
	}
	var params ccvtypes.Params
	k.cdc.MustUnmarshal(bz, &params)
	return params, nil
}

// SetParams sets the paramset for the consumer module
func (k Keeper) SetParams(ctx sdk.Context, params ccvtypes.Params) error {
	if err := params.Validate(); err != nil {
		return err
	}
	store := k.storeService.OpenKVStore(ctx)
	bz := k.cdc.MustMarshal(&params)
	return store.Set(types.ParametersKey(), bz)
}

// GetParams implements StakingKeeper GetParams interface method
// it returns an a empty stakingtypes.Params struct
// NOTE: this method must be implemented on the consumer keeper because the evidence module keeper
// in cosmos-sdk v0.50 requires this exact method with this exact signature to be available on the StakingKeepr
func (k Keeper) GetParams(context.Context) (stakingtypes.Params, error) {
	return stakingtypes.Params{}, nil
}

// GetEnabled returns the enabled flag for the consumer module
func (k Keeper) GetEnabled(ctx sdk.Context) bool {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'enabled': %v", err)
		return ccvtypes.Params{}.Enabled
	}
	return params.Enabled
}

func (k Keeper) GetBlocksPerDistributionTransmission(ctx sdk.Context) int64 {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'BlocksPerDistributionTransmission': %v", err)
		return ccvtypes.Params{}.BlocksPerDistributionTransmission
	}

	return params.BlocksPerDistributionTransmission
}

func (k Keeper) SetBlocksPerDistributionTransmission(ctx sdk.Context, bpdt int64) {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error setting parameter 'BlocksPerDistributionTransmission': %v", err)
		return
	}
	params.BlocksPerDistributionTransmission = bpdt
	k.SetParams(ctx, params)
}

func (k Keeper) GetDistributionTransmissionChannel(ctx sdk.Context) string {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'DistributionTransmissionChannel': %v", err)
		return ccvtypes.Params{}.DistributionTransmissionChannel
	}
	return params.DistributionTransmissionChannel
}

func (k Keeper) SetDistributionTransmissionChannel(ctx sdk.Context, channel string) {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error setting parameter 'DistributionTransmissionChannel': %v", err)
		return
	}
	params.DistributionTransmissionChannel = channel
	k.SetParams(ctx, params)
}

func (k Keeper) GetProviderFeePoolAddrStr(ctx sdk.Context) string {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'ProviderFeePoolAddrStr': %v", err)
		return ccvtypes.Params{}.ProviderFeePoolAddrStr
	}
	return params.ProviderFeePoolAddrStr

}

func (k Keeper) SetProviderFeePoolAddrStr(ctx sdk.Context, addr string) {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error setting parameter 'ProviderFeePoolAddrStr': %v", err)
		return
	}
	params.ProviderFeePoolAddrStr = addr
	k.SetParams(ctx, params)
}

// GetCCVTimeoutPeriod returns the timeout period for sent ccv related ibc packets
func (k Keeper) GetCCVTimeoutPeriod(ctx sdk.Context) time.Duration {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'CcvTimeoutPeriod': %v", err)
		return ccvtypes.Params{}.CcvTimeoutPeriod
	}
	return params.CcvTimeoutPeriod
}

// GetTransferTimeoutPeriod returns the timeout period for sent transfer related ibc packets
func (k Keeper) GetTransferTimeoutPeriod(ctx sdk.Context) time.Duration {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'TransferTimeoutPeriod': %v", err)
		return ccvtypes.Params{}.TransferTimeoutPeriod
	}
	return params.TransferTimeoutPeriod

}

// GetConsumerRedistributionFrac returns the fraction of tokens allocated to the consumer redistribution
// address during distribution events. The fraction is a string representing a
// decimal number. For example "0.75" would represent 75%.
func (k Keeper) GetConsumerRedistributionFrac(ctx sdk.Context) string {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'ConsumerRedistributionFraction': %v", err)
		return ccvtypes.Params{}.ConsumerRedistributionFraction
	}
	return params.ConsumerRedistributionFraction

}

// GetHistoricalEntries returns the number of historical info entries to persist in store
func (k Keeper) GetHistoricalEntries(ctx sdk.Context) int64 {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'HistoricalEntries': %v", err)
		return ccvtypes.Params{}.HistoricalEntries
	}
	return params.HistoricalEntries
}

// Only used to set an unbonding period in diff tests
// TODO @bermuell: move this to testutil
func (k Keeper) SetUnbondingPeriod(ctx sdk.Context, period time.Duration) {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error setting parameter 'UnbondingPeriod': %v", err)
		return
	}
	params.UnbondingPeriod = period
	k.SetParams(ctx, params)
}

// GetUnbondingPeriod returns the unbonding period of the consumer
func (k Keeper) GetUnbondingPeriod(ctx sdk.Context) time.Duration {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'UnbondingPeriod': %v", err)
		return ccvtypes.Params{}.UnbondingPeriod
	}
	return params.UnbondingPeriod
}

// GetSoftOptOutThreshold returns the percentage of validators at the bottom of the set
// that can opt out of running the consumer chain
func (k Keeper) GetSoftOptOutThreshold(ctx sdk.Context) string {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'SoftOptOutThreshold': %v", err)
		return ccvtypes.Params{}.SoftOptOutThreshold
	}
	return params.SoftOptOutThreshold
}

func (k Keeper) GetRewardDenoms(ctx sdk.Context) []string {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'RewardDenoms': %v", err)
		return ccvtypes.Params{}.RewardDenoms
	}
	return params.RewardDenoms
}

func (k Keeper) GetProviderRewardDenoms(ctx sdk.Context) []string {
	params, err := k.GetConsumerParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'UnbondingPeriod': %v", err)
		return ccvtypes.Params{}.ProviderRewardDenoms
	}
	return params.ProviderRewardDenoms
}
