package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

func NewConsumerStates(
	chainID,
	clientID,
	channelID string,
	initialHeight uint64,
	genesis ccv.ConsumerGenesisState,
	unbondingOpsIndexes []VscUnbondingOps,
	pendingValsetChanges []ccv.ValidatorSetChangePacketData,
	slashDowntimeAck []string,
) ConsumerState {
	return ConsumerState{
		ChainId:              chainID,
		ClientId:             clientID,
		ChannelId:            channelID,
		InitialHeight:        initialHeight,
		UnbondingOpsIndex:    unbondingOpsIndexes,
		PendingValsetChanges: pendingValsetChanges,
		ConsumerGenesis:      genesis,
		SlashDowntimeAck:     slashDowntimeAck,
	}
}

// zero consumer rewards allocation
func InitialConsumerRewardsAllocation() ConsumerRewardsAllocation {
	return ConsumerRewardsAllocation{
		Rewards: sdk.DecCoins{},
	}
}
