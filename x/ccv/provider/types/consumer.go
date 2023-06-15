package types

import (
	consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/v2/x/ccv/types"
)

func NewConsumerStates(
	chainID,
	clientID,
	channelID string,
	initialHeight uint64,
	genesis consumertypes.GenesisState,
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
