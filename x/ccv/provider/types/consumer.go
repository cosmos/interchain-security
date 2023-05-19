package types

import (
	consumertypes "github.com/octopus-network/interchain-security/x/ccv/consumer/types"
	ccv "github.com/octopus-network/interchain-security/x/ccv/types"
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
