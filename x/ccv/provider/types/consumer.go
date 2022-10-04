package types

import (
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func NewConsumerStates(
	chainID,
	clientID,
	channelID string,
	initialHeight uint64,
	lockUbdTimeout bool,
	genesis consumertypes.GenesisState,
	unbondingOpsIndexes []UnbondingOpIndex,
	pendingValsetChanges []ccv.ValidatorSetChangePacketData,
	slashDowntimeAck []string,
) ConsumerState {
	return ConsumerState{
		ChainId:                chainID,
		ClientId:               clientID,
		ChannelId:              channelID,
		InitialHeight:          initialHeight,
		LockUnbondingOnTimeout: true,
		UnbondingOpsIndex:      unbondingOpsIndexes,
		PendingValsetChanges:   pendingValsetChanges,
		ConsumerGenesis:        genesis,
		SlashDowntimeAck:       slashDowntimeAck,
	}
}
