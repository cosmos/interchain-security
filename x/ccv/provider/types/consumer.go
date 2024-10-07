package types

import (
	ccv "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

func NewConsumerStates(
	chainID,
	clientID,
	channelID string,
	initialHeight uint64,
	genesis ccv.ConsumerGenesisState,
	pendingValsetChanges []ccv.ValidatorSetChangePacketData,
	slashDowntimeAck []string,
	phase ConsumerPhase,
) ConsumerState {
	return ConsumerState{
		ChainId:              chainID,
		ClientId:             clientID,
		ChannelId:            channelID,
		InitialHeight:        initialHeight,
		PendingValsetChanges: pendingValsetChanges,
		ConsumerGenesis:      genesis,
		SlashDowntimeAck:     slashDowntimeAck,
		Phase:                phase,
	}
}
