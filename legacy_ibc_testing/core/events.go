package core

import (
	"strconv"

	abci "github.com/cometbft/cometbft/abci/types"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
)

/*
TODO: Remove after upgrading to ibc-go v5
legacy_ibc_testing is temporarily copied into the interchain-security repository for the purpose of testing only.
The integration test suites rely on modifications to ibc-go's test framework that cannot be back-ported to the canonical version that ics will rely on.
These files will be deprecated once ICS is able to upgrade to ibc-go v5.
*/

// ReconstructPacketFromEvent recreates a packet from an appropriate provided event
func ReconstructPacketFromEvent(event abci.Event) (packet types.Packet, err error) {
	attrMap := make(map[string][]byte)
	for _, attr := range event.Attributes {
		attrMap[string(attr.Key)] = []byte(attr.Value)
	}

	sequence, err := strconv.Atoi(string(attrMap[string(types.AttributeKeySequence)]))
	if err != nil {
		return packet, err
	}
	timeoutTimestamp, err := strconv.Atoi(string(attrMap[string(types.AttributeKeyTimeoutTimestamp)]))
	if err != nil {
		return packet, err
	}
	timeoutHeight, err := clienttypes.ParseHeight(string(attrMap[string(types.AttributeKeyTimeoutHeight)]))
	if err != nil {
		return packet, err
	}
	return types.NewPacket(
		attrMap[string(types.AttributeKeyData)], // data
		uint64(sequence),
		string(attrMap[string(types.AttributeKeySrcPort)]),    // sourcePort,
		string(attrMap[string(types.AttributeKeySrcChannel)]), // sourceChannel,
		string(attrMap[string(types.AttributeKeyDstPort)]),    // destinationPort,
		string(attrMap[string(types.AttributeKeyDstChannel)]), // destinationChannel string,
		timeoutHeight,
		uint64(timeoutTimestamp),
	), nil
}
