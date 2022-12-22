package ibctesting

import (
	"fmt"
	"strconv"

	sdk "github.com/cosmos/cosmos-sdk/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	connectiontypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	"github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// ParseClientIDFromEvents parses events emitted from a MsgCreateClient and returns the
// client identifier.
func ParseClientIDFromEvents(events sdk.Events) (string, error) {
	for _, ev := range events {
		if ev.Type == clienttypes.EventTypeCreateClient {
			for _, attr := range ev.Attributes {
				if string(attr.Key) == clienttypes.AttributeKeyClientID {
					return string(attr.Value), nil
				}
			}
		}
	}
	return "", fmt.Errorf("client identifier event attribute not found")
}

// ParseConnectionIDFromEvents parses events emitted from a MsgConnectionOpenInit or
// MsgConnectionOpenTry and returns the connection identifier.
func ParseConnectionIDFromEvents(events sdk.Events) (string, error) {
	for _, ev := range events {
		if ev.Type == connectiontypes.EventTypeConnectionOpenInit ||
			ev.Type == connectiontypes.EventTypeConnectionOpenTry {
			for _, attr := range ev.Attributes {
				if string(attr.Key) == connectiontypes.AttributeKeyConnectionID {
					return string(attr.Value), nil
				}
			}
		}
	}
	return "", fmt.Errorf("connection identifier event attribute not found")
}

// ParseChannelIDFromEvents parses events emitted from a MsgChannelOpenInit or
// MsgChannelOpenTry and returns the channel identifier.
func ParseChannelIDFromEvents(events sdk.Events) (string, error) {
	for _, ev := range events {
		if ev.Type == channeltypes.EventTypeChannelOpenInit || ev.Type == channeltypes.EventTypeChannelOpenTry {
			for _, attr := range ev.Attributes {
				if string(attr.Key) == channeltypes.AttributeKeyChannelID {
					return string(attr.Value), nil
				}
			}
		}
	}
	return "", fmt.Errorf("channel identifier event attribute not found")
}

// ParsePacketFromEvents parses events emitted from a MsgRecvPacket and returns the
// acknowledgement.
func ParsePacketFromEvents(events sdk.Events) (channeltypes.Packet, error) {
	for _, ev := range events {
		if ev.Type == channeltypes.EventTypeSendPacket {
			packet := channeltypes.Packet{}
			for _, attr := range ev.Attributes {
				switch string(attr.Key) {
				case channeltypes.AttributeKeyData:
					packet.Data = attr.Value

				case channeltypes.AttributeKeySequence:
					seq, err := strconv.ParseUint(string(attr.Value), 10, 64)
					if err != nil {
						return channeltypes.Packet{}, err
					}

					packet.Sequence = seq

				case channeltypes.AttributeKeySrcPort:
					packet.SourcePort = string(attr.Value)

				case channeltypes.AttributeKeySrcChannel:
					packet.SourceChannel = string(attr.Value)

				case channeltypes.AttributeKeyDstPort:
					packet.DestinationPort = string(attr.Value)

				case channeltypes.AttributeKeyDstChannel:
					packet.DestinationChannel = string(attr.Value)

				case channeltypes.AttributeKeyTimeoutHeight:
					height, err := clienttypes.ParseHeight(string(attr.Value))
					if err != nil {
						return channeltypes.Packet{}, err
					}

					packet.TimeoutHeight = height

				case channeltypes.AttributeKeyTimeoutTimestamp:
					timestamp, err := strconv.ParseUint(string(attr.Value), 10, 64)
					if err != nil {
						return channeltypes.Packet{}, err
					}

					packet.TimeoutTimestamp = timestamp

				default:
					continue
				}
			}

			return packet, nil
		}
	}
	return channeltypes.Packet{}, fmt.Errorf("acknowledgement event attribute not found")
}

// ParseAckFromEvents parses events emitted from a MsgRecvPacket and returns the
// acknowledgement.
func ParseAckFromEvents(events sdk.Events) ([]byte, error) {
	for _, ev := range events {
		if ev.Type == channeltypes.EventTypeWriteAck {
			for _, attr := range ev.Attributes {
				if string(attr.Key) == channeltypes.AttributeKeyAck {
					return attr.Value, nil
				}
			}
		}
	}
	return nil, fmt.Errorf("acknowledgement event attribute not found")
}

// ReconstructPacketFromEvent recreates a packet from an appropriate provided event
func ReconstructPacketFromEvent(event abci.Event) (packet types.Packet, err error) {
	attrMap := make(map[string][]byte)
	for _, attr := range event.Attributes {
		attrMap[string(attr.Key)] = attr.Value
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
		string(attrMap[string(types.AttributeKeySrcPort)]),    //sourcePort,
		string(attrMap[string(types.AttributeKeySrcChannel)]), //sourceChannel,
		string(attrMap[string(types.AttributeKeyDstPort)]),    //destinationPort,
		string(attrMap[string(types.AttributeKeyDstChannel)]), //destinationChannel string,
		timeoutHeight,
		uint64(timeoutTimestamp),
	), nil
}
