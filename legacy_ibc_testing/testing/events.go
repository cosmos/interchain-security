package testing

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	connectiontypes "github.com/cosmos/ibc-go/v7/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
)

/*
TODO: Remove after upgrading to ibc-go v5
legacy_ibc_testing is temporarily copied into the interchain-security repository for the purpose of testing only.
The integration test suites rely on modifications to ibc-go's test framework that cannot be back-ported to the canonical version that ics will rely on.
These files will be deprecated once ICS is able to upgrade to ibc-go v5.
*/

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

// ParseAckFromEvents parses events emitted from a MsgRecvPacket and returns the
// acknowledgement.
func ParseAckFromEvents(events sdk.Events) ([]byte, error) {
	for _, ev := range events {
		if ev.Type == channeltypes.EventTypeWriteAck {
			for _, attr := range ev.Attributes {
				if string(attr.Key) == channeltypes.AttributeKeyAck {
					return []byte(attr.Value), nil
				}
			}
		}
	}
	return nil, fmt.Errorf("acknowledgement event attribute not found")
}
