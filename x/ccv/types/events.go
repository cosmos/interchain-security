package types

// CCV events
const (
	EventTypeTimeout      = "timeout"
	EventTypePacket       = "ccv_packet"
	EventTypeChannelClose = "channel_closed"

	EventTypeConsumerChainAdded       = "ccv_consumer_added"
	EventTypeFeeTransferChannelOpened = "ccv_fee_channel_opened"

	AttributeKeyAckSuccess = "success"
	AttributeKeyAck        = "acknowledgement"
	AttributeKeyAckError   = "error"

	AttributeChainID = "chain_id"
)
