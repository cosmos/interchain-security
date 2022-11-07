package types

// CCV events
const (
	EventTypeTimeout      = "timeout"
	EventTypePacket       = "ccv_packet"
	EventTypeChannelClose = "channel_closed"

	EventTypeConsumerChainAdded       = "ccv_consumer_added"
	EventTypeFeeTransferChannelOpened = "ccv_fee_channel_opened"
	EventExecuteConsumerChainSlash    = "ccv_execute_consumer_chain_slash"

	AttributeKeyAckSuccess = "success"
	AttributeKeyAck        = "acknowledgement"
	AttributeKeyAckError   = "error"

	AttributeChainID          = "chain_id"
	AttributeValidatorAddres  = "validator_address"
	AttributeInfraction       = "infraction"
	AttributeInfractionHeight = "infraction_height"
	AttributeValSetUpdateID   = "valset_update_id"
)
