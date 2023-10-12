package types

// CCV events
const (
	EventTypeTimeout            = "timeout"
	EventTypePacket             = "ccv_packet"
	EventTypeChannelEstablished = "channel_established"

	AttributeKeyAckSuccess = "success"
	AttributeKeyAck        = "acknowledgement"
	AttributeKeyAckError   = "error"

	AttributeChainID          = "chain_id"
	AttributeValidatorAddress = "validator_address"
	AttributeInfractionType   = "infraction_type"

	AttributeValSetUpdateID = "valset_update_id"
)
