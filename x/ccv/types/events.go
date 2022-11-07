package types

// CCV events
const (
	EventTypeTimeout      = "timeout"
	EventTypePacket       = "ccv_packet"
	EventTypeChannelClose = "channel_closed"

	EventTypeConsumerChainAdded       = "consumer_added"
	EventTypeFeeTransferChannelOpened = "fee_channel_opened"
	EventExecuteConsumerChainSlash    = "execute_consumer_chain_slash"
	EventTypeFirstVSCPacket           = "first_vsc_packet"
	EventTypeFeeDistribution          = "fee_distribution"
	EventTypeSendSlashPacket          = "send_slash_packet"
	EventTypeSendMaturedVSCPacket     = "send_matured_vsc_packet"

	AttributeKeyAckSuccess = "success"
	AttributeKeyAck        = "acknowledgement"
	AttributeKeyAckError   = "error"

	AttributeChainID               = "chain_id"
	AttributeValidatorAddress      = "validator_address"
	AttributeInfractionType        = "infraction_type"
	AttributeInfractionHeight      = "infraction_height"
	AttributeConsumerHeight        = "consumer_height"
	AttributeValSetUpdateID        = "valset_update_id"
	AttributeTimestamp             = "timestamp"
	AttributeInitialHeight         = "initial_height"
	AttributeInitializationTimeout = "initialization_timeout"
	AttributeTrustingPeriod        = "trusting_period"
	AttributeUnbondingPeriod       = "unbonding_period"

	AttributeDistributionCurrentHeight = "current_distribution_height"
	AttributeDistributionNextHeight    = "next_distribution_height"
	AttributeDistributionFraction      = "distribution_fraction"
	AttributeDistributionTotal         = "total"
	AttributeDistributionToConsumer    = "consumer_amount"
	AttributeDistributionToProvider    = "provider_amount"
)
