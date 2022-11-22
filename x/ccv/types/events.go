package types

// CCV events
const (
	EventTypeTimeout                  = "timeout"
	EventTypePacket                   = "ccv_packet"
	EventTypeChannelEstablished       = "channel_established"
	EventTypeFeeTransferChannelOpened = "fee_transfer_channel_opened"
	EventTypeConsumerClientCreated    = "consumer_client_created"

	EventTypeExecuteConsumerChainSlash = "execute_consumer_chain_slash"
	EventTypeFeeDistribution           = "fee_distribution"
	EventTypeConsumerSlashRequest      = "consumer_slash_request"
	EventTypeVSCMatured                = "vsc_matured"

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
