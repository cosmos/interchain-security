package types

const (
	AttributeConsumerHeight = "consumer_height"
	AttributeTimestamp      = "timestamp"

	EventTypeFeeDistribution          = "fee_distribution"
	EventTypeVSCMatured               = "vsc_matured"
	EventTypeConsumerSlashRequest     = "consumer_slash_request"
	EventTypeFeeTransferChannelOpened = "fee_transfer_channel_opened"

	//#nosec G101 -- (false positive) this is not a hardcoded credential
	AttributeDistributionCurrentHeight = "current_distribution_height"
	AttributeDistributionNextHeight    = "next_distribution_height"
	AttributeDistributionFraction      = "distribution_fraction"
	AttributeDistributionTotal         = "total"
	AttributeDistributionToProvider    = "provider_amount"
)
