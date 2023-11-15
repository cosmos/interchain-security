package types

const (
	AttributeConsumerHeight = "consumer_height"
	AttributeTimestamp      = "timestamp"

	EventTypeFeeDistribution          = "fee_distribution"
	EventTypeVSCMatured               = "vsc_matured"
	EventTypeConsumerSlashRequest     = "consumer_slash_request"
	EventTypeFeeTransferChannelOpened = "fee_transfer_channel_opened"

	AttributeDistributionCurrentHeight = "current_distribution_height"
	//#nosec G101 -- (false positive) this is not a hardcoded credential
	AttributeDistributionNextHeight = "next_distribution_height"
	AttributeDistributionFraction   = "distribution_fraction"
	AttributeDistributionTotal      = "total"
	AttributeDistributionToProvider = "provider_amount"
)
